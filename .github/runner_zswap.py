#!/usr/bin/env python3
"""One ephemeral Linux trial: bounded zswap, unchanged child command, full telemetry.

No swapoff, packages, compressor changes, persistent configuration or
native timeout override. Privileged operations are confined to two sysfs writes
and read-only snapshots, plus a temporary debugfs mount if absent; the child
command runs as the invoking ordinary user.
"""
import argparse
import collections
import gzip
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import time

PARAMS = ("enabled", "max_pool_percent", "compressor", "zpool",
          "accept_threshold_percent", "shrinker_enabled")
COUNTERS = ("pool_total_size", "stored_pages", "pool_limit_hit",
            "written_back_pages", "reject_reclaim_fail", "reject_alloc_fail",
            "reject_kmemcache_fail", "reject_compress_fail",
            "reject_compress_poor", "decompress_fail")
CGFILES = ("memory.max", "memory.current", "memory.peak", "memory.events",
           "memory.events.local", "memory.swap.max", "memory.swap.current",
           "memory.zswap.max", "memory.zswap.current", "memory.zswap.writeback")
INTERVAL = 15
GUARD = 64 * 1024**2
KERNEL_FATAL = re.compile(r"Out of memory:|Killed process \d+|BUG:|Oops:|"
                          r"general protection fault|Kernel panic|memory corruption",
                          re.IGNORECASE)


class Unsafe(RuntimeError):
    pass


def integer(value):
    if not re.fullmatch(r"\d+", value):
        raise Unsafe(f"Invalid unsigned integer: {value!r}")
    return int(value)


def enabled(value):
    if value in ("Y", "1"):
        return True
    if value in ("N", "0"):
        return False
    raise Unsafe(f"Invalid boolean: {value!r}")


def key_values(text, units=False):
    result = {}
    for line in text.splitlines():
        words = line.replace(":", " ").split()
        if len(words) < 2:
            raise Unsafe(f"Malformed metric: {line!r}")
        value = integer(words[1])
        if units and len(words) == 3:
            if words[2] != "kB":
                raise Unsafe(f"Unknown metric unit: {line!r}")
            value *= 1024
        elif len(words) != 2:
            raise Unsafe(f"Malformed metric units: {line!r}")
        result[words[0]] = value
    return result


def swaps(text):
    lines = text.splitlines()
    if not lines or lines[0].split() != ["Filename", "Type", "Size", "Used", "Priority"]:
        raise Unsafe("Unexpected /proc/swaps header")
    result = []
    for line in lines[1:]:
        fields = line.split()
        if len(fields) != 5 or fields[1] not in ("file", "partition"):
            raise Unsafe(f"Unexpected swap record: {line!r}")
        name = re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), fields[0])
        size, used = integer(fields[2]) * 1024, integer(fields[3]) * 1024
        if size <= 0 or used > size or not re.fullmatch(r"-?\d+", fields[4]):
            raise Unsafe("Invalid swap capacity/priority")
        result.append(dict(name=name, type=fields[1], bytes=size,
                           used_bytes=used, priority=int(fields[4])))
    if not result:
        raise Unsafe("No active ordinary disk swap")
    if any(re.search(r"(?:^|/)zram\d+$", os.path.realpath(x["name"])) for x in result):
        raise Unsafe("Active zram swap: do not stack compression")
    return result


def budget(memtotal, limits, page_size):
    if memtotal <= 0 or page_size <= 0:
        raise Unsafe("Invalid physical memory/page size")
    effective = min([memtotal] + [integer(x) for x in limits if x != "max"])
    target = min(effective // 5, 4 * 1024**3)
    # Compute the ratio before byte rounding; two successive floors can turn
    # an exact 10% allowance into 9% merely because E/5 is not integral.
    percent = min(20 * effective // memtotal, 100 * (4 * 1024**3) // memtotal)
    if not 1 <= percent <= 20:
        raise Unsafe("Memory budget cannot represent a safe positive pool percentage")
    nominal = (memtotal // page_size * percent // 100) * page_size
    return dict(memtotal_bytes=memtotal, effective_bytes=effective,
                target_bytes=target, max_pool_percent=percent,
                nominal_pool_bytes=nominal, guard_bytes=GUARD,
                watchdog_bytes=nominal + GUARD, page_size=page_size,
                limitation="Admission limit, not total kernel/job RAM hard cap; sampling misses short peaks.")


def pressure(text):
    result = {}
    for line in text.splitlines():
        words = line.split()
        if len(words) != 5 or words[0] not in ("some", "full"):
            raise Unsafe("Malformed memory pressure record")
        values = {}
        for item in words[1:]:
            key, sep, value = item.partition("=")
            if not sep or key not in ("avg10", "avg60", "avg300", "total"):
                raise Unsafe("Malformed memory pressure value")
            if key == "total":
                values[key] = integer(value)
            else:
                if not re.fullmatch(r"\d+\.\d+", value):
                    raise Unsafe("Malformed memory pressure average")
                values[key] = float(value)
        if set(values) != {"avg10", "avg60", "avg300", "total"}:
            raise Unsafe("Missing memory pressure values")
        result[words[0]] = values
    if set(result) != {"some", "full"}:
        raise Unsafe("Missing memory pressure records")
    return result


class Linux:
    def __init__(self, prefix=Path("/")):
        self.prefix = Path(prefix)

    def path(self, name):
        return self.prefix / name.lstrip("/")

    def read(self, name):
        try:
            return self.path(name).read_text().strip()
        except OSError as exc:
            raise Unsafe(f"Required read failed: {name}: {exc}") from exc

    def optional(self, name):
        if not self.path(name).exists():
            return None
        return self.read(name)

    def parameters(self):
        return {key: self.read(f"/sys/module/zswap/parameters/{key}") for key in PARAMS}

    def zswap_counters(self):
        return {x: integer(self.read(f"/sys/kernel/debug/zswap/{x}")) for x in COUNTERS}

    def cgroups(self, pid):
        rows = self.read(f"/proc/{pid}/cgroup").splitlines()
        unified = [x[3:] for x in rows if x.startswith("0::")]
        if len(unified) != 1 or not unified[0].startswith("/") or ".." in Path(unified[0]).parts:
            raise Unsafe("Cannot establish unified cgroup path")
        mounts = []
        for line in self.read(f"/proc/{pid}/mountinfo").splitlines():
            left, sep, right = line.partition(" - ")
            if sep and right.split()[0] == "cgroup2":
                fields = left.split()
                root = re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), fields[3])
                mount = re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), fields[4])
                mounts.append((root, mount))
        if len(mounts) != 1 or mounts[0][0] != "/":
            raise Unsafe("Cannot establish full cgroup ancestor hierarchy")
        mount = Path(mounts[0][1])
        current = mount / unified[0].lstrip("/")
        nodes = []
        while True:
            values = {name: self.optional(str(current / name)) for name in CGFILES}
            if current != mount:
                for name in ("memory.max", "memory.current", "memory.events", "memory.swap.max",
                             "memory.zswap.max", "memory.zswap.writeback"):
                    if values[name] is None:
                        raise Unsafe(f"Cannot establish ancestor control {current / name}")
            for name in ("memory.max", "memory.swap.max", "memory.zswap.max"):
                if values[name] not in (None, "max"):
                    integer(values[name])
            if values["memory.zswap.writeback"] not in (None, "1"):
                raise Unsafe("Inherited zswap/disk writeback disabled")
            if values["memory.swap.max"] == "0" or values["memory.zswap.max"] == "0":
                raise Unsafe("Inherited swap or zswap disabled")
            nodes.append(dict(path=str(current), values=values))
            if current == mount:
                break
            current = current.parent
        return dict(path=unified[0], mount=str(mount), ancestors=nodes)

    def processes(self, pid):
        records = {}
        for entry in self.path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                text = (entry / "status").read_text()
                values = dict(line.split(":", 1) for line in text.splitlines() if ":" in line)
                records[int(entry.name)] = dict(pid=int(entry.name), ppid=int(values["PPid"]),
                    name=values["Name"].strip(),
                    memory_bytes={k: integer(values[k].split()[0]) * 1024
                                  for k in ("VmRSS", "VmSize", "VmSwap", "VmHWM") if k in values})
            except (FileNotFoundError, ProcessLookupError):
                continue
        selected = {pid}
        while True:
            children = {p for p, value in records.items() if value["ppid"] in selected}
            added = children - selected
            if not added:
                break
            selected.update(added)
        return [records[p] for p in sorted(selected) if p in records]

    def snapshot(self, anchor_pid, child_pid=None, include_zswap=True):
        params = self.parameters()
        memory_text = self.read("/proc/meminfo")
        memory = key_values(memory_text, units=True)
        memory_units = {line.split()[0].rstrip(":"): "bytes" if len(line.split()) == 3 else "count"
                        for line in memory_text.splitlines()}
        if "MemTotal" not in memory or "MemAvailable" not in memory:
            raise Unsafe("Missing required physical memory metrics")
        vmstat = key_values(self.read("/proc/vmstat"))
        for field in ("pgmajfault", "pswpin", "pswpout", "oom_kill"):
            if field not in vmstat:
                raise Unsafe(f"Missing vmstat metric {field}")
        cg = self.cgroups(anchor_pid)
        process_cg = self.cgroups(child_pid) if child_pid and self.path(f"/proc/{child_pid}").exists() else None
        return dict(timestamp=time.time(), monotonic=time.monotonic(), parameters=params,
                    zswap=self.zswap_counters() if include_zswap else None,
                    meminfo=memory, meminfo_units=memory_units, vmstat=vmstat,
                    pressure_memory=pressure(self.read("/proc/pressure/memory")),
                    swappiness=integer(self.read("/proc/sys/vm/swappiness")),
                    swaps=swaps(self.read("/proc/swaps")), cgroup=cg, child_cgroup=process_cg,
                    processes=self.processes(child_pid) if child_pid else [],
                    diskstats=self.read("/proc/diskstats"),
                    disk_free_bytes=os.statvfs("/").f_bavail * os.statvfs("/").f_frsize)


def kernel_messages():
    checked = subprocess.run(["dmesg", "--raw"], capture_output=True, text=True, timeout=10)
    if checked.returncode:
        raise Unsafe(f"Kernel-log read failed: {checked.stderr.strip()}")
    return [x for x in checked.stdout.splitlines() if KERNEL_FATAL.search(x)]


def with_kernel(fs, anchor_pid, child_pid=None, include_zswap=True):
    sample = fs.snapshot(anchor_pid, child_pid, include_zswap)
    sample["kernel_fatal_messages"] = kernel_messages()
    return sample


def configuration(fs):
    name = f"/boot/config-{platform.release()}"
    content = fs.optional(name)
    if content is None and fs.path("/proc/config.gz").exists():
        with gzip.open(fs.path("/proc/config.gz"), "rt") as stream:
            content = stream.read()
        name = "/proc/config.gz"
    return dict(path=name if content is not None else None,
                relevant_lines=[x for x in (content or "").splitlines()
                                if re.search(r"CONFIG_(ZSWAP|ZPOOL|ZSMALLOC|DEBUG_FS|MEMCG|CRYPTO_(LZO|LZ4|ZSTD))", x)],
                qualification="Runtime sysfs/readback and counters are required; missing config file is recorded, not an assumed missing feature.")


def ensure_debugfs(fs, evidence):
    """Reuse existing mount, or mount only debugfs at its conventional location."""
    target = "/sys/kernel/debug"

    def at_target():
        records = []
        for line in fs.read("/proc/self/mountinfo").splitlines():
            left, separator, right = line.partition(" - ")
            if separator and left.split()[4] == target:
                records.append(right.split()[0])
        return records

    before = at_target()
    evidence["debugfs"] = dict(mountpoint=target, before=before, mounted_by_helper=False)
    if before == ["debugfs"]:
        return
    if before:
        raise Unsafe("Debugfs mountpoint already occupied by a different filesystem")
    if not fs.path(target).is_dir() or fs.path(target).is_symlink():
        raise Unsafe("Unsafe or missing conventional debugfs mountpoint")
    command = ["mount", "-t", "debugfs", "debugfs", target]
    checked = subprocess.run(command, capture_output=True, text=True, timeout=10)
    evidence["debugfs"].update(command=command, exit=checked.returncode,
                               stdout=checked.stdout, stderr=checked.stderr, after=at_target())
    if checked.returncode or evidence["debugfs"]["after"] != ["debugfs"]:
        raise Unsafe("Temporary debugfs mount/readback failed")
    evidence["debugfs"]["mounted_by_helper"] = True


def prepare(fs, anchor_pid, evidence):
    evidence.update(original_parameters=fs.parameters(), writes=[],
                    configuration=configuration(fs), kernel=platform.uname()._asdict(),
                    cmdline=fs.read("/proc/cmdline"))
    ensure_debugfs(fs, evidence)
    # Capture physical memory and inherited controls even when lazy setup has
    # not yet created the debugfs counter directory. Unavailable is not zero.
    before = with_kernel(fs, anchor_pid, include_zswap=False)
    evidence["initial"] = before
    lazy = not fs.path("/sys/kernel/debug/zswap").exists()
    if lazy:
        before["zswap_telemetry"] = "unavailable_before_activation"
        if enabled(before["parameters"]["enabled"]):
            raise Unsafe("Enabled zswap has no counter directory")
        if not re.match(r"^6\.17(?:\.|-|$)", evidence["kernel"]["release"]):
            raise Unsafe("Missing counter directory on an unreviewed kernel lifecycle")
        evidence["lazy_initialization"] = dict(
            source="https://github.com/torvalds/linux/blob/v6.17/mm/zswap.c",
            basis="Disabled zswap_init skips zswap_setup; runtime enabled setter calls setup, which creates debugfs counters.",
            qualification="Missing directory permits this reviewed path but does not prove internal UNINIT; full post-enable telemetry remains mandatory.",
            preactivation_counters=None)
    else:
        before["zswap"] = fs.zswap_counters()
        before["zswap_telemetry"] = "available_before_activation"
        if before["zswap"]["pool_total_size"] or before["zswap"]["stored_pages"]:
            raise Unsafe("Initial compressed pool is not empty; no draining/reset permitted")
    if not before["parameters"]["compressor"] or not before["parameters"]["zpool"]:
        raise Unsafe("Cannot establish existing compressor/allocator")
    enabled(before["parameters"]["enabled"])
    integer(before["parameters"]["max_pool_percent"])
    limits = [x["values"]["memory.max"] for x in before["cgroup"]["ancestors"]
              if x["values"]["memory.max"] is not None]
    bound = budget(before["meminfo"]["MemTotal"], limits, os.sysconf("SC_PAGE_SIZE"))
    evidence["budget"] = bound
    # Existing lower finite cgroup zswap caps are safe and preserved, not raised.
    for key, value in (("max_pool_percent", str(bound["max_pool_percent"])), ("enabled", "1")):
        logical = f"/sys/module/zswap/parameters/{key}"
        target = fs.path(logical)
        evidence["writes"].append(dict(path=logical, requested=value, before=fs.read(logical)))
        with target.open("w") as stream:
            stream.write(value + "\n")
        actual = fs.read(logical)
        evidence["writes"][-1]["readback"] = actual
        if (key == "enabled" and not enabled(actual)) or (key != "enabled" and actual != value):
            raise Unsafe(f"Exact parameter readback failed: {key}")
    after = with_kernel(fs, anchor_pid)
    evidence["postactivation"] = after
    if lazy and (after["zswap"]["pool_total_size"] or after["zswap"]["stored_pages"]
                 or after["zswap"]["decompress_fail"]):
        raise Unsafe("First postactivation pool is not empty or has a decompression failure")
    for key in PARAMS:
        if key not in ("enabled", "max_pool_percent") and after["parameters"][key] != before["parameters"][key]:
            raise Unsafe(f"Unrequested parameter drift: {key}")
    evidence.update(prepared=after, status="prepared", created=time.time(),
                    image={key: os.environ.get(key) for key in ("ImageOS", "ImageVersion")},
                    anchor_pid=anchor_pid)
    reference = dict(before)
    reference["parameters"] = after["parameters"]
    if lazy:
        # No fabricated preactivation counters: comparison starts from the
        # first actually read complete, empty postactivation counter set.
        reference["zswap"] = after["zswap"]
    failures = fatal_findings(dict(prepared=reference, budget=bound), after)
    if failures:
        raise Unsafe(f"Unsafe change during preparation: {failures}")


def fatal_findings(state, sample):
    initial = state["prepared"]
    failures = []
    if sample["parameters"] != initial["parameters"]:
        failures.append("zswap parameter drift")
    if sample["swappiness"] != initial["swappiness"]:
        failures.append("swappiness drift")
    swap_identity = lambda items: sorted((x["name"], x["type"], x["bytes"], x["priority"]) for x in items)
    if swap_identity(sample["swaps"]) != swap_identity(initial["swaps"]):
        failures.append("backing swap capacity/priority drift")
    if sample["zswap"]["pool_total_size"] > state["budget"]["watchdog_bytes"]:
        failures.append("compressed allocator pool exceeded nominal cap plus 64 MiB guard")
    if sample["zswap"]["decompress_fail"] > initial["zswap"]["decompress_fail"]:
        failures.append("new decompression failure")
    if sample["vmstat"]["oom_kill"] > initial["vmstat"]["oom_kill"]:
        failures.append("new global OOM kill")
    old_messages = collections.Counter(initial["kernel_fatal_messages"])
    if collections.Counter(sample["kernel_fatal_messages"]) - old_messages:
        failures.append("new fatal kernel message")
    for cgkey in ("cgroup", "child_cgroup"):
        cg = sample[cgkey]
        if cg is None:
            continue
        if (cg["path"], cg["mount"]) != (initial["cgroup"]["path"], initial["cgroup"]["mount"]):
            failures.append("command/monitor cgroup moved")
            continue
        for old, current in zip(initial["cgroup"]["ancestors"], cg["ancestors"]):
            for key in ("memory.max", "memory.swap.max", "memory.zswap.max", "memory.zswap.writeback"):
                if old["values"][key] != current["values"][key]:
                    failures.append(f"ancestor control drift: {current['path']}/{key}")
            for name in ("memory.events", "memory.events.local"):
                if current["values"][name] is None:
                    continue
                previous = key_values(old["values"][name] or "")
                events = key_values(current["values"][name])
                if any(events.get(k, 0) > previous.get(k, 0) for k in ("oom", "oom_kill", "oom_group_kill")):
                    failures.append(f"new cgroup OOM event: {current['path']}")
    return sorted(set(failures))


def privileged(action, anchor_pid, child_pid=None):
    command = ["sudo", "-n", sys.executable, str(Path(__file__).resolve()), action,
               "--pid", str(anchor_pid)]
    if child_pid is not None:
        command += ["--child-pid", str(child_pid)]
    checked = subprocess.run(command, capture_output=True, text=True, timeout=30)
    try:
        data = json.loads(checked.stdout)
    except json.JSONDecodeError as exc:
        raise Unsafe(f"Privileged {action} invalid output: {checked.stdout!r}; {checked.stderr!r}") from exc
    data["privileged_stderr"] = checked.stderr
    if checked.returncode:
        data["privileged_exit"] = checked.returncode
    return data


def save(path, record):
    Path(path).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")


def stop_group(child, signum=signal.SIGTERM):
    try:
        os.killpg(child.pid, signum)
    except ProcessLookupError:
        child.poll()
        return
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        child.wait()


def run(args):
    if os.geteuid() == 0:
        raise Unsafe("Run orchestration as ordinary user; child must not run as root")
    if not args.command:
        raise Unsafe("Missing unchanged gate command after --")
    directory = Path(args.out).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    state = privileged("_prepare", os.getpid())
    state["image"] = {key: os.environ.get(key) for key in ("ImageOS", "ImageVersion")}
    save(directory / "prepare.json", state)
    if state.get("status") != "prepared" or state.get("privileged_exit"):
        return 2
    result = dict(command=args.command, native_timeout_override=None,
                  interval_seconds=INTERVAL, gate_returncode=None, fatal=[],
                  observed_max_pool_bytes=0, observed_max_stored_pages=0)
    child = None
    interrupted = []
    previous_handlers = {}

    def handle(signum, frame):
        interrupted.append(signum)
        # Do not wait for a privileged snapshot before forwarding cancellation:
        # the gate has its own session and does not receive our signal itself.
        if child is not None:
            try:
                os.killpg(child.pid, signum)
            except ProcessLookupError:
                pass

    for signum in (signal.SIGINT, signal.SIGTERM):
        previous_handlers[signum] = signal.signal(signum, handle)
    try:
        if interrupted:
            raise Unsafe("Interrupted before starting gate")
        child = subprocess.Popen(args.command, start_new_session=True)
        if interrupted:
            # Covers a signal received while Popen had not yet returned its PID.
            try:
                os.killpg(child.pid, interrupted[-1])
            except ProcessLookupError:
                child.poll()
        result["pid"] = child.pid
        with (directory / "telemetry.jsonl").open("w") as stream:
            while True:
                sample_start = time.monotonic()
                sample = privileged("_sample", os.getpid(), child.pid)
                failures = [sample.get("error", "snapshot failed")] if sample.get("privileged_exit") else fatal_findings(state, sample)
                if interrupted:
                    failures.append(f"orchestration interrupted: signal {interrupted[-1]}")
                sample["fatal"] = failures
                sample["phase"] = "fatal" if failures else "observed_exit" if child.poll() is not None else "periodic"
                if "zswap" in sample:
                    result["observed_max_pool_bytes"] = max(result["observed_max_pool_bytes"], sample["zswap"]["pool_total_size"])
                    result["observed_max_stored_pages"] = max(result["observed_max_stored_pages"], sample["zswap"]["stored_pages"])
                stream.write(json.dumps(sample, ensure_ascii=False) + "\n")
                stream.flush()
                if failures:
                    result["fatal"] = failures
                    stop_group(child, interrupted[-1] if interrupted else signal.SIGTERM)
                if child.poll() is not None:
                    result["gate_returncode"] = child.returncode
                    final = privileged("_sample", os.getpid(), child.pid)
                    final["phase"] = "final"
                    final_failures = [final.get("error", "final snapshot failed")] if final.get("privileged_exit") else fatal_findings(state, final)
                    final["fatal"] = final_failures
                    result["fatal"] = sorted(set(result["fatal"] + final_failures))
                    if "zswap" in final:
                        result["observed_max_pool_bytes"] = max(result["observed_max_pool_bytes"], final["zswap"]["pool_total_size"])
                        result["observed_max_stored_pages"] = max(result["observed_max_stored_pages"], final["zswap"]["stored_pages"])
                    stream.write(json.dumps(final, ensure_ascii=False) + "\n")
                    stream.flush()
                    result["final_sample"] = final
                    break
                until = sample_start + INTERVAL
                while child.poll() is None and not interrupted and time.monotonic() < until:
                    time.sleep(max(0.0, min(0.2, until - time.monotonic())))
    except Exception as exc:
        result["fatal"].append(f"monitor failure: {type(exc).__name__}: {exc}")
        if child is not None:
            stop_group(child)
            result["gate_returncode"] = child.returncode
        unavailable = dict(phase="final", status="unavailable", timestamp=time.time(),
                           error=str(exc), fatal=result["fatal"])
        result["final_sample"] = unavailable
        with (directory / "telemetry.jsonl").open("a") as stream:
            stream.write(json.dumps(unavailable) + "\n")
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
        result["compression_used"] = result["observed_max_stored_pages"] > 0
        save(directory / "result.json", result)
    code = result["gate_returncode"]
    if interrupted:
        return 128 + interrupted[-1]
    if result["fatal"]:
        return 2
    if code is None:
        return 2
    return code if code >= 0 else 128 - code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    for name in ("_prepare", "_sample"):
        p = sub.add_parser(name)
        p.add_argument("--pid", type=int, required=True)
        p.add_argument("--child-pid", type=int)
    p = sub.add_parser("prepare")
    p.add_argument("--out", required=True)
    p = sub.add_parser("run")
    p.add_argument("--out", required=True)
    p.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if platform.system() != "Linux":
        raise Unsafe("Linux hosted-runner helper only")
    if args.action.startswith("_"):
        if os.geteuid() != 0 or args.pid <= 0:
            raise Unsafe("Internal snapshot/setup requires sudo and valid anchor PID")
        record = {}
        try:
            if args.action == "_prepare":
                prepare(Linux(), args.pid, record)
            else:
                record = with_kernel(Linux(), args.pid, args.child_pid)
            print(json.dumps(record, ensure_ascii=False))
            return 0
        except Exception as exc:
            record.update(status="failed", error=f"{type(exc).__name__}: {exc}")
            print(json.dumps(record, ensure_ascii=False))
            return 2
    if args.action == "prepare":
        if os.geteuid() == 0:
            raise Unsafe("Invoke prepare as ordinary user")
        state = privileged("_prepare", os.getpid())
        state["image"] = {key: os.environ.get(key) for key in ("ImageOS", "ImageVersion")}
        save(args.out, state)
        return 0 if state.get("status") == "prepared" and not state.get("privileged_exit") else 2
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    return run(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Unsafe, OSError, subprocess.SubprocessError) as exc:
        print(f"zswap helper failed closed: {exc}", file=sys.stderr)
        sys.exit(2)
