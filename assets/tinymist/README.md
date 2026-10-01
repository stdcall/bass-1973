Tinymist cache-policy patch
==========================

Upstream: [Tinymist 0.15.8](https://github.com/Myriad-Dreamin/tinymist/tree/32f908199ee17ea295512bbc27166e890c438175).
Copyright 2023–2025 Myriad Dreamin, Nathan Varner.
License: Apache-2.0; [the exact upstream LICENSE](https://github.com/Myriad-Dreamin/tinymist/blob/32f908199ee17ea295512bbc27166e890c438175/LICENSE).

The accompanying cache-policy.patch modifies the CLI lint compilation and
expression-value tracing. It adds memo-cache eviction after the initial
compile and retains one memo generation after a completed trace.

Before tracing layout, it evaluates the same main source with the same
traced span and sink. If that evaluation has already filled the upstream
sink's ten-value limit, those exact values and styles are the complete
trace result: layout cannot append to a full sink. Otherwise it retains
the original full-document trace, including values produced during layout.
The limit and append behavior are defined by the
[locked Typst sink](https://github.com/Myriad-Dreamin/typst/blob/59b5999da8e74e74583069408d2564fc1f9bc973/crates/typst-library/src/engine.rs);
the original trace evaluates the main source before layout in the
[locked compiler](https://github.com/Myriad-Dreamin/typst/blob/59b5999da8e74e74583069408d2564fc1f9bc973/crates/typst/src/lib.rs).

Native compiler diagnostics, lint rules and dependency coverage are unchanged.
The patch is a local modification of the upstream source, not an upstream
release. The upstream license and attribution notices remain in the downloaded
source. When distributing a compiled tool, include the upstream license and
any applicable dependency notices with that distribution.
