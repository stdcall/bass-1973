Tinymist cache-policy patch
==========================

Upstream: [Tinymist 0.15.8](https://github.com/Myriad-Dreamin/tinymist/tree/32f908199ee17ea295512bbc27166e890c438175).
Copyright 2023–2025 Myriad Dreamin, Nathan Varner.
License: Apache-2.0; [the exact upstream LICENSE](https://github.com/Myriad-Dreamin/tinymist/blob/32f908199ee17ea295512bbc27166e890c438175/LICENSE).

The accompanying cache-policy.patch modifies the CLI lint compilation and
expression-value tracing cache lifetimes. It adds memo-cache eviction after
the initial compile and retains one memo generation after a full trace.
Native compiler diagnostics, lint rules and dependency coverage are unchanged.
The patch is a local modification of the upstream source, not an upstream
release. The upstream license and attribution notices remain in the downloaded
source. When distributing a compiled tool, include the upstream license and
any applicable dependency notices with that distribution.
