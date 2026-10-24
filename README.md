# lean-sudo

A drop-in replacement for `sudo` written in [Lean 4](https://lean-lang.org), with its
security-relevant logic (sudoers policy evaluation, environment sanitisation, CLI
parsing, credential-cache validity, the run/deny decision) formally verified in Lean.

**Status: work in progress.** See [DESIGN.md](DESIGN.md) for the architecture,
module contracts and the list of verified properties.
