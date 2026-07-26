---
title: Trust boundary
updated: 2026-07-26
tags: [trust, lean, verification]
---

# Trust boundary

Three claims must not be conflated:

- **Kernel-checked theorem:** a declaration imported by the root Lean library,
  with its proof reconstructed from definitions, lemmas, and embedded constants.
- **Executable verification:** an `IO` or C++ checker reports that an external
  artifact is internally consistent; this does not itself inhabit a Lean theorem.
- **Planned bridge:** the abstract theorem exists, but concrete checked-in data
  have not yet been connected to all of its hypotheses.

The embedded visible, `Trel_plus`, `Trel_minus`, and `U1_plus` results are in the
first category. The remaining three normal block certificates are currently in
the second category. Reflection/SCC identification and final normalization are
in the third.

`native_decide` is used to prove closed propositions about embedded bytes. Its
result is stored in `.olean` artifacts and checked through Lean's normal build
pipeline; the expensive computation is cached, which is why clean and warm
build times differ substantially.

For more detail, consult [LEAN.md](../LEAN.md) and
[Certificate pipeline](certificate-pipeline.md).
