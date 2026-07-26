---
title: Current status
updated: 2026-07-26
tags: [status, roadmap, pull-request]
---

# Current status

## Proved from embedded bytes

- The closed visible-factor replay reaches the normalized reduced denominator.
- `embeddedTrelPlus_rootMultiplicity_fifty_eq_one` proves native multiplicity 1.
- `embeddedTrelMinus_rootMultiplicity_fifty_eq_zero` proves native multiplicity 0.
- `embeddedU1Plus_rootMultiplicity_fifty_eq_zero` proves native multiplicity 0.

These public modules are imported by the root
[`KnuthFasc8aEx210.lean`](../KnuthFasc8aEx210.lean).

## Remaining concrete work

1. Embed and close `U1_minus`, `U2_plus`, and `U2_minus` rank certificates.
2. Formalize the concrete reflection/SCC decomposition and identify `Wrel` with
   the corresponding `Trel` operator.
3. Finish integer normalization and construct the final `WidthFiveCertificate`.

## Review gate

The draft pull request should move to ready-for-review after the remaining three
normal rank blocks pass root `lake build`, deterministic checkpoint comparison,
hash verification, and documentation audit. Reflection/SCC and final
normalization may then be reviewed as explicit follow-up milestones.
