---
title: Proof architecture
updated: 2026-07-26
tags: [architecture, lean, multiplicity]
---

# Proof architecture

The proof is organized as a narrowing chain:

1. Exact generators build the width-five transfer data and reflected blocks.
2. Certificate parsers give typed Lean representations of checked-in bytes.
3. Padé/Bézout and sparse-matrix soundness turn zero mismatch counters into
   mathematical identities and injectivity statements.
4. Rank-certificate theorems determine the multiplicity of `50` in concrete
   block characteristic polynomials over `F_101`.
5. Transfer multiplicity and denominator lemmas assemble block results and
   connect visible eigenvalues to the normalized reduced denominator.
6. The modular obstruction contradicts the proposed divisibility over `Q[z]`.

Key formal sources:

- [`CertificatePadeSoundness.lean`](../KnuthFasc8aEx210/CertificatePadeSoundness.lean)
- [`CertificateMatrixSoundness.lean`](../KnuthFasc8aEx210/CertificateMatrixSoundness.lean)
- [`TransferMultiplicity.lean`](../KnuthFasc8aEx210/TransferMultiplicity.lean)
- [`TransferDenominator.lean`](../KnuthFasc8aEx210/TransferDenominator.lean)
- [`Counterexample.lean`](../KnuthFasc8aEx210/Counterexample.lean)

The concrete embedded replays are deliberately split into bounded segment
modules. Lake can check those modules concurrently, after which small kernel
proofs compose the segment equalities into the public multiplicity theorem.

See [Certificate pipeline](certificate-pipeline.md) for the artifact flow and
[Trust boundary](trust-boundary.md) for the distinction between replay layers.
