---
title: Certificate pipeline
updated: 2026-07-26
tags: [certificates, reproducibility, krylov]
---

# Certificate pipeline

Each embedded rank proof uses three durable inputs:

- a sparse CSR matrix (`.kmc`);
- a Wiedemann/connection-polynomial certificate (`.kwc2`) and Padé witness
  (`.kpw1`);
- deterministic bounded Krylov checkpoints (`.krc1`).

[`CertificateFiles.lean`](../KnuthFasc8aEx210/CertificateFiles.lean) parses the
formats. [`RankCheckpointSoundness.lean`](../KnuthFasc8aEx210/RankCheckpointSoundness.lean)
relates a zero segment counter to exact moment and endpoint equalities. Embedded
data modules make the checked-in bytes closed Lean constants; independent
segment modules replay bounded portions with `native_decide`; orbit and stored
moment modules compose those local results; the certificate module publishes a
root-multiplicity theorem.

Current embedded checkpoint replays:

| Block | Segments | Result at 50 |
|---|---:|---:|
| `Trel_plus` | 33 | multiplicity 1 |
| `Trel_minus` | 33 | multiplicity 0 |
| `U1_plus` | 51 | multiplicity 0 |

Reproducibility commands:

```sh
lake build
make rank-checkpoint-verify
make hashes
```

The Make target regenerates each embedded `.krc1` file and compares it
byte-for-byte. See [Current status](current-status.md) for the unembedded blocks.
