---
title: Project overview
updated: 2026-07-26
tags: [overview, knuth, generating-functions]
---

# Project overview

The repository studies Knuth's Fascicle 8A Exercise 210 using exact transfer
matrices and a Lean formalization. The computational side produces sparse
matrices, polynomial data, and compact certificates over `F_101`. The formal
side connects checked multiplicities and visibility to an obstruction to the
proposed cubic divisibility relation.

The long-term target is a single inhabitant of `WidthFiveCertificate` whose
conclusion is the negation of the cubic divisibility claim. The reusable
algebraic endpoint already exists; remaining work is predominantly the concrete
connection from checked-in artifacts to all of its hypotheses.

Primary sources:

- [README](../README.md) for build and project orientation.
- [Lean notes](../LEAN.md) for the formal trust boundary and theorem inventory.
- [Proof narrative](../PROOF.md) for the mathematical argument.
- [`Counterexample.lean`](../KnuthFasc8aEx210/Counterexample.lean) for the final
  certificate interface and modular obstruction.

See [Proof architecture](proof-architecture.md) for the layer map and
[Current status](current-status.md) for the live frontier.
