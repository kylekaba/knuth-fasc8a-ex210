# Lean 4 verifier for Knuth Fascicle 8A, Exercise 210

This repository contains a Lean 4/Mathlib formalization of the algebraic core
of the width-5 counterexample and a Lean executable that independently checks
the checked-in certificate files. Mathlib is pinned to the release matching the
repository's Lean toolchain.

The large repository checkers establish the external certificate facts for the
factor `1 - 50 z` modulo `101`:

* the closed denominator has at least one visible copy;
* the open-side transfer determinant has exactly two copies;
* the open denominator divides that transfer determinant.

Lean represents the normalized denominators as polynomials in `Z[X]`, states
the proposed divisibility in `Q[X]`, uses Gauss's lemma to return to `Z[X]`,
and then reduces coefficients into `(ZMod 101)[X]`. It proves that the three
certificate facts contradict `Q_5(z)^3 | Q_5^+(z)`, and therefore disprove the
universal claim for all `m >= 5`.

The bordered-matrix argument from `PROOF.md` is also formalized: if the
bordered operator `[H v; phi 0]` is injective, `H v = 0`, and `phi v != 0`,
then `ker(H) = span(v)` and `v` is not in the range of `H`.
Lean additionally derives that the corresponding eigenvalue has root
multiplicity exactly one in the characteristic polynomial.

Type-check the Lean library (this does not run the certificate checker):

```sh
lake build
```

## Lean checker for certificate files

The executable `knuth_cert_check` reads the actual binary certificate files from
this repository checkout and checks:

* `KMP101`, `KMV101`, `KMW2CERT`, `KPB101W1`, and `KMC201` magic/version fields;
* Lean-computed SHA-256 hashes for the consumed matrix, certificate,
  polynomial, and eigenvector files against the upstream `SHA256SUMS` values;
* visible-factor files `Tall_plus.kmc`, `Tall_finish.vec`, `visible76.poly`,
  and `Trel_plus_eigen50.vec` parse with matching dimensions;
* exact dimensions, term counts, degrees, and nonzero constant coefficients;
* the six rank-certificate constants listed in the upstream proof;
* the stored `KMW2CERT` connection-polynomial prefix `1`;
* on every run, the exact Padé/Bézout identity `U D + V R = 1` from each
  compact `.kpw1` witness, where `D` is the stored connection polynomial and
  `R` is recomputed from the first `2N` moments; this certifies that no shorter
  scalar recurrence exists without relying on Berlekamp--Massey replay;
* a Lean replay of Berlekamp--Massey on the first `2N` stored moments in each
  rank certificate, checking that the resulting full-degree connection
  polynomial exactly matches the stored coefficients;
* the first 32 stored recurrence positions inside the Berlekamp--Massey input
  window for each rank certificate;
* the 32 stored post-Berlekamp--Massey recurrence-check moments in each rank
  certificate, over `F_101[t]/(t^2 - 2)`;
* the splitmix64 seed expansion used by the upstream rank verifier to generate
  diagonal preconditioners and probe vectors;
* a configurable prefix, or the full stream, of Wiedemann/Krylov moments
  recomputed from the actual sparse matrices and compared with the stored
  `.kwc2` moments; by default this checks the first two moments, including one
  sparse shifted/bordered operator application, and `all` checks every stored
  `2N + 32` moment;
* a configurable prefix of the visible-polynomial Horner loop
  `v <- A^2 v + coeff * beta` from the actual `Tall_plus.kmc`,
  `Tall_finish.vec`, and `visible76.poly` files; by default this checks the
  first two highest-degree coefficients;
* when the visible prefix argument is `all` or at least the polynomial length,
  the full visible-factor check from `src/verify_visible.cpp`:
  Lean computes `r = g(A^2) beta`, checks `A^2 r = 76 r`, derives
  `v = r + 50^{-1} A r`, checks `A v = 50 v`, verifies both bare coordinates
  are nonzero, and compares `v` against `Trel_plus_eigen50.vec` through the
  matrix state labels;
* CSR matrix structure: row pointers are monotone, the final row pointer equals
  the advertised entry count, column indices are in range, and coefficients are
  reduced modulo 101;
* the matrix state-label tail has exactly one 64-bit label per row;
* the `Trel_plus_eigen50.vec` residual against the actual `Trel_plus.kmc`
  sparse matrix, checking `(Trel_plus - 50I)v = 0` over `F_101`;
* exact file lengths with no trailing bytes;
* the FNV-64 matrix/eigenvector hashes embedded in `.kwc2` files, binding each
  certificate to the actual `.kmc` matrix and `.vec` eigenvector bytes, and the
  FNV-64 source-certificate hash embedded in each `.kpw1` witness.

Run:

```sh
lake build knuth_cert_check
.lake/build/bin/knuth_cert_check
```

The no-argument run is intentionally a quick smoke check. Its output is labeled
`SMOKE`; use `--full` for the complete replay described below.

Use named options to check longer rank-certificate Krylov and
visible-polynomial prefixes. Either count may be `all`:

```sh
.lake/build/bin/knuth_cert_check --krylov 4
.lake/build/bin/knuth_cert_check --krylov 4 --visible 4
.lake/build/bin/knuth_cert_check --krylov all --visible 0
.lake/build/bin/knuth_cert_check --krylov 0 --visible all
```

Use `--bm` to replay Berlekamp--Massey over the stored rank-certificate
moments. `--rank-limit` limits the number of rank certificates, which is useful
for timing:

```sh
.lake/build/bin/knuth_cert_check --krylov 0 --visible 0 --bm --rank-limit 1
.lake/build/bin/knuth_cert_check --krylov 0 --visible 0 --bm
```

The full certificate-file verification is:

```sh
.lake/build/bin/knuth_cert_check --full
```

That command is intentionally expensive. It prints progress every 5000
recomputed rank moments for long Krylov checks.

Expected output includes:

```text
PASS Lean parse visible files: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, visible_prefix_steps=2, visible_prefix_bare=0, eig_n=16831, pivot=0, pivot_value=37, sha256=ok
PASS Lean full visible factor: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, r_bare=67, v_bare=67, eigen76_bad=0, eigen50_bad=0, restricted_mismatch=0, pivot=0, pivot_value=37, sha256=ok
PASS Lean rank cert content: ./data/certs/Trel_plus_border.kwc2, n=16832, constant=23+34t, krylov_bad=0/33696 (full), bm_replay_degree=16832, bm_coefficient_bad=0, initial_recurrence_bad=0, extra_recurrence_bad=0, pade_bezout_bad=0, eigen_residual_bad=0, seed_diag_rejections=4, matrix_n=16831, entries=522193, sha256=ok
...
Lean certificate-file checks completed.
```

This is a real Lean-side check of the actual certificate files, including the
full visible-factor replay, exact Padé/Bézout checks, and a full
Berlekamp--Massey replay over the stored rank-certificate moments. In `--full`
mode, the Lean executable also recomputes
all `2N + 32` Wiedemann moments from the actual sparse matrices for all six rank
certificates.

## Trust boundary

There are two deliberately separate layers:

1. Lean's kernel checks the concrete polynomial argument, including
   constant-term-one primitiveness, Gauss's lemma, coefficient reduction,
   the `1 - 50X` multiplicity obstruction, and the bordered-matrix kernel/range
   lemma. It also proves that the encoded Padé convolution and zero mismatch
   count imply the complete polynomial Bézout identity, and composes that
   identity with the Hankel/Krylov nonsingularity theorem. The encoded byte
   dot product is proved equal to the ordinary `CertificateField` vector dot
   product used by scalar Krylov moments. Parsed CSR data, the `-50I` shift,
   and left/right diagonal preconditioning are represented as genuine linear
   endomorphisms for the normal rank certificates.
2. The `IO` executable parses and replays the checked-in computational
   certificates.

The executable reports a runtime success value; it does not construct a
kernel-checked inhabitant of `WidthFiveCertificate`. Consequently, this project
provides a Lean-implemented certificate verifier and a kernel-checked logical
and algebraic core, but not a single end-to-end kernel theorem derived from the
binary files. The transfer decomposition, its denominator interpretation, and
the conversion of runtime matrix checks into polynomial multiplicity proof
terms remain on the external side of the boundary.

The certificate-to-nonsingularity bridge is:

```lean
KnuthFasc8aEx210.PadeWitnessFile.injective_of_checked_pade
```

Its remaining computational premise is equality between the stored moments
and the scalar Krylov moments of the represented matrix operator.

Main theorem:

```lean
KnuthFasc8aEx210.WidthFiveCertificate.not_cubic_divisibility
```

The bordered-matrix conclusions are:

```lean
KnuthFasc8aEx210.ker_eq_span_of_bordered_injective
KnuthFasc8aEx210.not_mem_range_of_bordered_injective
KnuthFasc8aEx210.charpoly_rootMultiplicity_eq_one_of_bordered_injective
```
