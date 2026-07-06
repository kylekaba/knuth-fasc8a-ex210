# Lean 4 verifier for Knuth Fascicle 8A, Exercise 210

This repository contains a Lean 4 formalization of the logical core of the
width-5 counterexample and a Lean executable that independently checks the
checked-in certificate files.

The large repository checkers establish the external certificate facts for the
factor `1 - 50 z` modulo `101`:

* the closed denominator has at least one visible copy;
* the open-side transfer determinant has exactly two copies;
* the open denominator divides that transfer determinant.

Lean proves that these facts contradict the proposed divisibility
`Q_5(z)^3 | Q_5^+(z)`, and therefore disprove the universal claim for
all `m >= 5`.

Build:

```sh
lake build
```

## Lean checker for certificate files

The executable `knuth_cert_check` reads the actual binary certificate files from
this repository checkout and checks:

* `KMP101`, `KMV101`, `KMW2CERT`, and `KMC201` magic/version fields;
* Lean-computed SHA-256 hashes for the consumed matrix, certificate,
  polynomial, and eigenvector files against the upstream `SHA256SUMS` values;
* visible-factor files `Tall_plus.kmc`, `Tall_finish.vec`, `visible76.poly`,
  and `Trel_plus_eigen50.vec` parse with matching dimensions;
* exact dimensions, term counts, degrees, and nonzero constant coefficients;
* the six rank-certificate constants listed in the upstream proof;
* the stored `KMW2CERT` connection-polynomial prefix `1`;
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
  certificate to the actual `.kmc` matrix and `.vec` eigenvector bytes.

Run:

```sh
lake build knuth_cert_check
.lake/build/bin/knuth_cert_check
```

Pass a second argument to check a longer rank-certificate Krylov prefix, and a
third argument to check a longer visible-polynomial prefix. Either argument may
be `all` for the full replay:

```sh
.lake/build/bin/knuth_cert_check . 4
.lake/build/bin/knuth_cert_check . 4 4
.lake/build/bin/knuth_cert_check . all 0
.lake/build/bin/knuth_cert_check . 0 all
```

Pass `bm` as a fourth argument to replay Berlekamp--Massey over the stored
rank-certificate moments. A fifth argument limits the number of rank
certificates, which is useful for timing:

```sh
.lake/build/bin/knuth_cert_check . 0 0 bm 1
.lake/build/bin/knuth_cert_check . 0 0 bm
```

The full certificate-file verification is:

```sh
.lake/build/bin/knuth_cert_check . all all bm
```

That command is intentionally expensive. It prints progress every 5000
recomputed rank moments for long Krylov checks.

Expected output includes:

```text
PASS Lean parse visible files: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, visible_prefix_steps=2, visible_prefix_bare=0, eig_n=16831, pivot=0, pivot_value=37, sha256=ok
PASS Lean full visible factor: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, r_bare=67, v_bare=67, eigen76_bad=0, eigen50_bad=0, restricted_mismatch=0, pivot=0, pivot_value=37, sha256=ok
PASS Lean rank cert content: ./data/certs/Trel_plus_border.kwc2, n=16832, constant=23+34t, krylov_bad=0/33696 (full), bm_replay_degree=16832, bm_coefficient_bad=0, initial_recurrence_bad=0, extra_recurrence_bad=0, eigen_residual_bad=0, seed_diag_rejections=4, matrix_n=16831, entries=522193, sha256=ok
...
Lean certificate-file checks completed.
```

This is a real Lean-side check of the actual certificate files, including the
full visible-factor replay and a full Berlekamp--Massey replay over the stored
rank-certificate moments. With the `all all bm` arguments, the Lean executable
also recomputes all `2N + 32` Wiedemann moments from the actual sparse matrices
for all six rank certificates.

Main theorem:

```lean
KnuthFasc8aEx210.WidthFiveCertificate.not_cubic_divisibility
```

The concrete arithmetic obstruction is:

```lean
KnuthFasc8aEx210.repository_cubic_multiplicity_test_fails
```
