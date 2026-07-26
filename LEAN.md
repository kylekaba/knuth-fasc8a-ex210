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
* on every run, every one of the `N` recurrence positions in the full
  Berlekamp--Massey input window; the proof layer turns a zero mismatch count
  for this check into the exact recurrence identity used by the Padé/Krylov
  nonsingularity theorem;
* the 32 stored post-Berlekamp--Massey recurrence-check moments in each rank
  certificate, over `F_101[t]/(t^2 - 2)`;
* the splitmix64 seed expansion used by the upstream rank verifier to generate
  diagonal preconditioners and probe vectors;
* a configurable prefix, or the full stream, of Wiedemann/Krylov moments
  recomputed from the actual sparse matrices and compared with the stored
  `.kwc2` moments; by default this checks the first two moments, including one
  sparse shifted/bordered operator application, and `all` checks every stored
  `2N + 32` moment;
* for both normal and bordered certificates, the reported Krylov mismatch
  count is the same proof-shaped canonical-orbit function used by the kernel
  theorem; zero mismatches derive the replay orbit and every individual stored
  moment equality rather than assuming them;
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
* proof-shaped CSR column and row-interval counters, plus a seed-vector size
  counter; zero values supply the quantified bounds and byte dimensions used by
  the normal sparse-operator theorem;
* canonicality and nonzero counters for the right diagonal preconditioner;
  these prove it is surjective, allowing injectivity of `D_L B D_R` to imply
  injectivity of the raw bordered operator `B`;
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

That command is intentionally expensive. Both normal and bordered rank
certificates use directly evaluated proof-shaped mismatch counters.

Expected output includes:

```text
PASS Lean parse visible files: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, visible_prefix_steps=2, visible_prefix_bare=0, eig_n=16831, pivot=0, pivot_value=37, sha256=ok
PASS Lean full visible factor: Tall_plus_n=18325, Tall_plus_entries=565237, Trel_plus_n=16831, Trel_plus_entries=522193, finish_n=18325, degree(g)=4106, r_bare=67, v_bare=67, eigen76_bad=0, eigen50_bad=0, restricted_mismatch=0, pivot=0, pivot_value=37, sha256=ok
PASS Lean rank cert content: ./data/certs/Trel_plus_border.kwc2, n=16832, constant=23+34t, krylov_bad=0/33696 (full), bm_replay_degree=16832, bm_coefficient_bad=0, initial_recurrence_bad=0, extra_recurrence_bad=0, full_recurrence_bad=0, pade_bezout_bad=0, eigen_residual_bad=0, csr_column_bad=0, csr_row_pointer_bad=0, seed_size_bad=0, seed_dR_canonical_bad=0, seed_dR_zero_bad=0, seed_diag_rejections=4, matrix_n=16831, entries=522193, sha256=ok
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
   endomorphisms for the normal rank certificates, and each encoded normal
   CSR row is proved to evaluate to the corresponding shifted-operator row.
   Successful bytewise diagonal multiplication and full Krylov steps preserve
   this interpretation. Zero proof-shaped recurrence, canonical Krylov, and CSR
   mismatch counts now derive the orbit, all stored moment matches, and matrix
   bounds internally and compose with the Padé witness to prove normal-operator
   injectivity. The parsed bordered CSR map is also represented as the exact
   `[M - 50I, v; pivot, 0]` endomorphism, proved linearly equivalent to the
   abstract border operator, and connected directly to characteristic-root
   multiplicity one. Its byte replay now has a canonical orbit and zero-counter
   injectivity bridge parallel to the normal certificates. Proof-shaped
   diagonal and eigenvector-residual counters remove the preconditioners and
   yield root multiplicity one for the raw `Trel_plus` CSR matrix. Scalar
   extension is then removed: the bordered result gives multiplicity one and
   the five normal results give multiplicity zero for the native `F_101` CSR
   operators themselves. Lean assembles those conclusions into multiplicity
   two for the full reflected block product, proves that non-50 singleton SCCs
   contribute zero, and formalizes the adjugate construction of a scalar
   transfer rational function. Its constant-term-one normalized denominator
   is proved to divide `det(I-XM)`, yielding the modular cubic obstruction.
   At the recurrence layer, Lean now proves that every observable eigenvalue
   is a root of a forward recurrence polynomial and specializes reversal over
   `F_101`: an observable `50`-eigenvector for the reversed denominator
   recurrence forces `1-50X` to divide the denominator. It also proves that
   recurrences propagate across the startup vector's full Krylov span, that
   the certificate formula `r=g(M²)beta` lies in that span, and that
   `M²r=76r` implies `r+99Mr` is a `50`-eigenvector. The parsed CSR matrix,
   finish vector, and polynomial now feed a proof-shaped
   `visibleCertificateBad` counter; zero gives the closed visible-factor
   conclusion directly, while its native implementation runs the existing
   efficient Horner and CSR evaluator. A formal-power-series proof now shows
   that the adjugate rational function represents the scalar Krylov series,
   cancellation preserves that representation for the canonical reduced
   `RatFunc.denom`, and its reverse is an eventual recurrence. Consequently a
   zero visible counter proves the factor in the actual normalized reduced
   transfer denominator without an exposed recurrence assumption. The actual
   checked-in closed matrix, finish vector, polynomial, and 4,107-step Horner
   replay are now closed into this theorem: the bytes are embedded at
   elaboration, four bounded checkpoint segments are proved independently and
   composed in the kernel, and the final checkpoint's square-eigenvector and
   visible-coordinate check yield
   `embedded_visibleFactor_dvd_normalizedTransferDenominator`.
   The checked-in `Trel_plus` bordered rank certificate is likewise embedded.
   A deterministic `KRC101V1` file supplies 33 bounded Krylov checkpoints;
   independently checked segment equalities compose into all 33,664 stored
   moment matches. Together with the embedded Padé, CSR, diagonal, and
   eigenvector checks, this proves
   `embeddedTrelPlus_rootMultiplicity_fifty_eq_one` for the native `F_101`
   characteristic polynomial, without running the `IO` executable.
   The normal `Trel_minus` certificate follows the same bounded-checkpoint
   construction and proves
   `embeddedTrelMinus_rootMultiplicity_fifty_eq_zero` over the native field.
2. The `IO` executable parses and replays the checked-in computational
   certificates.

The executable reports a runtime success value; it does not construct a
kernel-checked inhabitant of `WidthFiveCertificate`. Consequently, this project
provides a Lean-implemented certificate verifier and a kernel-checked logical
and algebraic core, but not yet a single end-to-end theorem for the complete
counterexample. The closed visible-factor replay is now internal from embedded
checked-in bytes through the normalized reduced denominator, as is the
bordered `Trel_plus` rank-one result and the normal `Trel_minus` rank-zero
result. What remains on the external side is closing the four `U1`/`U2`
rank-certificate results from embedded bytes, the
concrete reflection/SCC decomposition and `Wrel ~= Trel`
identification, and the integer normalization/final `WidthFiveCertificate`
construction.

The certificate-to-nonsingularity bridge is:

```lean
KnuthFasc8aEx210.PadeWitnessFile.injective_of_checked_pade
KnuthFasc8aEx210.PadeWitnessFile.injective_normal_of_checked_full_recurrence
KnuthFasc8aEx210.PadeWitnessFile.injective_normal_of_checked_seed_counters
KnuthFasc8aEx210.PadeWitnessFile.injective_border_of_checked_seed_counters
```

The strongest normal-certificate theorem consumes zero executable counters,
certificate metadata, and the checked leading/nonzero-constant coefficients;
it no longer exposes orbit, individual moment, or quantified CSR premises.

Main theorem:

```lean
KnuthFasc8aEx210.WidthFiveCertificate.not_cubic_divisibility
```

The bordered-matrix conclusions are:

```lean
KnuthFasc8aEx210.ker_eq_span_of_bordered_injective
KnuthFasc8aEx210.not_mem_range_of_bordered_injective
KnuthFasc8aEx210.charpoly_rootMultiplicity_eq_one_of_bordered_injective
KnuthFasc8aEx210.csr_charpoly_rootMultiplicity_fifty_eq_one_of_bordered_injective
KnuthFasc8aEx210.csr_charpoly_rootMultiplicity_fifty_eq_one_of_checked_counters
```
