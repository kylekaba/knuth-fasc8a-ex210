# A certified counterexample at width 5

All matrices below have integer entries before reduction.  A bar denotes
reduction modulo 101.

## 1. Transfer decomposition

Adjoin a vertex `infinity` adjacent to every square.  Adding the two edges
from the endpoints of a Hamiltonian path to `infinity` is a bijection between
Hamiltonian paths on the board and Hamiltonian cycles in the augmented graph.

During a left-to-right transfer, the degree of `infinity` is nondecreasing and
can only pass through

    0 -> 1 -> 2.

With states ordered by this degree, the one-column open-tour transfer is block
upper triangular:

                         [ T  X  Z ]
                    B =  [ 0  U  Y ].
                         [ 0  0  W ]

`T` is the ordinary closed-tour transfer.  `U` is the one-endpoint sector.
After the second edge at `infinity` is chosen, contracting the two-edge path
through `infinity` gives the ordinary closed connectivity update, so the
relevant part of `W` is another copy of the closed transfer.

Endpoint edges may be selected in the last two board columns.  They are
therefore part of the terminal functional, not of a further stable transfer.
The function `finish_open` in `src/transfer_generator.cpp` implements those
terminal choices.  This point is checked by the small-width counts in Section
6 below.

States of `W` that cannot reach a terminal state may be deleted without
changing the scalar generating function.  Write the resulting block as
`Wrel`.  Therefore the reduced open denominator divides

    det(I-zT) det(I-zU) det(I-zWrel).                       (1)

This statement is over the integers, before reduction modulo 101.

## 2. Reproducible state-space data

The generator represents a partial 2-regular graph as a path forest on the
last two columns.  A frontier entry is bare, internal, or a degree-one path
endpoint; degree-one endpoints are paired exactly when they belong to the same
partial path.  The update rejects a cycle before the terminal step.  Since a
knight edge spans at most two columns, this is a complete frontier state.

The regenerated state graphs have the following exact sizes:

| sector | states | weighted transitions | non-singleton SCCs |
|---|---:|---:|---:|
| `T` | 36,380 | 1,149,818 | 33,409 |
| `U` | 107,444 | 3,566,822 | 51,112 and 47,198 |
| `W` | 48,973 | 1,395,976 | 33,409 and 10,235 |

There are 114 terminal states in `W`, and exactly 33,409 states can reach one
of them.  Those states are precisely the 33,409-state SCC.  The extractor
checks, edge by edge and with integer weights, that

    Wrel is permutation-similar to Trel,                   (2)

where `Trel` is the 33,409-state SCC of `T`.

Every SCC of `T` outside `Trel` is a singleton.  Every SCC of `U` outside its
two displayed components is a singleton.  Modulo 101, none of those singleton
blocks has diagonal entry 50.

## 3. A factor visible in the closed denominator

Horizontal reflection commutes with every transfer.  Over `F_101`, where 2 is
invertible, the transfer splits into symmetric and antisymmetric blocks.  The
full reachable symmetric closed block `A` has dimension 18,325.  Let `beta` be
the closed terminal vector and let `e` select the bare startup state.

The file `data/certs/visible76.poly` contains a polynomial `g` of degree 4106.
The verifier recomputes

    r = g(A^2) beta

and checks exactly that

    A^2 r = 76 r,                 e^T r = 67 != 0.          (3)

In `F_101`, `50^2=76` and `50^{-1}=99`.  Hence

    v = r + 99 A r

satisfies

    A v = 50 v,                  e^T v = 67 != 0.          (4)

Moreover `v` is a polynomial in `A` applied to `beta`.

Let `a_k=e^T A^k beta`.  Any recurrence satisfied by `(a_k)` is also satisfied
by every finite linear combination of its shifts.  In particular it is
satisfied by

    e^T A^k v = 67 * 50^k.

The latter sequence has minimal recurrence `x-50`.  Therefore the reduced
closed generating function over `F_101` has denominator divisible by

    1-50z.                                                   (5)

If `Q_5` is the primitive integer denominator with `Q_5(0)=1`, reduction of
the integer rational function can only cancel factors.  Thus (5) implies

    1-50z divides bar(Q_5).                                  (6)

The same verifier restricts `v` to the symmetric block of `Trel`; the result
is the nonzero eigenvector in
`data/certs/Trel_plus_eigen50.vec`.

## 4. Exact rank and algebraic-multiplicity certificates

Reflection gives the following blocks:

| block | symmetric dimension | antisymmetric dimension |
|---|---:|---:|
| `Trel` | 16,831 | 16,578 |
| `U1` | 25,617 | 25,495 |
| `U2` | 23,646 | 23,552 |

All rank certificates use

    K = F_101[t]/(t^2-2).

Since 2 is a nonsquare modulo 101, this is the field `F_(101^2)`.
Nonsingularity after scalar extension implies nonsingularity over `F_101`.

For a square matrix `H` of order `N`, the certificate fixes invertible diagonal
matrices `DL,DR` and vectors `u,w` in `K^N`, then supplies the exact moments

    s_k = u^T (DL H DR)^k w,       0 <= k < 2N+32.

The verifier regenerates `DL,DR,u,w` from the recorded seed, recomputes every
moment from the sparse matrix, and reruns Berlekamp--Massey on the first `2N`
moments.  A scalar minimal polynomial of degree `N` must equal the matrix
minimal polynomial and characteristic polynomial, because both divide a
characteristic polynomial of degree `N`.  A nonzero constant coefficient then
proves `H` nonsingular.  The extra 32 moments are independent recurrence
checks.  Randomness is used only to find the displayed data; verification of
the fixed data is deterministic and exact.

The certified results are:

| matrix being certified | certificate order | BM degree | constant coefficient |
|---|---:|---:|---:|
| bordered `Trel+` matrix | 16,832 | 16,832 | `23+34t` |
| `Trel- - 50I` | 16,578 | 16,578 | `56+31t` |
| `U1+ - 50I` | 25,617 | 25,617 | `80+91t` |
| `U1- - 50I` | 25,495 | 25,495 | `89+57t` |
| `U2+ - 50I` | 23,646 | 23,646 | `87+46t` |
| `U2- - 50I` | 23,552 | 23,552 | `16+38t` |

Here the bordered matrix is

                 [ Trel+ - 50I    v ]
            Kb = [                    ],                    (7)
                 [       e_p^T     0 ]

where `v_p != 0` and `(Trel+-50I)v=0`.

### Border lemma

Let `H v=0`, `v_p!=0`, and suppose

                 [ H   v ]
                 [ e_p 0 ]

is nonsingular.  Then `ker(H)=<v>`: subtracting a suitable multiple of `v`
from any vector in `ker(H)` gives a vector in the kernel of the bordered
matrix.  Also `v` is not in `im(H)`: if `Hx=v`, adjust `x` by a multiple of
`v` to make `x_p=0`, producing a nonzero kernel vector of the bordered matrix.
Thus the zero eigenvalue of `H` has one Jordan block and that block has size
one.  It is algebraically simple.

Applying the lemma to (7), 50 is algebraically simple in `Trel+`.  It is absent
from `Trel-`, so it is algebraically simple in `Trel`.  It is absent from both
reflection blocks of `U1` and `U2`.  By (2), it is algebraically simple in
`Wrel` as well.

Together with the singleton checks, the multiplicity of the factor `1-50z`
in the right side of (1), reduced modulo 101, is therefore exactly

    1 + 0 + 1 = 2.                                         (8)

## 5. Contradiction to cubic divisibility

Normalize `Q_5,Q_5^+` as primitive integer polynomials with constant term 1.
They divide characteristic determinants of integer transfer matrices, so this
normalization is available by Gauss's lemma.

Assume that

    Q_5(z)^3 divides Q_5^+(z) in Q[z].                       (9)

The reduced open denominator `Q_5^+` divides the integer transfer determinant
in (1).  Hence (9) implies, over `Z[z]`,

    Q_5(z)^3 divides det(I-zB).

Reducing modulo 101 and using (6) would force

    (1-50z)^3 divides det(I-z bar(B)).                       (10)

But (8) says that the multiplicity is exactly two.  This contradicts (10).
Consequently

    Q_5^+(z) is not divisible by Q_5(z)^3.

Thus the proposed assertion for every `m>=5` is false, with counterexample

    m = 5.

## 6. Independent and transfer-count sanity checks

`src/bruteforce_5x4.cpp` is an independent Held--Karp computation.  It obtains
164 directed Hamiltonian paths and hence 82 paths after identifying reversal.

The transfer terminal function gives

| n | closed `S_(5,n)` | open `S^+_(5,n)` |
|---:|---:|---:|
| 4 | 0 | 82 |
| 5 | 0 | 864 |
| 6 | 8 | 18,784 |
| 8 | 44,202 | 18,061,054 |
| 10 | 13,311,268 | 7,886,117,822 |
| 12 | 4,557,702,762 | 3,611,823,644,006 |

These checks are not used in the rank proof, but they audit the startup and
terminal conventions, including endpoints in the last board column.
