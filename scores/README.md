# The algebra of scores

The Lean library `ArtformScores`: a calculus of the simulation schemes studied in
the author's research ledger on lattice waves (`ALGEBRA-OF-SCORES.md` there). It
is not book text, and nothing here enters the library `ArtformTextbook` until the
book states it.

- **Steps.** A kick `K f` is the shear `e += f b`, and a move `M f` is the shear
  `b += f e`, on two channels with values in a commutative ring.
- **Scores.** A score is a list of steps in time order. The realizer sends it to its
  law in `SL(2, S)`.
- **Phase 1** proves the rules R1 (merging), R3 (Whitehead's rule), R4 (balanced
  movers) and R5 (time reversal), and the theorems T2 (the index), T12 (the reading
  and palindromes), T13 (the crystallographic pulls) and T14 (the caller's cut).
- **Phase 2** proves T1: every law of determinant 1 in `SL(2, R[x, 1/x])` is a score
  when `R` is a field, `Z/p^k` or `Z/n`.
  - Over a field, the proof is Euclid's algorithm on the first column, with
    polynomial division after a shift by a power of `x` (`Euclid.lean`).
  - Over `Z/p^k`, a law reduced modulo `p` is a score over `F_p`; lifted back, it
    leaves a law with a unit corner, which is `K(m) diag(u, 1/u) M(v)` (`Lifting.lean`).
  - Over `Z/n`, the Chinese remainder theorem splits the dial into prime powers
    (`CRT.lean`).
- **Phase 3** proves T4: on one mode over `F_p`, `p = 5, 7, 11, 13`, merging and
  Whitehead's rule present `SL(2, F_p)` on `X = M(1)` and `Y = K(1)`.
  - The presented group maps onto `SL(2, F_p)` (`OneMode.lean`).
  - It is no bigger: a coset table of `⟨X⟩` with `p² - 1` rows covers it
    (`Coset.lean`). Every edge of the table is a tree edge, the subgroup's edge, or a
    deduction from one relator through earlier edges, and Lean checks the table by
    computation (`decide +kernel`).
  - `scripts/one_mode_certificates.py` writes the four tables (`Certificates/`), by
    Todd–Coxeter enumeration; with `--check` it fails if a table differs from its output.
- **Phase 4** begins with R6, blocking (`Blocking.lean`).
  - Blocking reads an artform on `m` places as one with `2m` channels, through the matrix of
    multiplication by each stencil (`Algebra.leftMulMatrix`). The realizer commutes with it.
  - Red-black is a law of the blocked artform, since its kicks are placed steps. The blocked
    shift turns it into black-red, so it is the blocking of no law of the artform once the
    move couples red and black.
  - Every sublattice blocking is a case: the shifts by coset representatives are a basis of
    the stencils over the sublattice's stencils (`Checkerboard.lean`).
  - On `ℤ²` the checkerboard has the basis `1, x`, with `x² = u v` a unit. The book's face
    form `g = 4 - x - 1/x - y - 1/y` has the black part `-(1 + 1/u + 1/v + 1/(u v))`, so
    red-black with the half move `M(-λg/2)` is the blocking of no law of the plane.
- **Phase 4** continues with T7, the class of a law (`Classes.lean`, after Latimer and
  MacDuffee).
  - The row `(c, λ - a)` is a left eigenvector of a law of phase `t` on the curve
    `A_t = S[λ]/(λ² - tλ + 1)`.
  - Processing keeps the class of the ideal `(c, λ - a)`, when `t² - 4` is not a square.
  - A cyclic vector conjugates the law to the companion tick, so its class is trivial; and a
    law in the trivial class has a cyclic vector.
  - The correspondence is one to one: two laws of phase `t` are in one class exactly when
    processing turns one into the other.
  - Over a principal ideal domain, as `F[x, 1/x]` (`Euclid.lean`), every nonzero ideal of
    `A_t` is in the class of a law: the matrix of `λ` on a basis of the ideal.
- **Phase 4** continues with T15, the bells (`Bells.lean`; the ledger's finding 042).
  - A change is an involution, so the painted rows of every method obey the tick
    `u(t + 1) + u(t - 1) = (P_t + P_(t-1)) u(t)`. Two changes cut the row into mirror boxes
    and dodges.
  - Plain hunt is light in a mirror box: `P_X + P_Y = S_mirror`. Each bell's path is a circle
    of `2N` places folded onto the box, and the plain course has `2N` rows. The modes
    `cos(πk(2i + 1)/(2N))` have the eigenvalues `2 cos(πk/N)`.
  - Coxeter's rules present `S_N` on the swaps of neighbours (Moore 1897), against Mathlib's
    `CoxeterMatrix.A`. The descending runs `s_m ⋯ s_k` are coset representatives, so the
    presented group has at most `N!` elements.
  - Extents, the peals of all the rows (`Extents.lean`; finding 043): Rankin's parity, the
    lifting lemma, and the Fibonacci rule, by which a forward extent of `SL(2, p)` or
    `PSL(2, p)` under the leapfrog's `K` and `M` needs `4 ∣ α(p)`, the Fibonacci rank of
    apparition. So `SL(2, 5)` has none.
- **Plan.** The rest of Phase 4, as the author chooses.

`STATUS.md` gives the state of each statement, and `manifest.toml` its text.
