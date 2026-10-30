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
- **Plan.** Phase 4 is open, as the author chooses.

`STATUS.md` gives the state of each statement, and `manifest.toml` its text.
