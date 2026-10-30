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
  - One back-step forces `A B` or `B A` into `⟨A⁻¹ B⟩`, and the cat map's score of forward
    kicks and backward moves rings neither `SL(2, Z/n)` nor `PSL(2, Z/n)` for any `n ≥ 3`
    (`BackSteps.lean`).
  - The balance (`Runs.lean`): in any permutation of a finite group, each coset of `⟨c⟩` holds as
    many back-steps as elements `v` with `B v` the target of a back-step. It excludes one
    back-step, or two, by a small computation.
  - The table of extents (`ExtentTable.lean`; finding 043, Theorems S5.3 and S5.4): `2`, `16` and
    `768` extents on `Z/2`, `Z/3` and `Z/6`, counted exactly; none on `Z/n` for
    `n = 4, 5, 10, 11, 13`; some for `n = 7, 9, 12`; exactly two back-steps on `n = 4, 5, 10, 13`
    and on the two squares; at least three on `Z/11`. The runs are certificates, which
    `scripts/extent_certificates.py` writes (`Certificates/Extents.lean`) and the kernel checks on
    natural numbers.
  - A linear permutation law commutes with the shifts, so it only transports, in any dimension
    (`Transport.lean`; finding 082, without Theorem K).
- **Phase 4** continues with T13, the step groups and their geometry (findings 037 and 038).
  - `StepGroups.lean`, Theorem Q: the one-mode tick has finite order exactly at `μ = 1, 2, 3`. The
    step group lies in `Γ¹(μ)`, with equality exactly when `μ ≤ 4`, by a descent, and has the
    indices `1, 3, 8, 12` and then infinite index. It is free exactly when `μ ≥ 4`, by ping-pong.
  - `KleinMap.lean`, Theorem U: the primitive states of a dial up to sign form a regular map of type
    `{3, n}`, on whose directed edges `PSL(2, Z/n)` acts simply transitively, so
    `|PSL| = V n = 2 E = 3 F`. For `n = 3, 4, 5` these are the counts of the tetrahedron, the
    octahedron and the icosahedron. A law that fixes a vertex, an edge or a face has the trace
    `±2`, `0` or `±1`.
  - `StepPresentations.lean`, Theorem Q's table as presentations, by a ping-pong on the lines of
    `ℤ²`: the table's relations imply every relation at `μ = 1, 2, 3`, `Γ¹(3) ≅ Z ∗ Z₃`, and
    `Γ¹(4)` is free.
  - `TwoSquares.lean`, Theorem Y: the two squares generate `PGL(2, 5)` on the projective line over
    `F₅`, which is `S₅`, and their labelling is forced. `PSL(2, 5) ≅ A₅`.
- **Phase 4** continues with the smaller statements.
  - `Steinberg.lean`: R2, Steinberg's relations on `c` channels, with the sign of the commutator in
    time order; T1's fewest steps; and T2 as a group, `GL₂(S)/E₂(S) ≅ S*` over a field.
  - `FaceLink.lean`: T11. The link form is the face form conjugated by `diag(1, D*)`, and at the
    zero mode it is the identity, while the face form is a kick.
  - `PalindromeClasses.lean`: T12. A law is processing-equivalent to a palindrome exactly when some
    `P` reverses it with `-det P` a square. A class that time reversal fixes need not hold one.
  - `Callers.lean`: T14's rules and one cue, and T16, the duet.
  - T8, the classes of the leapfrog phase, S3.4 and S3.5 of finding 057:
    - `LeapfrogCurve.lean`: the normalization `F[s, 1/(s(s-1)(s-q))]` of the curve, its involution
      and its value on the fibre `E = F[r]/(r² - q)` over the node.
    - `LeapfrogUnits.lean`: `E^×/F^× ≅ U` (Hilbert 90), and the units of the normalization, whose
      images generate `⟨-1, ρ⟩`.
    - `LeapfrogClasses.lean`: the primitive eigenvector of a law, its stencil lattice and the
      classes.
    - `MagicStep.lean`: the magic step, by the normal form `[[x, 0], [w, 1/x]]`.
    - `LeapfrogPalindromes.lean`: T12's correction. A palindrome lies in the unglued class, the
      trivial class or the class of `κ = (1 - r)/w`, and each of them holds one; at the correction's
      fourteen pairs a class that time reversal fixes holds none.
    - `LeapfrogExamples.lean`: the finding's tables, computed from the theorems.
- **Plan.** The rest of the ledger is out of this library's reach. T3, T5, T6, T9, T10 and T14's spectral gaps are
  literature theorems beyond Mathlib or open problems.

`STATUS.md` gives the state of each statement, and `manifest.toml` its text.

The [independent review of 30 October 2026](review/audit-2026-10-30.md) records
verdicts for all nine scores handoffs and all 63 submitted entries: 54 approved
and nine returned. Each submitted Lean proposition has a checked proof;
`STATUS.md` counts it as **proved** only after independent approval against the
ledger. Returned claims, their valid intermediate results, and the remaining
proof-package requirements are detailed in the review.

The [repair handoff](review/repairs-2026-10-30.md) addresses all nine returns.
`ArtformScores/ReviewRepair/` adds the missing conclusions while retaining the
original propositions as conjuncts and callable lemmas. R4 now connects its
corrected time-order word to the diagonal law; R2's source bracket is explicit;
and the one-back-step package has a positive five-state witness. The manifest
maps the six stronger claims to their new proofs. The original return verdicts
remain in force until a different agent reviews the repairs. Checked repairs
are recorded as submitted, not independently approved.
