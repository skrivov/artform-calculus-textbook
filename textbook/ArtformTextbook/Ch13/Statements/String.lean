import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import ArtformTextbook.Ch11.Defs.Response
import ArtformTextbook.Ch12.Groups
import ArtformTextbook.Ch13.Defs.String

/-!
# Statements of Chapter 13: a flux string

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of `Ch13/Defs/String.lean`: the path `x₀ → x₁ → ⋯ → x_R` of `R` edges, its
link tables, the holonomy `P = Hol_U(γ) = U_R ⋯ U_1` of the path `γ` from `x₀` to `x_R`, and
matter at the two ends. The five colour groups are the cube group, the icosahedral group,
`C₃ × A₅`, Valentiner's group `S(1080)` (Chapter 12) and `SU(3)`, each with its triplet, the
inclusion into the `3 × 3` matrices (for `C₃ × A₅`, the triplet `(ω^j, g) ↦ ω^j g` of
Definition 12.11). A triplet is read as real when all its matrices are real.
-/

namespace Artform.Statement

open scoped Matrix ComplexConjugate

open Polynomial in
/-- **Proposition 13.1** (colourless states of a path). On a path whose matter sits at the two
ends, a colourless state depends on the links only through their product, the holonomy
`P = U_R ⋯ U_1` of `eq:path-holonomy`, and the colourless states of the path are the colourless
states of one edge with link `P`. With a quark source at `x₀`, an antiquark source at `x_R` and
`d` slots at each end, their number with `k` dynamical quarks is the coefficient of `z^k` in
`⟨χ(g) conj(χ(g)) det(1 + z g)^{2d}⟩_G`.

The path has `R ≥ 1` edges, so that its two ends are different vertices. The matter at the two
ends is any finite-dimensional matter on which the gauge pair `(h_{x₀}, h_{x_R}) ∈ G × G` acts by
matrices `Γ(h_{x₀}, h_{x_R})` (a representation), and `G` is any group; a colourless state of the
path is a coefficient table `ψ` over the link tables with `ψ(U^h) = Γ(h_{x₀}, h_{x_R}) ψ(U)`
(`PathCanvas.colourless`), and a colourless state of one edge is a table `φ` over the link values
with `φ(h_y P h_x⁻¹) = Γ(h_x, h_y) φ(P)` (`Edge.colourlessWith`, Definition 11.13 with this
matter). "Depends on the links only through `P`": two link tables with the same holonomy give the
same coefficients. "Are the colourless states of one edge with link `P`": a linear isomorphism
`e` with `(e ψ)(P(U)) = ψ(U)`. For the count the group is finite, with a triplet
`ρ : G →* Matrix C C ℂ` and `χ(g) = Tr ρ(g)`; the quark source is moved by `ρ`, the antiquark
source by its conjugate, and the `d = |S|` slots at each end are the modes of one edge from `x₀`
to `x_R` in any order (`PathCanvas.endMatter`); `det(1 + z g)` is `det(1 + z ρ(g))`, and
`⟨·⟩_G` is the average over `G`, a polynomial in `z`. "Their number with `k` dynamical quarks" is
the dimension of the colourless states whose every coefficient table has `k` quarks. -/
@[book "prop:ml-path"]
def mlPath : Prop :=
  (∀ (G : Type) [Group G] (N : Type) [Fintype N] [DecidableEq N]
      (Γ : G × G →* Matrix N N ℂ) (R : ℕ), 0 < R →
    (∀ ψ ∈ PathCanvas.colourless R Γ, ∀ U U' : (Canvas.path R).skeleton.LinkTable G,
      Skeleton.hol U (PathCanvas.γ R) = Skeleton.hol U' (PathCanvas.γ R) → ψ U = ψ U') ∧
    ∃ e : ↥(PathCanvas.colourless R Γ) ≃ₗ[ℂ] ↥(Edge.colourlessWith Γ),
      ∀ (ψ : ↥(PathCanvas.colourless R Γ)) (U : (Canvas.path R).skeleton.LinkTable G),
        (e ψ : G → N → ℂ) (Skeleton.hol U (PathCanvas.γ R)) =
          (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ) U) ∧
  ∀ (G : Type) [Group G] [Fintype G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S)) (R : ℕ),
    0 < R → ∀ k : ℕ,
    (Module.finrank ℂ ↥(PathCanvas.colourless R
        (PathCanvas.endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ PathCanvas.quarkSector R k) : ℂ) =
      ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, Polynomial.C ((ρ g).trace * conj (ρ g).trace) *
        (1 + (X : ℂ[X]) • (ρ g).map Polynomial.C).det ^ (2 * Fintype.card S)).coeff k

open Classical in
/-- **Theorem 13.2** (the string). Let a quark source sit at `x₀` and an antiquark source at
`x_R`, with no dynamical quarks.
1. For each of the five colour groups there is one colourless line, spanned by the string
   `ψ_{cc'}(U_1, …, U_R) = (U_1⁻¹ U_2⁻¹ ⋯ U_R⁻¹)_{cc'} = conj((U_R ⋯ U_1)_{c'c})`, with `c` the
   source index at `x₀` and `c'` the one at `x_R`: the antiquark's colour transported back along
   the path to the quark. On every link its table lies in the conjugate triplet block, declared at
   the level `E₃` and equal to the triplet block when the triplet is real, so under the declared
   law its electric energy is `κ E₃ R`: one level per link, linear in the length. No hop acts on
   it, and it is an eigenstate of `H`.
2. With two quark sources in place of a quark and an antiquark there is a colourless state
   exactly when the triplet is real, `⟨χ²⟩ = 1`, and it is the same string. For a complex triplet
   there is none: no string of any length joins two quarks.

The path has `R ≥ 1` edges. "With no dynamical quarks" is read as the book's proof reads it, with
`d = 0` in Proposition 13.1: the matter is the two sources alone (`PathCanvas.sourcePair`), the
quark source moved by `ρ` and the antiquark source by its conjugate, and the hop term of the law
`H = κ Σ_j H_{E,j} + Σ_j V_j` is zero ("with no dynamical quarks the second sum is zero", the
formation line of the string model), so that `H = κ Σ_j H_{E,j}`. "One colourless line spanned by
the string": the colourless states are the multiples of the string, which is not zero. "On every
link its table lies in the block": with the other links fixed, each coefficient of the string is a
table over the value of the link that lies in the block (Definition 11.3) of the conjugate
triplet. The declared law reads the electric energy of a link as an operator `X` on the tables of
one link that multiplies the block of the conjugate triplet by its declared level `E₃`
(Definition 11.9); for the four finite groups that operator is the convolution of
Definition 11.9 (`electricEnergy`), for every complete family of irreducible representations and
every table `E` that declares `E₃` on the members isomorphic to the conjugate triplet, and the
statement is made for it as well; for `SU(3)` the book defines no convolution, and the statement is
made for every operator with this property. "One level per link": the operator of each link
multiplies the string by `E₃`. "A colourless state" in part 2 means a nonzero one; "it is the same
string": the colourless states with two quark sources are the multiples of the string, whose
`(c, c')` coefficient is then `(U_R ⋯ U_1)_{c'c}`. `⟨χ²⟩` is the number of invariants of
`3 ⊗ 3` (`pairInvariants`, as `fig:mm-moments` counts it for `SU(3)`), and for the four finite
groups also the average of `χ(g)²`. -/
@[book "thm:ml-string"]
def mlString : Prop :=
  let real : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop :=
    fun _ _ ρ => ∀ g i j, conj (ρ g i j) = ρ g i j
  let claims : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop := fun G _ ρ =>
    ∀ R : ℕ, 0 < R →
      PathCanvas.colourless R (PathCanvas.sourcePair ρ (Edge.conjTriplet ρ)) =
        Submodule.span ℂ {PathCanvas.string R ρ} ∧
      PathCanvas.string R ρ ≠ 0 ∧
      (∀ (U : (Canvas.path R).skeleton.LinkTable G) (c c' : Fin 3),
        PathCanvas.string R ρ U (c, c') =
          conj (ρ (Skeleton.hol U (PathCanvas.γ R)) c' c)) ∧
      (∀ (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) (c c' : Fin 3),
        (fun g => PathCanvas.string R ρ ((Canvas.path R).setLink U j g) (c, c')) ∈
          block (Edge.conjTripletRep ρ)) ∧
      (real G ρ → block (Edge.conjTripletRep ρ) = block (Edge.tripletRep ρ)) ∧
      (∀ (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ) (κ : ℝ),
        (∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) →
        (∀ j : Fin R, (Canvas.path R).onLink (liftTable X) j (PathCanvas.string R ρ) =
          (E₃ : ℂ) • PathCanvas.string R ρ) ∧
        (κ : ℂ) • PathCanvas.electric R X (PathCanvas.string R ρ) =
          ((κ * E₃ * R : ℝ) : ℂ) • PathCanvas.string R ρ) ∧
      ((∃ ψ ∈ PathCanvas.colourless R (PathCanvas.sourcePair ρ ρ), ψ ≠ 0) ↔ real G ρ) ∧
      (real G ρ →
        PathCanvas.colourless R (PathCanvas.sourcePair ρ ρ) =
          Submodule.span ℂ {PathCanvas.string R ρ} ∧
        ∀ (U : (Canvas.path R).skeleton.LinkTable G) (c c' : Fin 3),
          PathCanvas.string R ρ U (c, c') = ρ (Skeleton.hol U (PathCanvas.γ R)) c' c) ∧
      (¬ real G ρ → PathCanvas.colourless R (PathCanvas.sourcePair ρ ρ) = ⊥) ∧
      Module.finrank ℂ ↥(pairInvariants ρ) = if real G ρ then 1 else 0
  let declared : (G : Type) → [Group G] → [Fintype G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop :=
    fun G _ _ ρ =>
      (∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
        IsCompleteFamily σ → ∀ (E : ι → ℚ) (E₃ : ℚ),
        (∀ i, Nonempty ((Edge.conjTripletRep ρ).Equiv (σ i)) → E i = E₃) →
        ∀ R : ℕ, 0 < R → ∀ κ : ℝ,
          (κ : ℂ) • PathCanvas.electric R (electricEnergy σ E) (PathCanvas.string R ρ) =
            ((κ * E₃ * R : ℝ) : ℂ) • PathCanvas.string R ρ) ∧
      groupAvg G (fun g => (ρ g).trace ^ 2) = if real G ρ then 1 else 0
  claims cubeGroup cubeTriplet ∧ claims icoGroup (ColourGroups.subTriplet icoGroup) ∧
  claims C3A5 ColourGroups.c3a5Triplet ∧ claims valentiner (ColourGroups.subTriplet valentiner) ∧
  claims (Matrix.specialUnitaryGroup (Fin 3) ℂ) ColourGroups.su3Triplet ∧
  declared cubeGroup cubeTriplet ∧ declared icoGroup (ColourGroups.subTriplet icoGroup) ∧
  declared C3A5 ColourGroups.c3a5Triplet ∧
  declared valentiner (ColourGroups.subTriplet valentiner)

open Classical in
/-- **Proposition 13.3** (the screening number). The least number of dynamical quarks with which
both sources are colourless without flux is `2` when the triplet is real and `3` when it is
complex. In the first case one quark sits at each source, in either spin: four states. In the
second, two quarks in the antisymmetric colour pair sit at the quark source, in any of the three
symmetric spin states, and one at the antiquark source: six states.

The setting is that of Proposition 13.1 and `fig:ml-string-census`: a path of `R ≥ 1` edges, a
quark source at `x₀`, an antiquark source at `x_R`, and two slots ("either spin") at each end,
the modes in any order; the statement is made for each of the five colour groups, a triplet being
real when its matrices are. "Colourless without flux" is the zero-flux sector: colourless states
constant in the link table (`PathCanvas.zeroFlux`), with `k` dynamical quarks
(`PathCanvas.quarkSector`); "the least number" is `k_min` with no nonzero such state for
`k < k_min`. The states are named by their vectors, as constant states: one quark at each
source, colour paired with it, in the slots `s` and `t` (`PathCanvas.pairScreen`); two quarks at
the quark source with the colour tensor `ε_{cab}`, in the slots `s ≤ t`, and one at the antiquark
source in the slot `u` (`PathCanvas.baryonScreen`), which is symmetric in `s` and `t`. "One quark
sits at each source" says that every such state has one quark at each end
(`PathCanvas.endSector`), and likewise for two and one. -/
@[book "prop:ml-screening"]
def mlScreening : Prop :=
  let real : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop :=
    fun _ _ ρ => ∀ g i j, conj (ρ g i j) = ρ g i j
  let claims : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop := fun G _ ρ =>
    ∀ (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (R : ℕ), 0 < R →
      let Z : ℕ → Submodule ℂ ((Canvas.path R).skeleton.LinkTable G →
          (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) := fun k =>
        PathCanvas.zeroFlux R (PathCanvas.endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓
          PathCanvas.quarkSector R k
      (real G ρ →
        (∀ k < 2, Z k = ⊥) ∧
        Z 2 = Submodule.span ℂ (Set.range fun st : Fin 2 × Fin 2 =>
          PathCanvas.constState R (G := G) (PathCanvas.pairScreen ord st.1 st.2)) ∧
        Z 2 ≤ PathCanvas.endSector R 1 1 ∧
        Module.finrank ℂ ↥(Z 2) = 4) ∧
      (¬ real G ρ →
        (∀ k < 3, Z k = ⊥) ∧
        Z 3 = Submodule.span ℂ (Set.range fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
          PathCanvas.constState R (G := G) (PathCanvas.baryonScreen ord p.1.1.1 p.1.1.2 p.2)) ∧
        (∀ s t u, PathCanvas.baryonScreen ord s t u = PathCanvas.baryonScreen ord t s u) ∧
        Z 3 ≤ PathCanvas.endSector R 2 1 ∧
        Module.finrank ℂ ↥(Z 3) = 6)
  claims cubeGroup cubeTriplet ∧ claims icoGroup (ColourGroups.subTriplet icoGroup) ∧
  claims C3A5 ColourGroups.c3a5Triplet ∧ claims valentiner (ColourGroups.subTriplet valentiner) ∧
  claims (Matrix.specialUnitaryGroup (Fin 3) ℂ) ColourGroups.su3Triplet

open Classical in
/-- **Proposition 13.4** (where the string and screened levels cross). For a quark source and an
antiquark source at distance `R`, the unscreened string has lower electric-plus-mass energy than
the minimal zero-flux screened state while `κ E₃ R < k_min M`, `k_min = 2` for a real triplet and
`3` for a complex one, and a screened state of Proposition 13.3 is lower beyond. With `E₃ = 4/3`
the crossing is at `R = 3M/(2κ)` for the rotation groups and at `R = 9M/(4κ)` for the others. The
hop conserves the quark number, so the two states lie in different sectors: the crossing is a
comparison of two levels of one law, not a decay.

The setting is that of Proposition 13.3 (two slots at each end, the modes in any order), for each
of the five colour groups, with `R ≥ 1`, a coupling `κ > 0` and a mass `M ≥ 0`. The
electric-plus-mass energy is `κ Σ_j H_{E,j} + H_M` (the string law's electric energy and the
declared mass term `H_M = M Σ_m n_m`): the electric energy of a link is an operator `X` on the
tables of one link that multiplies the block of the conjugate triplet by its declared level `E₃`
and the trivial block (the constant tables) by `0` (Definition 11.9); for the four finite groups
the convolution `electricEnergy` of Definition 11.9, for a complete family and an electric energy
table that declares `E₃` on the members isomorphic to the conjugate triplet, is such an operator,
and the statement says so. The unscreened string is the string with empty occupation tables
(`PathCanvas.stringState`); the minimal screened states are the zero-flux states with `k_min`
dynamical quarks. A state's level is its eigenvalue: the string's is `κ E₃ R`, every screened
state's is `k_min M`, and "lower" compares them, for any eigenvalues of the string and of a
nonzero screened state. "The two states lie in different sectors": the string has no dynamical
quark and the screened states have `k_min ≠ 0`; "the hop conserves the quark number": the hop of
one edge (Section 11.6, `Edge.hop`), which each `V_j` is, maps the states with `k` quarks to
states with `k` quarks. -/
@[book "prop:ml-breaking"]
def mlBreaking : Prop :=
  let real : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop :=
    fun _ _ ρ => ∀ g i j, conj (ρ g i j) = ρ g i j
  let kmin : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → ℕ :=
    fun G _ ρ => if real G ρ then 2 else 3
  let claims : (G : Type) → [Group G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop := fun G _ ρ =>
    (∀ (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ),
      (∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) → (∀ c : ℂ, X (fun _ => c) = 0) →
      ∀ (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (R : ℕ), 0 < R → ∀ κ M : ℝ, 0 < κ →
        0 ≤ M →
        let H := fun ψ : (Canvas.path R).skeleton.LinkTable G →
            (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ =>
          (κ : ℂ) • PathCanvas.electric R X ψ + PathCanvas.mass R M ψ
        let Z := PathCanvas.zeroFlux R (PathCanvas.endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓
          PathCanvas.quarkSector R (kmin G ρ)
        H (PathCanvas.stringState R ρ) =
          ((κ * E₃ * R : ℝ) : ℂ) • PathCanvas.stringState R ρ ∧
        (∀ ψ ∈ Z, H ψ = ((kmin G ρ * M : ℝ) : ℂ) • ψ) ∧
        (∀ ψ ∈ Z, ψ ≠ 0 → ∀ lstr lscr : ℝ,
          H (PathCanvas.stringState R ρ) = (lstr : ℂ) • PathCanvas.stringState R ρ →
          H ψ = (lscr : ℂ) • ψ →
            (lstr < lscr ↔ κ * E₃ * R < kmin G ρ * M) ∧
            (lscr < lstr ↔ kmin G ρ * M < κ * E₃ * R)) ∧
        (E₃ = 4 / 3 → ((κ * E₃ * R = kmin G ρ * M) ↔
          (R : ℝ) = if real G ρ then 3 * M / (2 * κ) else 9 * M / (4 * κ))) ∧
        PathCanvas.stringState (S := Fin 2) R ρ ∈ PathCanvas.quarkSector R 0 ∧
        Z ≤ PathCanvas.quarkSector R (kmin G ρ) ∧ kmin G ρ ≠ 0) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] (ord : LinearOrder (Edge.Mode (Fin 3) S)) (k : ℕ),
      ∀ ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) k),
        Edge.hop ρ ord ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) k)
  let declared : (G : Type) → [Group G] → [Fintype G] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Prop :=
    fun G _ _ ρ =>
      ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
        IsCompleteFamily σ → ∀ E : ι → ℚ, IsEnergyTable σ E → ∀ E₃ : ℚ,
        (∀ i, Nonempty ((Edge.conjTripletRep ρ).Equiv (σ i)) → E i = E₃) →
        (∀ f ∈ block (Edge.conjTripletRep ρ), electricEnergy σ E f = (E₃ : ℂ) • f) ∧
        ∀ c : ℂ, electricEnergy σ E (fun _ : G => c) = 0
  claims cubeGroup cubeTriplet ∧ claims icoGroup (ColourGroups.subTriplet icoGroup) ∧
  claims C3A5 ColourGroups.c3a5Triplet ∧ claims valentiner (ColourGroups.subTriplet valentiner) ∧
  claims (Matrix.specialUnitaryGroup (Fin 3) ℂ) ColourGroups.su3Triplet ∧
  declared cubeGroup cubeTriplet ∧ declared icoGroup (ColourGroups.subTriplet icoGroup) ∧
  declared C3A5 ColourGroups.c3a5Triplet ∧
  declared valentiner (ColourGroups.subTriplet valentiner)

end Artform.Statement
