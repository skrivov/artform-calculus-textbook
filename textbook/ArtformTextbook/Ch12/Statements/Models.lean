import ArtformTextbook.Ch12.Defs.Models
import ArtformTextbook.Ch12.Defs.Tensor
import ArtformTextbook.Ch12.Groups

/-!
# Statements of Chapter 12: the matter models on one edge with two slots

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of `Ch12/Defs/Models.lean`: three colours, two slots read as spin, one vertex
with the six modes `(c, s)` and one edge `x → y` with twelve. The five colour groups of the
chapter are Model I (the cube group, `cubeTriplet`), Model II (the icosahedral group,
`icoTriplet`), Refinement I (`C₃ × A₅`, `c3a5Triplet`), Refinement II (Valentiner's group,
`valentinerTriplet`) and the `SU(3)` reference (`su3Triplet`). The two real triplets have the pair
hop, `m = 1` in the tally of Theorem 11.20; the three complex ones, the `SU(3)`-type models, have
`m = 0`.

* **Zero-flux states.** A zero-flux state is constant in the link value (Definition 11.13), and the
  tally acts on it at every link value. A zero-flux state is read through its value `ψ(1)`, a
  coefficient table: `Edge.zeroFluxValues ρ ord` is the space of these values, and the tally acts
  on it as the matrix `Ω = Edge.tally ord m`. "`Ω` has the value `μ` with multiplicity `k` on the
  sector" is `Edge.sectorMult ρ ord Ω μ = k` for every `μ`, the multiplicity `0` for a value not
  listed: the multiplicities listed sum to the dimension of the sector, so the operator is
  diagonalizable there with exactly these values.
* **Orders of the modes.** A count or a spectrum is stated for every order `ord` of the modes. A
  claim about named states (the pair `D_x`, the chain, the singlet, the hole map) is stated in the
  order in which the book writes those states, `Edge.bookOrd`: `x` before `y`, colour before spin,
  "a product fills the ends in the order written".
-/

namespace Artform.Statement

open scoped Matrix ComplexConjugate

open Module

/-- **Proposition 12.1** (the eight invariants of a vertex with two slots). For the cube group
with two slots, the colourless states of one vertex number `1, 0, 1, 4, 1, 0, 1` by quark number,
eight in all, and the eight states of Figure `fig:mm-two-slot-invariants` are a basis of them. Six
of the eight are fixed by `SU(3)`; the pair and the paired holes are not.

The colourless states of one vertex are its invariant occupation tables
(`Edge.vertexInvariants`), the six modes in any order `ord`; the number with `k` quarks is the
dimension of those with `k` quarks, and none has more than six. The eight states are written in
creations as the figure prints them (`Vertex.eight`); "a basis" is: independent, and spanning the
invariants. "Fixed by `SU(3)`": fixed by `Γ(g)` for every `g ∈ SU(3)`; "not fixed": moved by some
`g ∈ SU(3)`. -/
@[book "prop:mm-two-slot-invariants"]
def mmTwoSlotInvariants : Prop :=
  ∀ ord : LinearOrder (Fin 3 × Fin 2),
    (∀ k : ℕ, finrank ℂ ↥(Edge.vertexInvariants cubeTriplet ord ⊓
        Fock.numberSector (Fin 3 × Fin 2) k) =
      if k = 0 then 1 else if k = 2 then 1 else if k = 3 then 4 else if k = 4 then 1
      else if k = 6 then 1 else 0) ∧
    finrank ℂ (Edge.vertexInvariants cubeTriplet ord) = 8 ∧
    LinearIndependent ℂ (Vertex.eight ord) ∧
    Submodule.span ℂ (Set.range (Vertex.eight ord)) = Edge.vertexInvariants cubeTriplet ord ∧
    (∀ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ, ∀ i : Fin 6,
      Fock.vertexGamma ord g *ᵥ Vertex.six ord i = Vertex.six ord i) ∧
    (∃ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
      Fock.vertexGamma ord g *ᵥ Vertex.pair ord ≠ Vertex.pair ord) ∧
    ∃ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
      Fock.vertexGamma ord g *ᵥ Vertex.holes ord ≠ Vertex.holes ord

open Classical in
/-- **Theorem 12.2** (every extra state is located in one average). Let `G ≤ SU(3)` be a finite
colour group with triplet character `χ`. The number of colourless states with `n` quarks on one
edge with `d` slots is
`Σ_{a+2b+3c=n} (2d)!/(a! b! c! (2d-a-b-c)!) ⟨χ^a χ̄^b⟩`,
the sum over `a, b, c ≥ 0` with `a + b + c ≤ 2d`. Every average of `G` is at least the
corresponding count for `SU(3)`, so every entry of the census of `G` is at least the entry for
`SU(3)`, and the difference is the same sum taken over the differences of the averages.

The group is any finite group `G` with a triplet `ρ : G → SU(3)`, `χ(g) = Tr ρ(g)` and
`⟨χ^a χ̄^b⟩ = (1/|G|) Σ_g χ(g)^a conj(χ(g))^b`; the `6d` modes of the edge are in any order. The
number of colourless states with `n` quarks is the dimension of the colourless states whose every
coefficient table has `n` quarks, as in Theorem 11.15, and for `SU(3)` it is the same dimension
with `G = SU(3)` (colourless states are functions of the link value; no measure enters). "The
count for `SU(3)`" is, as the book says before the theorem, the number of invariant tensors with
`a` upper and `b` lower indices (`tensorInvariants su3Triplet a b`); "every average is at least the
count" is read as: the average is the number of invariants of `G` in `3^{⊗a} ⊗ 3̄^{⊗b}`
(Proposition 11.5, as the book reads it), and that number is at least the count for `SU(3)`. -/
@[book "thm:mm-census-moments"]
def mmCensusMoments : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ),
    (∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (ord : LinearOrder (Edge.Mode (Fin 3) S)),
    let D : ℕ := 2 * Fintype.card S
    let avg : ℕ → ℕ → ℂ := fun a b =>
      (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ a * conj ((ρ g).trace) ^ b
    let su3Count : ℕ → ℕ → ℕ := fun a b => finrank ℂ ↥(tensorInvariants su3Triplet a b)
    let census : ℕ → ℕ := fun n => finrank ℂ ↥(Edge.colourless ρ ord ⊓
      Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) n))
    let su3Census : ℕ → ℕ := fun n => finrank ℂ ↥(Edge.colourless su3Triplet ord ⊓
      Edge.stateSector (Matrix.specialUnitaryGroup (Fin 3) ℂ)
        (Fock.numberSector (Edge.Mode (Fin 3) S) n))
    let coeff : ℕ × ℕ × ℕ → ℂ := fun t =>
      (D.factorial : ℂ) / ((t.1.factorial * t.2.1.factorial * t.2.2.factorial *
        (D - t.1 - t.2.1 - t.2.2).factorial : ℕ) : ℂ)
    let terms : ℕ → Finset (ℕ × ℕ × ℕ) := fun n =>
      (Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
        fun t => t.1 + 2 * t.2.1 + 3 * t.2.2 = n ∧ t.1 + t.2.1 + t.2.2 ≤ D
    (∀ n, (census n : ℂ) = ∑ t ∈ terms n, coeff t * avg t.1 t.2.1) ∧
    (∀ a b, avg a b = (finrank ℂ ↥(tensorInvariants ρ a b) : ℂ) ∧
      su3Count a b ≤ finrank ℂ ↥(tensorInvariants ρ a b)) ∧
    (∀ n, su3Census n ≤ census n) ∧
    ∀ n, (census n : ℂ) - su3Census n =
      ∑ t ∈ terms n, coeff t * (avg t.1 t.2.1 - su3Count t.1 t.2.1)

/-- **Proposition 12.3** (the pair is bound more tightly than the quartet). On the two-quark
zero-flux sector of Model I, spanned by the pair at `x` and the pair at `y` with unit norm,
`Ω = [[2, 2], [2, 2]]`, with the value `4` on the sum of the two pairs and `0` on their difference.
Without the pair-hop term `Ω` is `2` on both. The quartet at one vertex has `Ω = 3`.

Model I's tally is `Edge.tally bookOrd 1`; without the pair-hop term it is `Edge.tally bookOrd 0`.
The two-quark zero-flux sector is the space of the zero-flux values with two quarks; the pairs
are `D_x = Edge.pairX` and `D_y = Edge.pairY`, of squared norm `3` (as the book's proof says), and
with unit norm `D_x / ‖D_x‖`. "The matrix `Ω` in that basis" is: `Ω` sends each unit pair to
`2` times their sum. "The quartet at one vertex" is each member `q_x(m)` at `x` with `y` empty, and
`q_y(m)` at `y`. -/
@[book "prop:mm-diquark"]
def mmDiquark : Prop :=
  Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓ Fock.numberSector (Edge.Mode (Fin 3) (Fin 2)) 2 =
    Submodule.span ℂ {Edge.pairX, Edge.pairY} ∧
  Fock.hilbertNorm Edge.pairX ^ 2 = 3 ∧ Fock.hilbertNorm Edge.pairY ^ 2 = 3 ∧
  Edge.tally Edge.bookOrd 1 *ᵥ Fock.normalized Edge.pairX =
    (2 : ℂ) • Fock.normalized Edge.pairX + (2 : ℂ) • Fock.normalized Edge.pairY ∧
  Edge.tally Edge.bookOrd 1 *ᵥ Fock.normalized Edge.pairY =
    (2 : ℂ) • Fock.normalized Edge.pairX + (2 : ℂ) • Fock.normalized Edge.pairY ∧
  Edge.tally Edge.bookOrd 1 *ᵥ (Edge.pairX + Edge.pairY) = (4 : ℂ) • (Edge.pairX + Edge.pairY) ∧
  Edge.tally Edge.bookOrd 1 *ᵥ (Edge.pairX - Edge.pairY) = 0 ∧
  Edge.tally Edge.bookOrd 0 *ᵥ Fock.normalized Edge.pairX = (2 : ℂ) • Fock.normalized Edge.pairX ∧
  Edge.tally Edge.bookOrd 0 *ᵥ Fock.normalized Edge.pairY = (2 : ℂ) • Fock.normalized Edge.pairY ∧
  ∀ m : Fin 4, Edge.tally Edge.bookOrd 1 *ᵥ Edge.quartetX m = (3 : ℂ) • Edge.quartetX m ∧
    Edge.tally Edge.bookOrd 1 *ᵥ Edge.quartetY m = (3 : ℂ) • Edge.quartetY m

open Classical in
/-- **Theorem 12.4** (the spectrum of the tally on one edge). On the `36` zero-flux states of the
`SU(3)`-type models the tally has the values `0⁹ 3¹⁶ 4⁵ 6² (20/3)³ 8¹`, multiplicities as
exponents. On the `64` states of Model I it has `0¹⁴ 3³² 4¹⁰ (20/3)⁶ 8²`. The largest value, `8`,
is reached once in the first case and twice in the second: once by a state with three quarks at
each end, and once by a state on the chain of Figure `fig:mm-chain`. With the pair-hop term
removed by hand the spectrum on the `64` states is
`0⁹ 2⁴ (8/3)² 3³² (10/3)² 4⁹ 6² (20/3)³ 8¹`, and `8` is reached once.

The `SU(3)`-type models are Refinement I, Refinement II and `SU(3)`, with `m = 0`; Model I has
`m = 1`, and the control is its sector with `m = 0`. The counts and spectra hold in every order of
the modes. The states at `8` are named in the book's order: the state with three quarks at each
end is the spin-singlet two-baryon state `ψ₀` (`Edge.singlet`, with three quarks at each end),
and the state on the chain is the uniform vector `½ (c₁ + c₂ + c₃ + c₄)` (`Edge.chainGround`); the
values at `8` are spanned by them. -/
@[book "thm:mm-spectra"]
def mmSpectra : Prop :=
  let mult36 : ℂ → ℕ := fun μ =>
    if μ = 0 then 9 else if μ = 3 then 16 else if μ = 4 then 5 else if μ = 6 then 2
    else if μ = 20 / 3 then 3 else if μ = 8 then 1 else 0
  let mult64 : ℂ → ℕ := fun μ =>
    if μ = 0 then 14 else if μ = 3 then 32 else if μ = 4 then 10 else if μ = 20 / 3 then 6
    else if μ = 8 then 2 else 0
  let multControl : ℂ → ℕ := fun μ =>
    if μ = 0 then 9 else if μ = 2 then 4 else if μ = 8 / 3 then 2 else if μ = 3 then 32
    else if μ = 10 / 3 then 2 else if μ = 4 then 9 else if μ = 6 then 2 else if μ = 20 / 3 then 3
    else if μ = 8 then 1 else 0
  (∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    finrank ℂ ↥(Edge.zeroFluxValues c3a5Triplet ord) = 36 ∧
    finrank ℂ ↥(Edge.zeroFluxValues valentinerTriplet ord) = 36 ∧
    finrank ℂ ↥(Edge.zeroFluxValues su3Triplet ord) = 36 ∧
    finrank ℂ ↥(Edge.zeroFluxValues cubeTriplet ord) = 64 ∧
    ∀ μ : ℂ,
      Edge.sectorMult c3a5Triplet ord (Edge.tally ord 0) μ = mult36 μ ∧
      Edge.sectorMult valentinerTriplet ord (Edge.tally ord 0) μ = mult36 μ ∧
      Edge.sectorMult su3Triplet ord (Edge.tally ord 0) μ = mult36 μ ∧
      Edge.sectorMult cubeTriplet ord (Edge.tally ord 1) μ = mult64 μ ∧
      Edge.sectorMult cubeTriplet ord (Edge.tally ord 0) μ = multControl μ) ∧
  Edge.singlet ∈ Edge.endSector (Fin 3) (Fin 2) 3 3 ∧
  Edge.chainGround ∈ Submodule.span ℂ (Set.range Edge.chain) ∧
  Edge.zeroFluxValues c3a5Triplet Edge.bookOrd ⊓
      End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 0)) 8 =
    Submodule.span ℂ {Edge.singlet} ∧
  Edge.zeroFluxValues valentinerTriplet Edge.bookOrd ⊓
      End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 0)) 8 =
    Submodule.span ℂ {Edge.singlet} ∧
  Edge.zeroFluxValues su3Triplet Edge.bookOrd ⊓
      End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 0)) 8 =
    Submodule.span ℂ {Edge.singlet} ∧
  Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓
      End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 1)) 8 =
    Submodule.span ℂ {Edge.singlet, Edge.chainGround}

/-- **Proposition 12.5** (the two-baryon states are ordered by spin). The sixteen states with
three quarks at each end are the products of the two quartets, and `Ω` commutes with `S_z` on them.
By `S_z` the sector splits into `1, 2, 3, 4, 3, 2, 1` states for `S_z = 3, …, -3`, and on the
sectors `|S_z| = 3, 2, 1, 0` the tally has the values `{0}`, `{0, 4}`, `{0, 4, 20/3}` and
`{0, 4, 20/3, 8}`. Read with the spin ladder, the seven states of spin `3` carry `0`, the five of
spin `2` carry `4`, the three of spin `1` carry `20/3`, and the one state of spin `0` carries `8`.
The sector and its tally are the same in all five models.

The sector is the space of zero-flux values with three quarks at each end
(`Edge.endSector (Fin 3) (Fin 2) 3 3`). "The products of the two quartets" is stated in the
book's order, where products are defined (`Edge.prod`): the sector is spanned by the sixteen
products `q(i) ⊗ q(j)`, which are independent. The rest holds in every order of the modes, for
each of the five models with its tally (`m = 1` for the real triplets, `m = 0` for the others).
"The tally has the values `W` on the sector `S_z = s`" is: `μ` is the value of a nonzero state of
the sector with `S_z = s` exactly when `μ ∈ W`. A state of spin `S` is one with
`S² ψ = S (S + 1) ψ` (`Edge.spinSq`); "the states of spin `S` carry `μ`": there are `2S + 1` of
them, and each has the tally `μ`. "The same in all five models": the five sectors are one space,
and on it the tally with the pair hop is the tally without it. -/
@[book "prop:mm-spin-order"]
def mmSpinOrder : Prop :=
  Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓ Edge.endSector (Fin 3) (Fin 2) 3 3 =
    Submodule.span ℂ (Set.range fun p : Fin 4 × Fin 4 =>
      Edge.prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2)) ∧
  LinearIndependent ℂ (fun p : Fin 4 × Fin 4 =>
      Edge.prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2)) ∧
  ∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    let Sz := Matrix.toLin' Edge.spinZ
    let S2 := Matrix.toLin' (Edge.spinSq ord)
    let values : ℤ → Set ℂ := fun s =>
      if s = 3 then {0} else if s = 2 then {0, 4} else if s = 1 then {0, 4, 20 / 3}
      else {0, 4, 20 / 3, 8}
    let ladder : Submodule ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) →
        Matrix (Finset (Edge.Mode (Fin 3) (Fin 2))) (Finset (Edge.Mode (Fin 3) (Fin 2))) ℂ →
        Prop := fun Z X =>
      (∀ v ∈ Z, Matrix.toLin' X (Sz v) = Sz (Matrix.toLin' X v)) ∧
      (∀ s : ℤ, finrank ℂ ↥(Z ⊓ End.eigenspace Sz (s : ℂ)) =
        if |s| ≤ 3 then 4 - s.natAbs else 0) ∧
      (∀ s : ℤ, |s| ≤ 3 → ∀ μ : ℂ,
        Z ⊓ End.eigenspace Sz (s : ℂ) ⊓ End.eigenspace (Matrix.toLin' X) μ ≠ ⊥ ↔
          μ ∈ values |s|) ∧
      finrank ℂ ↥(Z ⊓ End.eigenspace S2 12) = 7 ∧
      Z ⊓ End.eigenspace S2 12 ≤ End.eigenspace (Matrix.toLin' X) 0 ∧
      finrank ℂ ↥(Z ⊓ End.eigenspace S2 6) = 5 ∧
      Z ⊓ End.eigenspace S2 6 ≤ End.eigenspace (Matrix.toLin' X) 4 ∧
      finrank ℂ ↥(Z ⊓ End.eigenspace S2 2) = 3 ∧
      Z ⊓ End.eigenspace S2 2 ≤ End.eigenspace (Matrix.toLin' X) (20 / 3) ∧
      finrank ℂ ↥(Z ⊓ End.eigenspace S2 0) = 1 ∧
      Z ⊓ End.eigenspace S2 0 ≤ End.eigenspace (Matrix.toLin' X) 8
    let Z33 := Edge.endSector (Fin 3) (Fin 2) 3 3
    ladder (Edge.zeroFluxValues cubeTriplet ord ⊓ Z33) (Edge.tally ord 1) ∧
    ladder (Edge.zeroFluxValues icoTriplet ord ⊓ Z33) (Edge.tally ord 1) ∧
    ladder (Edge.zeroFluxValues c3a5Triplet ord ⊓ Z33) (Edge.tally ord 0) ∧
    ladder (Edge.zeroFluxValues valentinerTriplet ord ⊓ Z33) (Edge.tally ord 0) ∧
    ladder (Edge.zeroFluxValues su3Triplet ord ⊓ Z33) (Edge.tally ord 0) ∧
    Edge.zeroFluxValues icoTriplet ord ⊓ Z33 = Edge.zeroFluxValues cubeTriplet ord ⊓ Z33 ∧
    Edge.zeroFluxValues c3a5Triplet ord ⊓ Z33 = Edge.zeroFluxValues cubeTriplet ord ⊓ Z33 ∧
    Edge.zeroFluxValues valentinerTriplet ord ⊓ Z33 =
      Edge.zeroFluxValues cubeTriplet ord ⊓ Z33 ∧
    Edge.zeroFluxValues su3Triplet ord ⊓ Z33 = Edge.zeroFluxValues cubeTriplet ord ⊓ Z33 ∧
    ∀ v ∈ Edge.zeroFluxValues cubeTriplet ord ⊓ Z33, Edge.tally ord 1 *ᵥ v = Edge.tally ord 0 *ᵥ v

/-- **Proposition 12.6** (the pair hop is the cause). Remove the pair-hop term from `Ω` by hand,
leaving the two there-and-back histories with the moment `1/3`. Then on the sixty-four states the
value `8` is reached once, by the spin-zero two-baryon state; the pair drops to `2`, below the
quartet's `3`; and the chain of Figure `fig:mm-chain` falls apart into the two full vertices at
`6` and the two mixed states at `10/3`. The values `2`, `8/3` and `10/3`, which no `SU(3)`-type
state takes, appear only in this control.

The control is `Edge.tally ord 0` on the zero-flux sector of Model I. The multiplicity of `8` is
stated in every order; the named states in the book's order. The spin-zero two-baryon state is
`ψ₀` (`Edge.singlet`): three quarks at each end and `S² ψ₀ = 0`. The pair `D_x`, `D_y`, the
quartet members `q_x(m)`, `q_y(m)` and the chain `c₁, …, c₄` are those of Proposition 12.3 and
Figure `fig:mm-chain`. "Appear only in this control": each of the three values has a nonzero
multiplicity in the control, and multiplicity zero in the tally of every other model, Models I
and II with the pair hop and the three `SU(3)`-type models. -/
@[book "prop:mm-control"]
def mmControl : Prop :=
  (∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    Edge.sectorMult cubeTriplet ord (Edge.tally ord 0) 8 = 1) ∧
  Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓
      End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 0)) 8 =
    Submodule.span ℂ {Edge.singlet} ∧
  Edge.singlet ∈ Edge.endSector (Fin 3) (Fin 2) 3 3 ∧
  Edge.spinSq Edge.bookOrd *ᵥ Edge.singlet = 0 ∧
  Edge.tally Edge.bookOrd 0 *ᵥ Edge.pairX = (2 : ℂ) • Edge.pairX ∧
  Edge.tally Edge.bookOrd 0 *ᵥ Edge.pairY = (2 : ℂ) • Edge.pairY ∧
  (∀ m : Fin 4, Edge.tally Edge.bookOrd 0 *ᵥ Edge.quartetX m = (3 : ℂ) • Edge.quartetX m ∧
    Edge.tally Edge.bookOrd 0 *ᵥ Edge.quartetY m = (3 : ℂ) • Edge.quartetY m) ∧
  (∀ i : Fin 4, Edge.tally Edge.bookOrd 0 *ᵥ Edge.chain i =
    (![6, 10 / 3, 10 / 3, 6] i : ℂ) • Edge.chain i) ∧
  ∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)), ∀ μ ∈ ({2, 8 / 3, 10 / 3} : Set ℂ),
    0 < Edge.sectorMult cubeTriplet ord (Edge.tally ord 0) μ ∧
    Edge.sectorMult cubeTriplet ord (Edge.tally ord 1) μ = 0 ∧
    Edge.sectorMult icoTriplet ord (Edge.tally ord 1) μ = 0 ∧
    Edge.sectorMult c3a5Triplet ord (Edge.tally ord 0) μ = 0 ∧
    Edge.sectorMult valentinerTriplet ord (Edge.tally ord 0) μ = 0 ∧
    Edge.sectorMult su3Triplet ord (Edge.tally ord 0) μ = 0

/-- **Proposition 12.7** (a symmetry that only a real triplet has). On the sixty-four zero-flux
states of Model I, `𝒮` and the parity `(-1)^{N_x}` commute with `Ω` and anticommute with each
other. Every value of `Ω` there has even multiplicity, and `𝒮` exchanges the two states at the
ground value `8`: the spin-zero two-baryon state, of odd parity, and the chain of pairs, of even
parity. Without the pair hop, `𝒮` does not commute with `Ω`.

`𝒮` is the hole map of the book's verifier (`Edge.holeMap`), which depends on the order of the
modes; it and the named states are taken in the book's order. "On the sixty-four states" is read
as: `𝒮` keeps the zero-flux sector of Model I (the book's proof says so), and the relations hold on
every state of the sector. The even multiplicities hold in every order. "Exchanges": `𝒮 ψ₀` is
the chain state `½ (c₁ + c₂ + c₃ + c₄)` and `𝒮` sends that back to `ψ₀`. "Of odd parity":
`(-1)^{N_x} ψ = -ψ`. "Does not commute": some state of the sector on which `Ω 𝒮 ≠ 𝒮 Ω` with
`m = 0`. -/
@[book "prop:mm-particle-hole"]
def mmParticleHole : Prop :=
  (∀ v ∈ Edge.zeroFluxValues cubeTriplet Edge.bookOrd,
    Edge.holeMap Edge.bookOrd *ᵥ v ∈ Edge.zeroFluxValues cubeTriplet Edge.bookOrd ∧
    Edge.tally Edge.bookOrd 1 *ᵥ (Edge.holeMap Edge.bookOrd *ᵥ v) =
      Edge.holeMap Edge.bookOrd *ᵥ (Edge.tally Edge.bookOrd 1 *ᵥ v) ∧
    Edge.tally Edge.bookOrd 1 *ᵥ (Edge.parityX *ᵥ v) =
      Edge.parityX *ᵥ (Edge.tally Edge.bookOrd 1 *ᵥ v) ∧
    Edge.holeMap Edge.bookOrd *ᵥ (Edge.parityX *ᵥ v) =
      -(Edge.parityX *ᵥ (Edge.holeMap Edge.bookOrd *ᵥ v))) ∧
  (∀ (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (μ : ℂ),
    Even (Edge.sectorMult cubeTriplet ord (Edge.tally ord 1) μ)) ∧
  Edge.holeMap Edge.bookOrd *ᵥ Edge.singlet = Edge.chainGround ∧
  Edge.holeMap Edge.bookOrd *ᵥ Edge.chainGround = Edge.singlet ∧
  Edge.parityX *ᵥ Edge.singlet = -Edge.singlet ∧
  Edge.parityX *ᵥ Edge.chainGround = Edge.chainGround ∧
  ∃ v ∈ Edge.zeroFluxValues cubeTriplet Edge.bookOrd,
    Edge.tally Edge.bookOrd 0 *ᵥ (Edge.holeMap Edge.bookOrd *ᵥ v) ≠
      Edge.holeMap Edge.bookOrd *ᵥ (Edge.tally Edge.bookOrd 0 *ᵥ v)

open Classical in
/-- **Proposition 12.10** (Models I and II share their zero-flux sector). The eight states of
Figure `fig:mm-two-slot-invariants` are the one-vertex invariants of Model II as well, the
zero-flux sectors of the two models are the same sixty-four states, and their tallies `Ω` are the
same operator, with the spectrum of Theorem 12.4.

"Are the invariants": independent and spanning the one-vertex invariants of the icosahedral group,
in any order of the modes. The sectors are compared through their values, in any order. "Their
tallies are the same operator": for each of the two models, and every orthogonal projector `P`
onto its zero-flux sector (as in Theorem 11.20), the second-order return `P V² P` of the model's
own hop is the operator `Ω = Edge.tally ord 1` on the sector; the spectrum is that of Model I in
Theorem 12.4. -/
@[book "prop:mm-same-sector"]
def mmSameSector : Prop :=
  (∀ ord : LinearOrder (Fin 3 × Fin 2), LinearIndependent ℂ (Vertex.eight ord) ∧
    Submodule.span ℂ (Set.range (Vertex.eight ord)) = Edge.vertexInvariants icoTriplet ord) ∧
  ∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    Edge.zeroFluxValues icoTriplet ord = Edge.zeroFluxValues cubeTriplet ord ∧
    finrank ℂ ↥(Edge.zeroFluxValues icoTriplet ord) = 64 ∧
    (∀ P : (icoGroup → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
        (icoGroup → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ),
      (∀ ψ, P ψ ∈ Edge.zeroFlux icoTriplet ord) → (∀ ψ ∈ Edge.zeroFlux icoTriplet ord, P ψ = ψ) →
      (∀ ψ φ, Edge.statePairing (P ψ) φ = Edge.statePairing ψ (P φ)) →
      ∀ ψ ∈ Edge.zeroFlux icoTriplet ord,
        P (Edge.hop icoTriplet ord (Edge.hop icoTriplet ord ψ)) =
          Edge.atEachLink (Edge.tally ord 1) ψ) ∧
    (∀ P : (cubeGroup → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
        (cubeGroup → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ),
      (∀ ψ, P ψ ∈ Edge.zeroFlux cubeTriplet ord) →
      (∀ ψ ∈ Edge.zeroFlux cubeTriplet ord, P ψ = ψ) →
      (∀ ψ φ, Edge.statePairing (P ψ) φ = Edge.statePairing ψ (P φ)) →
      ∀ ψ ∈ Edge.zeroFlux cubeTriplet ord,
        P (Edge.hop cubeTriplet ord (Edge.hop cubeTriplet ord ψ)) =
          Edge.atEachLink (Edge.tally ord 1) ψ) ∧
    ∀ μ : ℂ, Edge.sectorMult icoTriplet ord (Edge.tally ord 1) μ =
      Edge.sectorMult cubeTriplet ord (Edge.tally ord 1) μ ∧
      Edge.sectorMult icoTriplet ord (Edge.tally ord 1) μ =
        if μ = 0 then 14 else if μ = 3 then 32 else if μ = 4 then 10 else if μ = 20 / 3 then 6
        else if μ = 8 then 2 else 0

open Classical in
/-- **Proposition 12.12** (triality, and the pair moment). For Refinement I the census vanishes
at every quark number that is not a multiple of three; the pair moment is `⟨χ²⟩ = 0`, so the pair
hop is absent and `m = 0` in Theorem 11.20; the one-vertex invariants at two slots are the six
states of Figure `fig:mm-two-slot-invariants` that `SU(3)` fixes; and the zero-flux sector and the
tally are those of the first row of Figure `fig:mm-exchange-spectra`, with the ground value `8`
reached once.

The census is that of Theorem 11.15, the colourless states of one edge with `n` quarks, for any
number of slots and any order of the modes. `⟨χ²⟩ = (1/|G|) Σ_g χ(g)²` with `χ = C3A5.char`.
"`m = 0` in Theorem 11.20" is read as the hypothesis of that theorem for `m = 0`, that `3 ⊗ 3` has
no invariant (`ρ(U) T ρ(U)ᵀ = T` for all `U` forces `T = 0`), together with its conclusion for
this group: for every orthogonal projector `P` onto the zero-flux sector, `P V² P` is the tally
with `m = 0`. "The six states are the invariants": independent and spanning, in any order. "The
zero-flux sector and the tally are those of the first row": the zero-flux values are those of
`SU(3)`, and the tally `Edge.tally ord 0` has on them the spectrum of the `SU(3)`-type models in
Theorem 12.4, in which `8` has multiplicity one. -/
@[book "prop:mm-centre"]
def mmCentre : Prop :=
  (∀ (S : Type) [Fintype S] [DecidableEq S] (ord : LinearOrder (Edge.Mode (Fin 3) S)) (n : ℕ),
    ¬ 3 ∣ n → finrank ℂ ↥(Edge.colourless c3a5Triplet ord ⊓
      Edge.stateSector C3A5 (Fock.numberSector (Edge.Mode (Fin 3) S) n)) = 0) ∧
  groupAvg C3A5 (fun x => C3A5.char x ^ 2) = 0 ∧
  (∀ T : Matrix (Fin 3) (Fin 3) ℂ, (∀ U, c3a5Triplet U * T * (c3a5Triplet U)ᵀ = T) → T = 0) ∧
  (∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    ∀ P : (C3A5 → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
        (C3A5 → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ),
      (∀ ψ, P ψ ∈ Edge.zeroFlux c3a5Triplet ord) →
      (∀ ψ ∈ Edge.zeroFlux c3a5Triplet ord, P ψ = ψ) →
      (∀ ψ φ, Edge.statePairing (P ψ) φ = Edge.statePairing ψ (P φ)) →
      ∀ ψ ∈ Edge.zeroFlux c3a5Triplet ord,
        P (Edge.hop c3a5Triplet ord (Edge.hop c3a5Triplet ord ψ)) =
          Edge.atEachLink (Edge.tally ord 0) ψ) ∧
  (∀ ord : LinearOrder (Fin 3 × Fin 2), LinearIndependent ℂ (Vertex.six ord) ∧
    Submodule.span ℂ (Set.range (Vertex.six ord)) = Edge.vertexInvariants c3a5Triplet ord) ∧
  ∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    Edge.zeroFluxValues c3a5Triplet ord = Edge.zeroFluxValues su3Triplet ord ∧
    ∀ μ : ℂ, Edge.sectorMult c3a5Triplet ord (Edge.tally ord 0) μ =
      if μ = 0 then 9 else if μ = 3 then 16 else if μ = 4 then 5 else if μ = 6 then 2
      else if μ = 20 / 3 then 3 else if μ = 8 then 1 else 0

end Artform.Statement
