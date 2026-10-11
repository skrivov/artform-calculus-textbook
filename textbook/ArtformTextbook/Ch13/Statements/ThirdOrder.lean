import ArtformTextbook.Ch12.Groups
import ArtformTextbook.Ch13.Defs.ThirdOrder

/-!
# Statements of Chapter 13: the third-order transfer

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of Theorem 11.20: one edge with any number of slots, a finite colour group
with a triplet `ρ` in `SU(3)`, a complete family of irreducible representations with an electric
energy table, the energy law `κ H_E + V`, and any orthogonal projector `P` onto the zero-flux
sector. The third-order term is `Edge.thirdOrder` (`Ch13/Defs/ThirdOrder.lean`).
-/

namespace Artform.Statement

open scoped Matrix ComplexConjugate

open Module

open Classical in
/-- **Theorem 13.8** (the third-order transfer). On the zero-flux sector of one edge, the
third-order term of the energy law `eq:mt-energy-law` is `H⁽³⁾ = L/(κ E₃)²`, `L = P V³ P`, and
with the cubic moment `⟨U_{ij} U_{kl} U_{mn}⟩ = ε_{ikm} ε_{jln}/6` of Proposition 11.19,
`L = (1/6) Σ_{c,c'} sgn(c) sgn(c') A_{c₃c'₃} A_{c₂c'₂} A_{c₁c'₁} + h.c.` for a complex triplet,
the sum over the six orderings `c` of the target colours and the six orderings `c'` of the
source colours, with `A_{cc'} = Σ_s a†_{ycs} a_{xc's}` as in Theorem 11.20. For a real triplet
the same weight `sgn(c) sgn(c')/6` multiplies each of the eight words in which every factor is
`A` or `A†`.

The setting is that of Theorem 11.20 and of Proposition 11.19, on which the cubic moment rests:
a finite group `G` with a triplet `ρ : G → SU(3)`, irreducible, whose `3^{⊗3}` has exactly one
invariant; any number of slots and any order of the modes; a complete family `σ` with an electric
energy table `E` that declares `E₃` on the members isomorphic to the triplet or its conjugate;
`κ > 0`; and any orthogonal projector `P` onto the zero-flux sector.
* "The third-order term" is read as the book's proof reads it: `P V R V R V P`
  (`Edge.thirdOrder`), with `R = -(κ H_E)⁻¹` off the sector (`Edge.reducedResolvent`, zero on
  the sector), the other third-order terms carrying the factor `P V P`, which is zero; the
  statement says that `P V P = 0`.
* "A real triplet" is one whose matrices are real; "a complex triplet" is read through the
  centre, as for every complex model of the book: some element acts by `ω`, which makes the
  words with a conjugated entry average to zero (the book's reason, that
  `3 ⊗ 3 ⊗ 3̄` has no invariant, is a consequence).
* The words are `Edge.transferWords`, the sums written with `ε` in place of the signs of the
  orderings; "`L =` the words" holds on the zero-flux sector, at every link value.

The four finite models are stated as instances, for any number of slots: Models I and II, the
cube and icosahedral groups, real; Refinements I and II, `C₃ × A₅` and Valentiner's group,
complex. `SU(3)` itself is not covered: its projector averages over the link with the invariant
measure, which, as for Theorem 11.20, is not used. -/
@[book "thm:ml-transfer"]
def mlTransfer : Prop :=
  let claims : (G : Type) → [Group G] → [Fintype G] → (S : Type) → [Fintype S] →
      [DecidableEq S] → (G →* Matrix (Fin 3) (Fin 3) ℂ) → Bool → Prop :=
    fun G _ _ S _ _ ρ real =>
      ∀ (ord : LinearOrder (Edge.Mode (Fin 3) S)) (ι : Type) [Fintype ι] (d : ι → ℕ)
        (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)), IsCompleteFamily σ →
      ∀ E : ι → ℚ, IsEnergyTable σ E → ∀ E₃ : ℚ,
        (∀ i, (Nonempty ((Edge.tripletRep ρ).Equiv (σ i)) ∨
          Nonempty ((Edge.conjTripletRep ρ).Equiv (σ i))) → E i = E₃) →
      ∀ κ : ℝ, 0 < κ →
      ∀ P, Edge.IsZeroFluxProj ρ ord P →
        (∀ ψ, P (Edge.hop ρ ord (P ψ)) = 0) ∧
        ∀ ψ ∈ Edge.zeroFlux ρ ord,
          Edge.thirdOrder ρ ord σ E κ P ψ =
            (((κ * E₃ : ℝ) : ℂ) ^ 2)⁻¹ •
              P (Edge.hop ρ ord (Edge.hop ρ ord (Edge.hop ρ ord (P ψ)))) ∧
          P (Edge.hop ρ ord (Edge.hop ρ ord (Edge.hop ρ ord (P ψ)))) =
            Edge.atEachLink (Edge.transferWords ord real) ψ
  (∀ (G : Type) [Group G] [Fintype G] (S : Type) [Fintype S] [DecidableEq S]
      (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ), (∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) →
      (Edge.tripletRep ρ).IsIrreducible → finrank ℂ ↥(Edge.tripleInvariants ρ) = 1 →
      ∀ real : Bool, (real = true ∧ ∀ U i j, conj (ρ U i j) = ρ U i j) ∨
        (real = false ∧ ∃ h₀, ρ h₀ = Exact.omega • 1) →
      claims G S ρ real) ∧
  ∀ (S : Type) [Fintype S] [DecidableEq S],
    claims cubeGroup S cubeTriplet true ∧ claims icoGroup S icoTriplet true ∧
    claims C3A5 S c3a5Triplet false ∧ claims valentiner S valentinerTriplet false

end Artform.Statement
