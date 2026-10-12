import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Basic
import ArtformTextbook.Ch03.Defs.Recognition
import ArtformTextbook.Ch05.Holonomy

/-!
# Matter, constraints and gauge-safe profiles (*Matter, invariance, and constraints*)

* Definition 5.30: a representation of `G` on a finite-dimensional complex
  vector space `V` (Mathlib's `Representation ℂ G V`); a matter field, one
  vector at every vertex; and its covariant transport along an edge,
  `ψ_u ↦ ρ(U_e) ψ_u`.
* Definition 5.32: a Gauss constraint, a gauge-invariant predicate on the
  total states, selecting the legal ones. Its inhabitant at a state is a
  witness, a proof of a proposition that may have none. It moves nothing.
* Definition 5.33: a recognition profile is gauge-safe on a gauge state type
  when, for every state `x` and gauge change `α`, the identity correspondence on
  positions is an invertible match `x → α · x`. The profile reads each state
  on one set of positions (`GaugeReading`).
-/

namespace Artform

/-! ## Definition 5.30: matter fields and covariant transport -/

/-- **Definition 5.30** (matter field): a table `ψ : C₀(K) → V`, one vector `ψ_v`
at every vertex. -/
@[book "def:matter"]
def MatterField (X : Skeleton) (V : Type*) : Type _ := X.V → V

/-- **Definition 5.30** (covariant transport): for a representation `ρ` of `G`
on a finite-dimensional complex vector space `V`, the connection `U` transports
a matter field covariantly along the edge `e : u → v` by `ψ_u ↦ ρ(U_e) ψ_u`. -/
@[book "def:matter"]
def covariantTransport {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {X : Skeleton} (U : X.LinkTable G)
    (e : X.E) : V →ₗ[ℂ] V :=
  ρ (U e)

/-! ## Definition 5.32: Gauss constraints -/

/-- **Definition 5.32** (Gauss constraint): a predicate on the total states,
gauge-invariant under the action `act` of the gauge changes, which selects the
legal states. -/
@[book "def:gauss"]
structure GaussConstraint {𝒢 S : Type*} (act : 𝒢 → S → S) where
  /-- The predicate: an inhabitant at a state is a witness. -/
  holds : S → Prop
  /-- It is gauge-invariant. -/
  gauge_invariant : ∀ h x, holds (act h x) ↔ holds x

/-- The legal states that a Gauss constraint selects. -/
def GaussConstraint.legal {𝒢 S : Type*} {act : 𝒢 → S → S} (c : GaussConstraint act) : Set S :=
  {x | c.holds x}

/-! ## Definition 5.33: gauge-safe profiles -/

/-- A reading of the states of a gauge frame by the recognition profile `R`, on
one set of positions: the verdicts and values that `R` selects, at each state. -/
structure GaugeReading (R : RecognitionProfile) (S : Type*) where
  /-- The positions. -/
  Pos : Type
  [finitePos : Finite Pos]
  /-- The sort of each position. -/
  sort : Pos → R.PosSort
  /-- The verdicts of the selected relations at each state. -/
  rel : S → (r : R.Rel) → (Fin (R.relArity r) → Pos) → Option Bool
  /-- The values of the selected channels at each state. -/
  chan : S → (a : R.Chan) → (Fin (R.chanArity a) → Pos) → Option (R.Val a)
  rel_wellSorted : ∀ x r t, rel x r t ≠ none → ∀ i, sort (t i) = R.relSort r i
  chan_wellSorted : ∀ x a t, chan x a t ≠ none → ∀ i, sort (t i) = R.chanSort a i

attribute [instance] GaugeReading.finitePos

namespace GaugeReading

variable {R : RecognitionProfile} {S : Type*}

/-- The state `x`, as the profile reads it. -/
def state (ρ : GaugeReading R S) (x : S) : ProfiledState R where
  Pos := ρ.Pos
  sort := ρ.sort
  rel := ρ.rel x
  chan := ρ.chan x
  rel_wellSorted := ρ.rel_wellSorted x
  chan_wellSorted := ρ.chan_wellSorted x

/-- **Definition 5.33** (gauge-safe profile): for every state `x` and every gauge
change `α`, the identity correspondence on positions is an invertible match
`x → α · x`: a strong occurrence, with some label map, whose inverse is a strong
occurrence too. -/
@[book "def:gauge-safe"]
def GaugeSafe {𝒢 : Type*} (act : 𝒢 → S → S) (ρ : GaugeReading R S) : Prop :=
  ∀ (x : S) (α : 𝒢), ∃ g : R.Relabel,
    IsStrongOccurrence (ρ.state x) (ρ.state (act α x)) g id ∧
      IsStrongOccurrence (ρ.state (act α x)) (ρ.state x) g⁻¹ id

end GaugeReading

/-! ## Non-vacuity -/

/-- Loop-flatness of the link tables is a Gauss-type constraint: it is
invariant under the gauge action, which conjugates the holonomy of every
loop. -/
example {X : Skeleton} {G : Type*} [Group G] :
    GaussConstraint (fun (h : X.V → G) (U : X.LinkTable G) => Skeleton.gaugeAct h U) :=
  ⟨Skeleton.LoopFlat, fun h U => by
    constructor
    · intro hU v γ
      have := hU v γ
      rw [Skeleton.hol_gaugeAct] at this
      have h2 : Skeleton.hol U γ = (h v)⁻¹ * (h v * Skeleton.hol U γ * (h v)⁻¹) * h v := by
        group
      rw [h2, this]
      group
    · intro hU v γ
      rw [Skeleton.hol_gaugeAct, hU v γ]
      group⟩

/-- A reading whose verdicts and values do not depend on the state is
gauge-safe, with the trivial label map. -/
example {R : RecognitionProfile} {S 𝒢 : Type*} (act : 𝒢 → S → S) (P : Type) [Finite P]
    (sort : P → R.PosSort) :
    (⟨P, sort, fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ h => absurd rfl h,
      fun _ _ _ h => absurd rfl h⟩ : GaugeReading R S).GaugeSafe act := by
  intro x α
  refine ⟨1, ⟨Function.injective_id, fun _ => rfl, ?_, ?_, ?_⟩,
    ⟨Function.injective_id, fun _ => rfl, ?_, ?_, ?_⟩⟩ <;>
    intros <;> simp_all [GaugeReading.state]

end Artform
