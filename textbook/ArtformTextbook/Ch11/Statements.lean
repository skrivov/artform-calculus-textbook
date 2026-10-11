import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic
import ArtformTextbook.Meta.Book

/-!
# The statements of Chapter 11

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition. Representations are Mathlib's: finite-dimensional
complex representations of a finite group.
-/

namespace Artform.Statement

open scoped BigOperators ComplexConjugate

open Classical in
/-- **Proposition 11.5** (averaging counts). For a representation `W` of `G`,
the average `(1/|G|) Σ_U W(U)` is the projector onto the vectors fixed by `G`,
so the number of independent fixed vectors is `(1/|G|) Σ_U χ_W(U)`. For two
irreducible characters, `(1/|G|) Σ_U χ_ρ(U) conj(χ_σ(U))` is `1` when `ρ = σ`
and `0` otherwise; hence the number of times `ρ` occurs in `W` is
`(1/|G|) Σ_U χ_W(U) conj(χ_ρ(U))`. Here `ρ = σ` means that the two
representations are isomorphic, and the number of times `ρ` occurs in `W` is
the dimension of the equivariant maps from `ρ` to `W`. -/
@[book "prop:mt-average"]
def mtAverage : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (W : Representation ℂ G V),
      let avg : V →ₗ[ℂ] V := (Fintype.card G : ℂ)⁻¹ • ∑ g, W g
      avg ∘ₗ avg = avg ∧ LinearMap.range avg = W.invariants ∧
        (Module.finrank ℂ W.invariants : ℂ) = (Fintype.card G : ℂ)⁻¹ * ∑ g, W.character g) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
        (ρ : Representation ℂ G V) (σ : Representation ℂ G V'),
        ρ.IsIrreducible → σ.IsIrreducible →
        (Fintype.card G : ℂ)⁻¹ * ∑ g, ρ.character g * conj (σ.character g) =
          if Nonempty (ρ.Equiv σ) then 1 else 0) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
        (W : Representation ℂ G V) (ρ : Representation ℂ G V'), ρ.IsIrreducible →
        (Module.finrank ℂ (ρ.IntertwiningMap W) : ℂ) =
          (Fintype.card G : ℂ)⁻¹ * ∑ g, W.character g * conj (ρ.character g))

end Artform.Statement
