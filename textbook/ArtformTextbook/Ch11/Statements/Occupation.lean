import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import ArtformTextbook.Ch11.Defs.Occupation

/-!
# Statements of Chapter 11: many particles on the cells

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open scoped Matrix

/-- **Proposition 11.11** (the order is a presentation). Changing the order of the modes
conjugates every creation and every annihilation by one diagonal matrix `Σ` of signs, the same
for all of them. Every operator built from them is conjugated by `Σ`, every occupation number
`n_m = a†_m a_m` is unchanged, and every report, which reads squared sizes of coefficients on
basis states, is unchanged.

Here `ord₁` is the old order and `ord₂` the new one; an operator built from the creations and
annihilations is a noncommutative polynomial in them (`Fock.build`); `a†_m a_m` is, in either
order, the diagonal matrix of the occupation numbers `n_m`; and a report reads the squared size
of the coefficient of a built operator from one basis table to another. -/
@[book "prop:mt-order-witness"]
def mtOrderWitness : Prop :=
  ∀ (M : Type) [Fintype M] [DecidableEq M] (ord₁ ord₂ : LinearOrder M),
    ∃ Sig : Matrix (Finset M) (Finset M) ℂ,
      (∃ s : Finset M → ℂ, (∀ n, s n = 1 ∨ s n = -1) ∧ Sig = Matrix.diagonal s) ∧
      (∀ m, Fock.creation ord₂ m = Sig * Fock.creation ord₁ m * Sig⁻¹) ∧
      (∀ m, Fock.annihilation ord₂ m = Sig * Fock.annihilation ord₁ m * Sig⁻¹) ∧
      (∀ P : FreeAlgebra ℂ (M ⊕ M), Fock.build ord₂ P = Sig * Fock.build ord₁ P * Sig⁻¹) ∧
      (∀ m, Fock.creation ord₁ m * Fock.annihilation ord₁ m =
          Matrix.diagonal (fun n => if m ∈ n then 1 else 0) ∧
        Fock.creation ord₂ m * Fock.annihilation ord₂ m =
          Matrix.diagonal (fun n => if m ∈ n then 1 else 0)) ∧
      (∀ (P : FreeAlgebra ℂ (M ⊕ M)) (n' n : Finset M),
        ‖Fock.build ord₂ P n' n‖ ^ 2 = ‖Fock.build ord₁ P n' n‖ ^ 2)

/-- **Proposition 11.12** (second quantization is a homomorphism).
`Γ(g₂) Γ(g₁) = Γ(g₂ g₁)`, and `Γ(g) a†_{cs} Γ(g)⁻¹ = Σ_{c'} g_{c'c} a†_{c's}`. For a unitary
`g`, `Γ(g)` is unitary.

The modes of the vertex are the pairs `(c, s)` of a colour in `C` and a slot in `S` (the book's
`C` has three colours), in any chosen order; `g` in the second part is invertible, as `Γ(g)⁻¹`
requires. -/
@[book "prop:mt-gamma"]
def mtGamma : Prop :=
  ∀ (C S : Type) [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
    (ord : LinearOrder (C × S)),
    (∀ g₁ g₂ : Matrix C C ℂ,
      Fock.vertexGamma ord g₂ * Fock.vertexGamma ord g₁ = Fock.vertexGamma ord (g₂ * g₁)) ∧
    (∀ (g : GL C ℂ) (c : C) (s : S),
      Fock.vertexGamma ord g * Fock.creation ord (c, s) * (Fock.vertexGamma ord g)⁻¹ =
        ∑ c', (g : Matrix C C ℂ) c' c • Fock.creation ord (c', s)) ∧
    (∀ g ∈ Matrix.unitaryGroup C ℂ,
      Fock.vertexGamma ord g ∈ Matrix.unitaryGroup (Finset (C × S)) ℂ)

end Artform.Statement
