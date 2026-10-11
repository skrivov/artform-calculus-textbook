import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic
import ArtformTextbook.Meta.Book

/-!
# Tensors with upper and lower colour indices (Section 12.1, "Where the extra states come from")

The tensors with `a` upper and `b` lower colour indices, `3^{⊗a} ⊗ 3̄^{⊗b}`, are the coefficient
tables over the pairs of multi-indices `(i, j)`, `i : Fin a → Fin 3` and `j : Fin b → Fin 3`. A
matrix `g` acts on them by `g^{⊗a} ⊗ ḡ^{⊗b}`: the entry of `g` on each upper index and of its
complex conjugate on each lower index. The invariants of a colour group are the tensors that every
element fixes; for `SU(3)` (`ρ` the inclusion) their number is "the count for `SU(3)`" of
Theorem 12.2, the number of invariant tensors with `a` upper and `b` lower indices.
-/

namespace Artform

open scoped Matrix ComplexConjugate

/-- The multi-indices of the tensors with `a` upper and `b` lower indices. -/
abbrev TensorIdx (a b : ℕ) : Type := (Fin a → Fin 3) × (Fin b → Fin 3)

/-- The matrix of `g^{⊗a} ⊗ ḡ^{⊗b}`:
`((g^{⊗a} ⊗ ḡ^{⊗b}))_{(i,j),(i',j')} = Π_r g_{i_r i'_r} · Π_r conj(g_{j_r j'_r})`. -/
noncomputable def tensorPowMat (g : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℕ) :
    Matrix (TensorIdx a b) (TensorIdx a b) ℂ :=
  Matrix.of fun p q => (∏ r, g (p.1 r) (q.1 r)) * ∏ r, conj (g (p.2 r) (q.2 r))

/-- The invariant tensors of a colour group: the tensors with `a` upper and `b` lower indices
fixed by `ρ(h)^{⊗a} ⊗ conj(ρ(h))^{⊗b}` for every `h`. -/
noncomputable def tensorInvariants {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (a b : ℕ) : Submodule ℂ (TensorIdx a b → ℂ) where
  carrier := {T | ∀ h, tensorPowMat (ρ h) a b *ᵥ T = T}
  add_mem' {T T'} hT hT' h := by
    simp only [Set.mem_ofPred_eq] at hT hT'
    rw [Matrix.mulVec_add, hT, hT']
  zero_mem' h := Matrix.mulVec_zero _
  smul_mem' c T hT h := by
    simp only [Set.mem_ofPred_eq] at hT
    rw [Matrix.mulVec_smul, hT]

end Artform
