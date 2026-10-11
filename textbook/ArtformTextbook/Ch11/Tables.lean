import Mathlib.GroupTheory.Perm.Fin
import ArtformTextbook.Ch11.Statements.Tables

/-!
# The two write families (Proposition 11.2)

Both computations of the book are associativity in `G`.
-/

namespace Artform

section Writes

variable {G : Type*} [Group G] {A : Type*}

@[simp] theorem leftWrite_apply (h : G) (ψ : G → A) (U : G) :
    leftWrite h ψ U = ψ (h⁻¹ * U) := rfl

@[simp] theorem rightWrite_apply (h : G) (ψ : G → A) (U : G) :
    rightWrite h ψ U = ψ (U * h) := rfl

/-- `L_h L_k = L_{hk}`. -/
theorem leftWrite_leftWrite (h k : G) (ψ : G → A) :
    leftWrite h (leftWrite k ψ) = leftWrite (h * k) ψ := by
  funext U
  simp [mul_assoc]

/-- `R_h R_k = R_{hk}`. -/
theorem rightWrite_rightWrite (h k : G) (ψ : G → A) :
    rightWrite h (rightWrite k ψ) = rightWrite (h * k) ψ := by
  funext U
  simp [mul_assoc]

@[simp] theorem leftWrite_one (ψ : G → A) : leftWrite 1 ψ = ψ := by
  funext U
  simp

@[simp] theorem rightWrite_one (ψ : G → A) : rightWrite 1 ψ = ψ := by
  funext U
  simp

theorem leftWrite_rightWrite (h k : G) (ψ : G → A) :
    leftWrite h (rightWrite k ψ) = rightWrite k (leftWrite h ψ) := by
  funext U
  simp [mul_assoc]

end Writes

/-- **Proposition 11.2** (the two write families). Left and right writes commute with each
other, `L_h R_k = R_k L_h` for all `h, k`. A gauge change `(h_x, h_y)` acts on the link's
coefficient table by one write of each kind, `ψ ↦ L_{h_y} R_{h_x} ψ`,
`(L_{h_y} R_{h_x} ψ)(U) = ψ(h_y⁻¹ U h_x)`, the table that assigns to the moved link
`h_y U h_x⁻¹` the coefficient the old table assigned to `U`. -/
@[book "prop:mt-writes"]
theorem mtWrites : Statement.mtWrites := by
  intro G _ A
  refine ⟨leftWrite_rightWrite, fun hx hy ψ U => by simp [mul_assoc], fun hx hy ψ φ => ?_⟩
  constructor
  · intro h
    funext U
    have := h (hy⁻¹ * U * hx)
    simp only [leftWrite_apply, rightWrite_apply]
    rw [← this]
    congr 1
    group
  · rintro rfl U
    simp only [leftWrite_apply, rightWrite_apply]
    congr 1
    group

/-! ## Non-vacuity -/

/-- Proposition 11.2 on the book's `S₃` link: the gauge pair `((13), (12))` moves the
coefficient that the table `δ_e` has at the identity to the cell `(12)(13)`. -/
example :
    let ψ : Equiv.Perm (Fin 3) → ℤ := fun U => if U = 1 then 1 else 0
    leftWrite (Equiv.swap 0 1) (rightWrite (Equiv.swap 0 2) ψ)
      (Equiv.swap 0 1 * 1 * (Equiv.swap 0 2)⁻¹) = 1 := by
  intro ψ
  have h := ((mtWrites (Equiv.Perm (Fin 3)) ℤ).2.2 (Equiv.swap 0 2) (Equiv.swap 0 1) ψ
    (leftWrite (Equiv.swap 0 1) (rightWrite (Equiv.swap 0 2) ψ))).mpr rfl 1
  rw [h]
  simp [ψ]

end Artform
