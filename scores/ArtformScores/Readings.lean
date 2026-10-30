import ArtformScores.Statements

/-!
# What a run reveals

T12 of the algebra of scores: from rest, the output of a law depends only on its
phase and its reading; and a law with no cut is reversed by the reflection
`P₀ = diag(1, -1)`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

variable {S : Type*} [CommRing S]

/-- Cayley-Hamilton for a law: `T² = (tr T) T - 1`. -/
theorem sq_eq_phase_smul_sub (A : SpecialLinearGroup (Fin 2) S) :
    (A : Matrix (Fin 2) (Fin 2) S) * A =
      (A : Matrix (Fin 2) (Fin 2) S).trace • (A : Matrix (Fin 2) (Fin 2) S) - 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  · linear_combination (-1 : S) * hdet
  · ring
  · ring
  · linear_combination (-1 : S) * hdet

/-- The powers of a law obey the recurrence of its phase:
`T^(n+2) = (tr T) T^(n+1) - T^n`. -/
theorem pow_add_two (A : SpecialLinearGroup (Fin 2) S) (n : ℕ) :
    (A : Matrix (Fin 2) (Fin 2) S) ^ (n + 2) =
      (A : Matrix (Fin 2) (Fin 2) S).trace • (A : Matrix (Fin 2) (Fin 2) S) ^ (n + 1) -
        (A : Matrix (Fin 2) (Fin 2) S) ^ n := by
  rw [pow_add, sq, sq_eq_phase_smul_sub, Matrix.mul_sub, Matrix.mul_smul, mul_one, ← pow_succ]

/-- **T12** (the reading). -/
theorem readingDetermines : Statement.readingDetermines := by
  intro S _ T T' ht ha n b₀
  have key : ∀ m : ℕ,
      ((T : Matrix (Fin 2) (Fin 2) S) ^ m) 0 0 = ((T' : Matrix (Fin 2) (Fin 2) S) ^ m) 0 0 ∧
      ((T : Matrix (Fin 2) (Fin 2) S) ^ (m + 1)) 0 0 =
        ((T' : Matrix (Fin 2) (Fin 2) S) ^ (m + 1)) 0 0 := by
    intro m
    induction m with
    | zero => exact ⟨by simp, by simpa [reading] using ha⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [pow_add_two T m, pow_add_two T' m]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [ih.1, ih.2]
      simp only [phase] at ht
      rw [ht]
  simp [Matrix.SpecialLinearGroup.coe_pow, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    (key n).1]

/-- **T12** (palindromes). -/
@[ledger "T12"]
theorem palindrome : Statement.palindrome := by
  intro S _ T had
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, had]

/-! ## Non-vacuity

The move `M(2)` and the kick `K(3)` over `F₇` share the phase 2 and the reading
1, so the reading theorem applies to them. Strang's tick `K(1/2) M(-3) K(1/2)`
over `F₇` (with `1/2 = 4`) has no cut, so the palindrome theorem applies. -/

/-- The move `M(2)` and the kick `K(3)` over `F₇` share phase and reading. -/
theorem move_kick_share :
    phase (Step.move (2 : ZMod 7)).sl = phase (Step.kick 3).sl ∧
      reading (Step.move (2 : ZMod 7)).sl = reading (Step.kick 3).sl := by
  simp [phase, reading, Step.mat, Matrix.trace_fin_two]

/-- From rest, `M(2)` and `K(3)` give the same flux at every tick. -/
example (n : ℕ) (b₀ : ZMod 7) :
    Matrix.mulVec (((Step.move (2 : ZMod 7)).sl ^ n : SpecialLinearGroup (Fin 2) (ZMod 7)) :
      Matrix (Fin 2) (Fin 2) (ZMod 7)) ![b₀, 0] 0 =
    Matrix.mulVec (((Step.kick (3 : ZMod 7)).sl ^ n : SpecialLinearGroup (Fin 2) (ZMod 7)) :
      Matrix (Fin 2) (Fin 2) (ZMod 7)) ![b₀, 0] 0 :=
  readingDetermines (ZMod 7) _ _ move_kick_share.1 move_kick_share.2 n b₀

/-- Strang's tick over `F₇` has no cut. -/
theorem strang_no_cut :
    ((realize [Step.kick (4 : ZMod 7), Step.move (-3), Step.kick 4] :
      SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0 =
    ((realize [Step.kick (4 : ZMod 7), Step.move (-3), Step.kick 4] :
      SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) 1 1 := by
  simp only [realize_cons, realize_nil, one_mul, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl]
  decide

/-- So the reflection reverses Strang's tick. -/
example : !![1, 0; 0, -1] * ((realize [Step.kick (4 : ZMod 7), Step.move (-3), Step.kick 4] :
      SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) * !![1, 0; 0, -1] =
    (((realize [Step.kick (4 : ZMod 7), Step.move (-3), Step.kick 4])⁻¹ :
      SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) :=
  palindrome (ZMod 7) _ strang_no_cut

end Artform.Scores
