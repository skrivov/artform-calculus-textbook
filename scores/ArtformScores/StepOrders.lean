import ArtformScores.Statements

/-!
# The crystallographic pulls

T13 of the algebra of scores: the one-mode tick of the leapfrog, `K(1)` then
`M(-μ)`, is `[[1 - μ, -μ], [1, 1]]`. It has order 6, 4 and 3 at `μ = 1, 2, 3`,
and infinite order at `μ = 4`, where it is `-1` times a nontrivial unipotent.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

/-- The tick at pull `μ` is `[[1 - μ, -μ], [1, 1]]`. -/
theorem tick_mat (μ : ℤ) : (tick μ : Matrix (Fin 2) (Fin 2) ℤ) = !![1 - μ, -μ; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tick, Step.mat, Matrix.SpecialLinearGroup.coe_mul]
  all_goals ring

/-- A power of a tick is `1` exactly when the power of its matrix is `1`. -/
theorem tick_pow_eq_one_iff (μ : ℤ) (k : ℕ) :
    tick μ ^ k = 1 ↔ (!![1 - μ, -μ; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ k = 1 := by
  rw [← tick_mat, ← Matrix.SpecialLinearGroup.coe_pow]
  constructor
  · intro h
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  · intro h
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [h]; simp

/-- At the pull `μ = 4` the powers of the tick are
`(-1)^k [[1 + 2k, 4k], [-k, 1 - 2k]]`. -/
theorem tick_four_pow (k : ℕ) :
    (!![-3, -4; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ k =
      (-1 : ℤ) ^ k • !![1 + 2 * (k : ℤ), 4 * k; -k, 1 - 2 * k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    all_goals ring

/-- **T13** (the crystallographic pulls). -/
@[ledger "T13"]
theorem stepOrders : Statement.stepOrders := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [tick_pow_eq_one_iff]; decide
  · intro k h0 h6
    rw [Ne, tick_pow_eq_one_iff]
    interval_cases k <;> decide
  · rw [tick_pow_eq_one_iff]; decide
  · intro k h0 h4
    rw [Ne, tick_pow_eq_one_iff]
    interval_cases k <;> decide
  · rw [tick_pow_eq_one_iff]; decide
  · intro k h0 h3
    rw [Ne, tick_pow_eq_one_iff]
    interval_cases k <;> decide
  · intro k hk h
    rw [tick_pow_eq_one_iff] at h
    norm_num at h
    rw [tick_four_pow] at h
    have h10 := congrFun (congrFun h 1) 0
    simp at h10
    omega

/-! ## Non-vacuity

The statement has no hypotheses. Its first clause on the book's tick at the
pull 1, the score `K(1) M(-1)`: -/

/-- The book's tick at pull 1 has order 6. -/
example : realize [Step.kick (1 : ℤ), Step.move (-1)] ^ 6 = 1 := stepOrders.1.1

end Artform.Scores
