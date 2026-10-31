import ArtformScores.GravityBridge.Native.MetricCut.LeadingStatements
/-! # The original leading normal range and visible source return -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
variable {K : Type*} [Field K] [CharZero K]
open Matrix
lemma normal_leading_longitudinal (k : SVec K) (x : K × SVec K) :
    dot3 k (normalLeading k x).2 = 0 := by
  simp only [normalLeading, dot3_smul, dot3_add, dot3_self]
  ring
lemma normal_lift_return (k : SVec K) (rhs : K × SVec K) (a : K)
    (hR : rho2 k ≠ 0) (hr : dot3 k rhs.2 = 0) :
    normalLeading k (normalLift k rhs a) = rhs := by
  apply Prod.ext
  · dsimp [normalLeading, normalLift]
    field_simp
  · simp only [normalLeading, normalLift, dot3_add, dot3_smul, dot3_self, hr]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    field_simp
    ring
lemma normal_leading_range (k : SVec K) (rhs : K × SVec K) (hR : rho2 k ≠ 0) :
    (∃ x, normalLeading k x = rhs) ↔ dot3 k rhs.2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact normal_leading_longitudinal k x
  · intro hr
    exact ⟨normalLift k rhs 0, normal_lift_return k rhs 0 hR hr⟩
lemma normal_leading_kernel (k : SVec K) (x : K × SVec K) (hR : rho2 k ≠ 0) :
    normalLeading k x = 0 ↔ x.1 = 0 ∧ ∃ a : K, x.2 = a • k := by
  constructor
  · intro hx
    have ht := congrArg Prod.fst hx
    have hv := congrArg Prod.snd hx
    change (-101 / 20600 : K) * rho2 k * x.1 = 0 at ht
    have hc : (-101 / 20600 : K) * rho2 k ≠ 0 := mul_ne_zero (by norm_num) hR
    refine ⟨(mul_eq_zero.mp ht).resolve_left hc, dot3 k x.2 / rho2 k, ?_⟩
    ext i
    have hi := congrFun hv i
    change (-2422 / 29973 : K) * (-(rho2 k) * x.2 i + dot3 k x.2 * k i) = 0 at hi
    have hb : (-2422 / 29973 : K) ≠ 0 := by norm_num
    have hi' := (mul_eq_zero.mp hi).resolve_left hb
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -hi'
  · rintro ⟨h0, a, ha⟩
    rw [normalLeading, h0, ha]
    apply Prod.ext
    · simp
    · ext i
      change ((-2422 / 29973 : K) •
        (-rho2 k • (a • k) + dot3 k (a • k) • k)) i = 0
      simp only [dot3_smul, dot3_self, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring
-- With the literal leading visible blocks h²Y, h²X, their product is h⁴.
omit [CharZero K] in
lemma visible_return_factor {v n : Type*} [Fintype v]
    (h : K) (Y : Matrix n v K) (E : Matrix v v K) (X : Matrix v n K) :
    ((h ^ 2) • Y) * E * ((h ^ 2) • X) = h ^ 4 • (Y * E * X) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  ring
-- Exact source subtraction keeps the visible target and is not just a determinant.
omit [CharZero K] in
lemma visible_source_return {v n : Type*} [Fintype v] [Fintype n] [DecidableEq v]
    (C : Matrix n v K) (E : Matrix v v K) (X : Matrix v n K)
    (V : Matrix v v K) (s target : v → K) (c : n → K)
    (hE : E * V = 1) (hs : V *ᵥ s + X *ᵥ c = target) :
    C *ᵥ s = C *ᵥ (E *ᵥ target) - (C * E * X) *ᵥ c := by
  have he := congrArg (fun z => E *ᵥ z) hs
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec,
    Matrix.mulVec_mulVec] at he
  have he' : s = E *ᵥ target - (E * X) *ᵥ c := by rw [← he]; abel
  rw [he', Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
/-- **GAC2:metric-leading-range-return**
(the original leading normal range and visible source return). -/
@[ledger "GAC2:metric-leading-range-return"]
theorem leadingLaw : Statement.leadingLaw := by
  intro K _ _
  exact ⟨normal_leading_longitudinal,
    normal_lift_return,
    normal_leading_range,
    normal_leading_kernel,
    visible_return_factor,
    visible_source_return⟩
/-! ## Non-vacuity -/
example : normalLeading (![1, 2, 3] : SVec ℚ) (0, ![1, 2, 3]) = 0 ∧
    ¬ ∃ x, normalLeading (![1, 2, 3] : SVec ℚ) x = (0, ![1, 2, 3]) := by
  constructor
  · apply (normal_leading_kernel _ _ (by norm_num [rho2, dot3, Fin.sum_univ_succ])).2
    exact ⟨rfl, 1, by simp⟩
  · intro hx
    have hc := (normal_leading_range _ _
      (by norm_num [rho2, dot3, Fin.sum_univ_succ])).1 hx
    norm_num [dot3, Fin.sum_univ_succ] at hc
end Artform.Scores.GravityBridge.Native.MetricCut
