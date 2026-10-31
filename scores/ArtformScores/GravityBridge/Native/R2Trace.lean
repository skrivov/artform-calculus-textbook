import ArtformScores.GravityBridge.Native.R2Statements
import Mathlib.Tactic.ComputeDegree

/-! # Proofs of the original trace splitting and division-free monic reduction -/

namespace Artform.Scores.GravityBridge.Native.R2

open Polynomial Complex

set_option maxRecDepth 8192

lemma originalW_eq (a gamma s : ℝ) (hN : normal a (gamma ^ 2) s = 0) :
    originalW a gamma s = (s : ℂ) *
      ((3 / 2 + a - 3 * a ^ 2 + s * (a - 1 / 2 - gamma ^ 2) : ℝ) +
        I * ((1 + s) * gamma : ℝ)) := by
  apply Complex.ext
  · simp [originalW, zeta, pow_two, Complex.mul_re, Complex.mul_im]
    dsimp [normal] at hN
    linear_combination hN / 2
  · simp [originalW, zeta, pow_two, Complex.mul_re, Complex.mul_im]
    ring

set_option maxHeartbeats 0 in
-- The kernel normalizes the literal native products in both complex components.
lemma originalJ_rows (q R a G gamma s : ℝ) (hq : q ^ 2 = 103 / 2)
    (hg : gamma ^ 2 = G) (hN : normal a G s = 0) :
    originalJ q R a gamma s =
      (rows R a G s 0 : ℂ) + I * q * rows R a G s 1 +
        gamma * (q * rows R a G s 2 + I * rows R a G s 3) := by
  have hW := originalW_eq a gamma s (by simpa [hg] using hN)
  unfold originalJ
  rw [hW]
  unfold rows
  rw [← hq, ← hg]
  apply Complex.ext <;>
    simp [rowExpr, originalBhat, zeta, phaseL, phaseT, phaseDelta, pow_two,
      Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring

lemma rowPolys_eval (R a G s : ℝ) (i : Fin 4) :
    (rowPolys R a G i).eval s = rows R a G s i := by
  fin_cases i <;> simp [rowPolys, rows, rowExpr]

set_option maxHeartbeats 0 in
-- The expression has many constant leaves, but only three latitude factors.
lemma rowPolys_degree (R a G : ℝ) (i : Fin 4) :
    (rowPolys R a G i).natDegree ≤ 3 := by
  fin_cases i <;> dsimp [rowPolys, rowExpr] <;> compute_degree

lemma cubic_eval (P : Polynomial ℝ) (hP : P.natDegree ≤ 3) (s : ℝ) :
    P.eval s = P.coeff 3 * s ^ 3 + P.coeff 2 * s ^ 2 + P.coeff 1 * s + P.coeff 0 := by
  have hp := P.as_sum_range_C_mul_X_pow' (n := 4) (by omega)
  conv_lhs => rw [hp]
  simp [Finset.sum_range_succ]
  ring

lemma traceResidual_clear (q R a gamma s : ℝ) (hs : s ≠ 0) (hD : 3 - s ≠ 0)
    (hE : 1 - zeta a gamma ≠ 0) (hd : phaseDelta q R a gamma ≠ 0) :
    traceResidual q R a gamma s = 0 ↔ originalJ q R a gamma s = 0 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hDC : ((3 - s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  have hdC : ((phaseDelta q R a gamma : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hfactor : (s : ℂ) * (3 - s : ℝ) * (1 - zeta a gamma) *
      phaseDelta q R a gamma ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hsC hDC) hE) hdC
  have hid : (s : ℂ) * (3 - s : ℝ) * (1 - zeta a gamma) *
      phaseDelta q R a gamma * traceResidual q R a gamma s = originalJ q R a gamma s := by
    dsimp [traceResidual, originalJ]
    push_cast
    push_cast at hDC
    field_simp [hsC, hDC, hE, hdC]
    ring
  rw [← hid, mul_eq_zero, or_iff_right hfactor]

lemma signed_components (q gamma pe qe po qo : ℝ) (hq : q ≠ 0) (hg : gamma ≠ 0) :
    ((pe : ℂ) + I * q * qe + gamma * (q * po + I * qo) = 0 ∧
      (pe : ℂ) + I * q * qe - gamma * (q * po + I * qo) = 0) ↔
    pe = 0 ∧ qe = 0 ∧ po = 0 ∧ qo = 0 := by
  constructor
  · rintro ⟨hp, hm⟩
    have he : (pe : ℂ) + I * q * qe = 0 := by linear_combination (hp + hm) / 2
    have ho : (gamma : ℂ) * (q * po + I * qo) = 0 := by
      linear_combination (hp - hm) / 2
    have hgC : (gamma : ℂ) ≠ 0 := by exact_mod_cast hg
    have ho' := (mul_eq_zero.mp ho).resolve_left hgC
    have hpe := congrArg Complex.re he
    have hqe := congrArg Complex.im he
    have hpo := congrArg Complex.re ho'
    have hqo := congrArg Complex.im ho'
    simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero, one_mul, sub_zero,
      Complex.zero_re, Complex.zero_im] at hpe hqe hpo hqo
    exact ⟨hpe, (mul_eq_zero.mp hqe).resolve_left hq,
      (mul_eq_zero.mp hpo).resolve_left hq, hqo⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

lemma signed_trace_iff (q R a G gamma s : ℝ) (hq : q ^ 2 = 103 / 2)
    (hg : gamma ^ 2 = G) (hN : normal a G s = 0) (hq0 : q ≠ 0) (hg0 : gamma ≠ 0) :
    (originalJ q R a gamma s = 0 ∧ originalJ q R a (-gamma) s = 0) ↔
      ∀ i, rows R a G s i = 0 := by
  rw [originalJ_rows q R a G gamma s hq hg hN,
    originalJ_rows q R a G (-gamma) s hq (by simpa using hg) hN]
  simp only [Complex.ofReal_neg, neg_mul]
  rw [← sub_eq_add_neg]
  rw [signed_components q gamma _ _ _ _ hq0 hg0]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

lemma monic_remainder (P : Polynomial ℝ) (hP : P.natDegree ≤ 3) (a G s : ℝ) :
    P.eval s - (ell a G P * s + remainderConst a G P) =
      normal a G s * (P.coeff 3 * s + P.coeff 2 -
        (5 - 8 * a + 6 * G) * P.coeff 3) := by
  rw [cubic_eval P hP]
  dsimp [ell, remainderConst, normal]
  ring

lemma row_remainder_iff (R a G s : ℝ) (hN : normal a G s = 0) (i : Fin 4) :
    rows R a G s i = 0 ↔
      ell a G (rowPolys R a G i) * s + remainderConst a G (rowPolys R a G i) = 0 := by
  have h := monic_remainder (rowPolys R a G i) (rowPolys_degree R a G i) a G s
  rw [hN, zero_mul, rowPolys_eval, sub_eq_zero] at h
  rw [h]

/-- **GAC:r2-trace-reduction** (exact original trace and monic-normal arithmetic). -/
@[ledger "GAC:r2-trace-reduction"]
theorem traceReduction : Statement.traceReduction := by
  refine ⟨originalJ_rows, rowPolys_degree, monic_remainder, ?_, traceResidual_clear⟩
  intro q R a G gamma s hq hg hN hq0 hg0
  rw [signed_trace_iff q R a G gamma s hq hg hN hq0 hg0]
  exact forall_congr' (row_remainder_iff R a G s hN)

/-! ## Non-vacuity

This is a point on the original real normal chart with both phase determinants
nonzero. It witnesses the reduction hypotheses, not full-force feasibility.
-/

example : ∃ q : ℝ, 0 < q ∧ q ^ 2 = 103 / 2 ∧
    normal (1 : ℝ) (1 / 36) (3 / 2) = 0 ∧
    (1 / 6 : ℝ) ^ 2 = 1 / 36 ∧
    phaseDelta q 1 1 (1 / 6) ≠ 0 ∧ phaseDelta q 1 1 (-1 / 6) ≠ 0 ∧
    1 - zeta 1 (1 / 6) ≠ 0 ∧ 1 - zeta 1 (-1 / 6) ≠ 0 := by
  let q : ℝ := Real.sqrt (103 / 2)
  have hq : q ^ 2 = 103 / 2 := Real.sq_sqrt (by norm_num)
  have hqpos : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hqlt : q < 8 := by nlinarith [sq_nonneg (q - 8)]
  refine ⟨q, hqpos, hq, by norm_num [normal], by norm_num, ?_, ?_, ?_, ?_⟩
  · dsimp [phaseDelta]
    rw [hq]
    norm_num
    linarith
  · dsimp [phaseDelta]
    rw [hq]
    norm_num
    linarith
  · intro he
    have hi := congrArg Complex.im he
    norm_num [zeta] at hi
  · intro he
    have hi := congrArg Complex.im he
    norm_num [zeta] at hi

end Artform.Scores.GravityBridge.Native.R2
