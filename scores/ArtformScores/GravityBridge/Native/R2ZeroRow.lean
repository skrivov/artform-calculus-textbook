import ArtformScores.GravityBridge.Native.R2CertificateStatements
import ArtformScores.GravityBridge.Native.R2CertificateData
import ArtformScores.GravityBridge.Native.R2Exceptions

/-! # A kernel-checked certificate for the native R2 zero-row obstruction

The integer identity, every native input equality, the common-factor split
and the positive normal chart are proved in Lean. The discovery tools are
not trusted for these steps.
-/

namespace Artform.Scores.GravityBridge.Native.R2

open Polynomial

lemma cubic_coeff2 (P : Polynomial ℝ) (hP : P.natDegree ≤ 3) :
    P.coeff 2 = (P.eval 1 + P.eval (-1) - 2 * P.eval 0) / 2 := by
  rw [cubic_eval P hP 1, cubic_eval P hP (-1), cubic_eval P hP 0]
  ring

lemma cubic_coeff3 (P : Polynomial ℝ) (hP : P.natDegree ≤ 3) :
    P.coeff 3 = (P.eval 2 - 3 * P.eval 1 - P.eval (-1) + 3 * P.eval 0) / 6 := by
  rw [cubic_eval P hP 2, cubic_eval P hP 1, cubic_eval P hP (-1), cubic_eval P hP 0]
  ring

lemma cubic_coeff1 (P : Polynomial ℝ) (hP : P.natDegree ≤ 3) :
    P.coeff 1 = (P.eval 1 - P.eval (-1)) / 2 - P.coeff 3 := by
  rw [cubic_eval P hP 1, cubic_eval P hP (-1)]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_constant0 (R a G : ℝ) :
    constantQuotient R a G 0 = 1 * Certificate.g0 R a G := by
  dsimp [constantQuotient]
  rw [cubic_coeff2 _ (rowPolys_degree R a G 0),
    cubic_coeff3 _ (rowPolys_degree R a G 0)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g0]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_constant1 (R a G : ℝ) :
    constantQuotient R a G 1 = -1 * Certificate.g1 R a G := by
  dsimp [constantQuotient]
  rw [cubic_coeff2 _ (rowPolys_degree R a G 1),
    cubic_coeff3 _ (rowPolys_degree R a G 1)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g1]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_constant2 (R a G : ℝ) :
    constantQuotient R a G 2 = 1 * Certificate.g2 R a G := by
  dsimp [constantQuotient]
  rw [cubic_coeff2 _ (rowPolys_degree R a G 2),
    cubic_coeff3 _ (rowPolys_degree R a G 2)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g2]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_constant3 (R a G : ℝ) :
    constantQuotient R a G 3 = 1 * Certificate.g3 R a G := by
  dsimp [constantQuotient]
  rw [cubic_coeff2 _ (rowPolys_degree R a G 3),
    cubic_coeff3 _ (rowPolys_degree R a G 3)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g3]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_ell0 (R a G : ℝ) :
    ell a G (rowPolys R a G 0) = -1 * Certificate.g4 R a G := by
  dsimp [ell]
  rw [cubic_coeff1 _ (rowPolys_degree R a G 0),
    cubic_coeff2 _ (rowPolys_degree R a G 0),
    cubic_coeff3 _ (rowPolys_degree R a G 0)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g4]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_ell1 (R a G : ℝ) :
    ell a G (rowPolys R a G 1) = 1 * Certificate.g5 R a G := by
  dsimp [ell]
  rw [cubic_coeff1 _ (rowPolys_degree R a G 1),
    cubic_coeff2 _ (rowPolys_degree R a G 1),
    cubic_coeff3 _ (rowPolys_degree R a G 1)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g5]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_ell2 (R a G : ℝ) :
    ell a G (rowPolys R a G 2) = -1 * Certificate.g6 R a G := by
  dsimp [ell]
  rw [cubic_coeff1 _ (rowPolys_degree R a G 2),
    cubic_coeff2 _ (rowPolys_degree R a G 2),
    cubic_coeff3 _ (rowPolys_degree R a G 2)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g6]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Interpolate the actual cubic; no exported coefficient is assumed as a premise.
lemma certificate_ell3 (R a G : ℝ) :
    ell a G (rowPolys R a G 3) = -1 * Certificate.g7 R a G := by
  dsimp [ell]
  rw [cubic_coeff1 _ (rowPolys_degree R a G 3),
    cubic_coeff2 _ (rowPolys_degree R a G 3),
    cubic_coeff3 _ (rowPolys_degree R a G 3)]
  simp only [rowPolys_eval]
  dsimp [rows, rowExpr, constantSeeds, Certificate.g7]
  ring

namespace Certificate

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- Normalize the full integer certificate rather than trusting the discovery tool.
lemma polynomial_identity (R a G : ℝ) :
    w0 R a G * g0 R a G + w1 R a G * g1 R a G +
    w2 R a G * g2 R a G + w3 R a G * g3 R a G +
    w4 R a G * g4 R a G + w5 R a G * g5 R a G +
    w6 R a G * g6 R a G + w7 R a G * g7 R a G = nonzeroConstant := by
  unfold w0 w1 w2 w3 w4 w5 w6 w7 g0 g1 g2 g3 g4 g5 g6 g7 nonzeroConstant
  ring

end Certificate

lemma zero_row_obstruction (R a G : ℝ) (hb : 2 - 3 * a ≠ 0)
    (he : ∀ i, ell a G (rowPolys R a G i) = 0)
    (hn : ∀ i, remainderConst a G (rowPolys R a G i) = 0) : False := by
  have h0 : Certificate.g0 R a G = 0 := by
    have h := (constant_zero_iff R a G hb 0).mp (hn 0)
    rw [certificate_constant0] at h
    simpa using h
  have h1 : Certificate.g1 R a G = 0 := by
    have h := (constant_zero_iff R a G hb 1).mp (hn 1)
    rw [certificate_constant1] at h
    simpa using h
  have h2 : Certificate.g2 R a G = 0 := by
    have h := (constant_zero_iff R a G hb 2).mp (hn 2)
    rw [certificate_constant2] at h
    simpa using h
  have h3 : Certificate.g3 R a G = 0 := by
    have h := (constant_zero_iff R a G hb 3).mp (hn 3)
    rw [certificate_constant3] at h
    simpa using h
  have h4 : Certificate.g4 R a G = 0 := by
    have h := he 0
    rw [certificate_ell0] at h
    simpa using h
  have h5 : Certificate.g5 R a G = 0 := by
    have h := he 1
    rw [certificate_ell1] at h
    simpa using h
  have h6 : Certificate.g6 R a G = 0 := by
    have h := he 2
    rw [certificate_ell2] at h
    simpa using h
  have h7 : Certificate.g7 R a G = 0 := by
    have h := he 3
    rw [certificate_ell3] at h
    simpa using h
  have hid := Certificate.polynomial_identity R a G
  rw [h0, h1, h2, h3, h4, h5, h6, h7] at hid
  norm_num [Certificate.nonzeroConstant] at hid

/-- **GAC:r2-zero-row-exclusion**
(the all-zero exceptional stratum is absent on the large normal chart). -/
@[ledger "GAC:r2-zero-row-exclusion"]
theorem zeroRowExclusion : Statement.zeroRowExclusion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro R a G hb ⟨he, hn⟩
    exact zero_row_obstruction R a G hb he hn
  · rintro R a G s hN hG hs ⟨he, hn⟩
    exact zero_row_obstruction R a G (nonzero_b_on_large_normal a G s hN hG hs) he hn
  · intro q R a G gamma s hq hg hN hq0 hg0 hG hs hp hm
    by_contra hx
    push Not at hx
    have hr := (signed_trace_iff q R a G gamma s hq hg hN hq0 hg0).mp ⟨hp, hm⟩
    have hn : ∀ i, remainderConst a G (rowPolys R a G i) = 0 := by
      intro i
      have h := (row_remainder_iff R a G s hN i).mp (hr i)
      simpa [hx i] using h
    exact zero_row_obstruction R a G (nonzero_b_on_large_normal a G s hN hG hs) hx hn

/-! ## Non-vacuity

The large normal chart is inhabited independently of the excluded coefficient
zeros. The small-latitude b=0 chart is deliberately outside this corollary.
-/

example : normal (1 : ℝ) (1 / 36) (3 / 2) = 0 ∧
    (0 : ℝ) ≤ 1 / 36 ∧ (1 / 3 : ℝ) < 3 / 2 ∧
    ¬ ((∀ i, ell 1 (1 / 36) (rowPolys 1 1 (1 / 36) i) = 0) ∧
       (∀ i, remainderConst 1 (1 / 36) (rowPolys 1 1 (1 / 36) i) = 0)) := by
  refine ⟨by norm_num [normal], by norm_num, by norm_num, ?_⟩
  exact zeroRowExclusion.2.1 1 1 (1 / 36) (3 / 2) (by norm_num [normal])
    (by norm_num) (by norm_num)

example : normal (2 / 3 : ℝ) (1 / 36) (1 / 6) = 0 ∧
    ¬ (1 / 3 : ℝ) < 1 / 6 := by norm_num [normal]

end Artform.Scores.GravityBridge.Native.R2
