import ArtformScores.GravityBridge.Native.R2PhaseStatements
import ArtformScores.GravityBridge.Native.R2Trace

/-! # Original real-linear phase inverse, norm and guarded trace equivalence -/

namespace Artform.Scores.GravityBridge.Native.R2

open Complex

lemma original_phase_determinant (q R a gamma : ℝ) :
    Complex.normSq (phaseP q R a gamma) - Complex.normSq (phaseQ q a gamma) =
      phaseDelta q R a gamma := by
  simp [phaseP, phaseQ, zeta, phaseDelta, Complex.normSq_apply, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

lemma original_phase_numerator (q R a gamma : ℝ) :
    star (phaseP q R a gamma) * phaseL q R -
      phaseQ q a gamma * star (phaseL q R) = phaseT q R a gamma := by
  apply Complex.ext <;>
    simp [phaseP, phaseQ, phaseL, phaseT, zeta, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

lemma real_linear_phase_inverse (P Q V C : ℂ)
    (hd : Complex.normSq P - Complex.normSq Q ≠ 0) :
    (P * V + Q * star V = C) ↔
      V = (star P * C - Q * star C) / ((Complex.normSq P - Complex.normSq Q : ℝ) : ℂ) := by
  have hdc : (((Complex.normSq P - Complex.normSq Q : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hd
  rw [eq_div_iff hdc]
  have he : ((Complex.normSq P - Complex.normSq Q : ℝ) : ℂ) =
      P * star P - Q * star Q := by
    apply Complex.ext <;> simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  constructor
  · intro h
    have hc := congrArg star h
    simp only [star_add, star_mul, star_star] at hc
    rw [he]
    linear_combination star P * h - Q * hc
  · intro h
    rw [he] at h
    have hc := congrArg star h
    simp only [star_mul, star_sub, star_star] at hc
    have hi : ((Complex.normSq P - Complex.normSq Q : ℝ) : ℂ) *
        (P * V + Q * star V - C) = 0 := by
      rw [he]
      linear_combination P * h + Q * hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hdc)

lemma original_phase_iff (q R a gamma H : ℝ) (V : ℂ)
    (hd : phaseDelta q R a gamma ≠ 0) :
    (phaseP q R a gamma * V + phaseQ q a gamma * star V =
      (-2 * H : ℝ) * phaseL q R) ↔ V = regularV q R a gamma H := by
  rw [real_linear_phase_inverse _ _ _ _ (by rw [original_phase_determinant]; exact hd)]
  rw [original_phase_determinant]
  have hh : star ((-2 * H : ℝ) : ℂ) = ((-2 * H : ℝ) : ℂ) := by
    simp
  have he : star (phaseP q R a gamma) * ((-2 * H : ℝ) * phaseL q R) -
      phaseQ q a gamma * star ((-2 * H : ℝ) * phaseL q R) =
      (-2 * H : ℝ) * phaseT q R a gamma := by
    rw [star_mul, hh, ← original_phase_numerator]
    ring
  rw [he]
  rfl

lemma regularV_norm (q R a gamma H : ℝ) :
    Complex.normSq (regularV q R a gamma H) =
      4 * H ^ 2 * Complex.normSq (phaseT q R a gamma) / (phaseDelta q R a gamma) ^ 2 := by
  simp only [regularV, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma original_norm_iff (q R a gamma K H s : ℝ)
    (hK : K ^ 2 = s) (hH : K * H = a * s + (2 - 3 * a)) (hK0 : K ≠ 0)
    (hd : phaseDelta q R a gamma ≠ 0) :
    Complex.normSq (regularV q R a gamma H) = R * (3 - s) ↔
      phaseNorm q R a gamma s = 0 := by
  have hs : s ≠ 0 := by rw [← hK]; exact pow_ne_zero _ hK0
  have hh : (a * s + (2 - 3 * a)) ^ 2 = s * H ^ 2 := by rw [← hH, mul_pow, hK]
  rw [regularV_norm, div_eq_iff (pow_ne_zero 2 hd)]
  dsimp [phaseNorm]
  rw [hh]
  constructor
  · intro h
    linear_combination s * h
  · intro h
    have he : s * (4 * H ^ 2 * Complex.normSq (phaseT q R a gamma) -
        R * (3 - s) * phaseDelta q R a gamma ^ 2) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)

lemma original_regular_system_iff (q R a gamma K H s : ℝ) (V : ℂ)
    (hK : K ^ 2 = s) (hH : K * H = a * s + (2 - 3 * a)) (hK0 : K ≠ 0)
    (hs : s ≠ 0) (hD : 3 - s ≠ 0) (hE : 1 - zeta a gamma ≠ 0)
    (hd : phaseDelta q R a gamma ≠ 0) :
    ((phaseP q R a gamma * V + phaseQ q a gamma * star V =
        (-2 * H : ℝ) * phaseL q R) ∧
      Complex.normSq V = R * (3 - s) ∧ traceResidual q R a gamma s = 0) ↔
    (V = regularV q R a gamma H ∧ phaseNorm q R a gamma s = 0 ∧
      originalJ q R a gamma s = 0) := by
  constructor
  · rintro ⟨hv, hn, ht⟩
    have he := (original_phase_iff q R a gamma H V hd).mp hv
    subst V
    exact ⟨rfl, (original_norm_iff q R a gamma K H s hK hH hK0 hd).mp hn,
      (traceResidual_clear q R a gamma s hs hD hE hd).mp ht⟩
  · rintro ⟨rfl, hn, ht⟩
    exact ⟨(original_phase_iff q R a gamma H _ hd).mpr rfl,
      (original_norm_iff q R a gamma K H s hK hH hK0 hd).mpr hn,
      (traceResidual_clear q R a gamma s hs hD hE hd).mpr ht⟩

/-- **GAC:r2-phase-transfer** (original phase and norm, with the actual clearing guards). -/
@[ledger "GAC:r2-phase-transfer"]
theorem phaseTransfer : Statement.phaseTransfer :=
  ⟨original_phase_determinant, original_phase_numerator, original_phase_iff,
    original_norm_iff, original_regular_system_iff⟩

/-! ## Non-vacuity -/

example : (1 : ℂ) * 2 + 0 * star (2 : ℂ) = 2 ∧
    Complex.normSq (1 : ℂ) - Complex.normSq (0 : ℂ) ≠ 0 := by norm_num

-- An actual positive original normal chart with all phase/trace clearing guards.
example : ∃ q K H : ℝ, 0 < q ∧ q ^ 2 = 103 / 2 ∧ K ^ 2 = 3 / 2 ∧
    K * H = (1 : ℝ) * (3 / 2) + (2 - 3 * 1) ∧ K ≠ 0 ∧
    normal (1 : ℝ) (1 / 36) (3 / 2) = 0 ∧ phaseDelta q 1 1 (1 / 6) ≠ 0 ∧
    1 - zeta 1 (1 / 6) ≠ 0 ∧
    phaseP q 1 1 (1 / 6) * regularV q 1 1 (1 / 6) H +
      phaseQ q 1 (1 / 6) * star (regularV q 1 1 (1 / 6) H) =
        (-2 * H : ℝ) * phaseL q 1 := by
  let q : ℝ := Real.sqrt (103 / 2)
  let K : ℝ := Real.sqrt (3 / 2)
  let H : ℝ := (1 / 2) / K
  have hq : q ^ 2 = 103 / 2 := Real.sq_sqrt (by norm_num)
  have hqp : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hKp : 0 < K := Real.sqrt_pos.2 (by norm_num)
  have hK : K ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hd : phaseDelta q 1 1 (1 / 6) ≠ 0 := by
    dsimp [phaseDelta]
    rw [hq]
    norm_num
    linarith
  have hE : 1 - zeta 1 (1 / 6) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    norm_num [zeta] at hi
  refine ⟨q, K, H, hqp, hq, hK, ?_, ne_of_gt hKp, by norm_num [normal], hd, hE, ?_⟩
  · dsimp [H]
    field_simp
    ring
  · exact (original_phase_iff q 1 1 (1 / 6) H _ hd).mpr rfl

end Artform.Scores.GravityBridge.Native.R2
