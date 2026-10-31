import ArtformScores.GravityBridge.Native.R2PhaseStatements
import ArtformScores.GravityBridge.Native.R2ZeroRow

/-! # Excluding the shared factor directly from the necessary original norm constraint -/

namespace Artform.Scores.GravityBridge.Native.R2

open Complex Polynomial

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Normalize the full original complex phase products in the kernel.
lemma phaseNorm_difference (q R a gamma s : ℝ) :
    phaseNorm q R a gamma s - phaseNorm q R a (-gamma) s =
      16 * q * R * gamma *
        (2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2 -
          s * (3 - s) * evenDelta q R a (gamma ^ 2)) := by
  simp [phaseNorm, evenDelta, phaseT, phaseDelta, Complex.normSq_apply, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

lemma norm_odd_constraint (q R a gamma s : ℝ)
    (hq : q ≠ 0) (hR : R ≠ 0) (hg : gamma ≠ 0)
    (hp : phaseNorm q R a gamma s = 0) (hm : phaseNorm q R a (-gamma) s = 0) :
    s * (3 - s) * evenDelta q R a (gamma ^ 2) =
      2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2 := by
  have h := phaseNorm_difference q R a gamma s
  rw [hp, hm] at h
  have hn : 16 * q * R * gamma ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq) hR) hg
  have he := (mul_eq_zero.mp (show 16 * q * R * gamma *
      (2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2 -
        s * (3 - s) * evenDelta q R a (gamma ^ 2)) = 0 from by simpa using h.symm)).resolve_left hn
  linarith

lemma nonzero_b_from_norm_odd (q R a G s : ℝ)
    (hq : q ^ 2 = 103 / 2) (hR : 0 < R) (hG : 0 ≤ G) (hs : 0 < s)
    (hN : normal a G s = 0)
    (hf : s * (3 - s) * evenDelta q R a G =
      2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2) : 2 - 3 * a ≠ 0 := by
  intro hb
  have ha : a = 2 / 3 := by linarith
  subst a
  have hn : s = 1 / 3 - 6 * G := by
    dsimp [normal] at hN
    have he : s * (s - 1 / 3 + 6 * G) = 0 := by nlinarith [hN]
    have := (mul_eq_zero.mp he).resolve_left (ne_of_gt hs)
    linarith
  have hsbound : s ≤ 1 / 3 := by linarith
  have hd0 : evenDelta q 0 (2 / 3) G = (97 + 307 * s) / 12 := by
    dsimp [evenDelta]
    rw [hq]
    nlinarith [hn]
  have hdd : evenDelta q R (2 / 3) G - evenDelta q 0 (2 / 3) G =
      (1 + q ^ 2) * (4 / 9 + G) * R * (R + 2) := by
    dsimp [evenDelta]
    ring
  have hpos : 0 < (1 + q ^ 2) * (4 / 9 + G) * R * (R + 2) := by positivity
  have hd : 8 < evenDelta q R (2 / 3) G := by linarith
  have he : (3 - s) * evenDelta q R (2 / 3) G = (412 / 9) * s := by
    rw [hq] at hf
    have hx : s * ((3 - s) * evenDelta q R (2 / 3) G - (412 / 9) * s) = 0 := by
      nlinarith [hf]
    have := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hs)
    linarith
  have hl : (64 / 3 : ℝ) < (3 - s) * evenDelta q R (2 / 3) G := by
    nlinarith
  nlinarith

lemma no_zero_rows_from_odd (q R a G s : ℝ)
    (hq : q ^ 2 = 103 / 2) (hR : 0 < R) (hG : 0 ≤ G) (hs : 0 < s)
    (hN : normal a G s = 0)
    (hf : s * (3 - s) * evenDelta q R a G =
      2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2) :
    ¬ ((∀ i, ell a G (rowPolys R a G i) = 0) ∧
      (∀ i, remainderConst a G (rowPolys R a G i) = 0)) := by
  rintro ⟨he, hn⟩
  exact zero_row_obstruction R a G
    (nonzero_b_from_norm_odd q R a G s hq hR hG hs hN hf) he hn

lemma rows_root_unique (R a G s u : ℝ) (hb : 2 - 3 * a ≠ 0)
    (hs : normal a G s = 0) (hu : normal a G u = 0)
    (hps : ∀ i, rows R a G s i = 0) (hpu : ∀ i, rows R a G u i = 0) : s = u := by
  by_contra hsu
  have he : ∀ i, ell a G (rowPolys R a G i) = 0 := by
    intro i
    have h1 := (row_remainder_iff R a G s hs i).mp (hps i)
    have h2 := (row_remainder_iff R a G u hu i).mp (hpu i)
    have hz : ell a G (rowPolys R a G i) * (s - u) = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hsu)
  have hn : ∀ i, remainderConst a G (rowPolys R a G i) = 0 := by
    intro i
    have h := (row_remainder_iff R a G s hs i).mp (hps i)
    simpa [he i] using h
  exact zero_row_obstruction R a G hb he hn

lemma nonzero_pivot_from_norms (q R a gamma s : ℝ)
    (hq : q ^ 2 = 103 / 2) (hR : 0 < R) (hs : 0 < s) (hg : gamma ≠ 0)
    (hN : normal a (gamma ^ 2) s = 0)
    (hp : phaseNorm q R a gamma s = 0) (hm : phaseNorm q R a (-gamma) s = 0)
    (hjp : originalJ q R a gamma s = 0) (hjm : originalJ q R a (-gamma) s = 0) :
    ∃ i, ell a (gamma ^ 2) (rowPolys R a (gamma ^ 2) i) ≠ 0 := by
  have hq0 : q ≠ 0 := by intro he; rw [he] at hq; norm_num at hq
  have hf := norm_odd_constraint q R a gamma s hq0 (ne_of_gt hR) hg hp hm
  have hb := nonzero_b_from_norm_odd q R a (gamma ^ 2) s hq hR (sq_nonneg gamma) hs hN hf
  by_contra hx
  push Not at hx
  have hr := (signed_trace_iff q R a (gamma ^ 2) gamma s hq rfl hN hq0 hg).mp ⟨hjp, hjm⟩
  have hn : ∀ i, remainderConst a (gamma ^ 2) (rowPolys R a (gamma ^ 2) i) = 0 := by
    intro i
    have h := (row_remainder_iff R a (gamma ^ 2) s hN i).mp (hr i)
    simpa [hx i] using h
  exact zero_row_obstruction R a (gamma ^ 2) hb hx hn

/-- **GAC:r2-norm-chart** (extend the exclusion using the original odd norm equation). -/
@[ledger "GAC:r2-norm-chart"]
theorem normChart : Statement.normChart := by
  refine ⟨phaseNorm_difference, ?_, nonzero_pivot_from_norms, rows_root_unique⟩
  intro q R a G s hq hR hG hs hN hf
  exact ⟨nonzero_b_from_norm_odd q R a G s hq hR hG hs hN hf,
    no_zero_rows_from_odd q R a G s hq hR hG hs hN hf⟩

/-! ## Non-vacuity

The necessary odd norm/normal chart is inhabited at positive radius. It is not
asserted that this point satisfies either full phase norm or the original trace.
-/

example : ∃ q R : ℝ, q ^ 2 = 103 / 2 ∧ 0 < R ∧
    normal (1 : ℝ) (1 / 36) (3 / 2) = 0 ∧
    (3 / 2 : ℝ) * (3 - 3 / 2) * evenDelta q R 1 (1 / 36) =
      2 * q ^ 2 * (1 * (3 / 2) + (2 - 3 * 1)) ^ 2 := by
  let q : ℝ := Real.sqrt (103 / 2)
  let R : ℝ := Real.sqrt (1672 / 1295) - 1
  have hq : q ^ 2 = 103 / 2 := Real.sq_sqrt (by norm_num)
  have hr : (Real.sqrt (1672 / 1295 : ℝ)) ^ 2 = 1672 / 1295 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg (1672 / 1295 : ℝ)
  have hR : 0 < R := by dsimp [R]; nlinarith
  refine ⟨q, R, hq, hR, by norm_num [normal], ?_⟩
  dsimp [evenDelta, R]
  rw [hq]
  nlinarith

end Artform.Scores.GravityBridge.Native.R2
