import ArtformScores.GravityBridge.Native.CoordinateSymbol.BandStatements

/-! # Compact reflected native band and both light-cone inverse guards -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



lemma fixed_band_reflected (k : Fin 3 → ℝ) : fixedBand (-k) ↔ fixedBand k := by
  simp [fixedBand, radiusSquared]

lemma original_two_directions_in_band : fixedBand ![1, 2, 3] ∧ fixedBand ![1, 2, 4] := by
  constructor <;> refine ⟨by norm_num [radiusSquared], by norm_num [radiusSquared], ?_⟩
  all_goals intro i;fin_cases i <;> norm_num [radiusSquared]

lemma full_angular_guard (k : Fin 3 → ℝ) (hk : fixedBand k) :
    3 ≤ Real.sqrt (radiusSquared k) ∧ Real.sqrt (radiusSquared k) ≤ 5 ∧
      ∀ i, |k i| ≤ (9 / 10 : ℝ) * Real.sqrt (radiusSquared k) := by
  have hR : 0 ≤ radiusSquared k := by unfold radiusSquared;positivity
  have hs := Real.sq_sqrt hR
  have hn := Real.sqrt_nonneg (radiusSquared k)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hk.1]
  · nlinarith [hk.2.1]
  · intro i
    have hi := hk.2.2 i
    have ha := abs_nonneg (k i)
    have he := sq_abs (k i)
    nlinarith

lemma fixed_band_compact : IsCompact {k : Fin 3 → ℝ | fixedBand k} := by
  have hcR : Continuous radiusSquared := by unfold radiusSquared;fun_prop
  have hc : IsClosed {k : Fin 3 → ℝ | fixedBand k} := by
    have h1 : IsClosed {k : Fin 3 → ℝ | 9 ≤ radiusSquared k} :=
      isClosed_le continuous_const hcR
    have h2 : IsClosed {k : Fin 3 → ℝ | radiusSquared k ≤ 25} :=
      isClosed_le hcR continuous_const
    have h3 : ∀ i : Fin 3, IsClosed {k : Fin 3 → ℝ | (k i) ^ 2 ≤ (81 / 100 : ℝ) * radiusSquared
      k} :=
      fun i => isClosed_le ((continuous_apply i).pow 2) (continuous_const.mul hcR)
    simpa only [fixedBand, Set.ofPred_and, Set.ofPred_forall] using h1.inter (h2.inter
      (isClosed_iInter h3))
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 3 => (-5 : ℝ)) (fun _ => (5 :
    ℝ)))).of_isClosed_subset hc
  intro k hk
  have habs : ∀ i, |k i| ≤ 5 := by
    intro i
    have h := (full_angular_guard k hk).2.2 i
    have hr := (full_angular_guard k hk).2.1
    linarith
  exact ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩

lemma absolute_cube_bound (x b : ℝ) (hx : |x| ≤ b) : |x ^ 3| ≤ b * x ^ 2 := by
  calc
    _ = |x| * x ^ 2 := by rw [abs_pow, pow_succ, sq_abs];ring
    _ ≤ b * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)

lemma native_cubic_moment_bound (k : Fin 3 → ℝ) (ρ ε : ℝ)
    (hR : ρ ^ 2 = radiusSquared k) (hk : ∀ i, |k i| ≤ (1 - ε) * ρ) :
    |cubicMoment k| ≤ (1 - ε) * ρ ^ 3 := by
  have h0 := absolute_cube_bound (k 0) ((1 - ε) * ρ) (hk 0)
  have h1 := absolute_cube_bound (k 1) ((1 - ε) * ρ) (hk 1)
  have h2 := absolute_cube_bound (k 2) ((1 - ε) * ρ) (hk 2)
  calc
    _ ≤ |k 0 ^ 3 + k 1 ^ 3| + |k 2 ^ 3| := abs_add_le _ _
    _ ≤ |k 0 ^ 3| + |k 1 ^ 3| + |k 2 ^ 3| := by linarith [abs_add_le (k 0 ^ 3) (k 1 ^ 3)]
    _ ≤ ((1 - ε) * ρ) * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2) := by nlinarith
    _ = (1 - ε) * ρ ^ 3 := by
      change ((1 - ε) * ρ) * radiusSquared k = (1 - ε) * ρ ^ 3
      rw [← hR]
      ring

lemma both_light_cones_separated (k : Fin 3 → ℝ) (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hbound : |cubicMoment k| ≤ (1 - ε) * ρ ^ 3) :
    lightConeDiscriminant 1 ρ k ≤ -ε ^ 2 * ρ ^ 6 / 4 ∧
    lightConeDiscriminant (-1) ρ k ≤ -ε ^ 2 * ρ ^ 6 / 4 := by
  have hupper := (abs_le.mp hbound).2
  have hlower := (abs_le.mp hbound).1
  have hp : 0 < ε * ρ ^ 3 := by positivity
  have hplus : ε * ρ ^ 3 ≤ |cubicMoment k - ρ ^ 3| := by
    have hh := neg_le_abs (cubicMoment k - ρ ^ 3)
    nlinarith
  have hminus : ε * ρ ^ 3 ≤ |cubicMoment k + ρ ^ 3| := by
    have hh := le_abs_self (cubicMoment k + ρ ^ 3)
    nlinarith
  have hsplus := mul_self_le_mul_self (by positivity : 0 ≤ ε * ρ ^ 3) hplus
  have hsminus := mul_self_le_mul_self (by positivity : 0 ≤ ε * ρ ^ 3) hminus
  simp only [← sq, sq_abs] at hsplus hsminus
  constructor <;> unfold lightConeDiscriminant <;> nlinarith

lemma fixed_band_discriminant_budget (k : Fin 3 → ℝ) (hk : fixedBand k) :
    lightConeDiscriminant 1 (Real.sqrt (radiusSquared k)) k ≤ -729 / 400 ∧
    lightConeDiscriminant (-1) (Real.sqrt (radiusSquared k)) k ≤ -729 / 400 := by
  have ha := full_angular_guard k hk
  have hR : 0 ≤ radiusSquared k := by unfold radiusSquared;positivity
  have hb := native_cubic_moment_bound k (Real.sqrt (radiusSquared k)) (1 / 10)
    (Real.sq_sqrt hR) (by norm_num at * ;exact ha.2.2)
  have hd := both_light_cones_separated k (Real.sqrt (radiusSquared k)) (1 / 10)
    (by linarith [ha.1]) (by norm_num) hb
  have hp : (3 : ℝ) ^ 6 ≤ (Real.sqrt (radiusSquared k)) ^ 6 := by gcongr;exact ha.1
  constructor <;> nlinarith [hd.1, hd.2]

/-! ## Band witnesses -/

example : lightConeDiscriminant 1 (Real.sqrt (radiusSquared ![1, 2, 3])) ![1, 2, 3] ≠ 0 := by
  have hd := (fixed_band_discriminant_budget ![1, 2, 3] original_two_directions_in_band.1).1
  linarith

lemma original_light_cone_discriminants (k : Fin 3 → ℝ) (ρ : ℝ)
    (hρ : ρ ^ 2 = radiusSquared k) :
    simpleDiscriminant (componentSquares (lightConeMomentum 1 ρ k)) (lightConeMomentum 1 ρ k) =
      lightConeDiscriminant 1 ρ k ∧
    simpleDiscriminant (componentSquares (lightConeMomentum (-1) ρ k))
      (lightConeMomentum (-1) ρ k) = lightConeDiscriminant (-1) ρ k := by
  change ρ ^ 2 = k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 at hρ
  have hp : lorentzDot (lightConeMomentum 1 ρ k) (lightConeMomentum 1 ρ k) = 0 := by
    norm_num [lorentzDot, signature, lightConeMomentum, Fin.sum_univ_succ]
    linear_combination -hρ
  have hm : lorentzDot (lightConeMomentum (-1) ρ k) (lightConeMomentum (-1) ρ k) = 0 := by
    norm_num [lorentzDot, signature, lightConeMomentum, Fin.sum_univ_succ]
    linear_combination -hρ
  have hup : lorentzDot (componentSquares (lightConeMomentum 1 ρ k)) (lightConeMomentum 1 ρ k) =
      cubicMoment k - ρ ^ 3 := by
    norm_num [lorentzDot, signature, componentSquares, lightConeMomentum, cubicMoment,
      Fin.sum_univ_succ]
    ring
  have hum : lorentzDot (componentSquares (lightConeMomentum (-1) ρ k)) (lightConeMomentum (-1)
    ρ k) =
      cubicMoment k + ρ ^ 3 := by
    norm_num [lorentzDot, signature, componentSquares, lightConeMomentum, cubicMoment,
      Fin.sum_univ_succ]
    ring
  constructor
  · rw [simpleDiscriminant, hp, mul_zero, hup]
    simp [lightConeDiscriminant]
  · rw [simpleDiscriminant, hm, mul_zero, hum]
    simp [lightConeDiscriminant]

lemma actual_fixed_band_discriminants (k : Fin 3 → ℝ) (hk : fixedBand k) :
    simpleDiscriminant
      (componentSquares (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k))
      (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) ≤ -729 / 400 ∧
    simpleDiscriminant
      (componentSquares (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k))
      (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) ≤ -729 / 400 := by
  have hR : 0 ≤ radiusSquared k := by unfold radiusSquared;positivity
  have hd := original_light_cone_discriminants k (Real.sqrt (radiusSquared k)) (Real.sq_sqrt hR)
  rw [hd.1, hd.2]
  exact fixed_band_discriminant_budget k hk

lemma actual_fixed_band_inverse (k : Fin 3 → ℝ) (hk : fixedBand k) :
    (nativeUpperSymbol (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) *
      nativeCoordinateInverse (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) = 1 ∧
     nativeCoordinateInverse (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) *
      nativeUpperSymbol (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) = 1) ∧
    (nativeUpperSymbol (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) *
      nativeCoordinateInverse (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) = 1 ∧
     nativeCoordinateInverse (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) *
      nativeUpperSymbol (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) = 1) := by
  have hd := actual_fixed_band_discriminants k hk
  constructor
  · apply native_coordinate_both_inverse
    linarith [hd.1]
  · apply native_coordinate_both_inverse
    linarith [hd.2]

/-- **GAC2:native-reflected-band-inverse-guards**
(compact reflected native band and both light-cone inverse guards). -/
@[ledger "GAC2:native-reflected-band-inverse-guards"]
theorem bandLaw : Statement.bandLaw := by
  exact ⟨fixed_band_reflected,
    original_two_directions_in_band,
    full_angular_guard,
    fixed_band_compact,
    native_cubic_moment_bound,
    both_light_cones_separated,
    actual_fixed_band_discriminants,
    actual_fixed_band_inverse⟩

/-! ## Non-vacuity -/

example : nativeUpperSymbol (lightConeMomentum 1 (Real.sqrt (radiusSquared ![1, 2, 3])) ![1, 2,
  3]) *
    nativeCoordinateInverse (lightConeMomentum 1 (Real.sqrt (radiusSquared ![1, 2, 3])) ![1, 2,
      3]) = 1 :=
  (actual_fixed_band_inverse ![1, 2, 3] original_two_directions_in_band.1).1.1

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
