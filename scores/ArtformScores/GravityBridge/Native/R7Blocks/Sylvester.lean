import ArtformScores.GravityBridge.Native.R7Blocks.SylvesterStatements

/-! # A two-sided quadratic-resolvent Sylvester formula -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma quadratic_resolvent_commutes (r : ℝ) (N : Z →L[ℝ] Z) :
    (quadraticResolvent r N).comp N = N.comp (quadraticResolvent r N) := by
  apply ContinuousLinearMap.ext
  intro z
  simp [quadraticResolvent]

lemma inverse_commutes_with_native_block (r : ℝ) (N L : Z →L[ℝ] Z)
    (hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z) :
    N.comp L = L.comp N := by
  calc
    N.comp L = (L.comp (quadraticResolvent r N)).comp (N.comp L) := by rw [hLB]; rfl
    _ = L.comp (((quadraticResolvent r N).comp N).comp L) := by
      rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    _ = L.comp ((N.comp (quadraticResolvent r N)).comp L) := by
      rw [quadratic_resolvent_commutes]
    _ = L.comp (N.comp ((quadraticResolvent r N).comp L)) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = L.comp N := by rw [hBL]; rfl

lemma quadratic_sylvester_solves (r : ℝ) (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z)
    (hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z) :
    (quadraticSylvester S N L F).comp S - N.comp (quadraticSylvester S N L F) = F := by
  have hn := inverse_commutes_with_native_block r N L hLB hBL
  apply ContinuousLinearMap.ext
  intro y
  have hsy := congrArg (fun T : Y →L[ℝ] Y => T y) hS
  have hcomm (z : Z) : N (L z) = L (N z) := congrArg (fun T : Z →L[ℝ] Z => T z) hn
  have hreturn (z : Z) : L (N (N z) + r • z) = z :=
    congrArg (fun T : Z →L[ℝ] Z => T z) hLB
  change -(L (F (S (S y)) + N (F (S y)))) - N (-(L (F (S y) + N (F y)))) = F y
  change S (S y) = -r • y at hsy
  rw [hsy, map_neg, hcomm]
  simp only [map_add, map_smul, neg_smul, map_neg]
  calc
    _ = L (N (N (F y)) + r • F y) := by
      simp only [map_add, map_smul]
      abel
    _ = F y := hreturn (F y)

lemma quadratic_sylvester_unique (r : ℝ) (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z)
    (hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (hK : K.comp S - N.comp K = F) : K = quadraticSylvester S N L F := by
  apply ContinuousLinearMap.ext
  intro y
  have hsy := congrArg (fun T : Y →L[ℝ] Y => T y) hS
  have hk (x : Y) : K (S x) - N (K x) = F x :=
    congrArg (fun T : Y →L[ℝ] Z => T x) hK
  have hky : K (S y) = F y + N (K y) := by
    have hh := hk y
    exact sub_eq_iff_eq_add.mp hh
  have hh := hk (S y)
  change S (S y) = (-r) • y at hsy
  rw [hsy, map_smul, hky, map_add] at hh
  have hb : quadraticResolvent r N (K y) = -(F (S y) + N (F y)) := by
    change N (N (K y)) + r • K y = -(F (S y) + N (F y))
    rw [← hh]
    simp only [neg_smul]
    abel
  have hl := congrArg L hb
  have hreturn : L (quadraticResolvent r N (K y)) = K y :=
    congrArg (fun T : Z →L[ℝ] Z => T (K y)) hLB
  rw [hreturn, map_neg] at hl
  exact hl


lemma quadratic_sylvester_norm (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z) :
    ‖quadraticSylvester S N L F‖ ≤ ‖L‖ * ‖F‖ * (‖S‖ + ‖N‖) := by
  rw [quadraticSylvester, norm_neg]
  calc
    _ ≤ ‖L‖ * ‖F.comp S + N.comp F‖ := L.opNorm_comp_le _
    _ ≤ ‖L‖ * (‖F.comp S‖ + ‖N.comp F‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖L‖ * (‖F‖ * ‖S‖ + ‖N‖ * ‖F‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (F.opNorm_comp_le _) (N.opNorm_comp_le _))
        (norm_nonneg _)
    _ = ‖L‖ * ‖F‖ * (‖S‖ + ‖N‖) := by ring

lemma reference_sylvester_hypotheses :
    referenceOscillator.comp referenceOscillator =
      (-14 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
    referenceInverse.comp (quadraticResolvent 14 (0 : ℝ →L[ℝ] ℝ)) =
      ContinuousLinearMap.id ℝ ℝ ∧
    (quadraticResolvent 14 (0 : ℝ →L[ℝ] ℝ)).comp referenceInverse =
      ContinuousLinearMap.id ℝ ℝ := by
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro y
    apply Prod.ext <;> simp [referenceOscillator]
  · apply ContinuousLinearMap.ext
    intro y
    norm_num [referenceInverse, quadraticResolvent]
    ring
  · apply ContinuousLinearMap.ext
    intro y
    norm_num [referenceInverse, quadraticResolvent]
    ring

lemma reference_prepared_output :
    quadraticSylvester referenceOscillator 0 referenceInverse referenceForcing =
      (-18 / 3535 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro y
  simp [quadraticSylvester, referenceOscillator, referenceInverse, referenceForcing]
  ring

/-- **GAC2:quadratic-resolvent-sylvester**
(a two-sided quadratic-resolvent sylvester formula). -/
@[ledger "GAC2:quadratic-resolvent-sylvester"]
theorem sylvesterLaw : Statement.sylvesterLaw := by
  intro Y Z _ _ _ _
  exact ⟨quadratic_resolvent_commutes,
    inverse_commutes_with_native_block,
    quadratic_sylvester_solves,
    quadratic_sylvester_unique,
    quadratic_sylvester_norm,
    reference_sylvester_hypotheses,
    reference_prepared_output⟩

/-! ## Non-vacuity -/

example : (referenceForcing (1, 0)) ≠ 0 ∧
    (quadraticSylvester referenceOscillator 0 referenceInverse referenceForcing).comp
      referenceOscillator = referenceForcing := by
  constructor
  · norm_num [referenceForcing]
  · have h := quadratic_sylvester_solves 14 referenceOscillator 0 referenceInverse
      referenceForcing reference_sylvester_hypotheses.1
      reference_sylvester_hypotheses.2.1 reference_sylvester_hypotheses.2.2
    simpa using h

example : quadraticResolvent 14 (0 : ℝ →L[ℝ] ℝ) =
    (14 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  simp [quadraticResolvent]

end Artform.Scores.GravityBridge.Native.R7Blocks
