import ArtformScores.GravityBridge.RegulatorStatements

/-! # Spatial symmetry permits two coefficients in the declared interacting regulator -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma signed_spatial_quadratic_classification (a : Fin 4 → ℚ) (b : Fin 6 → ℚ) :
    spatialSignedKinetic a b ↔ b = 0 ∧ a 1 = a 2 ∧ a 2 = a 3 := by
  constructor
  · rintro ⟨hf, h12, h23⟩
    have hb0 := hf 0 ![1, 1, 0, 0]
    have hb1 := hf 0 ![1, 0, 1, 0]
    have hb2 := hf 0 ![1, 0, 0, 1]
    have hb3 := hf 1 ![0, 1, 1, 0]
    have hb4 := hf 1 ![0, 1, 0, 1]
    have hb5 := hf 2 ![0, 0, 1, 1]
    have h0 : b = 0 := by
      ext j
      fin_cases j <;>
        norm_num [quadraticKinetic, kineticReflection] at hb0 hb1 hb2 hb3 hb4 hb5 ⊢ <;>
        linarith
    have ha12 := h12 ![0, 1, 0, 0]
    have ha23 := h23 ![0, 0, 1, 0]
    simp [quadraticKinetic, kineticSwap12, kineticSwap23] at ha12 ha23
    exact ⟨h0, ha12.symm, ha23.symm⟩
  · rintro ⟨rfl, h12, h23⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i k
      fin_cases i <;> simp [quadraticKinetic, kineticReflection]
    · intro k
      simp [quadraticKinetic, kineticSwap12, h12]
      ring
    · intro k
      simp [quadraticKinetic, kineticSwap23, h23]
      ring

lemma spatial_kinetic_two_parameters (ct cs : ℚ) :
    spatialSignedKinetic ![ct, cs, cs, cs] 0 := by
  rw [signed_spatial_quadratic_classification]
  simp

lemma signed_class_not_time_space_equality :
    spatialSignedKinetic ![2, 1, 1, 1] 0 ∧
    quadraticKinetic ![2, 1, 1, 1] 0 ![1, 0, 0, 0] ≠
      quadraticKinetic ![2, 1, 1, 1] 0 ![0, 1, 0, 0] := by
  refine ⟨spatial_kinetic_two_parameters 2 1, ?_⟩
  norm_num [quadraticKinetic]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma walsh_four_orthogonal :
    ∀ k l : BinarySite, (∑ x, walshFour x k * walshFour x l) = if k = l then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma walsh_source_axis : ∀ (i : Fin 4) (k l : BinarySite),
    walshSourceGram (momentumAxis i) k l = if l = k ^^^ momentumAxis i then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma walsh_axis_gradient_gram : ∀ (i : Fin 4) (k l : BinarySite),
    (∑ x, walshAxisDifference i x k * walshAxisDifference i x l) =
      if k = l then 4 * (if k.val.testBit i.val then 1 else 0) else 0 := by
  decide +kernel

lemma local_precision_diagonal (ct cs : ℚ) (k l : BinarySite) :
    localPrecisionGram ct cs k l = if k = l then modePrecision ct cs k else 0 := by
  unfold localPrecisionGram
  simp_rw [walsh_four_orthogonal, walsh_axis_gradient_gram]
  by_cases h : k = l
  · simp [h, modePrecision, Fin.sum_univ_succ]
    split_ifs <;> ring
  · simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma regulator_spatial_responses (ct cs : ℚ) :
    loopResponse ct cs 1 = loopResponse ct cs 2 ∧
    loopResponse ct cs 2 = loopResponse ct cs 3 := by
  constructor <;>
    norm_num [loopResponse, modePrecision, momentumAxis, Fin.sum_univ_succ, Nat.testBit] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma anisotropic_loop_response :
    loopResponse 2 1 0 = 19 / 10 ∧ loopResponse 2 1 1 = 34 / 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma axis_representative_card : ∀ i : Fin 4, Fintype.card (AxisRepresentatives i) = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma axis_pair_partition : ∀ (i : Fin 4) (k : BinarySite),
    ∃! r : AxisRepresentatives i, k = r.val ∨ k = r.val ^^^ momentumAxis i := by
  unfold ExistsUnique
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma mode_precision_lower : ∀ k : BinarySite, 1 ≤ modePrecision 2 1 k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Expanding sixteen-site rational Fourier sums needs this bounded kernel-checking budget.
lemma pair_response_half : ∀ i : Fin 4,
    (∑ k : AxisRepresentatives i, 1 / pairWeight i k) = loopResponse 2 1 i / 2 := by
  decide +kernel

/-- **GAC:finite-regulator-symmetry** (exact finite regulator, without a native speed claim). -/
@[ledger "GAC:finite-regulator-symmetry"]
theorem regulatorLaw : Statement.regulatorLaw := by
  exact ⟨signed_spatial_quadratic_classification, spatial_kinetic_two_parameters,
    signed_class_not_time_space_equality, walsh_four_orthogonal, walsh_source_axis,
    walsh_axis_gradient_gram, local_precision_diagonal, regulator_spatial_responses,
    anisotropic_loop_response, axis_representative_card, axis_pair_partition,
    mode_precision_lower, pair_response_half⟩

/-! ## Non-vacuity -/

example : modePrecision 2 1 0 = 1 ∧ pairWeight 0 ⟨0, rfl⟩ = 3 := by
  decide +kernel

end

end Artform.Scores.GravityBridge
