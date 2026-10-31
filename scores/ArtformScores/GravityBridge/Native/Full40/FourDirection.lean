import ArtformScores.GravityBridge.Native.Full40.FourDirectionStatements

/-! # A noncollapsed four-shift finite periodic force test -/

namespace Artform.Scores.GravityBridge.Native.Full40



set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Normalize the complete finite periodic action and three independent coordinate tests.
lemma four_direction_action : completeQuadratic testStep (1 / 101) fullPulse = 12 / 101 :=
  by
    norm_num [completeQuadratic, nativeFirstVariation, nativeBilinear, nativeLU,
      linearComplement, connectionComplement, nativeV, flatComplement,
      nativeK, linearCurvature, rawPlaquetteContact, nativeLetters, nativeTheta,
      torsion, fullPulse, originTest, testStep, firstWedge, wedge, basisVector,
      complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
      lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
      bivSign, etaPair, eta, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Normalize the complete finite periodic action and three independent coordinate tests.
lemma four_direction_force_tests :
    nativeFirstVariation testStep (1 / 101) fullPulse (originTest 0) = 12 / 101 ∧
    nativeFirstVariation testStep (1 / 101) fullPulse (originTest 16) = -2 / 101 ∧
    nativeFirstVariation testStep (1 / 101) fullPulse (originTest 39) = 0 :=
  by
    norm_num [completeQuadratic, nativeFirstVariation, nativeBilinear, nativeLU,
      linearComplement, connectionComplement, nativeV, flatComplement,
      nativeK, linearCurvature, rawPlaquetteContact, nativeLetters, nativeTheta,
      torsion, fullPulse, originTest, testStep, firstWedge, wedge, basisVector,
      complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
      lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
      bivSign, etaPair, eta, Fin.sum_univ_succ]


lemma independent_test_steps : ∀ i j : Fin 4, i ≠ j →
    
    testStep i ≠ 0 ∧ testStep i ≠ testStep j ∧ testStep i + testStep j ≠ 0 := by decide +kernel

lemma nontrivial_four_differences : ∀ i : Fin 4,
    (fullPulse (0 + testStep i)).1 i i - (fullPulse 0).1 i i = -1 := by decide +kernel

lemma origin_test_zero_unit : originTest 0 = fieldCoordinates.symm
    (Pi.single (0, Sum.inl (0, 0)) (1 : ℚ)) := by
  classical
  funext x
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [originTest, fieldCoordinates, unpack, Pi.single_apply]
  · ext i a
    fin_cases i <;> fin_cases a <;>
      simp [originTest, fieldCoordinates, unpack, Pi.single_apply]

lemma origin_test_sixteen_unit : originTest 16 = fieldCoordinates.symm
    (Pi.single (0, Sum.inr (0, 0)) (1 : ℚ)) := by
  classical
  funext x
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [originTest, fieldCoordinates, unpack, Pi.single_apply]
  · ext i a
    fin_cases i <;> fin_cases a <;>
      simp [originTest, fieldCoordinates, unpack, Pi.single_apply]

lemma four_direction_actual_force :
    fullForce testStep (1 / 101 : ℚ) fullPulse (0, Sum.inl (0, 0)) = 12 / 101 ∧
    fullForce testStep (1 / 101 : ℚ) fullPulse (0, Sum.inr (0, 0)) = -2 / 101 := by
  constructor
  · change nativeFirstVariation _ _ _ _ = _
    convert four_direction_force_tests.1 using 1
    congr 1
    convert origin_test_zero_unit.symm using 1
    congr 1
    funext a
    simp [Pi.single_apply]
  · change nativeFirstVariation _ _ _ _ = _
    convert four_direction_force_tests.2.1 using 1
    congr 1
    convert origin_test_sixteen_unit.symm using 1
    congr 1
    funext a
    simp [Pi.single_apply]

/-- **GAC2:four-shift-original-force-test**
(a noncollapsed four-shift finite periodic force test). -/
@[ledger "GAC2:four-shift-original-force-test"]
theorem fourDirectionLaw : Statement.fourDirectionLaw := by
  exact ⟨four_direction_action,
    four_direction_force_tests,
    independent_test_steps,
    nontrivial_four_differences,
    four_direction_actual_force⟩

/-! ## Non-vacuity -/
example : (fullPulse 0).1 0 0 = 1 ∧ (fullPulse (testStep 0)).1 0 0 = 0 := by
  decide +kernel

end Artform.Scores.GravityBridge.Native.Full40
