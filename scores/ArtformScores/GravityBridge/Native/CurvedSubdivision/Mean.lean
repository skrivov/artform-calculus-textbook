import ArtformScores.GravityBridge.Native.CurvedSubdivision.MeanStatements

/-! # Original five transported complementary bivector terms -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
omit [CharZero K] in
lemma actual_boost_transport_fixes_complement (c s b : K) :
    transportedComplement c s b = complementaryBivector b := by
  ext a
  fin_cases a <;>
    norm_num [transportedComplement, complementaryBivector, wedge, basisVector, boost,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma original_five_term_average (c0 s0 c1 s1 b : K) :
    fiveTermComplement c0 s0 c1 s1 b = complementaryBivector b := by
  simp only [fiveTermComplement, actual_boost_transport_fixes_complement]
  module

lemma original_active_curvature_reading (c s : K) : activeCurvature c s = ![-s, 0, 0, 0, 0, 0] := by
  unfold activeCurvature
  rw [actual_inverse_skew_boost]
  rfl

lemma original_complete_curvature_fold (c0 s0 c1 s1 b cf sf : K) :
    completeCurvatureFold c0 s0 c1 s1 b cf sf = -b * sf := by
  norm_num [completeCurvatureFold, original_five_term_average, original_active_curvature_reading,
    complementaryBivector, wedge, basisVector, bivPair, bivSign, internalStar, Fin.sum_univ_succ]

/-- **GAC2:native-curved-five-transport**
(original five transported complementary bivector terms). -/
@[ledger "GAC2:native-curved-five-transport"]
theorem meanLaw : Statement.meanLaw := by
  intro K _ _
  exact ⟨actual_boost_transport_fixes_complement,
    original_five_term_average,
    original_active_curvature_reading,
    original_complete_curvature_fold⟩

/-! ## Non-vacuity -/
example : completeCurvatureFold (1 : ℚ) 0 (5 / 4) (3 / 4) 1 (17 / 8) (15 / 8) = -15 / 8 := by
  rw [original_complete_curvature_fold]
  norm_num

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
