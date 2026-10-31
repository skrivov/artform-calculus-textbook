import ArtformScores.GravityBridge.Native.CurvedSubdivision.WordsStatements

/-! # All six original based words and guarded reverse loops -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
omit [CharZero K] in
lemma actual_two_boost_product (c s d t : K) :
    boost c s * boost d t = boost (c * d + s * t) (s * d + c * t) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [boost, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
lemma all_original_owned_plaquettes (c0 s0 c1 s1 : K) (h0 : c0 ^ 2 - s0 ^ 2 = 1) :
    basedPlaquette c0 s0 c1 s1 = fun r =>
      if r = 0 then boost (c0 * c1 - s0 * s1) (c0 * s1 - s0 * c1) else 1 := by
  have hb := (boost_inverse_and_metric c0 s0 h0).2.1
  have ha : boost c0 (-s0) * boost c1 s1 =
      boost (c0 * c1 - s0 * s1) (c0 * s1 - s0 * c1) := by
    rw [actual_two_boost_product]
    congr 1 <;> ring
  funext r
  fin_cases r <;>
    simp [basedPlaquette, ownedEdge, reversedEdge, faceFirst, faceSecond, hb, ha]

omit [CharZero K] in
lemma all_original_reversed_plaquettes (c0 s0 c1 s1 : K) (h0 : c0 ^ 2 - s0 ^ 2 = 1) :
    reversePlaquette c0 s0 c1 s1 = fun r =>
      if r = 0 then boost (c0 * c1 - s0 * s1) (-(c0 * s1 - s0 * c1)) else 1 := by
  have hb := (boost_inverse_and_metric c0 s0 h0).2.1
  have ha : boost c1 (-s1) * boost c0 s0 =
      boost (c0 * c1 - s0 * s1) (-(c0 * s1 - s0 * c1)) := by
    rw [actual_two_boost_product]
    congr 1 <;> ring
  funext r
  fin_cases r <;>
    simp [reversePlaquette, ownedEdge, reversedEdge, faceFirst, faceSecond, hb, ha]

omit [CharZero K] in
lemma original_six_word_inverses (c0 s0 c1 s1 : K)
    (h0 : c0 ^ 2 - s0 ^ 2 = 1) (h1 : c1 ^ 2 - s1 ^ 2 = 1) (r : Fin 6) :
    basedPlaquette c0 s0 c1 s1 r * reversePlaquette c0 s0 c1 s1 r = 1 ∧
      reversePlaquette c0 s0 c1 s1 r * basedPlaquette c0 s0 c1 s1 r = 1 := by
  have hf : (c0 * c1 - s0 * s1) ^ 2 - (c0 * s1 - s0 * c1) ^ 2 = 1 := by
    calc
      _ = (c0 ^ 2 - s0 ^ 2) * (c1 ^ 2 - s1 ^ 2) := by ring
      _ = 1 := by rw [h0, h1];norm_num
  rw [congrFun (all_original_owned_plaquettes c0 s0 c1 s1 h0) r,
    congrFun (all_original_reversed_plaquettes c0 s0 c1 s1 h0) r]
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    exact ⟨(boost_inverse_and_metric _ _ hf).1, (boost_inverse_and_metric _ _ hf).2.1⟩
  · simp [hr]

lemma all_inverse_skew_faces (c0 s0 c1 s1 : K) (h0 : c0 ^ 2 - s0 ^ 2 = 1) :
    (fun r => (-1 / 2 : K) • (basedPlaquette c0 s0 c1 s1 r - reversePlaquette c0 s0 c1 s1 r)) =
      fun r => if r = 0 then lie ![-(c0 * s1 - s0 * c1), 0, 0, 0, 0, 0] else 0 := by
  rw [all_original_owned_plaquettes c0 s0 c1 s1 h0,
    all_original_reversed_plaquettes c0 s0 c1 s1 h0]
  funext r
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    exact actual_inverse_skew_boost _ _
  · simp [hr]

/-- **GAC2:native-six-curved-words**
(all six original based words and guarded reverse loops). -/
@[ledger "GAC2:native-six-curved-words"]
theorem wordsLaw : Statement.wordsLaw := by
  intro K _ _
  exact ⟨actual_two_boost_product,
    all_original_owned_plaquettes,
    all_original_reversed_plaquettes,
    original_six_word_inverses,
    all_inverse_skew_faces⟩

/-! ## Non-vacuity -/
example : basedPlaquette (1 : ℚ) 0 (5 / 4) (3 / 4) 0 = boost (5 / 4) (3 / 4) := by
  rw [all_original_owned_plaquettes 1 0 (5 / 4) (3 / 4) (by norm_num)]
  norm_num

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
