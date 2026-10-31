import ArtformScores.GravityBridge.Native.Full40.CoordinatesStatements

/-! # Original forty coordinates Gram and Hodge data -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

lemma coordinate_count : Fintype.card Coordinate = 40 := by decide +kernel
omit [Field K] [CharZero K] in
lemma unpack_pack (x : Full K) : unpack (pack x) = x := rfl
omit [Field K] [CharZero K] in
lemma pack_unpack (x : Coordinate → K) : pack (unpack x) = x := by
  funext i
  cases i <;> rfl
omit [CharZero K] in
lemma lie_coordinates (a : Biv K) : lieCoordinates (lie a) = a := by
  funext i
  fin_cases i <;> simp [lieCoordinates, lie]
omit [CharZero K] in
lemma lie_injective : Function.Injective (lie (K := K)) := by
  intro a b he
  have h := congrArg lieCoordinates he
  simpa only [lie_coordinates] using h
omit [CharZero K] in
lemma lie_metric_kernel (a : Biv K) : ∀ i j, metricVariation (lie a) i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [metricVariation, lie, eta]
lemma lie_kernel_surjective (F : Frame K) :
    (∀ i j, metricVariation F i j = 0) ↔ ∃ a : Biv K, F = lie a := by
  constructor
  · intro h
    refine ⟨lieCoordinates F, ?_⟩
    ext i j
    have he := h i j
    fin_cases i <;> fin_cases j <;>
      norm_num [metricVariation, eta, lie, lieCoordinates] at he ⊢
    all_goals first | exact he | exact he.symm | linear_combination he
  · rintro ⟨a, rfl⟩
    exact lie_metric_kernel a
lemma gram_trace (a b : Biv K) : bivPair a b = -(Matrix.trace (lie a * lie b)) / 2 := by
  simp [bivPair, bivSign, lie, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma gram_pair (a b : Biv K) : bivPair a b = ∑ i, gramConvert a i * b i := rfl
omit [CharZero K] in
lemma gram_convert_involution (a : Biv K) : gramConvert (gramConvert a) = a := by
  funext i
  fin_cases i <;> norm_num [gramConvert, bivSign]
omit [CharZero K] in
lemma frame_gram_involution (f : Frame K) : frameGram (frameGram f) = f := by
  ext i j
  fin_cases i <;> norm_num [frameGram, eta]
lemma biv_pair_nondegenerate (a : Biv K) (ha : ∀ b, bivPair a b = 0) : a = 0 := by
  funext i
  have hi := ha (Pi.single i 1)
  simp [bivPair, Pi.single_apply, mul_ite] at hi
  have hs : bivSign (K := K) i ≠ 0 := by
    dsimp [bivSign]
    split <;> norm_num
  exact hi.resolve_left hs
omit [CharZero K] in
lemma internal_star_square (a : Biv K) : internalStar (internalStar a) = -a := by
  funext i
  fin_cases i <;> simp [internalStar]
omit [CharZero K] in
lemma internal_star_selfadjoint (a b : Biv K) :
    bivPair (internalStar a) b = bivPair a (internalStar b) := by
  simp [bivPair, bivSign, internalStar, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma internal_star_gram (a b : Biv K) :
    bivPair a (internalStar b) =
      a 0 * b 3 + a 1 * b 4 + a 2 * b 5 + a 3 * b 0 + a 4 * b 1 + a 5 * b 2 := by
  simp [bivPair, bivSign, internalStar, Fin.sum_univ_succ]
  ring

/-- **GAC2:native-forty-coordinate-gram**
(original forty coordinates gram and hodge data). -/
@[ledger "GAC2:native-forty-coordinate-gram"]
theorem coordinatesLaw : Statement.coordinatesLaw := by
  intro K _ _
  exact ⟨coordinate_count,
    unpack_pack,
    pack_unpack,
    lie_coordinates,
    lie_injective,
    lie_metric_kernel,
    lie_kernel_surjective,
    gram_trace,
    gram_pair,
    gram_convert_involution,
    frame_gram_involution,
    biv_pair_nondegenerate,
    internal_star_square,
    internal_star_selfadjoint,
    internal_star_gram⟩

/-! ## Non-vacuity -/
example : bivPair ![1, 0, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0] = (-1 : ℝ) ∧
    bivPair ![0, 0, 0, 1, 0, 0] ![0, 0, 0, 1, 0, 0] = (1 : ℝ) := by
  norm_num [bivPair, bivSign, Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.Full40
