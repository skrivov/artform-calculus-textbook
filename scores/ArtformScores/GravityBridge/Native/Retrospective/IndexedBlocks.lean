import ArtformScores.GravityBridge.Native.Retrospective.IndexedBlocksStatements

/-! # Indexed original distinct and repeated connection restrictions -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Full40



open Full40

lemma constant_connection_density (t : ℚ) (A : Connection ℚ) :
    connectionDensity t A = ∑ r : Fin 6,
      (bivPair (flatComplement r) (internalStar
        (rawPlaquetteContact (fun _ => Unit.unit) (fun _ : Unit => (0, A))
          (fun _ : Unit => (0, A)) Unit.unit r)) +
       t * eta (faceFirst r) * eta (faceSecond r) * etaPair
        (nativeTheta (fun _ => Unit.unit) (fun _ : Unit => (0, A)) Unit.unit r)
        (nativeTheta (fun _ => Unit.unit) (fun _ : Unit => (0, A)) Unit.unit r)) := by
  have hk (r : Fin 6) : nativeK (fun _ => Unit.unit)
      (fun _ : Unit => (0, A)) Unit.unit r = 0 := by
    simp [nativeK, linearCurvature]
  unfold connectionDensity completeQuadratic nativeBilinear
  simp only [hk]
  have hz : internalStar (0 : Biv ℚ) = 0 := by
    ext a
    fin_cases a <;> simp [internalStar]
  have hp (a : Biv ℚ) : bivPair a 0 = 0 := by simp [bivPair]
  simp only [hz, hp, zero_add, Fintype.sum_unique, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Check the four original index triples against the full six-face density.
lemma indexed_distinct_density (s : Fin 4) (t : ℚ) (z : Fin 3 → ℚ) :
    connectionDensity t (distinctInput s z) = distinctDensity s t z := by
  rw [constant_connection_density]
  simp only [Fin.sum_univ_succ]
  fin_cases s <;>
    simp [distinctInput, distinctIndices, distinctDensity, rawPlaquetteContact,
      nativeLetters, nativeTheta, torsion, lie, flatComplement, complementSign,
      complementFirst, complementSecond, faceFirst, faceSecond, basisVector, wedge,
      bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair, bivSign,
      etaPair, eta, Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Check the four original index triples against the full six-face density.
lemma indexed_repeated_density (b : Fin 4) (t : ℚ) (z : Fin 3 → ℚ) :
    connectionDensity t (repeatedInput b z) = repeatedDensity b t z := by
  rw [constant_connection_density]
  simp only [Fin.sum_univ_succ]
  fin_cases b <;>
    simp [repeatedInput, Fin.succAbove, Fin.lt_def, repeatedDensity, rawPlaquetteContact,
      nativeLetters, nativeTheta, torsion, lie, flatComplement, complementSign,
      complementFirst, complementSecond, faceFirst, faceSecond, basisVector, wedge,
      bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair, bivSign,
      etaPair, eta, Fin.sum_univ_succ] <;> ring


lemma original_distinct_block_recovered (t : ℚ) (z : Fin 3 → ℚ) :
    connectionDensity t (distinctInput 0 z) =
      (∑ i, z i * (∑ j, paramConnection t i j * z j)) / 2 := by
  rw [indexed_distinct_density]
  simp [distinctDensity, distinctIndices, eta, paramConnection, curvatureBlock,
    torsionBlock, facePairing, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  ring

lemma indexed_repeated_block_recovered (b : Fin 4) (t : ℚ) (z : Fin 3 → ℚ) :
    connectionDensity t (repeatedInput b z) =
      (∑ i, z i * (∑ j, repeatedBlock b t i j * z j)) / 2 := by
  rw [indexed_repeated_density]
  simp [repeatedDensity, repeatedBlock, Fin.sum_univ_succ]
  ring

/-- **GAC2:indexed-original-connection-blocks**
(indexed original distinct and repeated connection restrictions). -/
@[ledger "GAC2:indexed-original-connection-blocks"]
theorem indexedBlocksLaw : Statement.indexedBlocksLaw := by
  
  exact ⟨indexed_distinct_density,
    indexed_repeated_density,
    original_distinct_block_recovered,
    indexed_repeated_block_recovered⟩

/-! ## Non-vacuity -/
example : connectionDensity (1 / 101) (distinctInput 0 ![1, 0, 0]) = -2 / 101 := by
  rw [indexed_distinct_density]
  norm_num [distinctDensity, distinctIndices, eta]
example : connectionDensity (1 / 101) (repeatedInput 0 ![1, 0, 0]) = -1 / 101 := by
  rw [indexed_repeated_density]
  norm_num [repeatedDensity, eta]

end Artform.Scores.GravityBridge.Native.Retrospective
