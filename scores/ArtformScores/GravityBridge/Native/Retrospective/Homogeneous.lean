import ArtformScores.GravityBridge.Native.Retrospective.HomogeneousStatements
/-! # The full original24 homogeneous connection partition and density -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Full40
open Full40
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Expand all24 original connection slots once to verify the full homogeneous decomposition.
lemma full_homogeneous_density (t : ℚ) (d e : Fin 4 → Fin 3 → ℚ) :
    connectionDensity t (assembleConnection d e) =
      (∑ s, distinctDensity s t (d s)) + ∑ b, repeatedDensity b t (e b) := by
  rw [constant_connection_density]
  simp only [Fin.sum_univ_succ]
  simp [assembleConnection, distinctInput, distinctIndices, repeatedInput, Fin.succAbove,
    Fin.lt_def, distinctDensity, repeatedDensity, rawPlaquetteContact,
    nativeLetters, nativeTheta, torsion, lie, flatComplement, complementSign,
    complementFirst, complementSecond, faceFirst, faceSecond, basisVector, wedge,
    bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair, bivSign,
    etaPair, eta, Fin.sum_univ_succ]
  ring
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the24 oriented original coordinates, including every boost and31 sign.
lemma connection_partition_left_inverse (A : Connection ℚ) :
    assembleConnection (distinctCoordinates A) (repeatedCoordinates A) = A := by
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    simp [assembleConnection, distinctCoordinates, repeatedCoordinates, orientedComponent,
      distinctInput, distinctIndices, repeatedInput, Fin.succAbove, Fin.lt_def,
      wedge, basisVector, Fin.sum_univ_succ]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Recover each of the12 distinct-index coordinates from the same signed assembly.
lemma connection_partition_distinct (d e : Fin 4 → Fin 3 → ℚ) :
    distinctCoordinates (assembleConnection d e) = d := by
  ext s j
  fin_cases s <;> fin_cases j <;>
    simp [assembleConnection, distinctCoordinates, orientedComponent,
      distinctInput, distinctIndices, repeatedInput, Fin.succAbove, Fin.lt_def,
      wedge, basisVector, Fin.sum_univ_succ]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Recover each of the12 repeated-index coordinates without changing the orientation.
lemma connection_partition_repeated (d e : Fin 4 → Fin 3 → ℚ) :
    repeatedCoordinates (assembleConnection d e) = e := by
  ext b j
  fin_cases b <;> fin_cases j <;>
    simp [assembleConnection, repeatedCoordinates, orientedComponent,
      distinctInput, distinctIndices, repeatedInput, Fin.succAbove, Fin.lt_def,
      wedge, basisVector, Fin.sum_univ_succ]
lemma arbitrary_connection_density (t : ℚ) (A : Connection ℚ) :
    connectionDensity t A =
      (∑ s, distinctDensity s t (distinctCoordinates A s)) +
      ∑ b, repeatedDensity b t (repeatedCoordinates A b) := by
  rw [← full_homogeneous_density, connection_partition_left_inverse]
/-- **GAC2:full24-homogeneous-decomposition**
(the full original24 homogeneous connection partition and density). -/
@[ledger "GAC2:full24-homogeneous-decomposition"]
theorem homogeneousLaw : Statement.homogeneousLaw := by
  exact ⟨full_homogeneous_density,
    connection_partition_left_inverse,
    connection_partition_distinct,
    connection_partition_repeated,
    arbitrary_connection_density⟩
/-! ## Non-vacuity -/
example : connectionDensity (1 / 101)
    (assembleConnection (fun _ => ![1, 1, 1]) (fun _ => ![2, 2, 2])) = -3006 / 101 := by
  rw [full_homogeneous_density]
  norm_num [distinctDensity, repeatedDensity, distinctIndices, eta, Fin.sum_univ_succ]
end Artform.Scores.GravityBridge.Native.Retrospective
