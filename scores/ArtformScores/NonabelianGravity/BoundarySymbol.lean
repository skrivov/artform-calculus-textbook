import ArtformScores.NonabelianGravity.BoundaryStencil

/-! # Full reciprocal-character native boundary symbol and exact boost witness -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundarySymbol
open Artform.Scores.GravityBridge.Native.Full40
open Artform.Scores.NonabelianGravity.Legendre (Point fieldPoint frameSlot connectionSlot)
variable {K : Type*} [Field K] [CharZero K]

abbrev SpaceTime := Fin 3 × Fin 3

def spatialStep : Fin 4 → SpaceTime := ![(1, 0), (0, 1), (0, 0), (0, 0)]

def characterField (z : K) (u v : Point K) (x : SpaceTime) : Full K :=
  if x.1 = 0 then
    (fun i j => z ^ x.2.val * u (frameSlot i j),
     fun i a => z ^ x.2.val * u (connectionSlot i a))
  else if x.1 = 1 then
    (fun i j => (z⁻¹) ^ x.2.val * v (frameSlot i j),
     fun i a => (z⁻¹) ^ x.2.val * v (connectionSlot i a))
  else 0

def characterQuadratic (z : K) (u v : Point K) : K :=
  let q := characterField z u v
  (∑ r, (bivPair (nativeLU spatialStep q 0 r) (internalStar (nativeK spatialStep q 0 r)) +
    bivPair (flatComplement r) (internalStar (rawPlaquetteContact spatialStep q q 0 r)))) +
  (1 / 101 : K) * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
    etaPair (nativeTheta spatialStep q 0 r) (nativeTheta spatialStep q 0 r))

def nativeMixed (z : K) (u v : Point K) : K :=
  characterQuadratic z u v - characterQuadratic z u 0 - characterQuadratic z 0 v

def mixedApply (z : K) (v : Point K) (i : Fin 40) : K :=
  match i.val with
  | 0 => ((2 / 101 : K) + (-2 / 101 : K) * z) * v 1
  | 1 => ((-2 / 101 : K)) * v 1 +
      ((1 / 2 : K)) * v 33 +
      ((-1 / 2 : K)) * v 38
  | 2 => ((-2 / 101 : K)) * v 2 +
      ((-1 / 4 : K) + (-1 / 4 : K) * z) * v 27 +
      ((1 / 2 : K)) * v 37
  | 3 => ((-2 / 101 : K)) * v 3 +
      ((1 / 4 : K) + (1 / 4 : K) * z) * v 26 +
      ((-1 / 2 : K)) * v 31
  | 4 => ((-2 / 101 : K) + (2 / 101 : K) * z) * v 5
  | 5 => ((2 / 101 : K)) * v 5 +
      ((-1 / 2 : K)) * v 29 +
      ((-1 / 2 : K)) * v 36
  | 6 => ((2 / 101 : K)) * v 6 +
      ((1 / 4 : K) + (1 / 4 : K) * z) * v 23
  | 7 => ((2 / 101 : K)) * v 7 +
      ((1 / 4 : K) + (1 / 4 : K) * z) * v 24
  | 8 => ((-2 / 101 : K) + (2 / 101 : K) * z) * v 9
  | 9 => ((2 / 101 : K)) * v 9 +
      ((1 / 2 : K)) * v 28
  | 10 => ((2 / 101 : K)) * v 10 +
      ((-1 / 4 : K) + (-1 / 4 : K) * z) * v 22 +
      ((-1 / 2 : K)) * v 36
  | 11 => ((2 / 101 : K)) * v 11 +
      ((1 / 2 : K)) * v 30
  | 12 => ((-2 / 101 : K) + (2 / 101 : K) * z) * v 13
  | 13 => ((2 / 101 : K)) * v 13 +
      ((1 / 2 : K)) * v 34
  | 14 => ((2 / 101 : K)) * v 14 +
      ((1 / 2 : K)) * v 35
  | 15 => ((2 / 101 : K)) * v 15 +
      ((-1 / 4 : K) + (-1 / 4 : K) * z) * v 22 +
      ((-1 / 2 : K)) * v 29
  | 16 => ((-2 / 101 : K)) * v 1 +
      ((-1 / 4 : K) * z⁻¹ + (1 / 4 : K) * z) * v 10 +
      ((-1 / 4 : K) * z⁻¹ + (1 / 4 : K) * z) * v 15 +
      ((1 / 2 : K)) * v 33 +
      ((-1 / 2 : K)) * v 38
  | 17 => ((-2 / 101 : K)) * v 2 +
      ((1 / 4 : K) * z⁻¹ + (-1 / 4 : K) * z) * v 6 +
      ((-1 / 4 : K) + (-1 / 4 : K) * z) * v 27 +
      ((1 / 2 : K)) * v 37
  | 18 => ((-2 / 101 : K)) * v 3 +
      ((1 / 4 : K) * z⁻¹ + (-1 / 4 : K) * z) * v 7 +
      ((1 / 4 : K) + (1 / 4 : K) * z) * v 26 +
      ((-1 / 2 : K)) * v 31
  | 19 => ((2 / 101 : K)) * v 11 +
      ((-2 / 101 : K)) * v 14 +
      ((1 / 2 : K)) * v 30 +
      ((-1 / 2 : K)) * v 35
  | 20 => ((1 / 4 : K) * z⁻¹ + (-1 / 4 : K) * z) * v 3 +
      ((-2 / 101 : K)) * v 7 +
      ((2 / 101 : K)) * v 13 +
      ((-1 / 4 : K) + (-1 / 4 : K) * z) * v 24 +
      ((1 / 2 : K)) * v 34
  | 21 => ((-1 / 4 : K) * z⁻¹ + (1 / 4 : K) * z) * v 2 +
      ((2 / 101 : K)) * v 6 +
      ((-2 / 101 : K)) * v 9 +
      ((1 / 4 : K) + (1 / 4 : K) * z) * v 23 +
      ((-1 / 2 : K)) * v 28
  | 22 => ((-2 / 101 : K)) * v 5 +
      ((1 / 4 : K) * z⁻¹ + (1 / 4 : K)) * v 10 +
      ((1 / 4 : K) * z⁻¹ + (1 / 4 : K)) * v 15
  | 23 => ((-1 / 4 : K) * z⁻¹ + (-1 / 4 : K)) * v 6 +
      ((-2 / 101 : K)) * v 9
  | 24 => ((-1 / 4 : K) * z⁻¹ + (-1 / 4 : K)) * v 7 +
      ((-2 / 101 : K)) * v 13
  | 26 => ((-1 / 4 : K) * z⁻¹ + (-1 / 4 : K)) * v 3
  | 27 => ((1 / 4 : K) * z⁻¹ + (1 / 4 : K)) * v 2
  | 28 => ((-2 / 101 : K)) * v 6 +
      ((-1 / 2 : K)) * v 9
  | 29 => ((1 / 2 : K)) * v 5 +
      ((-2 / 101 : K)) * v 10 +
      ((1 / 2 : K)) * v 15
  | 30 => ((-1 / 2 : K)) * v 11 +
      ((-2 / 101 : K)) * v 14
  | 31 => ((1 / 2 : K)) * v 3
  | 33 => ((-1 / 2 : K)) * v 1
  | 34 => ((-2 / 101 : K)) * v 7 +
      ((-1 / 2 : K)) * v 13
  | 35 => ((-2 / 101 : K)) * v 11 +
      ((-1 / 2 : K)) * v 14
  | 36 => ((1 / 2 : K)) * v 5 +
      ((1 / 2 : K)) * v 10 +
      ((-2 / 101 : K)) * v 15
  | 37 => ((-1 / 2 : K)) * v 2
  | 38 => ((1 / 2 : K)) * v 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Expand the literal mixed density, retaining both reciprocal spatial characters.
lemma native_mixed_formula (z : K) (hz : z ≠ 0) (u v : Point K) :
    nativeMixed z u v = dotProduct u (mixedApply z v) := by
  norm_num [nativeMixed, characterQuadratic, characterField, spatialStep,
    nativeLU, linearComplement, connectionComplement, nativeV, flatComplement,
    nativeK, linearCurvature, rawPlaquetteContact, nativeLetters, nativeTheta,
    torsion, fieldPoint, frameSlot, connectionSlot, firstWedge, wedge,
    basisVector, complementFirst, complementSecond, complementSign,
    faceFirst, faceSecond, lie, bivBracket, cross3, boostPart, spatialPart,
    internalStar, bivPair, bivSign, etaPair, eta, Fin.sum_univ_succ,
    dotProduct, mixedApply]
  field_simp [hz]
  ring

def witnessWeight (z : K) (i : Fin 40) : K :=
  let T := 10201 + 10589 * z
  if i = 5 then T else if i = 10 ∨ i = 15 then -T else
  if i = 22 then 1196 * z else if i = 29 ∨ i = 36 then
    -(2 / 101) * (10201 + 9393 * z) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- A complete row identity isolates one boost coordinate without a guessed nullspace.
lemma left_witness (z : K) (hz : z ≠ 0) (v : Point K) :
    dotProduct (witnessWeight z) (mixedApply z v) =
      ((10201 + 10589 * z) * (1 + z) / 2) * v 22 := by
  norm_num [dotProduct, witnessWeight, mixedApply, Fin.sum_univ_succ]
  field_simp [hz]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Evaluate the complete source-bound column at all40 output rows.
lemma column22 (z : K) : mixedApply z (fun i => if i = 22 then 1 else 0) =
    fun i => if i = 10 ∨ i = 15 then -(1 + z) / 4 else 0 := by
  funext i
  fin_cases i <;> norm_num [mixedApply]
  all_goals ring

end Artform.Scores.NonabelianGravity.BoundarySymbol
