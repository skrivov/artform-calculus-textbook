import ArtformScores.NonabelianGravity.NativeRotation

/-! # Zero-extension and all incident density cells for the native test -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NativeRotation
open Artform.Scores.GravityBridge.Native.Full40

def pulse {X : Type} [Zero X] [DecidableEq X] (u : Full ℚ) (x : X) : Full ℚ :=
  if x = 0 then u else 0

def integerStep : Fin 4 → ℤ := ![1, 0, 0, 0]

/-- The literal summand of the existing complete native bilinear action. -/
def density {X : Type} [AddCommGroup X] (d : Fin 4 → X)
    (q p : NativeField X ℚ) (x : X) : ℚ :=
  (∑ r, (bivPair (nativeLU d q x r) (internalStar (nativeK d p x r)) +
    bivPair (flatComplement r) (internalStar (rawPlaquetteContact d q p x r)))) +
    (1 / 101 : ℚ) * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
      etaPair (nativeTheta d q x r) (nativeTheta d p x r))

lemma density_source {X : Type} [AddCommGroup X] [Fintype X]
    (d : Fin 4 → X) (q p : NativeField X ℚ) :
    nativeBilinear d (1 / 101) q p = ∑ x, density d q p x := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expand every face of the complete density, including the fixed outgoing halo.
lemma halo_density (u v : Full ℚ) :
    density step (pulse u) (pulse v) (1 : Time) = 0 := by
  norm_num [density, nativeLU, linearComplement, connectionComplement, nativeV,
    flatComplement, nativeK, linearCurvature, rawPlaquetteContact, nativeLetters,
    nativeTheta, torsion, pulse, step, firstWedge, wedge, basisVector,
    complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
    lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
    bivSign, etaPair, eta, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check the full original stencil for arbitrary owned coframe and connection values.
lemma integer_density_zero (u v : Full ℚ) (x : ℤ) (h0 : x ≠ 0) (hm : x ≠ -1) :
    density integerStep (pulse u) (pulse v) x = 0 := by
  have h1 : x + 1 ≠ 0 := by omega
  norm_num [density, nativeLU, linearComplement, connectionComplement, nativeV,
    flatComplement, nativeK, linearCurvature, rawPlaquetteContact, nativeLetters,
    nativeTheta, torsion, pulse, integerStep, firstWedge, wedge, basisVector,
    complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
    lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
    bivSign, etaPair, eta, Fin.sum_univ_succ, h0, h1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Compare every complete density term at both incident integer/cycle cells.
lemma density_binding (u v : Full ℚ) :
    density step (pulse u) (pulse v) (0 : Time) =
      density integerStep (pulse u) (pulse v) 0 ∧
    density step (pulse u) (pulse v) (2 : Time) =
      density integerStep (pulse u) (pulse v) (-1) := by
  constructor <;>
    norm_num [density, nativeLU, linearComplement, connectionComplement, nativeV,
      flatComplement, nativeK, linearCurvature, rawPlaquetteContact, nativeLetters,
      nativeTheta, torsion, pulse, step, integerStep, firstWedge, wedge, basisVector,
      complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
      lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
      bivSign, etaPair, eta, Fin.sum_univ_succ]

def ownedBilinear (u v : Full ℚ) : ℚ :=
  density integerStep (pulse u) (pulse v) (-1) +
    density integerStep (pulse u) (pulse v) 0

lemma owned_action_binding (u v : Full ℚ) :
    nativeBilinear step (1 / 101) (pulse u) (pulse v) = ownedBilinear u v := by
  rw [density_source]
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [halo_density, (density_binding u v).1, (density_binding u v).2]
  simp [ownedBilinear, add_comm]

lemma basis_pulse (j : Fin 3) : basis j = pulse (basis j 0) := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [pulse]
  · apply Prod.ext <;> ext i a <;> simp [basis, pulse, hx]

lemma test_pulse (c : Coordinate) : test c = pulse (unpack (Pi.single c 1)) := rfl

lemma trial_pulse (v : Fin 3 → ℚ) : trial v = pulse (trial v 0) := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [pulse]
  · apply Prod.ext <;> ext i a <;> simp [trial, basis, pulse, hx]

lemma owned_row_binding (v : Fin 3 → ℚ) (c : Coordinate) :
    ownedBilinear (trial v 0) (unpack (Pi.single c 1)) +
      ownedBilinear (unpack (Pi.single c 1)) (trial v 0) = forceTable v c := by
  rw [← owned_action_binding, ← owned_action_binding, ← trial_pulse, ← test_pulse]
  change nativeFirstVariation step (1 / 101) (trial v) (test c) = _
  rw [← force_test]
  exact actual_rows v c

end Artform.Scores.NonabelianGravity.NativeRotation
