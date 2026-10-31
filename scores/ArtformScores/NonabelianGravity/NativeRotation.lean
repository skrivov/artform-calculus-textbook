import ArtformScores.GravityBridge.Native.Full40.PhysicalSign

/-! # A conditional fixed-coframe rotational import test

This is the zero spatial character of the complete flat quadratic candidate.
It is not a field map from the curved dipole or an infinitesimal score law.
The three-cycle stores one owned time site and two fixed zero halo sites.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NativeRotation
open Artform.Scores.GravityBridge.Native.Full40

abbrev Time := Fin 3

def step : Fin 4 → Time := ![1, 0, 0, 0]

def basis (j : Fin 3) (x : Time) : Full ℚ :=
  (0, fun i a => if x = 0 ∧ i.val = j.val + 1 ∧ a.val = j.val + 3 then 1 else 0)

def test (c : Coordinate) (x : Time) : Full ℚ :=
  if x = 0 then unpack (Pi.single c 1) else 0

def coefficient (j : Fin 3) (c : Coordinate) : ℚ :=
  match c with
  | Sum.inl _ => 0
  | Sum.inr (i, a) =>
    if (i, a) = (1, 3) ∨ (i, a) = (2, 4) ∨ (i, a) = (3, 5) then
      if i.val = j.val + 1 then 4 / 101 else -99 / 101
    else 0

def probe (u : Full ℚ) (x : Time) : Full ℚ := if x = 0 then u else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Normalize the complete finite action against an arbitrary forty-component test.
lemma complete_pairing (j : Fin 3) (u : Full ℚ) :
    nativeFirstVariation step (1 / 101) (basis j) (probe u) =
      coefficient j (Sum.inr (1, 3)) * u.2 1 3 +
      coefficient j (Sum.inr (2, 4)) * u.2 2 4 +
      coefficient j (Sum.inr (3, 5)) * u.2 3 5 := by
  fin_cases j <;>
    norm_num [nativeFirstVariation, nativeBilinear, nativeLU,
      linearComplement, connectionComplement, nativeV, flatComplement,
      nativeK, linearCurvature, rawPlaquetteContact, nativeLetters, nativeTheta,
      torsion, basis, probe, step, firstWedge, wedge, basisVector,
      complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
      lie, bivBracket, cross3, boostPart, spatialPart, internalStar, bivPair,
      bivSign, etaPair, eta, Fin.sum_univ_succ, coefficient] <;> ring

lemma complete_columns : ∀ (j : Fin 3) (c : Coordinate),
    nativeFirstVariation step (1 / 101) (basis j) (test c) = coefficient j c := by
  intro j c
  change nativeFirstVariation step (1 / 101) (basis j)
    (probe (unpack (Pi.single c 1))) = _
  rw [complete_pairing]
  fin_cases j <;> rcases c with ⟨i, a⟩ | ⟨i, a⟩ <;>
    fin_cases i <;> fin_cases a <;>
    norm_num [coefficient, unpack, Pi.single_apply]

lemma test_unit (c : Coordinate) : test c = fieldCoordinates.symm
    (Pi.single (0, c) (1 : ℚ)) := by
  classical
  funext x
  apply Prod.ext
  · ext i a
    simp [test, fieldCoordinates, unpack, Pi.single_apply]
    split_ifs <;> simp_all
  · ext i a
    simp [test, fieldCoordinates, unpack, Pi.single_apply]
    split_ifs <;> simp_all

lemma force_test (q : NativeField Time ℚ) (c : Coordinate) :
    fullForce step (1 / 101) q (0, c) =
      nativeFirstVariation step (1 / 101) q (test c) := by
  change nativeFirstVariation _ _ _ _ = _
  congr 1
  convert (test_unit c).symm using 1
  congr 1
  funext a
  simp [Pi.single_apply]

lemma actual_columns (j : Fin 3) (c : Coordinate) :
    fullForce step (1 / 101) (basis j) (0, c) = coefficient j c := by
  rw [force_test]
  exact complete_columns j c

def trial (v : Fin 3 → ℚ) : NativeField Time ℚ :=
  v 0 • basis 0 + v 1 • basis 1 + v 2 • basis 2

def residual (v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![(4 * v 0 - 99 * v 1 - 99 * v 2) / 101,
    (-99 * v 0 + 4 * v 1 - 99 * v 2) / 101,
    (-99 * v 0 - 99 * v 1 + 4 * v 2) / 101]

def forceTable (v : Fin 3 → ℚ) : Coordinate → ℚ :=
  Sum.elim (fun _ => 0) (fun ia =>
    if ia = (1, 3) then residual v 0 else
    if ia = (2, 4) then residual v 1 else
    if ia = (3, 5) then residual v 2 else 0)

lemma actual_rows (v : Fin 3 → ℚ) (c : Coordinate) :
    fullForce step (1 / 101) (trial v) (0, c) = forceTable v c := by
  have hc (j : Fin 3) : firstVariationMap step (1 / 101) (test c) (basis j) =
      coefficient j c := by
    change nativeFirstVariation _ _ _ _ = _
    rw [first_variation_symmetric]
    exact complete_columns j c
  rw [force_test, first_variation_symmetric]
  change firstVariationMap step (1 / 101) (test c) (trial v) = _
  simp only [trial, map_add, map_smul, smul_eq_mul, hc]
  rcases c with ⟨i, a⟩ | ⟨i, a⟩
  · simp [coefficient, forceTable]
  · fin_cases i <;> fin_cases a <;>
      norm_num [coefficient, forceTable, residual] <;> ring

lemma residual_zero_iff (v : Fin 3 → ℚ) : residual v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [residual] at h0 h1 h2
    funext i
    fin_cases i <;> norm_num <;> linarith
  · rintro rfl
    ext i
    fin_cases i <;> norm_num [residual]

lemma owned_force_zero_iff (v : Fin 3 → ℚ) :
    (∀ c, fullForce step (1 / 101) (trial v) (0, c) = 0) ↔ v = 0 := by
  simp only [actual_rows]
  constructor
  · intro h
    apply (residual_zero_iff v).mp
    have h0 := h (Sum.inr (1, 3))
    have h1 := h (Sum.inr (2, 4))
    have h2 := h (Sum.inr (3, 5))
    norm_num [forceTable] at h0 h1 h2
    ext i
    fin_cases i <;> assumption
  · rintro rfl c
    rcases c with ij | ia
    · rfl
    · simp [forceTable, residual]

lemma trace_residual : residual ![1, 1, 1] = fun _ => -194 / 101 := by
  ext i
  fin_cases i <;> norm_num [residual]

lemma traceless_residual (v : Fin 3 → ℚ) (h : v 0 + v 1 + v 2 = 0) :
    residual v = (103 / 101 : ℚ) • v := by
  ext i
  fin_cases i <;> norm_num [residual] <;> linarith

end Artform.Scores.NonabelianGravity.NativeRotation
