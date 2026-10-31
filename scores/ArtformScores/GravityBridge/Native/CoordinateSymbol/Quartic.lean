import ArtformScores.GravityBridge.Native.CoordinateSymbol.Inverse
/-! # Supporting original coordinate algebra -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol
open Matrix
variable {K : Type*} [Field K] [CharZero K]

def faceDot (F G : Mat4 (K := K)) : K :=
  (∑ i, ∑ j, signature i * signature j * F i j * G i j) / 2

def faceCross (F G : Mat4 (K := K)) : Mat4 (K := K) :=
  fun a b => ∑ l, signature l * F a l * G b l

def schurFacePair (F G : Mat4 (K := K)) : Mat4 (K := K) :=
  (2 / 101 : K) • ((((9999 / 9991 : K) * faceDot F G) • etaMatrix) +
    ((10201 / 10300 - 9999 / 9991 : K) • faceCross F G))

def timeMomentum (j z : K) (k : Fin 3 → K) : Vec4 (K := K) :=
  ![-j * z, k 0, k 1, k 2]

def faceConstant (k : Fin 3 → K) : Mat4 (K := K) :=
  simpleFace (componentSquares (![0, k 0, k 1, k 2] : Vec4 (K := K))) ![0, k 0, k 1, k 2]

def faceLinear (j : K) (k : Fin 3 → K) : Mat4 (K := K) :=
  !![0, j * k 0 ^ 2 / 2, j * k 1 ^ 2 / 2, j * k 2 ^ 2 / 2;
     -j * k 0 ^ 2 / 2, 0, 0, 0;-j * k 1 ^ 2 / 2, 0, 0, 0;-j * k 2 ^ 2 / 2, 0, 0, 0]

def faceQuadratic (k : Fin 3 → K) : Mat4 (K := K) :=
  !![0, -k 0 / 2, -k 1 / 2, -k 2 / 2;k 0 / 2, 0, 0, 0;k 1 / 2, 0, 0, 0;k 2 / 2, 0, 0, 0]

def nativeUpperCoefficients (j : K) (k : Fin 3 → K) : Fin 5 → Mat4 (K := K) :=
  let A := faceConstant k
  let B := faceLinear j k
  let C := faceQuadratic k
  ![schurFacePair A A, schurFacePair A B + schurFacePair B A,
    schurFacePair A C + schurFacePair B B + schurFacePair C A,
    schurFacePair B C + schurFacePair C B, schurFacePair C C]

def matrixPolynomial (g : Fin 5 → Mat4 (K := K)) (z : K) : Mat4 (K := K) :=
  g 0 + z • g 1 + z ^ 2 • g 2 + z ^ 3 • g 3 + z ^ 4 • g 4

lemma original_gram_face_identity (u p : Vec4 (K := K)) :
    simpleDiscriminant u p = faceDot (simpleFace u p) (simpleFace u p) := by
  norm_num [simpleDiscriminant, faceDot, simpleFace, lorentzDot, signature, Fin.sum_univ_succ]
  ring

lemma native_symbol_schur_pair (p : Vec4 (K := K)) :
    nativeUpperSymbol p = schurFacePair (simpleFace (componentSquares p) p)
      (simpleFace (componentSquares p) p) := by
  rw [nativeUpperSymbol, schurFacePair, ← original_gram_face_identity]
  rfl

lemma temporal_face_coefficients (j z : K) (k : Fin 3 → K) (hj : j ^ 2 = -1) :
    simpleFace (componentSquares (timeMomentum j z k)) (timeMomentum j z k) =
      faceConstant k + z • faceLinear j k + z ^ 2 • faceQuadratic k := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [simpleFace, componentSquares, timeMomentum, faceConstant, faceLinear,
      faceQuadratic] <;>
    ring_nf <;> simp only [hj] <;> ring

lemma schur_pair_add_left (F G H : Mat4 (K := K)) :
    schurFacePair (F + G) H = schurFacePair F H + schurFacePair G H := by
  ext a b
  simp [schurFacePair, faceDot, faceCross, add_mul, mul_add, Finset.sum_add_distrib]
  ring

lemma schur_pair_add_right (F G H : Mat4 (K := K)) :
    schurFacePair F (G + H) = schurFacePair F G + schurFacePair F H := by
  ext a b
  simp [schurFacePair, faceDot, faceCross, mul_add, Finset.sum_add_distrib]
  ring

lemma schur_pair_smul_left (F G : Mat4 (K := K)) (a : K) :
    schurFacePair (a • F) G = a • schurFacePair F G := by
  ext i j
  simp [schurFacePair, faceDot, faceCross, Fin.sum_univ_succ]
  ring

lemma schur_pair_smul_right (F G : Mat4 (K := K)) (a : K) :
    schurFacePair F (a • G) = a • schurFacePair F G := by
  ext i j
  simp [schurFacePair, faceDot, faceCross, Fin.sum_univ_succ]
  ring

lemma complete_native_quartic (j z : K) (k : Fin 3 → K) (hj : j ^ 2 = -1) :
    nativeUpperSymbol (timeMomentum j z k) = matrixPolynomial (nativeUpperCoefficients j k) z := by
  rw [native_symbol_schur_pair]
  simp only [temporal_face_coefficients j z k hj]
  change _ = schurFacePair (faceConstant k) (faceConstant k) +
    z • (schurFacePair (faceConstant k) (faceLinear j k) +
      schurFacePair (faceLinear j k) (faceConstant k)) +
    z ^ 2 • (schurFacePair (faceConstant k) (faceQuadratic k) +
      schurFacePair (faceLinear j k) (faceLinear j k) +
      schurFacePair (faceQuadratic k) (faceConstant k)) +
    z ^ 3 • (schurFacePair (faceLinear j k) (faceQuadratic k) +
      schurFacePair (faceQuadratic k) (faceLinear j k)) +
    z ^ 4 • schurFacePair (faceQuadratic k) (faceQuadratic k)
  simp only [schur_pair_add_left, schur_pair_add_right, schur_pair_smul_left,
    schur_pair_smul_right, smul_add, smul_smul]
  module

/-! ## Non-vacuity -/

example : nativeUpperSymbol (timeMomentum Complex.I (2 : ℂ) ![1, 2, 3]) =
    matrixPolynomial (nativeUpperCoefficients Complex.I ![1, 2, 3]) 2 := by
  exact complete_native_quartic Complex.I 2 ![1, 2, 3] Complex.I_sq

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
