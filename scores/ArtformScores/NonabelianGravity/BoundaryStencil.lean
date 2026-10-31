import ArtformScores.NonabelianGravity.LegendreSource

/-! # Four-corner source binding for the full native density -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundarySymbol
open Artform.Scores.GravityBridge.Native.Full40
variable {X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]

def twoShift (a b : X) : Fin 4 → X := ![a, b, 0, 0]

def nativeCutDensity (d : Fin 4 → X) (q : NativeField X K) : K :=
  (∑ r, (bivPair (nativeLU d q 0 r) (internalStar (nativeK d q 0 r)) +
    bivPair (flatComplement r) (internalStar (rawPlaquetteContact d q q 0 r)))) +
  (1 / 101 : K) * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
    etaPair (nativeTheta d q 0 r) (nativeTheta d q 0 r))

omit [CharZero K] in
lemma four_corner_density (a b : X) (c d : Y) (q : NativeField X K) (p : NativeField Y K)
    (h0 : q 0 = p 0) (ha : q a = p c) (hb : q b = p d) (hab : q (a + b) = p (c + d)) :
    nativeCutDensity (twoShift a b) q = nativeCutDensity (twoShift c d) p := by
  have hlu (r : Fin 6) : nativeLU (twoShift a b) q 0 r = nativeLU (twoShift c d) p 0 r := by
    fin_cases r <;> simp_all [nativeLU, linearComplement, connectionComplement,
      nativeV, twoShift, faceFirst, faceSecond]
  have hk (r : Fin 6) : nativeK (twoShift a b) q 0 r = nativeK (twoShift c d) p 0 r := by
    fin_cases r <;> simp_all [nativeK, linearCurvature, twoShift, faceFirst, faceSecond]
  have ht (r : Fin 6) : nativeTheta (twoShift a b) q 0 r = nativeTheta (twoShift c d) p 0 r := by
    funext i
    fin_cases r <;> simp_all [nativeTheta, torsion, twoShift, faceFirst, faceSecond]
  have hl (r : Fin 6) :
      nativeLetters (twoShift a b) q 0 r = nativeLetters (twoShift c d) p 0 r := by
    fin_cases r <;> simp_all [nativeLetters, twoShift, faceFirst, faceSecond]
  simp only [nativeCutDensity, hlu, hk, ht, rawPlaquetteContact, hl]

end Artform.Scores.NonabelianGravity.BoundarySymbol
