import ArtformScores.NonabelianGravity.LegendrePolynomial

/-! # Actual full-coordinate cut action and its affine background boundary term

This is the quadratic Taylor model, in the spatial-zero character, of the
original physically unselected native action. No nonlinear history or physical
mode selection is inferred. Every native complement/contact/torsion term remains.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]

abbrev Point (K : Type*) := Fin 40 → K
abbrev Time := Fin 3

def step : Fin 4 → Time := ![1, 0, 0, 0]

def frameSlot (i j : Fin 4) : Fin 40 := ⟨4 * i.val + j.val, by omega⟩
def connectionSlot (i : Fin 4) (a : Fin 6) : Fin 40 :=
  ⟨16 + 6 * i.val + a.val, by omega⟩
def slot : Coordinate → Fin 40 := Sum.elim (fun ij => frameSlot ij.1 ij.2)
  (fun ia => connectionSlot ia.1 ia.2)

lemma slot_bijective : Function.Bijective slot := by decide +kernel

def fieldPoint (u : Point K) : Full K :=
  (fun i j => u (frameSlot i j), fun i a => u (connectionSlot i a))

def twoTime (u v : Point K) (x : Time) : Full K :=
  if x = 0 then fieldPoint u else if x = 1 then fieldPoint v else 0

/-- The literal complete native bilinear density, before assembling in time. -/
def cellBilinear (q p : NativeField Time K) : K :=
  (∑ r, (bivPair (nativeLU step q 0 r) (internalStar (nativeK step p 0 r)) +
    bivPair (flatComplement r) (internalStar (rawPlaquetteContact step q p 0 r)))) +
    (1 / 101 : K) * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
      etaPair (nativeTheta step q 0 r) (nativeTheta step p 0 r))

def cellQuadratic (u v : Point K) : K := cellBilinear (twoTime u v) (twoTime u v)

def linearCell (u v : Point K) : K :=
  ∑ r, bivPair (flatComplement r) (internalStar (nativeK step (twoTime u v) 0 r))

def cutAction (u v : Point K) : K := linearCell u v + cellQuadratic u v

def join (u v : Point K) (n : Fin 80) : K :=
  if h : n.val < 40 then u ⟨n.val, h⟩ else v ⟨n.val - 40, by omega⟩

def evaluate (data : List ((Fin 80 × Fin 80) × ℤ)) (w : Fin 80 → K) : K :=
  data.foldr (fun t acc => (t.2 : K) * w t.1.1 * w t.1.2 + acc) 0

def polynomial (u v : Point K) : K := evaluate terms (join u v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Expand all six faces with arbitrary independent old/new40 coordinates.
lemma source_polynomial (u v : Point K) :
    (202 : K) * cellQuadratic u v = polynomial u v := by
  norm_num [cellQuadratic, cellBilinear, nativeLU,
    linearComplement, connectionComplement, nativeV, flatComplement,
    nativeK, linearCurvature, rawPlaquetteContact, nativeLetters, nativeTheta,
    torsion, twoTime, fieldPoint, frameSlot, connectionSlot, step, firstWedge, wedge,
    basisVector, complementFirst, complementSecond, complementSign,
    faceFirst, faceSecond, lie, bivBracket, cross3, boostPart, spatialPart,
    internalStar, bivPair, bivSign, etaPair, eta, Fin.sum_univ_succ,
    polynomial, evaluate, terms, join]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Retain the linear curvature divergence that contributes affine endpoint momenta.
omit [CharZero K] in
lemma linear_cell_formula (u v : Point K) :
    linearCell u v = u 22 + u 29 + u 36 - (v 22 + v 29 + v 36) := by
  norm_num [linearCell, nativeK, linearCurvature, flatComplement,
    twoTime, fieldPoint, frameSlot, connectionSlot, step, wedge, basisVector,
    complementFirst, complementSecond, complementSign, faceFirst, faceSecond,
    internalStar, bivPair, bivSign, Fin.sum_univ_succ]
  ring

end Artform.Scores.NonabelianGravity.Legendre
