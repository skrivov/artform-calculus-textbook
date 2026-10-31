import ArtformScores.GravityBridge.Native.Full40.Torsion
import ArtformScores.GravityBridge.Native.Full40.Plaquette

/-! # Complete original flat quadratic variation on periodic fields -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]

def cross3 (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def boostPart (a : Biv K) : Fin 3 → K := ![a 0, a 1, a 2]

def spatialPart (a : Biv K) : Fin 3 → K := ![a 3, a 4, a 5]

def bivBracket (a b : Biv K) : Biv K :=
  let u := -(cross3 (spatialPart a) (boostPart b)) - cross3 (boostPart a) (spatialPart b)
  let v := cross3 (boostPart a) (boostPart b) - cross3 (spatialPart a) (spatialPart b)
  ![u 0, u 1, u 2, v 0, v 1, v 2]

abbrev NativeField (X K : Type*) := X → Full K

def wedge (u v : Vec K) : Biv K :=
  ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0,
    u 0 * v 3 - u 3 * v 0, u 2 * v 3 - u 3 * v 2,
    u 3 * v 1 - u 1 * v 3, u 1 * v 2 - u 2 * v 1]

def basisVector (i : Fin 4) : Vec K := fun a => if a = i then 1 else 0

def complementFirst (r : Fin 6) : Fin 4 := ![2, 1, 1, 0, 0, 0] r

def complementSecond (r : Fin 6) : Fin 4 := ![3, 3, 2, 3, 2, 1] r

def complementSign (r : Fin 6) : K := ![1, -1, 1, 1, -1, 1] r

def flatComplement (r : Fin 6) : Biv K := complementSign (K := K) r •
  wedge (basisVector (complementFirst r)) (basisVector (complementSecond r))

def firstWedge (F : Frame K) (i j : Fin 4) : Biv K :=
  wedge (fun a => F a i) (basisVector j) + wedge (basisVector i) (fun a => F a j)

def linearComplement (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) : Biv K :=
  let i := complementFirst r
  let j := complementSecond r
  let k := faceFirst r
  let l := faceSecond r
  (complementSign (K := K) r / 4) •
    (firstWedge (q x).1 i j + firstWedge (q (x + d k)).1 i j +
      firstWedge (q (x + d l)).1 i j + firstWedge (q (x + d k + d l)).1 i j)

def nativeV (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) : Biv K :=
  let k := faceFirst r
  let l := faceSecond r
  (1 / 8 : K) • ((3 : K) • (q x).2 k + (q (x + d l)).2 k +
    (3 : K) • (q x).2 l + (q (x + d k)).2 l)

def connectionComplement (d : Fin 4 → X) (q : NativeField X K) (x : X)
    (r : Fin 6) : Biv K := -bivBracket (nativeV d q x r) (flatComplement r)

def nativeLU (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) : Biv K :=
  linearComplement d q x r + connectionComplement d q x r

def nativeK (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) : Biv K :=
  linearCurvature d (fun v => (q v).2) x (faceFirst r) (faceSecond r)

def nativeTheta (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) : Vec K :=
  torsion d (fun v => (q v).1) (fun v => (q v).2) x (faceFirst r) (faceSecond r)

def nativeLetters (d : Fin 4 → X) (q : NativeField X K) (x : X)
    (r : Fin 6) : Fin 4 → Biv K :=
  let k := faceFirst r
  let l := faceSecond r
  ![-(q x).2 l, -(q (x + d l)).2 k, (q (x + d k)).2 l, (q x).2 k]

def rawPlaquetteContact (d : Fin 4 → X) (q p : NativeField X K) (x : X)
    (r : Fin 6) : Biv K :=
  let a := nativeLetters d q x r
  let b := nativeLetters d p x r
  (-1 / 2 : K) • (bivBracket (a 0) (b 1) + bivBracket (a 0) (b 2) +
    bivBracket (a 0) (b 3) + bivBracket (a 1) (b 2) +
    bivBracket (a 1) (b 3) + bivBracket (a 2) (b 3))

def nativeBilinear [Fintype X] (d : Fin 4 → X) (kappa : K) (q p : NativeField X K) : K :=
  ∑ x, ((∑ r, (bivPair (nativeLU d q x r)
    (internalStar (nativeK d p x r)) +
    bivPair (flatComplement r) (internalStar (rawPlaquetteContact d q p x r)))) +
    kappa * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
      etaPair (nativeTheta d q x r) (nativeTheta d p x r)))

def completeQuadratic [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K) : K :=
  nativeBilinear d kappa q q

def nativeFirstVariation [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K) : K := nativeBilinear d kappa q p + nativeBilinear d kappa p q

end Artform.Scores.GravityBridge.Native.Full40
