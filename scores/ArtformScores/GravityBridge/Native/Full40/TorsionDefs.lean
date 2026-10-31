import ArtformScores.GravityBridge.Native.Full40.Coordinates
import ArtformScores.GravityBridge.Native.Full40.Shifts

/-! # The full flat torsion map and Lorentz columns -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]

def torsion (d : Fin 4 → X) (f : X → Frame K) (A : X → Connection K)
    (x : X) (i j a : Fin 4) : K :=
  f (x + d i) a j - f x a j - (f (x + d j) a i - f x a i) -
    lie (A x i) a j + lie (A x j) a i

def gaugeFrame (w : X → Biv K) : X → Frame K := fun x => lie (w x)

def gaugeConnection (d : Fin 4 → X) (w : X → Biv K) : X → Connection K :=
  fun x i => w (x + d i) - w x

def linearCurvature (d : Fin 4 → X) (A : X → Connection K)
    (x : X) (i j : Fin 4) : Biv K :=
  A (x + d j) i - A x i - (A (x + d i) j - A x j)

def faceFirst (r : Fin 6) : Fin 4 := ![0, 0, 0, 1, 1, 2] r

def faceSecond (r : Fin 6) : Fin 4 := ![1, 2, 3, 2, 3, 3] r

def torsionDensity (kappa : K) (theta : Fin 4 → Fin 4 → Vec K) : K :=
  kappa * ∑ r, eta (faceFirst r) * eta (faceSecond r) *
    etaPair (theta (faceFirst r) (faceSecond r)) (theta (faceFirst r) (faceSecond r))

def torsionMixed (kappa : K) (theta test : Fin 4 → Fin 4 → Vec K) : K :=
  2 * kappa * ∑ r, eta (faceFirst r) * eta (faceSecond r) *
    etaPair (theta (faceFirst r) (faceSecond r)) (test (faceFirst r) (faceSecond r))

end Artform.Scores.GravityBridge.Native.Full40
