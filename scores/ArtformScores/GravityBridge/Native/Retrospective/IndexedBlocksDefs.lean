import ArtformScores.GravityBridge.Native.Full40.Quadratic
import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverse

/-! # Indexed original distinct and repeated connection restrictions -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Full40



def distinctIndices (s : Fin 4) : Fin 3 → Fin 4 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3]] s

def distinctInput (s : Fin 4) (z : Fin 3 → ℚ) : Connection ℚ := fun i =>
  ∑ j : Fin 3, if i = distinctIndices s j then z j •
    wedge (basisVector (distinctIndices s (j + 1)))
      (basisVector (distinctIndices s (j + 2))) else 0

def repeatedInput (b : Fin 4) (z : Fin 3 → ℚ) : Connection ℚ := fun i =>
  ∑ j : Fin 3, if i = b.succAbove j then z j •
    wedge (basisVector (b.succAbove j)) (basisVector b) else 0

def connectionDensity (t : ℚ) (A : Connection ℚ) : ℚ :=
  completeQuadratic (fun _ : Fin 4 => Unit.unit) t (fun _ : Unit => (0, A))

def distinctDensity (s : Fin 4) (t : ℚ) (z : Fin 3 → ℚ) : ℚ :=
  let a := distinctIndices s 0
  let b := distinctIndices s 1
  let c := distinctIndices s 2
  2 * t * eta a * eta b * eta c * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) -
    (1 - 2 * t) * (eta c * z 0 * z 1 + eta b * z 0 * z 2 + eta a * z 1 * z 2)

def repeatedDensity (b : Fin 4) (t : ℚ) (z : Fin 3 → ℚ) : ℚ :=
  eta b * (t * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) -
    (z 0 * z 1 + z 0 * z 2 + z 1 * z 2))

def repeatedBlock (b : Fin 4) (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => eta b * (if i = j then 2 * t else -1)

end Artform.Scores.GravityBridge.Native.Retrospective
