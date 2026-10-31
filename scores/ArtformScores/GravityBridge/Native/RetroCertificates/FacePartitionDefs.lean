import ArtformScores.GravityBridge.Native.RetroCertificates.Slots

/-! # All original constitutive face slots in eight signed blocks -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

abbrev NativeFace (K : Type*) := Matrix (Fin 6) (Fin 4) K

def faceIndex : Fin 8 → Fin 3 → Fin 6 × Fin 4 := ![
  ![(0, 0), (3, 2), (4, 3)], ![(0, 1), (1, 2), (2, 3)], ![(0, 2), (1, 1), (3, 0)],
  ![(0, 3), (2, 1), (4, 0)], ![(1, 0), (3, 1), (5, 3)], ![(1, 3), (2, 2), (5, 0)],
  ![(2, 0), (4, 1), (5, 2)], ![(3, 3), (4, 2), (5, 1)]]

def faceWire (s : Fin 8) : Fin 3 → K :=
  ![![1, -1, -1], ![1, 1, 1], ![1, -1, -1], ![1, -1, -1], ![1, 1, -1], ![1, -1, -1], ![1, 1, 1],
    ![1, -1, 1]] s

def faceRead (Z : NativeFace K) (s : Fin 8) (i : Fin 3) : K :=
  faceWire s i * Z (faceIndex s i).1 (faceIndex s i).2

def faceAssemble (v : Fin 8 → Fin 3 → K) : NativeFace K := fun r a =>
  ∑ s, ∑ i, if faceIndex s i = (r, a) then faceWire s i * v s i else 0

def faceAlpha (s : Fin 8) : K :=
  ![103 / 101, -103 / 101, -103 / 101, -103 / 101, 103 / 101, -103 / 101, 103 / 101, 103 / 101] s

def faceBeta (s : Fin 8) : K :=
  ![-1 / 101, 1 / 101, 2 / 101, 2 / 101, -1 / 101, 2 / 101, -1 / 101, -2 / 101] s

def faceInverseBlock (s : Fin 8) : Three (K := K) := fun i j =>
  (if i = j then faceAlpha s else 0) + faceBeta s

def faceForwardBlock (s : Fin 8) : Three (K := K) := fun i j =>
  (if i = j then (faceAlpha s)⁻¹ else 0)-
    faceBeta s / (faceAlpha s * (faceAlpha s + 3 * faceBeta s))

end Artform.Scores.GravityBridge.Native.RetroCertificates
