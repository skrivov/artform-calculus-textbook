import ArtformScores.GravityBridge.Native.RetroCertificates.FacePartition
import ArtformScores.GravityBridge.Native.TTCross.Source

/-! # Original full face inverse and exact curvature Woodbury return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

def curvatureD (s : Fin 4) : Three (K := K) :=
  let C : Three (K := K) := !![0, -1, -1;-1, 0, 1;-1, 1, 0]
  if s = 3 then -(signS * C * signS) else C

def curvatureR (b : Fin 4) : Three (K := K) := (eta (K := K) b) • !![0, -1, -1;-1, 0, -1;-1, -1, 0]

def curvatureDH (s : Fin 4) : Three (K := K) :=
  let H : Three (K := K) := !![-1 / 2, -1 / 2, -1 / 2;-1 / 2, -1 / 2, 1 / 2;-1 / 2, 1 / 2, -1 / 2]
  if s = 3 then -(signS * H * signS) else H

def curvatureRH (b : Fin 4) : Three (K := K) :=
  (eta (K := K) b) • !![1 / 2, -1 / 2, -1 / 2;-1 / 2, 1 / 2, -1 / 2;-1 / 2, -1 / 2, 1 / 2]

def curvatureApply (A : Connection K) : Connection K :=
  gAssemble (fun s => curvatureD s *ᵥ gDistinct A s) (fun b => curvatureR b *ᵥ gRepeated A b)

def curvatureReturn (A : Connection K) : Connection K :=
  gAssemble (fun s => curvatureDH s *ᵥ gDistinct A s) (fun b => curvatureRH b *ᵥ gRepeated A b)

def nativeFaceInverse (Z : NativeFace K) : NativeFace K :=
  faceAssemble (fun s => faceInverseBlock s *ᵥ faceRead Z s)

def directCurvatureReturn (A : Connection K) : Connection K :=
  !![(1 / 2) * A 0 0 + (1 / 2) * A 2 5 + (-1 / 2) * A 3 4, (1 / 2) * A 0 1 + (-1 / 2) * A 1 5 +
    (1 / 2) * A 3 3, (1 / 2) * A 0 2 + (1 / 2) * A 1 4 + (-1 / 2) * A 2 3, (-1 / 2) * A 0 3 + (1
    / 2) * A 2 2 + (-1 / 2) * A 3 1, (-1 / 2) * A 0 4 + (-1 / 2) * A 1 2 + (1 / 2) * A 3 0, (-1
    / 2) * A 0 5 + (1 / 2) * A 1 1 + (-1 / 2) * A 2 0;
  (-1 / 2) * A 1 0 + (1 / 2) * A 2 1 + (1 / 2) * A 3 2, (1 / 2) * A 0 5 + (-1 / 2) * A 1 1 + (-1
    / 2) * A 2 0, (-1 / 2) * A 0 4 + (-1 / 2) * A 1 2 + (-1 / 2) * A 3 0, (1 / 2) * A 1 3 + (-1
    / 2) * A 2 4 + (-1 / 2) * A 3 5, (1 / 2) * A 0 2 + (1 / 2) * A 1 4 + (1 / 2) * A 2 3, (-1 /
    2) * A 0 1 + (1 / 2) * A 1 5 + (1 / 2) * A 3 3;
  (-1 / 2) * A 0 5 + (-1 / 2) * A 1 1 + (-1 / 2) * A 2 0, (1 / 2) * A 1 0 + (-1 / 2) * A 2 1 +
    (1 / 2) * A 3 2, (1 / 2) * A 0 3 + (-1 / 2) * A 2 2 + (-1 / 2) * A 3 1, (-1 / 2) * A 0 2 +
    (1 / 2) * A 1 4 + (1 / 2) * A 2 3, (-1 / 2) * A 1 3 + (1 / 2) * A 2 4 + (-1 / 2) * A 3 5, (1
    / 2) * A 0 0 + (1 / 2) * A 2 5 + (1 / 2) * A 3 4;
  (1 / 2) * A 0 4 + (-1 / 2) * A 1 2 + (-1 / 2) * A 3 0, (-1 / 2) * A 0 3 + (-1 / 2) * A 2 2 +
    (-1 / 2) * A 3 1, (1 / 2) * A 1 0 + (1 / 2) * A 2 1 + (-1 / 2) * A 3 2, (1 / 2) * A 0 1 + (1
    / 2) * A 1 5 + (1 / 2) * A 3 3, (-1 / 2) * A 0 0 + (1 / 2) * A 2 5 + (1 / 2) * A 3 4, (-1 /
    2) * A 1 3 + (-1 / 2) * A 2 4 + (1 / 2) * A 3 5]

end Artform.Scores.GravityBridge.Native.RetroCertificates
