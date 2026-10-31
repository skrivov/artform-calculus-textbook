import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost
import ArtformScores.GravityBridge.Native.Full40.Torsion

/-! # All six original based words and guarded reverse loops -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40

variable {K : Type*} [Field K] [CharZero K]

def ownedEdge (c0 s0 c1 s1 : K) (next : Bool) (i : Fin 4) : Frame K :=
  if i = 1 then if next then boost c1 s1 else boost c0 s0 else 1

def reversedEdge (c0 s0 c1 s1 : K) (next : Bool) (i : Fin 4) : Frame K :=
  ownedEdge c0 (-s0) c1 (-s1) next i

def basedPlaquette (c0 s0 c1 s1 : K) (r : Fin 6) : Frame K :=
  let i := faceFirst r
  let l := faceSecond r
  reversedEdge c0 s0 c1 s1 false l * reversedEdge c0 s0 c1 s1 (l==0) i *
    ownedEdge c0 s0 c1 s1 (i==0) l * ownedEdge c0 s0 c1 s1 false i

def reversePlaquette (c0 s0 c1 s1 : K) (r : Fin 6) : Frame K :=
  let i := faceFirst r
  let l := faceSecond r
  reversedEdge c0 s0 c1 s1 false i * reversedEdge c0 s0 c1 s1 (i==0) l *
    ownedEdge c0 s0 c1 s1 (l==0) i * ownedEdge c0 s0 c1 s1 false l

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
