import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost

/-! # Actual sourced two-cube incidence and inherited coframes -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



abbrev CubeCell := Fin 3 × Fin 3 × Fin 3 × Fin 3

abbrev SplitCell := Fin 5 × Fin 3 × Fin 3 × Fin 3

def axisDimension (n : ℕ) : ℕ := n%2

def cubeDimension (x : CubeCell) : ℕ :=
  axisDimension x.1.val + axisDimension x.2.1.val +
    axisDimension x.2.2.1.val + axisDimension x.2.2.2.val

def splitDimension (x : SplitCell) : ℕ :=
  axisDimension x.1.val + axisDimension x.2.1.val +
    axisDimension x.2.2.1.val + axisDimension x.2.2.2.val

def cubeCount (k : ℕ) : ℕ := (Finset.univ.filter (fun x : CubeCell => cubeDimension x = k)).card

def splitCount (k : ℕ) : ℕ := (Finset.univ.filter (fun x : SplitCell => splitDimension x = k)).card

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
