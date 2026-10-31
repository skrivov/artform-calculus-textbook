import ArtformScores.GravityBridge.Defs

/-! # Independent shifts and the periodic incoming transpose -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {X K : Type*} [AddCommGroup X] [CommRing K]

def shift (d : X) (f : X → K) : X → K := fun x => f (x + d)

def difference (d : X) (f : X → K) : X → K := shift d f - f

abbrev Grid := Fin 4 → ZMod 3

def gridUnit (i : Fin 4) : Grid := fun j => if j = i then 1 else 0

def gridPulse (x : Grid) : ℚ := if x = 0 then 1 else 0

end Artform.Scores.GravityBridge.Native.Full40
