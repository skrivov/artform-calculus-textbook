import ArtformScores.GravityBridge.Native.Full40.Coordinates
import ArtformScores.GravityBridge.Native.NativeCurrent.Coordinates

/-! # Literal16+24 scaling and all current contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators
open Full40

variable {K : Type*} [Field K] [CharZero K]

def frameOnly (x : Full K) : Full K := (x.1, 0)

def connectionOnly (x : Full K) : Full K := (0, x.2)

def physicalForty (h : K) (x : Full K) : Full K := (x.1, (-h) • x.2)

def coordinateGram (x : Full K) : Full K :=
  (frameGram x.1, fun i => gramConvert (x.2 i))

def originalCoordinateDual (x y : Full K) : K := ∑ a, pack x a * pack y a

end Artform.Scores.GravityBridge.Native.GreenComposition
