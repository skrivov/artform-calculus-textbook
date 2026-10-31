import ArtformScores.GravityBridge.Native.Full40.Shifts

/-! # Owned spatial windows retain their incoming boundary -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open scoped BigOperators

variable {X K : Type*} [Fintype X] [AddCommGroup X] [Field K]

def ownedPairing (owner f g : X → K) : K := ∑ x, owner x * f x * g x

def ownedBoundary (owner f g : X → K) (s : X) : K :=
  ∑ x, (owner x - owner (x + s)) * f x * g (x + s)

def window5 : ZMod 5 → ℚ := fun x => if x = 0 ∨ x = 1 then 1 else 0

def leftEdge5 : ZMod 5 → ℚ := fun x => if x = 1 then 1 else 0

def rightEdge5 : ZMod 5 → ℚ := fun x => if x = 2 then 1 else 0

end Artform.Scores.GravityBridge.Native.NativeCurrent
