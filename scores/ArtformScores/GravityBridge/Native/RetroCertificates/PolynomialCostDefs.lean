import ArtformScores.GravityBridge.Native.RetroCertificates.OddInverse
import ArtformScores.GravityBridge.Native.RetroCertificates.All24Programs

/-! # Exact degree-five inverse can cost more than block return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



inductive NativeRef where
  | input
  | slot (i : ℕ)
  deriving DecidableEq

inductive NativeGate where
  | applyB (r : NativeRef)
  | scale (c : ℚ) (r : NativeRef)
  | add (a b : NativeRef)
  deriving DecidableEq

def nativeResolve (A : Connection ℚ) (registers : List (Connection ℚ)) : NativeRef → Connection ℚ
  | .input => A
  | .slot i => registers.getD i 0

def nativeGateValue (A : Connection ℚ) (r : List (Connection ℚ)) : NativeGate → Connection ℚ
  | .applyB x => fullBApply (nativeResolve A r x)
  | .scale c x => c • nativeResolve A r x
  | .add x y => nativeResolve A r x + nativeResolve A r y

def nativeRun (program : List NativeGate) (A : Connection ℚ) : List (Connection ℚ) :=
  program.foldl (fun r g => r ++ [nativeGateValue A r g]) []

def oddNativeProgram : List NativeGate := [
  .applyB .input, .applyB (.slot 0), .applyB (.slot 1), .applyB (.slot 2), .applyB (.slot 3),
  .scale inverseP1 (.slot 0), .scale inverseP3 (.slot 2), .scale inverseP5 (.slot 4),
  .add (.slot 5) (.slot 6), .add (.slot 8) (.slot 7)]

def nativeValidRef (n : ℕ) : NativeRef → Bool
  | .input => true
  | .slot i => decide (i < n)

def nativeValidGate (n : ℕ) : NativeGate → Bool
  | .applyB r => nativeValidRef n r
  | .scale _ r => nativeValidRef n r
  | .add a b => nativeValidRef n a && nativeValidRef n b

def nativeValid : ℕ → List NativeGate → Bool
  | _, [] => true
  | n, g::gs => nativeValidGate n g && nativeValid (n + 1) gs

def nativeScaleCost (program : List NativeGate) : ℕ :=
  (program.map (fun g => match g with | .applyB _ => 72 | .scale _ _ => 24 | .add _ _ => 0)).sum

def nativeAddCost (program : List NativeGate) : ℕ :=
  (program.map (fun g => match g with | .applyB _ => 48 | .scale _ _ => 0 | .add _ _ => 24)).sum

end Artform.Scores.GravityBridge.Native.RetroCertificates
