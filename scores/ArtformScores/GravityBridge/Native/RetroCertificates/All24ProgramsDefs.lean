import ArtformScores.GravityBridge.Native.TTCross.Full24
import ArtformScores.GravityBridge.Native.Retrospective.BlockPrograms

/-! # Verified arbitrary-input original24 inverse programs -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



def repeatedDense : List ScalarGate := [
  .scale (9999 / 20600) (.input 0), .scale (-10201 / 20600) (.input 1),
  .add (.slot 0) (.slot 1), .scale (-10201 / 20600) (.input 2), .add (.slot 2) (.slot 3),
  .scale (-10201 / 20600) (.input 0), .scale (9999 / 20600) (.input 1),
  .add (.slot 5) (.slot 6), .scale (-10201 / 20600) (.input 2), .add (.slot 7) (.slot 8),
  .scale (-10201 / 20600) (.input 0), .scale (-10201 / 20600) (.input 1),
  .add (.slot 10) (.slot 11), .scale (9999 / 20600) (.input 2), .add (.slot 12) (.slot 13)]

def repeatedRank : List ScalarGate := [
  .scale (101 / 103) (.input 0), .scale (101 / 103) (.input 1),
  .scale (101 / 103) (.input 2), .add (.input 0) (.input 1),
  .add (.slot 3) (.input 2), .scale (-10201 / 20600) (.slot 4),
  .add (.slot 0) (.slot 5), .add (.slot 1) (.slot 5), .add (.slot 2) (.slot 5)]

def runBlock (rank repeated : Bool) (z : Fin 3 → ℚ) : Fin 3 → ℚ :=
  if rank then programOutput (if repeated then repeatedRank else rankBlockProgram) ![6, 7, 8] z
  else programOutput (if repeated then repeatedDense else denseBlockProgram) ![4, 9, 14] z

def signVector (z : Fin 3 → ℚ) : Fin 3 → ℚ := ![z 0, -z 1, -z 2]

def fullProgram (rank : Bool) (A : Connection ℚ) : Connection ℚ :=
  gAssemble (fun s => if s = 3 then -signVector (runBlock rank false (signVector (gDistinct A s)))
    else runBlock rank false (gDistinct A s))
    (fun b => (eta (K := ℚ) b) • runBlock rank true (gRepeated A b))

def fullScaleCount (rank : Bool) : ℕ :=
  4 * scaleCount (if rank then rankBlockProgram else denseBlockProgram) +
    4 * scaleCount (if rank then repeatedRank else repeatedDense)

def fullAddCount (rank : Bool) : ℕ :=
  4 * addCount (if rank then rankBlockProgram else denseBlockProgram) +
    4 * addCount (if rank then repeatedRank else repeatedDense)

end Artform.Scores.GravityBridge.Native.RetroCertificates
