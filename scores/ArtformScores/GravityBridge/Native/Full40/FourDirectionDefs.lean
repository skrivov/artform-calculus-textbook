import ArtformScores.GravityBridge.Native.Full40.Force

/-! # A noncollapsed four-shift finite periodic force test -/

namespace Artform.Scores.GravityBridge.Native.Full40



abbrev TestGrid := Fin 17

def testStep (i : Fin 4) : TestGrid := ![1, 2, 4, 8] i

def fullPulse (x : TestGrid) : Full ℚ :=
  (fun i j => if x = 0 ∧ i = j then 1 else 0, 0)

def originTest (n : Fin 40) (x : TestGrid) : Full ℚ :=
  (fun i j => if x = 0 ∧ n.val = 4 * i.val + j.val then 1 else 0,
   fun i a => if x = 0 ∧ n.val = 16 + 6 * i.val + a.val then 1 else 0)

end Artform.Scores.GravityBridge.Native.Full40
