import ArtformScores.GravityBridge.Defs
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Controlled L2 pair exhaustion with background separation -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {X : Type*}

noncomputable def l2Seed : lp (fun _ : ℤ => ℝ) 2 := lp.single 2 0 1

end Artform.Scores.GravityBridge.Native.GreenComposition
