import ArtformScores.GravityBridge.Native.CoordinateSymbol.Axis

/-! # Native frequency degrees and source-dependent response -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

def explicitFaceInput : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun a b c => if a = 0 ∧ b = 1 ∧ c = 3 then 1 else 0

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
