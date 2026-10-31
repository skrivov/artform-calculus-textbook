import ArtformScores.GravityBridge.Native.Retrospective.FirstContact
/-! # The actual solved source and a declared one-multiplication lower bound -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
inductive ZeroCostWire where
  | input
  | negativeInput
  | constant (c : ℚ)
def wireValue : ZeroCostWire → ℚ → ℚ
  | .input, z => z
  | .negativeInput, z => -z
  | .constant c, _ => c
def oneMultiplySchur (z : ℚ) : Fin 3 → ℚ :=
  let s := (-101 / 103 : ℚ) * z
  ![s, s, 0]
end Artform.Scores.GravityBridge.Native.Retrospective
