import ArtformScores.GravityBridge.Native.TTCross.Source

/-! # All24 independent connection residual and native physical sign -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def independentReturn (Z : Matrix (Fin 6) (Fin 4) K) : Connection K :=
  fullHApply ((-2 / 101 : K) • nativeSourceAdjoint Z)

def onWaveCrossZ (j a q v : K) : Matrix (Fin 6) (Fin 4) K :=
  threeBlockFace ![(-2 * a ^ 2 * q - j * a * v) / 4, -a ^ 2 * q / 2, j * a * v / 4]
    ![(-2 * a ^ 2 * q + j * a * v) / 4, -a ^ 2 * q / 2, -j * a * v / 4]
    ![0, -a ^ 2 * q / 2, -a ^ 2 * q / 2]

end Artform.Scores.GravityBridge.Native.TTCross
