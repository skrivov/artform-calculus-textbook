import ArtformScores.GravityBridge.Native.TTCross.FullRows
import ArtformScores.GravityBridge.Native.TTCross.Prepared

/-! # Actual TT source range and failure of global preparation bounds -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def sourceVelocity (a r : K) : K := -(9991 : K) * r / (198 * a ^ 4)

end Artform.Scores.GravityBridge.Native.TTCross
