import ArtformScores.GravityBridge.Native.TTCross.FullRowsDefs

/-! # Embed the actual paired source in all four coordinate rows -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-four-row-source-embedding**
(embed the actual paired source in all four coordinate rows). -/
@[ledger "GAC2:native-four-row-source-embedding"]
def fullRowsLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j a : K) (_hj : j ^ 2 = -1),
    (fun r => nativeUpperCoefficients j ![a, -a, 0] r *ᵥ ![0, 0, 0, 1]) =
      fun r => rowCoefficients a r • ![0, 0, 0, 1]) ∧
    (∀ (j a : K) (_hj : j ^ 2 = -1) (x : Fin 5 → K),
    fullCoordinateRow j a x = (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * scalarRow a x) • ![0, 0,
      0, 1]) ∧
    (∀ (j a v : K) (_hj : j ^ 2 = -1) (x : Fin 5 → K),
    fullCoordinateRow j a x + actualCrossSource a v =
      (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * (scalarRow a x + 2 * a ^ 2 * v)) • ![0, 0, 0, 1]) ∧
    (∀ (j a v : K) (_hj : j ^ 2 = -1) (x : Fin 5 → K)
    (_hx : scalarRow a x = -2 * a ^ 2 * v),
    fullCoordinateRow j a x + actualCrossSource a v = 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
