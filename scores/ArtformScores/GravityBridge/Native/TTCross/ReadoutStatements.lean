import ArtformScores.GravityBridge.Native.TTCross.ReadoutDefs

/-! # Read inverse and explicit budget on the paired native band slice -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:paired-band-preparation-readout**
(read inverse and explicit budget on the paired native band slice). -/
@[ledger "GAC2:paired-band-preparation-readout"]
def readoutLaw : Prop :=
    (∀ (a : ℝ) (u : Fin 2 → ℝ),
    pairedReadout (preparedJet a u) = u) ∧
    (∀ (a : ℝ) (_hlo : 9 / 2 ≤ a ^ 2),
    a ≠ 0) ∧
    (∀ (a : ℝ) (u : Fin 2 → ℝ)
    (_hlo : 9 / 2 ≤ a ^ 2) (_hhi : a ^ 2 ≤ 25 / 2),
    |preparedJet a u 0| ≤ |u 1| / 9 ∧ |preparedJet a u 3| ≤ 25 * |u 0|) ∧
    (pairedReadout (![1, 0, 0, 0] : Fin 4 → ℝ) = pairedReadout 0 ∧
      (![1, 0, 0, 0] : Fin 4 → ℝ) ≠ 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
