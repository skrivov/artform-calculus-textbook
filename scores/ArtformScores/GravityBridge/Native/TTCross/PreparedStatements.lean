import ArtformScores.GravityBridge.Native.TTCross.PreparedDefs

/-! # Original paired-axis TT graph with its complete preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-paired-tt-preparation**
(original paired-axis tt graph with its complete preparation). -/
@[ledger "GAC2:native-paired-tt-preparation"]
def preparedLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (a : K) (_ha : a ≠ 0) (u : Fin 2 → K),
    forcedJetStep a u (preparedJet a u) = preparedJet a (pairedTTStep a u)) ∧
    (∀ (a : K) (u : Fin 2 → K),
    ![preparedJet a u 1, preparedJet a u 2] = u) ∧
    (∀ (a : K),
    Function.Injective (preparedJet (K := K) a)) ∧
    (∀ (a : K) (u : Fin 2 → K),
    preparedJet a u = 0 ↔ u = 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
