import ArtformScores.GravityBridge.Native.TTCross.HistoryDefs

/-! # Bounded native coordinate history does not determine preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-bounded-history-ambiguity**
(bounded native coordinate history does not determine preparation). -/
@[ledger "GAC2:native-bounded-history-ambiguity"]
def historyLaw : Prop :=
    (∀ (a t : ℝ),
    HasDerivAt (fun s => boundedHomogeneousJet a s 0) (boundedHomogeneousJet a t 1) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 1) (boundedHomogeneousJet a t 2) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 2) (boundedHomogeneousJet a t 3) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 3) (boundedHomogeneousJet a t 4) t) ∧
    (∀ (a t : ℝ),
    scalarRow a (boundedHomogeneousJet a t) = 0) ∧
    (∀ (a t : ℝ),
    |boundedHomogeneousJet a t 0| ≤ 1) ∧
    (∀ (a : ℝ) (x : Fin 5 → ℝ),
    scalarRow a (x + boundedHomogeneousJet a 0) = scalarRow a x ∧
      (x + boundedHomogeneousJet a 0) 0 ≠ x 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
