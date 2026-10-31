import ArtformScores.GravityBridge.Native.NativeCurrent.OwnedWindowDefs

/-! # Owned spatial windows retain their incoming boundary -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent.Statement

open scoped BigOperators

/-- **GAC2:owned-window-incoming-boundary**
(owned spatial windows retain their incoming boundary). -/
@[ledger "GAC2:owned-window-incoming-boundary"]
def ownedWindowLaw : Prop :=
  ∀ (X K : Type) [Fintype X] [AddCommGroup X] [Field K],
    (∀ (owner f g : X → K) (s : X),
    ownedPairing owner f (fun x => g (x + s))-
      ownedPairing owner (fun x => f (x - s)) g = ownedBoundary owner f g s) ∧
    (∀ (f g : X → K) (s : X),
    ownedPairing (fun _ => 1) f (fun x => g (x + s)) =
      ownedPairing (fun _ => 1) (fun x => f (x - s)) g) ∧
    (ownedBoundary window5 leftEdge5 rightEdge5 1 = 1)

end Artform.Scores.GravityBridge.Native.NativeCurrent.Statement
