import ArtformScores.GravityBridge.Native.Full40.ShiftsDefs

/-! # Independent shifts and the periodic incoming transpose -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:native-shift-adjoint**
(independent shifts and the periodic incoming transpose). -/
@[ledger "GAC2:native-shift-adjoint"]
def shiftsLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [CommRing K],
    (∀ (a b : X) (f : X → K),
    shift a (shift b f) = shift (a + b) f) ∧
    (∀ (a b : X) (f : X → K),
    shift a (shift b f) = shift b (shift a f)) ∧
    (∀ (a : X) (f : X → K),
    shift (-a) (shift a f) = f) ∧
    (∀ (a b : X) (f : X → K),
    difference a (difference b f) = difference b (difference a f)) ∧
    (∀ [Fintype X] (a : X) (f g : X → K),
    ∑ x, shift a f x * g x = ∑ x, f x * shift (-a) g x) ∧
    (∀ [Fintype X] (a : X) (f g : X → K),
    ∑ x, difference a f x * g x = ∑ x, f x * difference (-a) g x) ∧
    (∀ i j : Fin 4, i ≠ j →
    shift (gridUnit i) gridPulse (-gridUnit i) = 1 ∧
    shift (gridUnit j) gridPulse (-gridUnit i) = 0)

end Artform.Scores.GravityBridge.Native.Full40.Statement
