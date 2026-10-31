import ArtformScores.GravityBridge.Native.TTCross.GreenDefs

/-! # Full four-jet scalar current and its prepared pullback -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-scalar-fourjet-current**
(full four-jet scalar current and its prepared pullback). -/
@[ledger "GAC2:native-scalar-fourjet-current"]
def greenLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (a : K) (x y : Fin 5 → K),
    scalarGreen a (nextFour x) (firstFour y) + scalarGreen a (firstFour x) (nextFour y) =
      x 0 * scalarRow a y - scalarRow a x * y 0) ∧
    (∀ (a : K) (_ha : a ≠ 0) (u v : Fin 2 → K),
    scalarGreen a (preparedJet a u) (preparedJet a v) =
      -(5 / 2 : K) * (u 0 * v 1 - u 1 * v 0)) ∧
    (∀ (a : K) (x y : Fin 5 → K) (f g : K)
    (_hx : scalarRow a x = f) (_hy : scalarRow a y = g),
    scalarGreen a (nextFour x) (firstFour y) + scalarGreen a (firstFour x) (nextFour y) =
      x 0 * g - f * y 0) ∧
    (∀ (a : K) (u v : Fin 2 → K),
    preparedJet a u 0 * (-2 * a ^ 2 * v 1) - (-2 * a ^ 2 * u 1) * preparedJet a v 0 = 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
