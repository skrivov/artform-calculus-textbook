import ArtformScores.GravityBridge.Native.CoordinateSymbol.InverseDefs

/-! # Original coordinate symbol and guarded two-sided inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-coordinate-two-sided-inverse**
(original coordinate symbol and guarded two-sided inverse). -/
@[ledger "GAC2:native-coordinate-two-sided-inverse"]
def inverseLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (C : Mat4 (K := K)) (d a b : K) (_hC : C * C = d • C),
    twoValueSymbol C d a b * twoValueNumerator C d a b = (a * b * d ^ 2) • 1 ∧
    twoValueNumerator C d a b * twoValueSymbol C d a b = (a * b * d ^ 2) • 1) ∧
    (∀ (C : Mat4 (K := K)) (d a b : K) (_hC : C * C = d • C)
    (_hd : d ≠ 0) (_ha : a ≠ 0) (_hb : b ≠ 0),
    twoValueSymbol C d a b * twoValueInverse C d a b = 1 ∧
    twoValueInverse C d a b * twoValueSymbol C d a b = 1) ∧
    (∀ (p : Vec4 (K := K))
    (_hd : simpleDiscriminant (componentSquares p) p ≠ 0),
    nativeUpperSymbol p * nativeCoordinateInverse p = 1 ∧
    nativeCoordinateInverse p * nativeUpperSymbol p = 1) ∧
    (∀ (p : Vec4 (K := K))
    (_hd : simpleDiscriminant (componentSquares p) p ≠ 0),
    nativeLowerSymbol p * nativeLowerInverse p = 1 ∧
    nativeLowerInverse p * nativeLowerSymbol p = 1)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
