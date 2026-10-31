import ArtformScores.GravityBridge.Native.Full40.CoordinatesDefs

/-! # Original forty coordinates Gram and Hodge data -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:native-forty-coordinate-gram**
(original forty coordinates gram and hodge data). -/
@[ledger "GAC2:native-forty-coordinate-gram"]
def coordinatesLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (Fintype.card Coordinate = 40) ∧
    (∀ (x : Full K),
    unpack (pack x) = x) ∧
    (∀ (x : Coordinate → K),
    pack (unpack x) = x) ∧
    (∀ (a : Biv K),
    lieCoordinates (lie a) = a) ∧
    (Function.Injective (lie (K := K))) ∧
    (∀ (a : Biv K),
    ∀ i j, metricVariation (lie a) i j = 0) ∧
    (∀ (F : Frame K),
    (∀ i j, metricVariation F i j = 0) ↔ ∃ a : Biv K, F = lie a) ∧
    (∀ (a b : Biv K),
    bivPair a b = -(Matrix.trace (lie a * lie b)) / 2) ∧
    (∀ (a b : Biv K),
    bivPair a b = ∑ i, gramConvert a i * b i) ∧
    (∀ (a : Biv K),
    gramConvert (gramConvert a) = a) ∧
    (∀ (f : Frame K),
    frameGram (frameGram f) = f) ∧
    (∀ (a : Biv K) (_ha : ∀ b, bivPair a b = 0),
    a = 0) ∧
    (∀ (a : Biv K),
    internalStar (internalStar a) = -a) ∧
    (∀ (a b : Biv K),
    bivPair (internalStar a) b = bivPair a (internalStar b)) ∧
    (∀ (a b : Biv K),
    bivPair a (internalStar b) =
      a 0 * b 3 + a 1 * b 4 + a 2 * b 5 + a 3 * b 0 + a 4 * b 1 + a 5 * b 2)

end Artform.Scores.GravityBridge.Native.Full40.Statement
