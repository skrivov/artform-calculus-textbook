import ArtformScores.GravityBridge.Native.GreenComposition.FortyContactsDefs

/-! # Literal16+24 scaling and all current contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators
open Full40

/-- **GAC2:literal-full40-current-contacts**
(literal16+24 scaling and all current contacts). -/
@[ledger "GAC2:literal-full40-current-contacts"]
def fortyContactsLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (h : K) (x : Full K),
    physicalForty h x = frameOnly x - h • connectionOnly x) ∧
    (∀ (B : (Full K) →ₗ[K] (Full K) →ₗ[K] K) (h : K) (x y : Full K),
    B (physicalForty h x) (physicalForty h y) =
      B (frameOnly x) (frameOnly y) - h * B (frameOnly x) (connectionOnly y)-
      h * B (connectionOnly x) (frameOnly y) + h ^ 2 * B (connectionOnly x) (connectionOnly y)) ∧
    (∀ (x y : Full K),
    originalCoordinateDual x (coordinateGram y) =
      (∑ i, ∑ j, eta i * x.1 i j * y.1 i j) + (∑ i, bivPair (x.2 i) (y.2 i))) ∧
    (∀ (h cut pairing : K),
    h * (h ^ 3 * pairing) * cut = h ^ 4 * (pairing * cut))

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
