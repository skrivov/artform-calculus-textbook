import ArtformScores.GravityBridge.Native.Retrospective.IndexedBlocksDefs

/-! # Indexed original distinct and repeated connection restrictions -/

namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement

open Full40

/-- **GAC2:indexed-original-connection-blocks**
(indexed original distinct and repeated connection restrictions). -/
@[ledger "GAC2:indexed-original-connection-blocks"]
def indexedBlocksLaw : Prop :=
  
    (∀ (s : Fin 4) (t : ℚ) (z : Fin 3 → ℚ),
    connectionDensity t (distinctInput s z) = distinctDensity s t z) ∧
    (∀ (b : Fin 4) (t : ℚ) (z : Fin 3 → ℚ),
    connectionDensity t (repeatedInput b z) = repeatedDensity b t z) ∧
    (∀ (t : ℚ) (z : Fin 3 → ℚ),
    connectionDensity t (distinctInput 0 z) =
      (∑ i, z i * (∑ j, paramConnection t i j * z j)) / 2) ∧
    (∀ (b : Fin 4) (t : ℚ) (z : Fin 3 → ℚ),
    connectionDensity t (repeatedInput b z) =
      (∑ i, z i * (∑ j, repeatedBlock b t i j * z j)) / 2)

end Artform.Scores.GravityBridge.Native.Retrospective.Statement
