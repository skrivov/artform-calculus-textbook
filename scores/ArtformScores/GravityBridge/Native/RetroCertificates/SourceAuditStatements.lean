import ArtformScores.GravityBridge.Native.RetroCertificates.SourceAuditDefs

/-! # Selected native sources do not certify the full inverse -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-source-only-certificate-audit**
(selected native sources do not certify the full inverse). -/
@[ledger "GAC2:native-source-only-certificate-audit"]
def sourceAuditLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (p m s : Fin 3 → K),
    sourceOnlyReturn (threeConnection p m s) = fullHApply (threeConnection p m s)) ∧
    (∀ (p m s : Fin 3 → K),
    sourceOnlyReturn (nativeSourceAdjoint (threeBlockFace p m s)) =
      fullHApply (nativeSourceAdjoint (threeBlockFace p m s))) ∧
    (∀ (z : Fin 3 → K) (b : Fin 4),
    sourceOnlyReturn (gRepeatedInput b z) = 0) ∧
    ((∀ p m s : Fin 3 → ℚ, sourceOnlyReturn (threeConnection p m s) =
      fullHApply (threeConnection p m s)) ∧
    fullBApply (sourceOnlyReturn (gRepeatedInput 1 (![1, 0, 0] : Fin 3 → ℚ))) ≠ 
      gRepeatedInput 1 ![1, 0, 0])

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
