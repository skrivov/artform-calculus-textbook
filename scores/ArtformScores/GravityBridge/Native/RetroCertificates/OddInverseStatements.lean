import ArtformScores.GravityBridge.Native.RetroCertificates.OddInverseDefs

/-! # Original full24 inverse as an odd degree-five polynomial -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:original-global-odd-inverse**
(original full24 inverse as an odd degree-five polynomial). -/
@[ledger "GAC2:original-global-odd-inverse"]
def oddInverseLaw : Prop :=
    ((∀ s : Fin 4, oddInverse (distinctB s) = distinctH s) ∧
    (∀ b : Fin 4, oddInverse (repeatB b) = repeatH b)) ∧
    (∀ (n : ℕ) (A : Connection ℚ),
    (∀ s, gDistinct (nativePower n A) s = (distinctB s) ^ n *ᵥ gDistinct A s) ∧
    (∀ b, gRepeated (nativePower n A) b = (repeatB b) ^ n *ᵥ gRepeated A b)) ∧
    (∀ (A : Connection ℚ),
    globalOddInverse A = fullHApply A) ∧
    (∀ (A : Connection ℚ),
    fullBApply (globalOddInverse A) = A ∧ globalOddInverse (fullBApply A) = A)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
