import ArtformScores.GravityBridge.Native.RetroCertificates.All24ProgramsDefs

/-! # Verified arbitrary-input original24 inverse programs -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:verified-all24-rank-return**
(verified arbitrary-input original24 inverse programs). -/
@[ledger "GAC2:verified-all24-rank-return"]
def all24ProgramsLaw : Prop :=
    (∀ (rank : Bool) (A : Connection ℚ),
    fullProgram rank A = fullHApply A) ∧
    (∀ (rank : Bool) (A : Connection ℚ),
    fullBApply (fullProgram rank A) = A ∧ fullProgram rank (fullBApply A) = A) ∧
    (validProgram 0 repeatedRank = true ∧ validProgram 0 repeatedDense = true ∧
    fullScaleCount false = 72 ∧ fullAddCount false = 48 ∧
    fullScaleCount true = 32 ∧ fullAddCount true = 40) ∧
    ((∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < repeatedDense.length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < repeatedRank.length) ∧
    (∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < denseBlockProgram.length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < rankBlockProgram.length)) ∧
    (∀ (cs ca : ℚ) (_hs : 0 < cs) (_ha : 0 ≤ ca),
    (fullScaleCount true : ℚ) * cs + (fullAddCount true : ℚ) * ca <
      (fullScaleCount false : ℚ) * cs + (fullAddCount false : ℚ) * ca) ∧
    (validProgram 0 denseBlockProgram = true ∧ validProgram 0 rankBlockProgram = true ∧
    validProgram 0 repeatedDense = true ∧ validProgram 0 repeatedRank = true)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
