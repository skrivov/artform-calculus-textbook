import ArtformScores.GravityBridge.Native.RetroCertificates.TemplatesDefs

/-! # Two template checks certify both original24 inverse orders -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-two-template-certificate**
(two template checks certify both original24 inverse orders). -/
@[ledger "GAC2:native-two-template-certificate"]
def templatesLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (D R : Three (K := K))
    (_hD : D * timeB = 1) (_hR : R * repeatB 1 = 1),
    ∀ A : Connection K, fullBApply (templateReturn D R A) = A ∧
      templateReturn D R (fullBApply A) = A) ∧
    (timeH (K := K) * timeB = 1 ∧ repeatH (K := K) 1 * repeatB 1 = 1) ∧
    (2 * 3 * 3 = 18 ∧ 24 * 24 = 576 ∧ 2 * 3 * 3 * 3 = 54 ∧ 2 * 3 * 3 * (3 - 1) = 36 ∧
      24 * 24 * 24 = 13824 ∧ 24 * 24 * (24 - 1) = 13248)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
