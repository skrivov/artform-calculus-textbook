import ArtformScores.GravityBridge.Native.RetroCertificates.ModalDegreeDefs

/-! # Native modal interpolation requires the fifth-degree term -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-modal-inverse-degree**
(native modal interpolation requires the fifth-degree term). -/
@[ledger "GAC2:native-modal-inverse-degree"]
def modalDegreeLaw : Prop :=
    ((∀ i : Fin 6, fullBApply (sixEigenvectors i) = sixEigenvalues i • sixEigenvectors i ∧
      sixEigenvectors i ≠ 0) ∧
    (∀ i j : Fin 6, i ≠ j → sixEigenvalues i ≠ sixEigenvalues j)) ∧
    (∀ (p1 p3 p5 : ℚ)
    (_ha : (p1 * (194 / 101) + p3 * (194 / 101) ^ 3 + p5 * (194 / 101) ^ 5) * (194 / 101) = 1)
    (_hb : (p1 * (103 / 101) + p3 * (103 / 101) ^ 3 + p5 * (103 / 101) ^ 5) * (103 / 101) = 1)
    (_hc : (p1 * (200 / 101) + p3 * (200 / 101) ^ 3 + p5 * (200 / 101) ^ 5) * (200 / 101) = 1),
    p1 = inverseP1 ∧ p3 = inverseP3 ∧ p5 = inverseP5) ∧
    (¬ ∃ p1 p3 : ℚ,
      (p1 * (194 / 101) + p3 * (194 / 101) ^ 3) * (194 / 101) = 1 ∧
      (p1 * (103 / 101) + p3 * (103 / 101) ^ 3) * (103 / 101) = 1 ∧
      (p1 * (200 / 101) + p3 * (200 / 101) ^ 3) * (200 / 101) = 1)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
