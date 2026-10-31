import ArtformScores.GravityBridge.Native.RetroCertificates.TemplatesStatements

/-! # Two template checks certify both original24 inverse orders -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40 TTCross
lemma two_template_certificate_complete (D R : Three (K := K))
    (hD : D * timeB = 1) (hR : R * repeatB 1 = 1) :
    ∀ A : Connection K, fullBApply (templateReturn D R A) = A ∧
      templateReturn D R (fullBApply A) = A := by
  have hd : D = timeH := by
    calc D = D * 1 := by rw [Matrix.mul_one]
         _ = D * (timeB * timeH) := by rw [actual_three_block_inverse.1]
         _ = (D * timeB) * timeH := by rw [Matrix.mul_assoc]
         _ = timeH := by rw [hD, Matrix.one_mul]
  have hr : R = repeatH 1 := by
    calc R = R * 1 := by rw [Matrix.mul_one]
         _ = R * (repeatB 1 * repeatH 1) := by rw [(all_repeated_inverses (K := K) 1).1]
         _ = (R * repeatB 1) * repeatH 1 := by rw [Matrix.mul_assoc]
         _ = repeatH 1 := by rw [hR, Matrix.one_mul]
  have he (A : Connection K) : templateReturn D R A = fullHApply A := by
    rw [hd, hr]
    unfold templateReturn fullHApply
    congr 1
    funext b
    congr 1
    ext i j
    simp [repeatH, eta]
  intro A
  simp only [he]
  exact original_full24_inverse A

lemma actual_original_two_templates :
    timeH (K := K) * timeB = 1 ∧ repeatH (K := K) 1 * repeatB 1 = 1 :=
  ⟨actual_three_block_inverse.2.1, (all_repeated_inverses 1).2⟩

lemma exact_replay_obligation_counts :
    2 * 3 * 3 = 18 ∧ 24 * 24 = 576 ∧ 2 * 3 * 3 * 3 = 54 ∧ 2 * 3 * 3 * (3 - 1) = 36 ∧
      24 * 24 * 24 = 13824 ∧ 24 * 24 * (24 - 1) = 13248 := by decide +kernel

/-- **GAC2:native-two-template-certificate**
(two template checks certify both original24 inverse orders). -/
@[ledger "GAC2:native-two-template-certificate"]
theorem templatesLaw : Statement.templatesLaw := by
  intro K _ _
  exact ⟨two_template_certificate_complete,
    actual_original_two_templates,
    exact_replay_obligation_counts⟩

/-! ## Non-vacuity -/
example : ∀ A : Connection ℚ, fullBApply (templateReturn timeH (repeatH 1) A) = A ∧
    templateReturn timeH (repeatH 1) (fullBApply A) = A :=
  two_template_certificate_complete _ _ actual_original_two_templates.1
    actual_original_two_templates.2

end Artform.Scores.GravityBridge.Native.RetroCertificates
