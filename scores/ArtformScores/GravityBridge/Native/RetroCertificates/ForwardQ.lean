import ArtformScores.GravityBridge.Native.RetroCertificates.ForwardQStatements

/-! # Verified cheaper complete original constitutive forward map -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



open Matrix Full40 TTCross

lemma complete_original_Q_program (rank : Bool) (Z : NativeFace ℚ) :
    fullFaceProgram false rank Z = nativeConstitutiveQ Z := by
  rw [full_face_code_semantics]
  simp only [Bool.false_eq_true, ite_false]
  have he : (fun s => faceForwardBlock s *ᵥ faceRead Z s) = faceRead (nativeConstitutiveQ Z) := by
    funext s
    exact (original_constitutive_face_blocks Z s).symm
  rw [he, native_face_partition_left]

lemma complete_Q_matched_costs :
    faceProgramScales false false = 72 ∧ faceProgramAdds false false = 48 ∧
    faceProgramScales false true = 32 ∧ faceProgramAdds false true = 40 :=
  (face_codes_valid_and_costs false).2

lemma complete_Q_weighted_saving (cs ca : ℚ) (hs : 0 < cs) (ha : 0 ≤ ca) :
    (faceProgramScales false true : ℚ) * cs + (faceProgramAdds false true : ℚ) * ca <
      (faceProgramScales false false : ℚ) * cs + (faceProgramAdds false false : ℚ) * ca := by
  obtain ⟨h1, h2, h3, h4⟩ := complete_Q_matched_costs
  rw [h1, h2, h3, h4]
  norm_num
  nlinarith

lemma complete_forward_code_guards (s : Fin 8) :
    Retrospective.validProgram 0 (rankFaceCode false s) = true ∧
    Retrospective.validProgram 0 (denseFaceCode false s) = true ∧
    (∀ i : Fin 3,(![4,9,14] : Fin 3 → ℕ) i < (denseFaceCode false s).length) ∧
    (∀ i : Fin 3,(![6,7,8] : Fin 3 → ℕ) i < (rankFaceCode false s).length) := by
  exact ⟨((face_codes_valid_and_costs false).1 s).1,
    ((face_codes_valid_and_costs false).1 s).2,
    (face_code_output_slots false s).1,(face_code_output_slots false s).2⟩

/-- **GAC2:native-full-Q-program**
(verified cheaper complete original constitutive forward map). -/
@[ledger "GAC2:native-full-Q-program"]
theorem forwardQLaw : Statement.forwardQLaw := by
  exact ⟨complete_original_Q_program,
    complete_Q_matched_costs,
    complete_Q_weighted_saving,
    complete_forward_code_guards⟩

/-! ## Non-vacuity -/
example : fullFaceProgram false true (!![1, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0;0, 0, 0,
  0;0, 0, 0, 0]) =
    nativeConstitutiveQ (!![1, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0;0, 0, 0, 0] :
      NativeFace ℚ) :=
  complete_original_Q_program true _

end Artform.Scores.GravityBridge.Native.RetroCertificates
