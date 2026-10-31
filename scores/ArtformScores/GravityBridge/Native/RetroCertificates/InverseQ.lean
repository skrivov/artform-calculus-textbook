import ArtformScores.GravityBridge.Native.RetroCertificates.InverseQStatements

/-! # Verified complete inverse constitutive map on held-out inputs -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



open Matrix Full40 TTCross

lemma complete_original_Q_inverse_program (rank : Bool) (Z : NativeFace ℚ) :
    fullFaceProgram true rank Z = nativeFaceInverse Z := by
  rw [full_face_code_semantics]
  rfl

lemma inverse_program_solves_both (rank : Bool) (Z : NativeFace ℚ) :
    nativeConstitutiveQ (fullFaceProgram true rank Z) = Z ∧
      fullFaceProgram true rank (nativeConstitutiveQ Z) = Z := by
  simp only [complete_original_Q_inverse_program]
  exact original_full_constitutive_inverse Z

lemma complete_Q_inverse_matched_costs :
    faceProgramScales true false = 72 ∧ faceProgramAdds true false = 48 ∧
    faceProgramScales true true = 32 ∧ faceProgramAdds true true = 40 :=
  (face_codes_valid_and_costs true).2

lemma complete_Q_inverse_weighted_saving (cs ca : ℚ) (hs : 0 < cs) (ha : 0 ≤ ca) :
    (faceProgramScales true true : ℚ) * cs + (faceProgramAdds true true : ℚ) * ca <
      (faceProgramScales true false : ℚ) * cs + (faceProgramAdds true false : ℚ) * ca := by
  obtain ⟨h1, h2, h3, h4⟩ := complete_Q_inverse_matched_costs
  rw [h1, h2, h3, h4]
  norm_num
  nlinarith

lemma complete_inverse_code_guards (s : Fin 8) :
    Retrospective.validProgram 0 (rankFaceCode true s) = true ∧
    Retrospective.validProgram 0 (denseFaceCode true s) = true ∧
    (∀ i : Fin 3,(![4,9,14] : Fin 3 → ℕ) i < (denseFaceCode true s).length) ∧
    (∀ i : Fin 3,(![6,7,8] : Fin 3 → ℕ) i < (rankFaceCode true s).length) := by
  exact ⟨((face_codes_valid_and_costs true).1 s).1,
    ((face_codes_valid_and_costs true).1 s).2,
    (face_code_output_slots true s).1,(face_code_output_slots true s).2⟩

/-- **GAC2:native-full-Q-inverse-program**
(verified complete inverse constitutive map on held-out inputs). -/
@[ledger "GAC2:native-full-Q-inverse-program"]
theorem inverseQLaw : Statement.inverseQLaw := by
  exact ⟨complete_original_Q_inverse_program,
    inverse_program_solves_both,
    complete_Q_inverse_matched_costs,
    complete_Q_inverse_weighted_saving,
    complete_inverse_code_guards⟩

/-! ## Non-vacuity -/
example : nativeConstitutiveQ (fullFaceProgram true true (fun _ _ => 1 : NativeFace ℚ)) =
    (fun _ _ => 1) := (inverse_program_solves_both true _).1

end Artform.Scores.GravityBridge.Native.RetroCertificates
