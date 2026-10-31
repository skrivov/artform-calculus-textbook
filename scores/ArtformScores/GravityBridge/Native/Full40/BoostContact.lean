import ArtformScores.GravityBridge.Native.Full40.BoostContactStatements
/-! # The original temporal boost quarter-contact -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
lemma third_jet_boost (n : Fin 3 → K) (a : K) :
    coordinateLorentz (lowerThirdJet n a) =
      ![n 0 * a / 2, n 1 * a / 2, n 2 * a / 2, 0, 0, 0] := by
  ext j
  fin_cases j <;> simp [coordinateLorentz, lowerThirdJet]
lemma temporal_contact_quarter (n : Fin 3 → K) (a : K) :
    temporalBoostContact n a = ![n 0 * a / 4, n 1 * a / 4, n 2 * a / 4, 0, 0, 0] := by
  rw [temporalBoostContact, third_jet_boost]
  ext j
  fin_cases j <;> simp <;> ring
lemma temporal_contact_zero_iff (n : Fin 3 → K) (hn : ∃ j, n j ≠ 0) (a : K) :
    temporalBoostContact n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rcases hn with ⟨j, hj⟩
    have hb : n j * a / 4 = 0 := by
      have he := congrArg (fun z : Biv K => z (Fin.castAdd 3 j)) h
      rw [temporal_contact_quarter] at he
      fin_cases j <;> simpa using he
    have hab : n j * a = 0 := (div_eq_zero_iff).mp hb |>.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hab).resolve_left hj
  · rintro rfl
    rw [temporal_contact_quarter]
    simp
lemma native_contact_sign (h : K) (n : Fin 3 → K) (a : K) :
    -h • temporalBoostContact n a =
      ![-h * n 0 * a / 4, -h * n 1 * a / 4, -h * n 2 * a / 4, 0, 0, 0] := by
  rw [temporal_contact_quarter]
  ext j
  fin_cases j <;> simp <;> ring
omit [CharZero K] in
lemma zero_cut_inverse_contact (E C : Biv K →ₗ[K] Biv K) (z : Biv K) (hz : z = 0)
    (n : Fin 3 → K) (a kappa : K) :
    temporalBoostContact n a - (2 * kappa) • E (C z) = temporalBoostContact n a := by
  simp [hz]
/-- **GAC2:temporal-boost-quarter-contact**
(the original temporal boost quarter-contact). -/
@[ledger "GAC2:temporal-boost-quarter-contact"]
theorem boostContactLaw : Statement.boostContactLaw := by
  intro K _ _
  exact ⟨third_jet_boost,
    temporal_contact_quarter,
    temporal_contact_zero_iff,
    native_contact_sign,
    zero_cut_inverse_contact⟩
/-! ## Non-vacuity -/
example : temporalBoostContact (![1, 0, 0] : Fin 3 → ℚ) 4 = ![1, 0, 0, 0, 0, 0] := by
  rw [temporal_contact_quarter]
  norm_num
example : (-1 / 2 : ℚ) • temporalBoostContact (![1, 0, 0] : Fin 3 → ℚ) 4 = ![-1 / 2, 0, 0, 0, 0, 0] 
    := by
  rw [temporal_contact_quarter]
  norm_num
end Artform.Scores.GravityBridge.Native.Full40
