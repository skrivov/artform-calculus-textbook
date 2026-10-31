import ArtformScores.GravityBridge.Native.Retrospective.FirstContactStatements
/-! # The full signed inverse in the first connection contact -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Matrix
lemma full_inverse_source (z : ℚ) : polynomialInverse (1 / 101) *ᵥ connectionSource z =
    (-101 / 103 : ℚ) • connectionSource z := by
  change polynomialInverse kappa *ᵥ connectionSource z = _
  rw [native_inverse_polynomial]
  ext i
  fin_cases i <;>
    norm_num [connectionSource, curvatureBlock, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Fin.sum_univ_succ] <;>
    ring
lemma full_first_contact (z : ℚ) :
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) =
      (2 / 103 : ℚ) • connectionSource z := by
  rw [full_inverse_source]
  module
lemma first_contact_curvature_error (z : ℚ) :
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) -
      curvatureOnlyPreparation (1 / 101) z = (-4 / 10403 : ℚ) • connectionSource z := by
  rw [full_first_contact]
  unfold curvatureOnlyPreparation
  module
lemma first_contact_error_zero_iff (z : ℚ) :
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) =
      curvatureOnlyPreparation (1 / 101) z ↔ z = 0 := by
  constructor
  · intro h
    have he := first_contact_curvature_error z
    rw [h, sub_self] at he
    have hz := congrArg (fun v : Fin 3 → ℚ => v 1) he
    simp [connectionSource] at hz
    linarith
  · rintro rfl
    rw [full_first_contact]
    ext i
    fin_cases i <;> norm_num [connectionSource, curvatureOnlyPreparation]
/-- **GAC2:full-inverse-first-contact**
(the full signed inverse in the first connection contact). -/
@[ledger "GAC2:full-inverse-first-contact"]
theorem firstContactLaw : Statement.firstContactLaw := by
  exact ⟨full_inverse_source,
    full_first_contact,
    first_contact_curvature_error,
    first_contact_error_zero_iff⟩
/-! ## Non-vacuity -/
example : ((-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource 1) -
    curvatureOnlyPreparation (1 / 101) 1) 1 = 4 / 10403 := by
  rw [first_contact_curvature_error]
  norm_num [connectionSource]
end Artform.Scores.GravityBridge.Native.Retrospective
