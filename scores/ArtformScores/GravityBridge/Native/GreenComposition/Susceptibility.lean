import ArtformScores.GravityBridge.Native.GreenComposition.SusceptibilityStatements

/-! # Held-out source susceptibility and mixed boundary contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

lemma detail_source_susceptibility (c a b j dj : K) (hc : c ≠ 0) :
    sourceMiddle c a b (j + dj) - sourceMiddle c a b j = dj / (4 * c) ∧
    sourceEffective c a b (j + dj) - sourceEffective c a b j =
      -sourceMiddle c a b j * dj - dj ^ 2 / (8 * c) := by
  unfold sourceMiddle sourceEffective
  constructor <;> field_simp <;> ring

lemma source_endpoint_mixed_contact (c a b j da db dj : K) (hc : c ≠ 0) :
    sourceEffective c (a + da) (b + db) (j + dj) - sourceEffective c (a + da) (b + db) j-
      sourceEffective c a b (j + dj) + sourceEffective c a b j = -dj * (da + db) / 2 := by
  unfold sourceEffective
  field_simp
  ring

lemma source_contact_omission_changes_middle (c a b j : K) (hc : c ≠ 0) :
    sourceMiddle c a b j = (a + b) / 2 ↔ j = 0 := by
  unfold sourceMiddle
  constructor
  · intro he
    have hh : j / (4 * c) = 0 := by linear_combination he
    exact (div_eq_zero_iff).mp hh |>.resolve_right (mul_ne_zero (by norm_num) hc)
  · rintro rfl;simp

lemma heldout_response_contacts :
    sourceMiddle (1 / 101 : ℚ) (-1) 3 (5 / 101) - sourceMiddle (1 / 101) (-1) 3 (4 / 101) = 1 / 4 ∧
    sourceEffective (1 / 101 : ℚ) 0 5 (5 / 101) - sourceEffective (1 / 101) 0 5 (4 / 101)-
      sourceEffective (1 / 101) (-1) 3 (5 / 101) + sourceEffective (1 / 101) (-1) 3 (4 / 101) =
        -3 / 202 := by
  norm_num [sourceMiddle, sourceEffective]

/-- **GAC2:heldout-source-boundary-susceptibility**
(held-out source susceptibility and mixed boundary contacts). -/
@[ledger "GAC2:heldout-source-boundary-susceptibility"]
theorem susceptibilityLaw : Statement.susceptibilityLaw := by
  intro K _ _
  exact ⟨detail_source_susceptibility,
    source_endpoint_mixed_contact,
    source_contact_omission_changes_middle,
    heldout_response_contacts⟩

/-! ## Non-vacuity -/
example : sourceMiddle (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 := nonzero_source_heldout.1

end Artform.Scores.GravityBridge.Native.GreenComposition
