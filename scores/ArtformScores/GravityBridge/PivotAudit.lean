import ArtformScores.GravityBridge.PivotAuditStatements
/-! # Native guarded pivot substitution -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native.R2
lemma pivot_normal_iff (l n : Fin 4 → ℝ) (nu k : ℝ) (i : Fin 4) (hi : l i ≠ 0) :
    (pivotLatitude l n i) ^ 2 + nu * pivotLatitude l n i + k = 0 ↔
      pivotNormal l n nu k i = 0 := by
  have he : (l i) ^ 2 * ((pivotLatitude l n i) ^ 2 + nu * pivotLatitude l n i + k) =
      pivotNormal l n nu k i := by
    dsimp [pivotLatitude, pivotNormal]
    field_simp
    ring
  rw [← he, mul_eq_zero]
  simp [pow_ne_zero 2 hi]
lemma guarded_pivot_substitution (l n : Fin 4 → ℝ) (nu k : ℝ) (i : Fin 4)
    (hi : l i ≠ 0) (P : ℝ → Prop) :
    (∃ s : ℝ, s ^ 2 + nu * s + k = 0 ∧ (∀ j, l j * s + n j = 0) ∧ P s) ↔
      pivotNormal l n nu k i = 0 ∧ (∀ j, l i * n j - l j * n i = 0) ∧
        P (pivotLatitude l n i) := by
  constructor
  · rintro ⟨s, hN, hr, hP⟩
    have hs : s = pivotLatitude l n i := by
      dsimp [pivotLatitude]
      apply (eq_div_iff hi).mpr
      linarith [hr i]
    subst s
    exact ⟨(pivot_normal_iff l n nu k i hi).mp hN,
      ((pivot_case l n i hi _).mp hr).2, hP⟩
  · rintro ⟨hN, hm, hP⟩
    refine ⟨pivotLatitude l n i, (pivot_normal_iff l n nu k i hi).mpr hN, ?_, hP⟩
    apply (pivot_case l n i hi _).mpr
    refine ⟨?_, hm⟩
    dsimp [pivotLatitude]
    field_simp
    ring
lemma native_guarded_pivot (R a G : ℝ) (i : Fin 4)
    (hi : ell a G (rowPolys R a G i) ≠ 0) (P : ℝ → Prop) :
    (∃ s : ℝ, normal a G s = 0 ∧ (∀ j, rows R a G s j = 0) ∧ P s) ↔
      pivotNormal (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j))
        (5 - 8 * a + 6 * G) (2 * (2 - 3 * a) ^ 2) i = 0 ∧
      (∀ j, ell a G (rowPolys R a G i) * remainderConst a G (rowPolys R a G j) -
        ell a G (rowPolys R a G j) * remainderConst a G (rowPolys R a G i) = 0) ∧
      P (pivotLatitude (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j)) i) := by
  have hg := guarded_pivot_substitution (fun j => ell a G (rowPolys R a G j))
    (fun j => remainderConst a G (rowPolys R a G j))
    (5 - 8 * a + 6 * G) (2 * (2 - 3 * a) ^ 2) i hi P
  rw [← hg]
  constructor
  · rintro ⟨s, hN, hr, hP⟩
    exact ⟨s, hN, fun j => (row_remainder_iff R a G s hN j).mp (hr j), hP⟩
  · rintro ⟨s, hN, hr, hP⟩
    have hn : normal a G s = 0 := hN
    exact ⟨s, hn, fun j => (row_remainder_iff R a G s hn j).mpr (hr j), hP⟩
lemma native_signed_guarded_pivot (q R a G gamma : ℝ)
    (hq : q ^ 2 = 103 / 2) (hg : gamma ^ 2 = G) (hq0 : q ≠ 0) (hg0 : gamma ≠ 0)
    (i : Fin 4) (hi : ell a G (rowPolys R a G i) ≠ 0) (P : ℝ → Prop) :
    (∃ s : ℝ, normal a G s = 0 ∧
      (originalJ q R a gamma s = 0 ∧ originalJ q R a (-gamma) s = 0) ∧ P s) ↔
      pivotNormal (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j))
        (5 - 8 * a + 6 * G) (2 * (2 - 3 * a) ^ 2) i = 0 ∧
      (∀ j, ell a G (rowPolys R a G i) * remainderConst a G (rowPolys R a G j) -
        ell a G (rowPolys R a G j) * remainderConst a G (rowPolys R a G i) = 0) ∧
      P (pivotLatitude (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j)) i) := by
  rw [← native_guarded_pivot R a G i hi P]
  constructor
  · rintro ⟨s, hN, hj, hP⟩
    exact ⟨s, hN, (signed_trace_iff q R a G gamma s hq hg hN hq0 hg0).mp hj, hP⟩
  · rintro ⟨s, hN, hr, hP⟩
    exact ⟨s, hN, (signed_trace_iff q R a G gamma s hq hg hN hq0 hg0).mpr hr, hP⟩
/-- **GAC:guarded-pivot-substitution** (native guarded pivot substitution). -/
@[ledger "GAC:guarded-pivot-substitution"]
theorem pivotAuditLaw : Statement.pivotAuditLaw := by
  exact ⟨pivot_normal_iff,
    guarded_pivot_substitution,
    native_guarded_pivot,
    native_signed_guarded_pivot⟩
/-! ## Non-vacuity -/
example : ell 1 (1 / 36) (rowPolys 1 1 (1 / 36) 0) ≠ 0 := by
  rw [Native.R2.certificate_ell0]
  norm_num [Native.R2.Certificate.g4]
example : (∃ s : ℝ, s ^ 2 - 1 = 0 ∧
    (∀ _j : Fin 4, (1 : ℝ) * s + (-1) = 0) ∧ 0 < s) := by
  exact ⟨1, by norm_num, by intro _j; norm_num, by norm_num⟩
end
end Artform.Scores.GravityBridge
