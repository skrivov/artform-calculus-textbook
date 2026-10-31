import ArtformScores.GravityBridge.Native.Retrospective.SchurSourceStatements

/-! # Full source Schur reduction with exact reconstruction -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix

variable {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

lemma full_source_schur_equivalence (A : V →ₗ[R] V) (B : W →ₗ[R] V)
    (C : V →ₗ[R] W) (D E : W →ₗ[R] W)
    (hDE : ∀ w, D (E w) = w) (hED : ∀ w, E (D w) = w)
    (u f : V) (v a : W) :
    (A f + B a = u ∧ C f + D a = v) ↔
      (schurMap A B C E f = schurRightHandSide B E u v ∧
        a = reconstructAuxiliary C E v f) := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have ha : a = E (v - C f) := by
      have he : D a = v - C f := by rw [← hsecond]; abel
      rw [← hED a, he]
    refine ⟨?_, ha⟩
    rw [ha] at hfirst
    simp only [map_sub] at hfirst
    change A f - B (E (C f)) = u - B (E v)
    rw [← hfirst]
    abel
  · rintro ⟨hfirst, ha⟩
    rw [ha]
    constructor
    · change A f - B (E (C f)) = u - B (E v) at hfirst
      simp only [reconstructAuxiliary, map_sub]
      calc
        A f + (B (E v) - B (E (C f))) =
            (A f - B (E (C f))) + B (E v) := by abel
        _ = u := eq_sub_iff_add_eq.mp hfirst
    · rw [reconstructAuxiliary, hDE]
      abel

/-- **GAC2:guarded-schur-source-reconstruction**
(full source schur reduction with exact reconstruction). -/
@[ledger "GAC2:guarded-schur-source-reconstruction"]
theorem schurSourceLaw : Statement.schurSourceLaw := by
  intro R V W _ _ _ _ _
  exact full_source_schur_equivalence

/-! ## Non-vacuity -/
def schurToyScale (t : ℚ) : ℚ →ₗ[ℚ] ℚ := t • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
example : (∀ w : ℚ, schurToyScale 2 (schurToyScale (1 / 2) w) = w) ∧
    (∀ w : ℚ, schurToyScale (1 / 2) (schurToyScale 2 w) = w) ∧
    schurMap (schurToyScale 2) (schurToyScale 1) (schurToyScale 1)
      (schurToyScale (1 / 2)) 1 =
      schurRightHandSide (schurToyScale 1) (schurToyScale (1 / 2)) 4 5 ∧
    reconstructAuxiliary (schurToyScale 1) (schurToyScale (1 / 2)) 5 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    norm_num [schurToyScale]
    ring
  · intro w
    norm_num [schurToyScale]
    ring
  · norm_num [schurMap, schurRightHandSide, schurToyScale]
  · norm_num [reconstructAuxiliary, schurToyScale]

end Artform.Scores.GravityBridge.Native.Retrospective
