import ArtformScores.GravityBridge.Native.GreenComposition.AffineSourceStatements

/-! # Affine boundary composition retains independent source contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

lemma boundary_step_iff (c a b j pin pout : K) (hc : c ≠ 0) :
    boundaryStep c j (a, pin) = (b, pout) ↔
      pin = inputMomentum c a b j ∧ pout = outputMomentum c a b j := by
  simp only [boundaryStep, Prod.mk.injEq, inputMomentum, outputMomentum]
  constructor
  · rintro ⟨ha, hp⟩
    have he : pin = c * (b - a) + j / 2 := by field_simp at ha;linear_combination ha / 2
    constructor
    · exact he
    · rw [← hp, he];ring
  · rintro ⟨rfl, rfl⟩
    constructor
    · field_simp;ring
    · ring

lemma two_boundary_steps (c j l : K) (x : K × K) :
    boundaryStep c l (boundaryStep c j x) =
      (x.1 + (2 * x.2 - (3 * j + l) / 2) / c, x.2 - j - l) := by
  apply Prod.ext
  · dsimp only [boundaryStep]
    ring
  · rfl

lemma composed_source_square (c a m b j l : K) (hc : c ≠ 0) :
    sourceEffective c a m j + sourceEffective c m b l =
      composeEffective c a b j l + c * (m - composeMiddle c a b j l) ^ 2 := by
  unfold sourceEffective composeEffective composeMiddle
  field_simp
  ring

lemma composed_middle_force (c a m b j l : K) (hc : c ≠ 0) :
    outputMomentum c a m j = inputMomentum c m b l ↔ m = composeMiddle c a b j l := by
  unfold outputMomentum inputMomentum composeMiddle
  constructor
  · intro he
    have hr : (a + b) / 2 + (j + l) / (4 * c) = (2 * c * (a + b) + j + l) / (4 * c) := by
      field_simp [hc]
      ring
    rw [hr, eq_div_iff (mul_ne_zero (by norm_num : (4 : K) ≠ 0) hc)]
    linear_combination 2 * he
  · intro he;rw [he];field_simp;ring

lemma independent_source_contacts :
    composeEffective (1 / 101 : ℚ) 0 4 (2 / 101) (4 / 101) ≠ composeEffective (1 / 101 : ℚ) 0 4
      (6 / 101) 0 := by
  norm_num [composeEffective]

/-- **GAC2:source-complete-affine-boundary-composition**
(affine boundary composition retains independent source contacts). -/
@[ledger "GAC2:source-complete-affine-boundary-composition"]
theorem affineSourceLaw : Statement.affineSourceLaw := by
  intro K _ _
  exact ⟨boundary_step_iff,
    two_boundary_steps,
    composed_source_square,
    composed_middle_force,
    independent_source_contacts⟩

/-! ## Non-vacuity -/
example : boundaryStep (1 / 101 : ℚ) (4 / 101)
    (boundaryStep (1 / 101) (2 / 101) (0, 8 / 101)) = (11, 2 / 101) := by
  norm_num [boundaryStep]

end Artform.Scores.GravityBridge.Native.GreenComposition
