import ArtformScores.GravityBridge.Native.NormalDivergence.PhysicalStatements

/-! # Complete normal divergence and the supplied physical third group -/

namespace Artform.Scores.GravityBridge.Native.NormalDivergence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
lemma complete_electric_cancellation (d : V3 K) (e et : M3 K) (c : V3 K) :
    dot3 d (normalVector d e et c) = primaryDivergence d c := by
  simp [dot3, normalVector, primaryDivergence, antisymmetricFaces, Fin.sum_univ_succ]
  ring

lemma pair_divergence_identity (d u : V3 K) :
    primaryDivergence d (curlFaces d u) = (1 / 101 : K) *
      ((∑ i, (d i) ^ 3) * dot3 d u - (∑ i, (d i) ^ 2) * dot3 (fun i => (d i) ^ 2) u) := by
  simp [primaryDivergence, curlFaces, dot3, Fin.sum_univ_succ]
  ring


lemma physical_h1_cut_row (p q s ji jj : K) :
    h1CutRow p q 0 0 (s * p) (s * q) (2 * ji) (2 * jj) =
      -((1 / 101 : K) * (101 / 97) * (101 / 103)) * (p * jj - q * ji) := by
  unfold h1CutRow
  ring

-- Literal physical second response, retaining all three spatial components.
lemma physical_second_moments : dot3 referenceD physicalJ2 = 0 ∧
    dot3 (fun i => (referenceD i) ^ 2) physicalJ2 = -268 * (101 / 39964 : ℂ) / 5 := by
  norm_num [dot3, referenceD, physicalJ2, Fin.sum_univ_succ]
  ring_nf
  norm_num

lemma complete_physical_third_group :
    primaryDivergence referenceD physicalH1Faces =
      3752 * (1 / 101 : ℂ) ^ 2 * (101 / 97) * (101 / 103) * (101 / 39964) / 5 := by
  norm_num [primaryDivergence, physicalH1Faces, curlFaces, referenceD, physicalJ2]
  ring_nf
  norm_num

/-- **GAC2:normal-divergence-physical-group**
(complete normal divergence and the supplied physical third group). -/
@[ledger "GAC2:normal-divergence-physical-group"]
theorem physicalLaw : Statement.physicalLaw := by
  intro K _ _
  exact ⟨complete_electric_cancellation,
    pair_divergence_identity,
    physical_h1_cut_row,
    physical_second_moments,
    complete_physical_third_group⟩

/-! ## Non-vacuity -/

example : physicalJ2 0 ≠ 0 ∧ primaryDivergence referenceD physicalH1Faces ≠ 0 := by
  constructor
  · norm_num [physicalJ2]
  · rw [complete_physical_third_group]
    norm_num

end Artform.Scores.GravityBridge.Native.NormalDivergence
