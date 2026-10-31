import ArtformScores.GravityBridge.Native.GreenComposition.FortyContactsStatements

/-! # Literal16+24 scaling and all current contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators
open Full40

variable {K : Type*} [Field K] [CharZero K]

open Full40
omit [CharZero K] in
lemma literal_physical_split (h : K) (x : Full K) :
    physicalForty h x = frameOnly x - h • connectionOnly x := by
  ext <;> simp [physicalForty, frameOnly, connectionOnly]

omit [CharZero K] in
lemma forty_current_all_contacts (B : (Full K) →ₗ[K] (Full K) →ₗ[K] K) (h : K) (x y : Full K) :
    B (physicalForty h x) (physicalForty h y) =
      B (frameOnly x) (frameOnly y) - h * B (frameOnly x) (connectionOnly y)-
      h * B (connectionOnly x) (frameOnly y) + h ^ 2 * B (connectionOnly x) (connectionOnly y) := by
  rw [literal_physical_split, literal_physical_split]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

omit [CharZero K] in
lemma complete_original_gram (x y : Full K) :
    originalCoordinateDual x (coordinateGram y) =
      (∑ i, ∑ j, eta i * x.1 i j * y.1 i j) + (∑ i, bivPair (x.2 i) (y.2 i)) := by
  simp [originalCoordinateDual, Fintype.sum_prod_type, pack, coordinateGram,
    frameGram, gramConvert, bivPair, mul_left_comm, mul_assoc]

omit [CharZero K] in
lemma literal_measure_factor (h cut pairing : K) : h * (h ^ 3 * pairing) * cut = h ^ 4 *
  (pairing * cut) := by ring

/-- **GAC2:literal-full40-current-contacts**
(literal16+24 scaling and all current contacts). -/
@[ledger "GAC2:literal-full40-current-contacts"]
theorem fortyContactsLaw : Statement.fortyContactsLaw := by
  intro K _ _
  exact ⟨literal_physical_split,
    forty_current_all_contacts,
    complete_original_gram,
    literal_measure_factor⟩

/-! ## Non-vacuity -/
example : bivPair (![1, 0, 0, 0, 0, 0] : Biv ℚ) ![1, 0, 0, 0, 0, 0] = -1 := by
  norm_num [bivPair, bivSign, Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.GreenComposition
