import ArtformScores.NonabelianGravity.QuantumCarrierDefs

/-! # Exact native coordinate selection before Ward reduction -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination Legendre BoundaryHistory
open Artform.Scores.GravityBridge.Native.Full40

lemma coordinate_injective : Function.Injective nativeCoordinate := by decide +kernel
lemma selected_range (k : Index 2) : selected k ↔ ∃ j : SliceIndex, nativeCoordinate j = k := by
  revert k
  decide +kernel

lemma embed_restrict_entry (q : Whole) (k : Index 2) :
    embed (restrict q) k = if selected k then q k else 0 := by
  classical
  by_cases hk : selected k
  · obtain ⟨j, hj⟩ := (selected_range k).mp hk
    rw [ite_eq_left hk]
    unfold embed restrict
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      have hc : nativeCoordinate i ≠ k := by
        intro hi
        exact hij (coordinate_injective (hi.trans hj.symm))
      simp [hc]
    · simp
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i _
    have hc : nativeCoordinate i ≠ k := by
      intro hi
      exact hk ((selected_range k).mpr ⟨i, hi⟩)
    simp [hc]

set_option maxHeartbeats 2000000 in
-- Only the six removed Ward entries and eight inactive entries require cancellation.
lemma normalized_in_slice (q : Whole) : embed (restrict (normalize q)) = normalize q := by
  funext k
  rw [embed_restrict_entry]
  rcases k with ⟨t, i⟩
  fin_cases t <;> fin_cases i <;>
    norm_num [selected, normalize, project_entry, gauge, gaugeParameter, gaugeFirst,
      gaugeSecond, lie]
end Artform.Scores.NonabelianGravity.QuantumComposition
