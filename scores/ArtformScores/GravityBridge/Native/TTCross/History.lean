import ArtformScores.GravityBridge.Native.TTCross.HistoryStatements

/-! # Bounded native coordinate history does not determine preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



noncomputable section

lemma bounded_history_derivatives (a t : ℝ) :
    HasDerivAt (fun s => boundedHomogeneousJet a s 0) (boundedHomogeneousJet a t 1) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 1) (boundedHomogeneousJet a t 2) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 2) (boundedHomogeneousJet a t 3) t ∧
    HasDerivAt (fun s => boundedHomogeneousJet a s 3) (boundedHomogeneousJet a t 4) t := by
  have hc := (Real.hasDerivAt_cos (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have hs := (Real.hasDerivAt_sin (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  constructor
  · convert hc using 1 <;> dsimp [boundedHomogeneousJet, Function.comp_def]
    ring
  constructor
  · convert hs.const_mul (-a) using 1 <;>
      dsimp [boundedHomogeneousJet, Function.comp_def]
    ring
  constructor
  · convert hc.const_mul (-a ^ 2) using 1 <;>
      dsimp [boundedHomogeneousJet, Function.comp_def]
    ring
  · convert hs.const_mul (a ^ 3) using 1 <;>
      dsimp [boundedHomogeneousJet, Function.comp_def]
    ring

lemma bounded_history_actual_row (a t : ℝ) : scalarRow a (boundedHomogeneousJet a t) = 0 := by
  norm_num [scalarRow, boundedHomogeneousJet]
  ring

lemma globally_bounded_history (a t : ℝ) : |boundedHomogeneousJet a t 0| ≤ 1 := by
  exact Real.abs_cos_le_one (a * t)

lemma same_forcing_different_history (a : ℝ) (x : Fin 5 → ℝ) :
    scalarRow a (x + boundedHomogeneousJet a 0) = scalarRow a x ∧
      (x + boundedHomogeneousJet a 0) 0 ≠ x 0 := by
  constructor
  · have hh := bounded_history_actual_row a 0
    simp only [scalarRow, Pi.add_apply] at *
    linear_combination hh
  · norm_num [boundedHomogeneousJet]

/-- **GAC2:native-bounded-history-ambiguity**
(bounded native coordinate history does not determine preparation). -/
@[ledger "GAC2:native-bounded-history-ambiguity"]
theorem historyLaw : Statement.historyLaw := by
  exact ⟨bounded_history_derivatives,
    bounded_history_actual_row,
    globally_bounded_history,
    same_forcing_different_history⟩

/-! ## Non-vacuity -/
example : scalarRow 3 (boundedHomogeneousJet 3 0) = 0 ∧ boundedHomogeneousJet 3 0 0 = 1 :=
  ⟨bounded_history_actual_row _ _, by norm_num [boundedHomogeneousJet]⟩
end

end Artform.Scores.GravityBridge.Native.TTCross
