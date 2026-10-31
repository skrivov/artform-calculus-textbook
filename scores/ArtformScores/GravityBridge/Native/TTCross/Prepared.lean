import ArtformScores.GravityBridge.Native.TTCross.PreparedStatements

/-! # Original paired-axis TT graph with its complete preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

lemma actual_prepared_graph (a : K) (ha : a ≠ 0) (u : Fin 2 → K) :
    forcedJetStep a u (preparedJet a u) = preparedJet a (pairedTTStep a u) := by
  ext i
  fin_cases i <;> norm_num [forcedJetStep, preparedJet, pairedTTStep]
  all_goals field_simp
  all_goals ring

omit [CharZero K] in
lemma prepared_jet_read (a : K) (u : Fin 2 → K) :
    ![preparedJet a u 1, preparedJet a u 2] = u := by
  ext i
  fin_cases i <;> rfl

omit [CharZero K] in
lemma prepared_graph_injective (a : K) : Function.Injective (preparedJet (K := K) a) := by
  intro u v h
  have hread := congrArg (fun x : Fin 4 → K => ![x 1, x 2]) h
  simpa only [prepared_jet_read] using hread

omit [CharZero K] in
lemma zero_preparation_intersection (a : K) (u : Fin 2 → K) :
    preparedJet a u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · exact congrFun h 1
    · exact congrFun h 2
  · intro h
    subst u
    ext i
    fin_cases i <;> simp [preparedJet]

/-- **GAC2:native-paired-tt-preparation**
(original paired-axis tt graph with its complete preparation). -/
@[ledger "GAC2:native-paired-tt-preparation"]
theorem preparedLaw : Statement.preparedLaw := by
  intro K _ _
  exact ⟨actual_prepared_graph,
    prepared_jet_read,
    prepared_graph_injective,
    zero_preparation_intersection⟩

/-! ## Non-vacuity -/
example : preparedJet (1 : ℚ) ![0, 1] = ![-1 / 2, 0, 1, 0] := by
  norm_num [preparedJet]

end Artform.Scores.GravityBridge.Native.TTCross
