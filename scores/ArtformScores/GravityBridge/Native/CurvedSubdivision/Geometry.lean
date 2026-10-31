import ArtformScores.GravityBridge.Native.CurvedSubdivision.GeometryStatements

/-! # Actual sourced two-cube incidence and inherited coframes -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



lemma actual_cell_counts :
    (cubeCount 0, cubeCount 1, cubeCount 2, cubeCount 3, cubeCount 4) = (16, 32, 24, 8, 1) ∧
    (splitCount 0, splitCount 1, splitCount 2, splitCount 3, splitCount 4) = (24, 52, 42, 15, 2)
      := by
  decide +kernel

lemma actual_half_chart_and_volume (K : Type) [Field K] [CharZero K] (h b : K) :
    inheritedCoframe h b * Matrix.diagonal ![1 / 2, 1, 1, 1] = inheritedCoframe (h / 2) b ∧
    (inheritedCoframe (h / 2) b).det + (inheritedCoframe (h / 2) b).det =
      (inheritedCoframe h b).det :=
  ⟨actual_half_chart h b, actual_child_volume h b⟩

lemma actual_shared_facet (K : Type) [Field K] [CharZero K] (h b : K) (i : Fin 3) (a : Fin 4) :
    inheritedCoframe (h / 2) b a i.succ = inheritedCoframe h b a i.succ :=
  intrinsic_shared_columns h b i a

/-- **GAC2:native-two-cube-incidence**
(actual sourced two-cube incidence and inherited coframes). -/
@[ledger "GAC2:native-two-cube-incidence"]
theorem geometryLaw : Statement.geometryLaw := by
  exact ⟨actual_cell_counts,
    actual_half_chart_and_volume,
    actual_shared_facet⟩

/-! ## Non-vacuity -/
example : cubeCount 4 = 1 ∧ splitCount 4 = 2 := by decide +kernel

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
