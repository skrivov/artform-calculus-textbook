import ArtformScores.NonabelianGravity.AnalyticStatements
import ArtformScores.NonabelianGravity.GeometryPreflight

/-! # Checked analytic submissions with their exact, unreduced scope -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity

/-- **NGB:analytic-interpretation** (actual analytic form evaluations). -/
@[ledger "NGB:analytic-interpretation"]
theorem analyticInterpretation : Statement.analyticInterpretation := by
  refine ⟨?_,Maurer.twoValue_wedge,?_,Maurer.witnessCurve_norm,Maurer.analytic_baseline_value⟩
  · intro c g x t hc hd
    exact Maurer.curveWord_derivative c g x t hc hd
  · intro c d g x y t hc hd hcx hdy
    exact ⟨Maurer.analyticTwiceOmega_value c d g x y t hc hd hcx hdy,
      Maurer.analytic_pullbacks c d g x y t hc hd hcx hdy⟩

/-- **NGB:stabilizer-preservation** (unchanged full stabilizer). -/
@[ledger "NGB:stabilizer-preservation"]
theorem stabilizerPreservation : Statement.stabilizerPreservation := by
  intro G _ w s
  exact ⟨run_injective w,run_stabilizer w s⟩

/-- **NGB:geometric-preflight** (actual Gauss-valid unit-quaternion control). -/
@[ledger "NGB:geometric-preflight"]
theorem geometricPreflight : Statement.geometricPreflight := by
  refine ⟨no_four_valent_vertex,cycleState_gauss quaternionI,?_,cycle_unit_norm,
    kicked_cycle_unit_norm,impulse_class_changes.1,impulse_class_changes.2,impulse_not_conjugate⟩
  rw [Gauss,kick_defect]
  exact cycleState_gauss quaternionI

/-! ## Non-vacuity -/
example : Maurer.analyticTwiceOmega (Maurer.witnessCurve 0) (Maurer.witnessCurve 7) 0
    Maurer.original ≠ 0 := by rw [Maurer.analytic_baseline_value]; norm_num
example : stabilizer (tick (cycleState quaternionI))=stabilizer (cycleState quaternionI) :=
  run_stabilizer _ _
example : ∀ v, (star v).length<4 := by decide +kernel
end Artform.Scores.NonabelianGravity
