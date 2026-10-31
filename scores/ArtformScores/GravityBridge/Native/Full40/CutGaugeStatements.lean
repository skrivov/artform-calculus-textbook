import ArtformScores.GravityBridge.Native.Full40.CutGaugeDefs
/-! # Six-component native cut gauge readouts and their forward frame cost -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:native-cut-gauge-readouts**
(six-component native cut gauge readouts and their forward frame cost). -/
@[ledger "GAC2:native-cut-gauge-readouts"]
def cutGaugeLaw : Prop :=
  ∀ (X : Type) [AddCommGroup X],
    (∀ (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ) (x : X),
    (cutGauge h d c (0, x)).1 = 0) ∧
    (∀ (h : ℝ) (_hh : h ≠ 0) (d : Fin 3 → X)
    (c : X → Biv ℝ) (x : X),
    (cutGauge h d c (0, x)).2 0 = c x) ∧
    (∀ (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (x : X) (i : Fin 3),
    (cutGauge h d c (0, x)).2 i.succ = 0) ∧
    (∀ (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (x : X) (i j : Fin 4),
    HasDerivAt (fun t : ℝ => (cutGauge h d c (t, x)).1 i j) 0 0) ∧
    (∀ (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (tx : ℝ × X) (i j : Fin 4),
    metricVariation (cutGauge h d c tx).1 i j = 0) ∧
    (∀ (h : ℝ) (_hh : h ≠ 0) (d : Fin 3 → X)
    (c : X → Biv ℝ) (x : X),
    (cutGauge h d c (h, x)).1 = lie (c x)) ∧
    (∀ (h : ℝ) (_hh : h ≠ 0)
    (d : Fin 3 → X) (c : X → Biv ℝ) (x : X)
    (_hc : (cutGauge h d c (h, x)).1 = 0),
    c x = 0)
end Artform.Scores.GravityBridge.Native.Full40.Statement
