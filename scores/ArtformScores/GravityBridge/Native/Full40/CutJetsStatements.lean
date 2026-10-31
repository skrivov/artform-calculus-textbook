import ArtformScores.GravityBridge.Native.Full40.CutJetsDefs
/-! # Exact coframe value and velocity recovery and its connection limit -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:coframe-cut-value-velocity**
(exact coframe value and velocity recovery and its connection limit). -/
@[ledger "GAC2:coframe-cut-value-velocity"]
def cutJetsLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (F G : Fin 2 → Frame K)
    (_hm : ∀ n, metricVariation (F n) = metricVariation (G n))
    (_hw : ∀ n, coframeLorentz (F n) = coframeLorentz (G n)),
    F = G) ∧
    (∀ (F G : Fin 2 → Frame K),
    F = G ↔
    (∀ n, metricVariation (F n) = metricVariation (G n)) ∧
    (∀ n, coframeLorentz (F n) = coframeLorentz (G n))) ∧
    (metricVariation (lie (![1, 0, 0, 0, 0, 0] : Biv ℚ)) =
      metricVariation (0 : Frame ℚ) ∧
    lie (![1, 0, 0, 0, 0, 0] : Biv ℚ) ≠ 0) ∧
    (∃ Q R : Fin 2 → Full ℚ, (∀ n, (Q n).1 = (R n).1) ∧
      (Q 0).2 ≠ (R 0).2)
end Artform.Scores.GravityBridge.Native.Full40.Statement
