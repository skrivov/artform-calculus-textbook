import ArtformScores.GravityBridge.Native.Full40.SplitDefs
/-! # The exact metric and coframe Lorentz isomorphism -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:metric-coframe-lorentz-isomorphism**
(the exact metric and coframe lorentz isomorphism). -/
@[ledger "GAC2:metric-coframe-lorentz-isomorphism"]
def splitLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (F : Frame K),
    coframeReconstruct (metricVariation F) (coframeLorentz F) = F) ∧
    (∀ (m : symmetricFrames (K := K)) (w : Biv K),
    metricVariation (coframeReconstruct m.val w) = m.val) ∧
    (∀ (m : symmetricFrames (K := K)) (w : Biv K),
    coframeLorentz (coframeReconstruct m.val w) = w) ∧
    (Nonempty (Frame K ≃ₗ[K] (symmetricFrames (K := K) × Biv K))) ∧
    (∀ (F G : Frame K)
    (_hm : metricVariation F = metricVariation G) (_hw : coframeLorentz F = coframeLorentz G),
    F = G)
end Artform.Scores.GravityBridge.Native.Full40.Statement
