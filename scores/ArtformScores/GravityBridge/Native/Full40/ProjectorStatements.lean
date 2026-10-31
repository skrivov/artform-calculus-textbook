import ArtformScores.GravityBridge.Native.Full40.ProjectorDefs
/-! # The coframe Lorentz projector with compatible sources -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:coframe-projector-compatible-sources**
(the coframe lorentz projector with compatible sources). -/
@[ledger "GAC2:coframe-projector-compatible-sources"]
def projectorLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [Field K] [CharZero K],
    (∀ (w : Biv K),
    coframeLorentz (lie w) = w) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K),
    lorentzReadout (gaugeField d w) = w) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K),
    lorentzReadout (projectField d q) = 0) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K),
    projectField d (projectField d q) = projectField d q) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K),
    projectField d (gaugeField d w) = 0) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K),
    projectField d q = q ↔ lorentzReadout q = 0) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K),
    projectField d q = 0 ↔ ∃ w, q = gaugeField d w) ∧
    (∀ (d : Fin 4 → X) (J : NativeField X K →ₗ[K] K),
    (∀ w, J (gaugeField d w) = 0) ↔ ∀ q, J (projectField d q) = J q) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K)
    (x : X) (i j : Fin 4),
    metricVariation (projectField d q x).1 i j =
      metricVariation (q x).1 i j) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K),
    fullForce d kappa (projectField d q) = fullForce d kappa q) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K),
    ∀ w, firstVariationMap d kappa q (gaugeField d w) = 0)
end Artform.Scores.GravityBridge.Native.Full40.Statement
