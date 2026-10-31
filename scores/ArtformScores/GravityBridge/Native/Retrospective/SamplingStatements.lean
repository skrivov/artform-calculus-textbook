import ArtformScores.GravityBridge.Native.Retrospective.SamplingDefs
/-! # Centered and physical first-order connection sampling -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
/-- **GAC2:connection-first-order-sampling**
(centered and physical first-order connection sampling). -/
@[ledger "GAC2:connection-first-order-sampling"]
def samplingLaw : Prop :=
  ∀ (K V W : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    (∀ (L : W →ₗ[K] W) (q : W × W),
    physicalJet L (centerJet L q) = q) ∧
    (∀ (L : W →ₗ[K] W) (q : W × W),
    centerJet L (physicalJet L q) = q) ∧
    (∀ (L : W →ₗ[K] W) (Omega : V →ₗ[K] W)
    (E : W →ₗ[K] W) (R : V →ₗ[K] W) (kappa : K) (f : V),
    physicalJet L (Omega f, -(2 * kappa) • E (R f)) =
      (Omega f, sampledFirstReturn L Omega E R kappa f)) ∧
    (∀ (L : W →ₗ[K] W) (Omega : V →ₗ[K] W)
    (E : W →ₗ[K] W) (R : V →ₗ[K] W) (kappa : K) (f : V),
    (centerJet L (Omega f, sampledFirstReturn L Omega E R kappa f)).2 =
      -(2 * kappa) • E (R f))
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
