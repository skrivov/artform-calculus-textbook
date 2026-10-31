import ArtformScores.GravityBridge.Native.Retrospective.SamplingStatements
/-! # Centered and physical first-order connection sampling -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
omit [CharZero K] [AddCommGroup V] [Module K V] in
lemma sampling_inverse_left (L : W →ₗ[K] W) (q : W × W) :
    physicalJet L (centerJet L q) = q := by
  rcases q with ⟨q0, q1⟩
  simp [physicalJet, centerJet]
omit [CharZero K] [AddCommGroup V] [Module K V] in
lemma sampling_inverse_right (L : W →ₗ[K] W) (q : W × W) :
    centerJet L (physicalJet L q) = q := by
  rcases q with ⟨q0, q1⟩
  simp [physicalJet, centerJet]
omit [CharZero K] in
lemma physical_first_coefficient (L : W →ₗ[K] W) (Omega : V →ₗ[K] W)
    (E : W →ₗ[K] W) (R : V →ₗ[K] W) (kappa : K) (f : V) :
    physicalJet L (Omega f, -(2 * kappa) • E (R f)) =
      (Omega f, sampledFirstReturn L Omega E R kappa f) := by
  apply Prod.ext
  · rfl
  · dsimp [physicalJet, sampledFirstReturn]
    module
omit [CharZero K] in
lemma centering_recovers_contact (L : W →ₗ[K] W) (Omega : V →ₗ[K] W)
    (E : W →ₗ[K] W) (R : V →ₗ[K] W) (kappa : K) (f : V) :
    (centerJet L (Omega f, sampledFirstReturn L Omega E R kappa f)).2 =
      -(2 * kappa) • E (R f) := by
  dsimp [centerJet, sampledFirstReturn]
  module
/-- **GAC2:connection-first-order-sampling**
(centered and physical first-order connection sampling). -/
@[ledger "GAC2:connection-first-order-sampling"]
theorem samplingLaw : Statement.samplingLaw := by
  intro K V W _ _ _ _ _ _
  exact ⟨sampling_inverse_left,
    sampling_inverse_right,
    physical_first_coefficient,
    centering_recovers_contact⟩
/-! ## Non-vacuity -/
example : physicalJet (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (1, -2 / 101) = (1, 97 / 202) ∧
    centerJet (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (1, 97 / 202) = (1, -2 / 101) := by
  norm_num [physicalJet, centerJet]
end Artform.Scores.GravityBridge.Native.Retrospective
