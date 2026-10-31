import ArtformScores.GravityBridge.Native.Full40.Quadratic
/-! # Centered and physical first-order connection sampling -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
def centerJet (L : W →ₗ[K] W) (q : W × W) : W × W :=
  (q.1, q.2 - (1 / 2 : K) • L q.1)
def physicalJet (L : W →ₗ[K] W) (q : W × W) : W × W :=
  (q.1, q.2 + (1 / 2 : K) • L q.1)
def sampledFirstReturn (L : W →ₗ[K] W) (Omega : V →ₗ[K] W)
    (E : W →ₗ[K] W) (R : V →ₗ[K] W) (kappa : K) (f : V) : W :=
  (1 / 2 : K) • L (Omega f) - (2 * kappa) • E (R f)
end Artform.Scores.GravityBridge.Native.Retrospective
