import ArtformScores.GravityBridge.Native.Retrospective.SchurSource
/-! # Source-dependent stationary action and auxiliary reconstruction -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
def sourceAction (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) (a : W) : K :=
  A f f / 2 + B f a + D a a / 2 - u f - v a
def returnedAuxiliary (B : V →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (v : W →ₗ[K] K) (f : V) : W := E (v - B f)
def sourceEffective (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (E : (W →ₗ[K] K) →ₗ[K] W) (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) : K :=
  A f f / 2 - u f - (v - B f) (E (v - B f)) / 2
end Artform.Scores.GravityBridge.Native.Retrospective
