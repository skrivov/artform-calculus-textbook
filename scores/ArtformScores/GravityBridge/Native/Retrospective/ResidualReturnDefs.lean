import ArtformScores.GravityBridge.Native.Retrospective.SchurSource
/-! # The exact independent connection return retains its residual -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Ring K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
def connectionResidual (C : V →ₗ[K] W) (D : W →ₗ[K] W) (u : V) (v : W) : W := C u + D v
def connectionGraph (C : V →ₗ[K] W) (E : W →ₗ[K] W) : V →ₗ[K] W := -(E.comp C)
end Artform.Scores.GravityBridge.Native.Retrospective
