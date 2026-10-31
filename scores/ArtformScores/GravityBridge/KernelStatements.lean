import ArtformScores.GravityBridge.KernelDefs

/-! # Literal finite processing statements -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:finite-processing** (complete processing of finite source kernels).
All density, preparation and boundary data transform. Source dependence is
pointwise; no differentiability or infinite integral is assumed. -/
@[ledger "GAC:finite-processing"]
def finiteProcessing : Prop :=
  (∀ (X X' Y Y' Z Z' K : Type) [Fintype Y] [Fintype Y'] [CommSemiring K]
    (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : Y → K) (a : BoundaryKernel X Y K) (b : BoundaryKernel Y Z K),
    weightedCompose (transportFunction eY μ) (transportKernel eX eY a)
        (transportKernel eY eZ b) =
      transportKernel eX eZ (weightedCompose μ a b)) ∧
  (∀ (J X X' Y Y' K : Type)
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y'] [CommSemiring K]
    (eX : J → X ≃ X') (eY : J → Y ≃ Y')
    (μ : J → X → K) (ν : J → Y → K) (ψ : J → X → K)
    (a : J → BoundaryKernel X Y K) (φ : J → Y → K) (j : J),
    closedAmplitude (transportFunction (eX j) (μ j)) (transportFunction (eY j) (ν j))
        (transportFunction (eX j) (ψ j)) (transportKernel (eX j) (eY j) (a j))
        (transportFunction (eY j) (φ j)) =
      closedAmplitude (μ j) (ν j) (ψ j) (a j) (φ j))

end Artform.Scores.GravityBridge.Statement
