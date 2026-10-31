import ArtformScores.GravityBridge.Defs

/-! # Finite source kernels with preparation and measure data -/

namespace Artform.Scores.GravityBridge

/-- A finite boundary kernel, with its incoming argument first. -/
abbrev BoundaryKernel (X Y K : Type*) := X → Y → K

/-- Compose two kernels with the declared measure of the intermediate data. -/
def weightedCompose {X Y Z K : Type*} [Fintype Y] [CommSemiring K]
    (μ : Y → K) (a : BoundaryKernel X Y K) (b : BoundaryKernel Y Z K) :
    BoundaryKernel X Z K := fun x z => ∑ y, a x y * μ y * b y z

/-- Transport all values of a field or density under a finite bijection. -/
def transportFunction {X X' K : Type*} (e : X ≃ X') (f : X → K) : X' → K :=
  fun x' => f (e.symm x')

/-- Transport both declared boundary arguments of a kernel. -/
def transportKernel {X X' Y Y' K : Type*} (eX : X ≃ X') (eY : Y ≃ Y')
    (a : BoundaryKernel X Y K) : BoundaryKernel X' Y' K :=
  fun x' y' => a (eX.symm x') (eY.symm y')

/-- Close a kernel with its preparation, test and both boundary densities. -/
def closedAmplitude {X Y K : Type*} [Fintype X] [Fintype Y] [CommSemiring K]
    (μ : X → K) (ν : Y → K) (ψ : X → K) (a : BoundaryKernel X Y K)
    (φ : Y → K) : K :=
  ∑ x, ∑ y, ψ x * μ x * a x y * ν y * φ y

end Artform.Scores.GravityBridge
