import ArtformScores.GravityBridge.KernelStatements

/-! # Finite processing transforms sources preparations and measures together -/

namespace Artform.Scores.GravityBridge

theorem weightedCompose_transport {X X' Y Y' Z Z' K : Type*}
    [Fintype Y] [Fintype Y'] [CommSemiring K]
    (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z')
    (μ : Y → K) (a : BoundaryKernel X Y K) (b : BoundaryKernel Y Z K) :
    weightedCompose (transportFunction eY μ) (transportKernel eX eY a)
        (transportKernel eY eZ b) =
      transportKernel eX eZ (weightedCompose μ a b) := by
  funext x' z'
  unfold weightedCompose transportFunction transportKernel
  exact (Fintype.sum_equiv eY _ _ (fun y => by simp)).symm

theorem closedAmplitude_transport {X X' Y Y' K : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y'] [CommSemiring K]
    (eX : X ≃ X') (eY : Y ≃ Y') (μ : X → K) (ν : Y → K) (ψ : X → K)
    (a : BoundaryKernel X Y K) (φ : Y → K) :
    closedAmplitude (transportFunction eX μ) (transportFunction eY ν)
        (transportFunction eX ψ) (transportKernel eX eY a) (transportFunction eY φ) =
      closedAmplitude μ ν ψ a φ := by
  unfold closedAmplitude transportFunction transportKernel
  apply (Fintype.sum_equiv eX _ _ ?_).symm
  intro x
  simp only [Equiv.symm_apply_apply]
  exact Fintype.sum_equiv eY _ _ (fun y => by simp)

/-- **GAC:finite-processing** (complete processing of finite source kernels). -/
@[ledger "GAC:finite-processing"]
theorem finiteProcessing : Statement.finiteProcessing := by
  constructor
  · intro X X' Y Y' Z Z' K _ _ _ eX eY eZ μ a b
    exact weightedCompose_transport eX eY eZ μ a b
  · intro J X X' Y Y' K _ _ _ _ _ eX eY μ ν ψ a φ j
    exact closedAmplitude_transport (eX j) (eY j) (μ j) (ν j) (ψ j) (a j) (φ j)

/-! ## Non-vacuity -/

def twoWeight : Fin 2 → ℚ := fun i => if i = 0 then 1 else 2

def selectZero : BoundaryKernel Unit (Fin 2) ℚ := fun _ i => if i = 0 then 1 else 0

def readBoth : BoundaryKernel (Fin 2) Unit ℚ := fun _ _ => 1

/-- A nonconstant measure and a nontrivial permutation satisfy the complete law. -/
example :
    weightedCompose (transportFunction (Equiv.swap (0 : Fin 2) 1) twoWeight)
      (transportKernel (Equiv.refl Unit) (Equiv.swap (0 : Fin 2) 1) selectZero)
      (transportKernel (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Unit) readBoth) =
    transportKernel (Equiv.refl Unit) (Equiv.refl Unit)
      (weightedCompose twoWeight selectZero readBoth) :=
  weightedCompose_transport _ _ _ _ _ _

/-- Leaving the intermediate measure untransformed changes the amplitude. -/
example :
    weightedCompose twoWeight selectZero readBoth () () = 1 ∧
    weightedCompose twoWeight
      (transportKernel (Equiv.refl Unit) (Equiv.swap (0 : Fin 2) 1) selectZero)
      (transportKernel (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Unit) readBoth) () () = 2 := by
  norm_num [weightedCompose, twoWeight, selectZero, readBoth, transportKernel,
    Fin.sum_univ_two, Equiv.swap_apply_def]

end Artform.Scores.GravityBridge
