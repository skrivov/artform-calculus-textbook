import ArtformScores.GravityBridge.Defs
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # Admitted source-restricted current radical -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def admittedRadical (W : Submodule K V) (B : V →ₗ[K] V →ₗ[K] K) : Submodule K V where
  carrier := {g | g ∈ W ∧ ∀ w ∈ W, B g w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨W.add_mem hx.1 hy.1, ?_⟩
    intro w hw
    simp [hx.2 w hw, hy.2 w hw]
  smul_mem' := by
    intro a x hx
    refine ⟨W.smul_mem a hx.1, ?_⟩
    intro w hw
    simp [hx.2 w hw]

end Artform.Scores.GravityBridge.Native.NativeCurrent
