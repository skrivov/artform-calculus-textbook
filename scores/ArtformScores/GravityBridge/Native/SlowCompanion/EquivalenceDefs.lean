import ArtformScores.GravityBridge.Defs
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # Admitted source and observation agreement -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K H S O F : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup S] [Module K S] [AddCommGroup O] [Module K O]
  [AddCommGroup F] [Module K F]

def compatibleChanges (W : Submodule K H) (J : H →ₗ[K] F) (read : H →ₗ[K] O) :
    Submodule K H := W⊓J.ker⊓read.ker

end Artform.Scores.GravityBridge.Native.SlowCompanion
