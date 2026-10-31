import ArtformScores.GravityBridge.Defs

/-! # Exact finite-support stencil actions and a dense constant-field projector -/

namespace Artform.Scores.GravityBridge

open scoped Pointwise

variable {K G : Type*} [Semiring K] [AddMonoid G]

noncomputable def stencilAct (p : AddMonoidAlgebra K G) (v : G → K) (x : G) : K :=
  p.coeff.sum fun a c => c * v (x + a)

noncomputable def HasStencilRadius {d : ℕ} (p : AddMonoidAlgebra K (Fin d → ℤ)) (r : ℕ) : Prop :=
  ∀ a ∈ p.coeff.support, ∀ i, (a i).natAbs ≤ r

noncomputable def averagingMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun _ _ => 1 / (n + 1 : ℚ)

end Artform.Scores.GravityBridge
