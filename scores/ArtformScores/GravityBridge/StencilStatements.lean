import ArtformScores.GravityBridge.StencilDefs

/-! # Exact stencil bounds and a dense law agreeing on constant fields -/

namespace Artform.Scores.GravityBridge.Statement

open scoped Pointwise

/-- **GAC:stencil-support** (composition is local with its explicit support). -/
@[ledger "GAC:stencil-support"]
def stencilSupport : Prop :=
  (∀ (K G : Type*) [Semiring K] [AddMonoid G] [DecidableEq G],
    (∀ (p q : AddMonoidAlgebra K G) (v : G → K) (x : G),
      stencilAct (p * q) v x = stencilAct p (fun y => stencilAct q v y) x) ∧
    Function.Injective (stencilAct (K := K) (G := G)) ∧
    (∀ p q : AddMonoidAlgebra K G,
      (p * q).coeff.support ⊆ p.coeff.support + q.coeff.support)) ∧
  (∀ (K : Type*) [Semiring K] (d : ℕ)
    (p q : AddMonoidAlgebra K (Fin d → ℤ)) (r s : ℕ),
    HasStencilRadius p r → HasStencilRadius q s → HasStencilRadius (p * q) (r + s)) ∧
  (∀ n : ℕ,
    (∀ c : ℚ, Matrix.mulVec (averagingMatrix n) (fun _ => c) = fun _ => c) ∧
    ∀ i j : Fin (n + 1), averagingMatrix n i j ≠ 0) ∧
  (∃ p q : AddMonoidAlgebra ℚ ℤ,
    1 ∈ p.coeff.support + q.coeff.support ∧ 1 ∉ (p * q).coeff.support)

end Artform.Scores.GravityBridge.Statement
