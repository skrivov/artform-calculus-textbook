import ArtformScores.GravityBridge.Native.GreenComposition.TemporalDefs

/-! # Finite-range temporal cut with its original incoming terms -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:complete-temporal-cut-stencil**
(finite-range temporal cut with its original incoming terms). -/
@[ledger "GAC2:complete-temporal-cut-stencil"]
def temporalLaw : Prop :=
  ∀ (K : Type) [CommRing K],
    (∀ (f : ℤ → K) (n : ℤ) (r : ℕ),
    (∑ j ∈ Finset.range r, (f (n - (j : ℤ)) - f (n - 1 - (j : ℤ)))) = f n - f (n - (r : ℤ))) ∧
    (∀ (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ),
    cutSum edge R n - cutSum edge R (n - 1) = rowSkew edge R n) ∧
    (∀ (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ) (h f g : K)
    (_hrow : rowSkew edge R n = g - f),
    h * cutSum edge R n - h * cutSum edge R (n - 1) = h * (g - f)) ∧
    (∀ {V : Type*} (B : ℕ → V → V → K)
    (x y : ℤ → V) (R : ℕ) (n : ℤ),
    cutSum (operatorEdge B x y) R n - cutSum (operatorEdge B x y) R (n - 1) =
      pairedIncomingStencil B x y R n - pairedIncomingStencil B y x R n) ∧
    (cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 1-
      cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 0 = 1)

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
