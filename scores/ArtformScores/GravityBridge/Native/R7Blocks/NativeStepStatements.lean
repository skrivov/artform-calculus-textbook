import ArtformScores.GravityBridge.Native.R7Blocks.NativeStepDefs

/-! # Single-step invariance in the original Hilbert norm -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:hilbert-single-step-generator**
(single-step invariance in the original hilbert norm). -/
@[ledger "GAC2:hilbert-single-step-generator"]
def nativeStepLaw : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    (∀ (W : Submodule ℝ H) [W.HasOrthogonalProjection],
    W.starProjection * W.starProjection = W.starProjection ∧
    ‖W.starProjection‖ ≤ 1 ∧ ‖(1 : H →L[ℝ] H) - W.starProjection‖ ≤ 1) ∧
    (∀ (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (T : H →L[ℝ] H),
    (∀ y ∈ W, T y ∈ W) ↔ ((1 : H →L[ℝ] H) - W.starProjection) * T * W.starProjection = 0) ∧
    (∀ (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (h a : ℝ) (_hh : 0 < h) (_hA : ‖A‖ ≤ a)
    (_hsmall : Real.exp (h * a) - 1 < 1)
    (_hstep : ∀ y ∈ W, NormedSpace.exp (h • A) y ∈ W),
    ∀ y ∈ W, A y ∈ W) ∧
    (∀ (W : Submodule ℝ H)
    (_hclosed : IsClosed (W : Set H))
    (A : H →L[ℝ] H) (h a : ℝ) (_hh : 0 < h) (_hA : ‖A‖ ≤ a)
    (_hsmall : Real.exp (h * a) - 1 < 1)
    (_hstep : ∀ y ∈ W, NormedSpace.exp (h • A) y ∈ W),
    ∀ y ∈ W, A y ∈ W) ∧
    (∀ {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z) (K : Y →L[ℝ] Z)
    (A : H →L[ℝ] H) (h a : ℝ) (_hh : 0 < h) (_hA : ‖A‖ ≤ a)
    (_hsmall : Real.exp (h * a) - 1 < 1)
    (_hstep : ∀ w, R w = K (Q w) →
      R (NormedSpace.exp (h • A) w) = K (Q (NormedSpace.exp (h • A) w))),
    ∀ w, R w = K (Q w) → R (A w) = K (Q (A w)))

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
