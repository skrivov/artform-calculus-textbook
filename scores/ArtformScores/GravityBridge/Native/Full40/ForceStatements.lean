import ArtformScores.GravityBridge.Native.Full40.ForceDefs
/-! # The original full coordinate force from the complete quadratic action -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:full-coordinate-variational-force**
(the original full coordinate force from the complete quadratic action). -/
@[ledger "GAC2:full-coordinate-variational-force"]
def forceLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [Field K] [CharZero K],
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K) (q p : NativeField X K),
    nativeFirstVariation d kappa q p = ∑ a, fullForce d kappa q a * fieldCoordinates p a) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K),
    fullForce d kappa q = 0 ↔ ∀ p, nativeFirstVariation d kappa q p = 0) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K),
    nativeFirstVariation d kappa q p =
      nativeFirstVariation d kappa p q) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K),
    (fullJacobian d kappa).transpose = fullJacobian d kappa) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K),
    fullForce d kappa q = Matrix.mulVec (fullJacobian d kappa) (fieldCoordinates q)) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K),
    nativeFirstVariation d kappa q p =
      directFirstVariation d kappa q p) ∧
    (∀ [Fintype X],
    Fintype.card (X × Coordinate) = 40 * Fintype.card X) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : ℝ)
    (q p : NativeField X ℝ),
    HasDerivAt
    (fun epsilon : ℝ => completeQuadratic d kappa (q + epsilon • p))
    (nativeFirstVariation d kappa q p) 0)
end Artform.Scores.GravityBridge.Native.Full40.Statement
