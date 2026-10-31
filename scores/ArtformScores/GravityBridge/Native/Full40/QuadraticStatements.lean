import ArtformScores.GravityBridge.Native.Full40.QuadraticDefs

/-! # Complete original flat quadratic variation on periodic fields -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:complete-flat-quadratic-variation**
(complete original flat quadratic variation on periodic fields). -/
@[ledger "GAC2:complete-flat-quadratic-variation"]
def quadraticLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [Field K] [CharZero K],
    (∀ (a b : Biv K),
    lie (bivBracket a b) = commutator (lie a) (lie b)) ∧
    (∀ (a b : Biv K),
    internalStar (bivBracket a b) = bivBracket a (internalStar b)) ∧
    (∀ (a b c : Biv K),
    bivPair (bivBracket a b) c + bivPair b (bivBracket a c) = 0) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p t : NativeField X K),
    nativeBilinear d kappa (q + p) t = nativeBilinear d kappa q t + nativeBilinear d kappa p t) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p t : NativeField X K),
    nativeBilinear d kappa q (p + t) = nativeBilinear d kappa q p + nativeBilinear d kappa q t) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa c : K)
    (q p : NativeField X K),
    nativeBilinear d kappa (c • q) p = c * nativeBilinear d kappa q p) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa c : K)
    (q p : NativeField X K),
    nativeBilinear d kappa q (c • p) = c * nativeBilinear d kappa q p) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa epsilon : K)
    (q p : NativeField X K),
    completeQuadratic d kappa (q + epsilon • p) = completeQuadratic d kappa q +
      epsilon * nativeFirstVariation d kappa q p + epsilon ^ 2 * completeQuadratic d kappa p) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6),
    lie (rawPlaquetteContact d q q x r) =
      curvatureJet (orderedFourJet (fun a => lie (nativeLetters d q x r a))) 2)

end Artform.Scores.GravityBridge.Native.Full40.Statement
