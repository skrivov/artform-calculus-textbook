import ArtformScores.GravityBridge.Native.Full40.WardDefs
/-! # The full original mixed Lorentz Ward identity -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:full-mixed-lorentz-ward**
(the full original mixed lorentz ward identity). -/
@[ledger "GAC2:full-mixed-lorentz-ward"]
def wardLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [Field K] [CharZero K],
    (∀ (w : Biv K) (i j : Fin 4),
    firstWedge (lie w) i j = bivBracket w (wedge (basisVector i) (basisVector j))) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6),
    nativeLU d (gaugeField d w) x r = bivBracket (w x) (flatComplement r)) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6),
    nativeK d (gaugeField d w) x r = 0) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6),
    nativeTheta d (gaugeField d w) x r = 0) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K) (w : X → Biv K)
    (x : X) (r : Fin 6),
    nativeK d (gaugeCorrection d q w) x r +
      rawPlaquetteContact d q (gaugeField d w) x r +
      rawPlaquetteContact d (gaugeField d w) q x r =
        bivBracket (w x) (nativeK d q x r)) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (q : NativeField X K)
    (r : Fin 6) (C : Biv K),
    ∑ x, bivPair C (internalStar (nativeK d q x r)) = 0) ∧
    (∀ (d : Fin 4 → X) (q : NativeField X K) (w : X → Biv K)
    (x : X) (r : Fin 6),
    bivPair (nativeLU d (gaugeField d w) x r) (internalStar (nativeK d q x r)) +
      bivPair (flatComplement r) (internalStar
        (rawPlaquetteContact d q (gaugeField d w) x r +
         rawPlaquetteContact d (gaugeField d w) q x r)) =
    -bivPair (flatComplement r) (internalStar (nativeK d (gaugeCorrection d q w) x r))) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K) (w : X → Biv K),
    nativeFirstVariation d kappa q (gaugeField d w) = 0) ∧
    (∀ [Fintype X] (d : Fin 4 → X) (kappa : K) (w : X → Biv K),
    fullForce d kappa (gaugeField d w) = 0) ∧
    (∀ (d : Fin 4 → X),
    Function.Injective (gaugeField d (K := K)))
end Artform.Scores.GravityBridge.Native.Full40.Statement
