import ArtformScores.GravityBridge.Native.CoordinateSymbol.ScalingDefs

/-! # Native frequency degrees and source-dependent response -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-frequency-response-scaling**
(native frequency degrees and source-dependent response). -/
@[ledger "GAC2:native-frequency-response-scaling"]
def scalingLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (s : K) (p : Vec4 (K := K)),
    simpleFace (componentSquares (s • p)) (s • p) = s ^ 3 • simpleFace (componentSquares p) p) ∧
    (∀ (s : K) (p : Vec4 (K := K)),
    simpleDiscriminant (componentSquares (s • p)) (s • p) =
      s ^ 6 * simpleDiscriminant (componentSquares p) p) ∧
    (∀ (s : K) (p : Vec4 (K := K)),
    nativeUpperSymbol (s • p) = s ^ 6 • nativeUpperSymbol p) ∧
    (∀ (j s : K) (p : Vec4 (K := K))
    (Q : Fin 4 → Fin 4 → Fin 4 → K),
    mixedFaceSource j (s • p) (fun a b c => s ^ 2 * Q a b c) = s ^ 5 • mixedFaceSource j p Q) ∧
    (∀ (s : K) (p : Vec4 (K := K)) (_hs : s ≠ 0)
    (_hd : simpleDiscriminant (componentSquares p) p ≠ 0),
    nativeCoordinateInverse (s • p) = (s ^ 6)⁻¹ • nativeCoordinateInverse p) ∧
    (∀ (s : K) (p : Vec4 (K := K)) (_hs : s ≠ 0)
    (_hd : simpleDiscriminant (componentSquares p) p ≠ 0),
    nativeLowerInverse (s • p) = (s ^ 6)⁻¹ • nativeLowerInverse p) ∧
    (∀ (j s : K) (p : Vec4 (K := K))
    (Q : Fin 4 → Fin 4 → Fin 4 → K) (_hs : s ≠ 0)
    (_hd : simpleDiscriminant (componentSquares p) p ≠ 0),
    nativeLowerInverse (s • p) *ᵥ mixedFaceSource j (s • p) (fun a b c => s ^ 2 * Q a b c) =
      s⁻¹ • (nativeLowerInverse p *ᵥ mixedFaceSource j p Q)) ∧
    (nativeLowerInverse (![-1, 1, 0, 0] : Vec4 (K := ℝ)) *ᵥ
      mixedFaceSource 1 ![-1, 1, 0, 0] explicitFaceInput = ![0, 0, 0, -9991 / 9999]) ∧
    (∀ (s : ℝ) (_hs : s ≠ 0),
    (nativeLowerInverse (s • (![-1, 1, 0, 0] : Vec4 (K := ℝ))) *ᵥ
      mixedFaceSource 1 (s • ![-1, 1, 0, 0])
        (fun a b c => s ^ 2 * explicitFaceInput a b c)) 3 = -(9991 / 9999 : ℝ) / s)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
