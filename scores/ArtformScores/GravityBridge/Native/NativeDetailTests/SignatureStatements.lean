import ArtformScores.GravityBridge.Native.NativeDetailTests.SignatureDefs

/-! # Complete original constitutive quadratic has both algebraic signs -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix Full40 TTCross RetroCertificates MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-constitutive-diagonal-signs**
(complete original constitutive quadratic has both algebraic signs). -/
@[ledger "GAC2:native-constitutive-diagonal-signs"]
def signatureLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (z : Fin 3 → K),
    inverseModes (orthogonalModes z) = z ∧ orthogonalModes (inverseModes z) = z) ∧
    (∀ (z : Fin 8 → Fin 3 → K),
    nativeFaceQuadratic (faceModes z) = ∑ s : Fin 8, ∑ i : Fin 3, modeDiagonal s i * (z s i) ^ 2) ∧
    (positiveModeCount = 12 ∧ negativeModeCount = 12 ∧
      (∀ s : Fin 8, ∀ i : Fin 3, modeDiagonal (K := ℚ) s i ≠ 0)) ∧
    (nativeFaceQuadratic (faceModes (fun s => if s = 0 then ![1, 0, 0] else 0) : NativeFace ℚ) =
      202 / 103 ∧
    nativeFaceQuadratic (faceModes (fun s => if s = 1 then ![1, 0, 0] else 0) : NativeFace ℚ) =
      -202 / 103)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
