import ArtformScores.GravityBridge.Native.RetroCertificates.FacePartitionDefs

/-! # All original constitutive face slots in eight signed blocks -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-full-face-rank-partition**
(all original constitutive face slots in eight signed blocks). -/
@[ledger "GAC2:native-full-face-rank-partition"]
def facePartitionLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (Z : NativeFace K),
    faceAssemble (faceRead Z) = Z) ∧
    (∀ (v : Fin 8 → Fin 3 → K),
    faceRead (faceAssemble v) = v) ∧
    (∀ (s : Fin 8),
    faceAlpha (K := K) s ≠ 0 ∧ faceAlpha (K := K) s + 3 * faceBeta s ≠ 0) ∧
    (∀ (s : Fin 8),
    faceInverseBlock (K := K) s * faceForwardBlock s = 1 ∧
      faceForwardBlock (K := K) s * faceInverseBlock s = 1) ∧
    (∀ (Z : NativeFace K) (s : Fin 8),
    faceRead (nativeConstitutiveQ Z) s = faceForwardBlock s *ᵥ faceRead Z s)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
