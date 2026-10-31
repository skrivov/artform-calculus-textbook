import ArtformScores.GravityBridge.Native.RetroCertificates.ConstitutiveInverseDefs

/-! # Original full face inverse and exact curvature Woodbury return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-full-constitutive-inverse**
(original full face inverse and exact curvature woodbury return). -/
@[ledger "GAC2:native-full-constitutive-inverse"]
def constitutiveInverseLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (A B : Connection ℚ),
    Retrospective.connectionDensity 0 (A + B) - Retrospective.connectionDensity 0 A-
      Retrospective.connectionDensity 0 B = dotConnection B (curvatureApply A)) ∧
    (∀ (A : Connection K),
    curvatureApply (curvatureReturn A) = A ∧ curvatureReturn (curvatureApply A) = A) ∧
    (∀ (Z : NativeFace K),
    nativeConstitutiveQ (nativeFaceInverse Z) = Z ∧ nativeFaceInverse (nativeConstitutiveQ Z) = Z) ∧
    (∀ (Z : NativeFace K),
    nativeFaceInverse Z = nativeFaceGram Z + (2 / 101 : K) • nativeConnectionT
      (curvatureReturn (nativeSourceAdjoint (nativeFaceGram Z))))

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
