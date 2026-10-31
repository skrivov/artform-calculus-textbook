import ArtformScores.GravityBridge.Native.TTCross.SourceDefs

/-! # Actual24-connection constitutive return and leading TT cross source -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:original-full24-tt-cross-source**
(actual24-connection constitutive return and leading tt cross source). -/
@[ledger "GAC2:original-full24-tt-cross-source"]
def sourceLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (A B : Connection ℚ),
    Retrospective.connectionDensity (1 / 101) (A + B) - Retrospective.connectionDensity (1 / 101) A-
      Retrospective.connectionDensity (1 / 101) B = dotConnection B (fullBApply A)) ∧
    (∀ (A : Connection K), fullBApply (fullHApply A) = A ∧
      fullHApply (fullBApply A) = A) ∧
    (∀ (p m s : Fin 3 → K),
    nativeConstitutiveQ (threeBlockFace p m s) =
      threeBlockFace (-p - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ p))
        (-m - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ m))
        (s - (2 / 101 : K) • ((spaceT * spaceH * spaceT.transpose) *ᵥ s))) ∧
    (∀ (j z a : K) (_hj : j ^ 2 = -1),
    nativeConstitutiveQ (literalChristoffelZ j z a) = crossQFaces j z a) ∧
    (∀ (j z a : K) (_hj : j ^ 2 = -1) (_hz : z ^ 2 = -2 * a ^ 2),
    CoordinateSymbol.mixedFaceSource j (CoordinateSymbol.timeMomentum j z ![a, -a, 0])
      (originalFaceInput (nativeConstitutiveQ (literalChristoffelZ j z a))) =
      (-(2 / 101 : K) * (9999 / 9991) * a ^ 4 * z) • ![0, 0, 0, 1])

end Artform.Scores.GravityBridge.Native.TTCross.Statement
