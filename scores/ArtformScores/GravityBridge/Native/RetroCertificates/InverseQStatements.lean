import ArtformScores.GravityBridge.Native.RetroCertificates.InverseQDefs

/-! # Verified complete inverse constitutive map on held-out inputs -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-full-Q-inverse-program**
(verified complete inverse constitutive map on held-out inputs). -/
@[ledger "GAC2:native-full-Q-inverse-program"]
def inverseQLaw : Prop :=
    (∀ (rank : Bool) (Z : NativeFace ℚ),
    fullFaceProgram true rank Z = nativeFaceInverse Z) ∧
    (∀ (rank : Bool) (Z : NativeFace ℚ),
    nativeConstitutiveQ (fullFaceProgram true rank Z) = Z ∧
      fullFaceProgram true rank (nativeConstitutiveQ Z) = Z) ∧
    (faceProgramScales true false = 72 ∧ faceProgramAdds true false = 48 ∧
    faceProgramScales true true = 32 ∧ faceProgramAdds true true = 40) ∧
    (∀ (cs ca : ℚ) (_hs : 0 < cs) (_ha : 0 ≤ ca),
    (faceProgramScales true true : ℚ) * cs + (faceProgramAdds true true : ℚ) * ca <
      (faceProgramScales true false : ℚ) * cs + (faceProgramAdds true false : ℚ) * ca) ∧
    (∀ (s : Fin 8),
    Retrospective.validProgram 0 (rankFaceCode true s) = true ∧
    Retrospective.validProgram 0 (denseFaceCode true s) = true ∧
    (∀ i : Fin 3,(![4,9,14] : Fin 3 → ℕ) i < (denseFaceCode true s).length) ∧
    (∀ i : Fin 3,(![6,7,8] : Fin 3 → ℕ) i < (rankFaceCode true s).length))

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
