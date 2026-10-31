import ArtformScores.GravityBridge.Native.RetroCertificates.ForwardQDefs

/-! # Verified cheaper complete original constitutive forward map -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-full-Q-program**
(verified cheaper complete original constitutive forward map). -/
@[ledger "GAC2:native-full-Q-program"]
def forwardQLaw : Prop :=
    (∀ (rank : Bool) (Z : NativeFace ℚ),
    fullFaceProgram false rank Z = nativeConstitutiveQ Z) ∧
    (faceProgramScales false false = 72 ∧ faceProgramAdds false false = 48 ∧
    faceProgramScales false true = 32 ∧ faceProgramAdds false true = 40) ∧
    (∀ (cs ca : ℚ) (_hs : 0 < cs) (_ha : 0 ≤ ca),
    (faceProgramScales false true : ℚ) * cs + (faceProgramAdds false true : ℚ) * ca <
      (faceProgramScales false false : ℚ) * cs + (faceProgramAdds false false : ℚ) * ca) ∧
    (∀ (s : Fin 8),
    Retrospective.validProgram 0 (rankFaceCode false s) = true ∧
    Retrospective.validProgram 0 (denseFaceCode false s) = true ∧
    (∀ i : Fin 3,(![4,9,14] : Fin 3 → ℕ) i < (denseFaceCode false s).length) ∧
    (∀ i : Fin 3,(![6,7,8] : Fin 3 → ℕ) i < (rankFaceCode false s).length))

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
