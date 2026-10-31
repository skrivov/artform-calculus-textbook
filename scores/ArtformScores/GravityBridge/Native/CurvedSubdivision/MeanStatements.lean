import ArtformScores.GravityBridge.Native.CurvedSubdivision.MeanDefs

/-! # Original five transported complementary bivector terms -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-curved-five-transport**
(original five transported complementary bivector terms). -/
@[ledger "GAC2:native-curved-five-transport"]
def meanLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (c s b : K),
    transportedComplement c s b = complementaryBivector b) ∧
    (∀ (c0 s0 c1 s1 b : K),
    fiveTermComplement c0 s0 c1 s1 b = complementaryBivector b) ∧
    (∀ (c s : K),
    activeCurvature c s = ![-s, 0, 0, 0, 0, 0]) ∧
    (∀ (c0 s0 c1 s1 b cf sf : K),
    completeCurvatureFold c0 s0 c1 s1 b cf sf = -b * sf)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
