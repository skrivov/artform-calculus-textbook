import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost
import ArtformScores.GravityBridge.Native.Full40.Quadratic

/-! # Original five transported complementary bivector terms -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40

variable {K : Type*} [Field K] [CharZero K]

def complementaryBivector (b : K) : Biv K := wedge (b • basisVector 2) (basisVector 3)

def transportedComplement (c s b : K) : Biv K :=
  wedge (boost c (-s) *ᵥ (b • basisVector 2)) (boost c (-s) *ᵥ basisVector 3)

def fiveTermComplement (c0 s0 c1 s1 b : K) : Biv K :=
  (1 / 4 : K) • complementaryBivector b + (1 / 4 : K) • complementaryBivector b +
    (1 / 4 : K) • transportedComplement c0 s0 b +
    (1 / 8 : K) • transportedComplement c1 s1 b +
    (1 / 8 : K) • transportedComplement c0 s0 b

def activeCurvature (c s : K) : Biv K := lieCoordinates (rootBoostCurvature c s)

def completeCurvatureFold (c0 s0 c1 s1 b cf sf : K) : K :=
  ∑ r : Fin 6, if r = 0 then bivPair (fiveTermComplement c0 s0 c1 s1 b)
    (internalStar (activeCurvature cf sf)) else 0

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
