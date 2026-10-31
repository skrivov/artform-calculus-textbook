import ArtformScores.GravityBridge.Native.MetricCut.Coordinates
/-! # The original leading normal range and visible source return -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
variable {K : Type*} [Field K] [CharZero K]
def normalLeading (k : SVec K) (x : K × SVec K) : K × SVec K :=
  ((-101 / 20600 : K) * rho2 k * x.1,
   (-2422 / 29973 : K) • (-rho2 k • x.2 + dot3 k x.2 • k))
def normalLift (k : SVec K) (rhs : K × SVec K) (a : K) : K × SVec K :=
  (rhs.1 / ((-101 / 20600 : K) * rho2 k),
    (-1 / ((-2422 / 29973 : K) * rho2 k)) • rhs.2 + a • k)
end Artform.Scores.GravityBridge.Native.MetricCut
