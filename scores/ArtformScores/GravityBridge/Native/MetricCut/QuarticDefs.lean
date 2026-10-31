import ArtformScores.GravityBridge.Native.MetricCut.Leading
/-! # The supplied native quartic contacts with both elimination returns -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
def nativeKappa : ℚ := 1/101
def nativeA : ℚ := 101/103
def nativeG : ℚ := 101/97
def nativeE : ℚ := 202/9991
def nativeHd : ℚ := 9999/9991
def nativeD : ℚ := 10201/10300
def nativeBeta : ℚ := -2422/29973
def quarticRawConstant : ℚ := nativeKappa *
  (nativeHd + (nativeKappa * nativeA^2 + nativeE) * (nativeHd-nativeD)/nativeHd) / 12
def quarticTopReturn : ℚ :=
  nativeKappa^4 * nativeG^2 * nativeA^2 / (4*nativeBeta)
def quarticConstant : ℚ := quarticRawConstant + quarticTopReturn
def dependentFourth (T phi : ℚ) : ℚ := -(nativeHd-nativeD)*T*phi/nativeHd
def normalFourthDivergence (W T phi : ℚ) : ℚ :=
  nativeKappa^2*nativeA^2*W/12-nativeKappa*(nativeHd+nativeE)*T*phi/12
def fullThirdSourceDerivative (W T phi : ℚ) : ℚ := -nativeKappa*nativeE*(W+T*phi)/2
def visibleFourthDivergence (T phi : ℚ) : ℚ :=
  normalFourthDivergence (dependentFourth T phi) T phi -
    fullThirdSourceDerivative (dependentFourth T phi) T phi / 6
noncomputable def cubicColumn (rho : ℂ) (v : SVec ℂ) : SVec ℂ :=
  (-Complex.I * (nativeKappa : ℂ)^2 * (nativeG : ℂ) * (nativeA : ℂ)*rho/2) • v
noncomputable def topInverse (rho : ℂ) (v : SVec ℂ) : SVec ℂ :=
  (-1/((nativeBeta : ℂ)*rho^2)) • v
noncomputable def angularVector (k : SVec ℝ) : SVec ℝ :=
  projector3 k *ᵥ (fun i => k i ^ 2)
noncomputable def angularSquare (k : SVec ℝ) : ℝ := dot3 (angularVector k) (angularVector k)
noncomputable def quarticScalar (k : SVec ℝ) : ℝ := -(quarticConstant : ℝ)*angularSquare k
end Artform.Scores.GravityBridge.Native.MetricCut
