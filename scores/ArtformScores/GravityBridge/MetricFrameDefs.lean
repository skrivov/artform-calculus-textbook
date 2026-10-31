import ArtformScores.GravityBridge.LinearDefs
/-! # Metric jets and independent frame connection data -/
namespace Artform.Scores.GravityBridge
noncomputable section
def nativeEta (i : Fin 4) : ℚ := if i = 0 then -1 else 1
def coframeMetricVariation (F : Matrix (Fin 4) (Fin 4) ℚ) (i j : Fin 4) : ℚ :=
  nativeEta i * F i j + nativeEta j * F j i
def metricFromFrame (E : Matrix (Fin 4) (Fin 4) ℚ) (i j : Fin 4) : ℚ :=
  ∑ a, nativeEta a * E a i * E a j
def finiteLorentzFrame : Matrix (Fin 4) (Fin 4) ℚ :=
  !![5 / 3, 4 / 3, 0, 0; 4 / 3, 5 / 3, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def lorentzGenerator (b r : Fin 3 → ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, b 0, b 1, b 2;
     b 0, 0, -r 2, r 1;
     b 1, r 2, 0, -r 0;
     b 2, -r 1, r 0, 0]
def pureFrameConnection (k : Fin 4 → ℚ) (F : Matrix (Fin 4) (Fin 4) ℚ)
    (i a b : Fin 4) : ℚ := k i * F a b
def linearTorsionSymbol (k : Fin 4 → ℚ) (F : Matrix (Fin 4) (Fin 4) ℚ)
    (A : Fin 4 → Fin 4 → Fin 4 → ℚ) (i j a : Fin 4) : ℚ :=
  k i * F a j - k j * F a i - A i a j + A j a i
def linearCurvatureSymbol (k : Fin 4 → ℚ) (A : Fin 4 → Fin 4 → Fin 4 → ℚ)
    (i j a b : Fin 4) : ℚ := k i * A j a b - k j * A i a b
end
end Artform.Scores.GravityBridge
