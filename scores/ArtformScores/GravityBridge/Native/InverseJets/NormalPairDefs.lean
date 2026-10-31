import ArtformScores.GravityBridge.Native.InverseJets.Signed

/-! # Original normal pair and independent cubic incoming test contacts -/

namespace Artform.Scores.GravityBridge.Native.InverseJets

open Matrix



def metricGamma0 (l p q ni nj mij : ℚ) : Fin 3 → ℚ :=
  ![(l * mij + p * nj - q * ni) / 2, (l * mij + q * ni - p * nj) / 2, -(p * nj + q * ni - l *
    mij) / 2]

def metricGamma2 (l p q ni nj mij : ℚ) : Fin 3 → ℚ :=
  ![(l ^ 3 * mij + p ^ 3 * nj - q ^ 3 * ni) / 12, (l ^ 3 * mij + q ^ 3 * ni - p ^ 3 * nj) / 12,
    -(p ^ 3 * nj + q ^ 3 * ni - l ^ 3 * mij) / 12]

def metricPairZ1 (l p q ni nj mij : ℚ) : Fin 3 → ℚ :=
  fun i => (![l - p, l - q, p - q] i) / 2 * metricGamma0 l p q ni nj mij i

def metricPairZ3 (l p q ni nj mij : ℚ) : Fin 3 → ℚ := fun i =>
  (![l - p, l - q, p - q] i) / 2 * metricGamma2 l p q ni nj mij i -
  (![l ^ 3 - p ^ 3, l ^ 3 - q ^ 3, p ^ 3 - q ^ 3] i) / 24 * metricGamma0 l p q ni nj mij i

def highest2 (f : ℚ → Fin 3 → ℚ) : Fin 3 → ℚ :=
  (1 / 2 : ℚ) • (f 2 - 2 • f 1 + f 0)

def highest4 (f : ℚ → Fin 3 → ℚ) : Fin 3 → ℚ :=
  (1 / 24 : ℚ) • (f 4 - 4 • f 3 + 6 • f 2 - 4 • f 1 + f 0)

def incomingCubicTest (p q : ℚ) (value derivative : Fin 3 → ℚ) : ℚ :=
  (p ^ 2 * q * (p ^ 2 - q ^ 2) / 24) * value 0 - (p * q ^ 2 * (p ^ 2 - q ^ 2) / 24) * value 1-
    (p ^ 2 * q ^ 2 * (p - q) / 24) * value 2 -
    (p * q * (p ^ 2 - q ^ 2) / 24) * derivative 0 + (p * q * (p ^ 2 - q ^ 2) / 24) * derivative 1

end Artform.Scores.GravityBridge.Native.InverseJets
