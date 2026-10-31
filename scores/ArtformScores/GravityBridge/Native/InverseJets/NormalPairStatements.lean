import ArtformScores.GravityBridge.Native.InverseJets.NormalPairDefs

/-! # Original normal pair and independent cubic incoming test contacts -/

namespace Artform.Scores.GravityBridge.Native.InverseJets.Statement

open Matrix

/-- **GAC2:normal-pair-incoming-contacts**
(original normal pair and independent cubic incoming test contacts). -/
@[ledger "GAC2:normal-pair-incoming-contacts"]
def normalPairLaw : Prop :=
    (∀ (l p q ni nj mij : ℚ),
    (firstH l p q *ᵥ metricPairZ1 l p q ni nj mij) 2 =
      -(1 / 101 * signedG * signedA : ℚ) * (l - p) * (l - q) * (p * nj - q * ni) / 2) ∧
    (∀ (l p q : ℚ),
    metricPairZ3 l p q p q 0 =
      ![p * q * (p ^ 2 - q ^ 2) * (l - p) / 24, -p * q * (p ^ 2 - q ^ 2) * (l - q) / 24, p ^ 2 *
        q ^ 2 * (p - q) / 24]) ∧
    (∀ (l p q c0 ci cj : ℚ),
    metricPairZ1 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci) =
      l ^ 2 • ((1 / 2 : ℚ) • ![p * cj, q * ci, 0]) +
      l • ((1 / 2 : ℚ) • ![-p ^ 2 * cj, -q ^ 2 * ci, 0]) +
      (1 / 2 : ℚ) • ![0, 0, -(p - q) * p * q * c0]) ∧
    (∀ (l p q c0 ci cj : ℚ),
    metricPairZ3 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci) =
      l ^ 4 • ((1 / 24 : ℚ) • ![q * ci, p * cj, 0]) +
      l ^ 3 • ((1 / 24 : ℚ) •
        ![-p * (p * cj + q * ci), -q * (q * ci + p * cj), (p - q) * (p * cj + q * ci)]) +
      l ^ 2 • ((1 / 24 : ℚ) • ![p ^ 3 * cj - q ^ 3 * ci, q ^ 3 * ci - p ^ 3 * cj, 0]) +
      l • ((1 / 24 : ℚ) • ![p * q ^ 3 * ci + (p ^ 3 * q - q ^ 3 * p) * c0,
        q * p ^ 3 * cj + (q ^ 3 * p - p ^ 3 * q) * c0, -(p - q) * (p ^ 3 * cj + q ^ 3 * ci)]) +
      (1 / 24 : ℚ) • ![-p * (p ^ 3 * q - q ^ 3 * p) * c0, -q * (q ^ 3 * p - p ^ 3 * q) * c0,
        p ^ 2 * q ^ 2 * (p - q) * c0]) ∧
    (∀ (p q c0 ci cj : ℚ),
    highest2 (fun l => metricPairZ1 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci)) =
      (1 / 2 : ℚ) • ![p * cj, q * ci, 0]) ∧
    (∀ (p q c0 ci cj : ℚ),
    highest4 (fun l => metricPairZ3 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci)) =
      (1 / 24 : ℚ) • ![q * ci, p * cj, 0]) ∧
    (∀ (p q ci cj : ℚ),
    (secondH 1 0 0 *ᵥ ((1 / 2 : ℚ) • ![p * cj, q * ci, 0])) 2 +
      (signedH0 *ᵥ ((1 / 24 : ℚ) • ![q * ci, p * cj, 0])) 2 =
      ((1 / 101 : ℚ) * signedA ^ 2 / 12) * (q * ci - p * cj)) ∧
    (∀ (l p q : ℚ),
    metricPairZ3 (-l) (-p) (-q) (-p) (-q) 0 =
      l • ![-p * q * (p ^ 2 - q ^ 2) / 24, p * q * (p ^ 2 - q ^ 2) / 24, 0] +
      ![p ^ 2 * q * (p ^ 2 - q ^ 2) / 24, -p * q ^ 2 * (p ^ 2 - q ^ 2) / 24, -p ^ 2 * q ^ 2 * (p
        - q) / 24]) ∧
    (∀ (p q : ℚ) (value derivative : Fin 3 → ℚ)
    (_hv : value = 0) (_hs : derivative 0 = derivative 1),
    incomingCubicTest p q value derivative = 0) ∧
    (∀ (a : ℚ),
    (signedH0 *ᵥ ![a, a, 0]) 0 = (signedH0 *ᵥ ![a, a, 0]) 1)

end Artform.Scores.GravityBridge.Native.InverseJets.Statement
