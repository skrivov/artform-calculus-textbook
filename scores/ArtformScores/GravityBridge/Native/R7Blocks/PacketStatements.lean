import ArtformScores.GravityBridge.Native.R7Blocks.PacketDefs

/-! # Bounded packet witnesses and operator-norm quantifiers -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:packet-operator-witness**
(bounded packet witnesses and operator-norm quantifiers). -/
@[ledger "GAC2:packet-operator-witness"]
def packetLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (A : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ)
    (y : Y) (d : ℝ) (_hy : ‖y‖ ≤ 1) (_hφ : ‖φ‖ ≤ 1) (_hw : d ≤ |φ (A y)|),
    d ≤ ‖A‖) ∧
    (∀ (A A₀ : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ)
    (y : Y) (d ε : ℝ) (_hy : ‖y‖ ≤ 1) (_hφ : ‖φ‖ ≤ 1)
    (_hw : d ≤ |φ (A₀ y)|) (_hε : ‖A - A₀‖ ≤ ε),
    d - ε ≤ ‖A‖) ∧
    (∀ (A : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ) (y : Y),
    |φ (A y)| ≤ ‖φ‖ * ‖A‖ * ‖y‖)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
