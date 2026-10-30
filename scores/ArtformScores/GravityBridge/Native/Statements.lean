import ArtformScores.GravityBridge.Native.Defs

/-! # Finite native block statements for the gravity calculus campaign -/

namespace Artform.Scores.GravityBridge.Native.Statement

open Matrix

/-- **GAC:native-distinct-block** (the signed native Schur cancellation). -/
@[ledger "GAC:native-distinct-block"]
def distinctBlock : Prop :=
  connectionBlock.det = 2058146 / 1030301 ∧
  ∀ z : ℚ, schurCovector z = ![-101 * z / 103, -101 * z / 103, 0]

/-- **GAC:temporal-witness** (a rational transverse traceless symbol witness). -/
@[ledger "GAC:temporal-witness"]
def temporalWitness : Prop :=
  polarization.transpose = polarization ∧
  polarization.trace = 0 ∧
  polarization *ᵥ momentum = 0 ∧
  rhoSquared momentum = 14 ∧
  diagonalContraction momentum polarization = -36 / 35 ∧
  temporalSymbol momentum polarization = 36 / 505 ∧
  temporalSymbol momentum polarization ≠ 0

end Artform.Scores.GravityBridge.Native.Statement
