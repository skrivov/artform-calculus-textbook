import ArtformScores.GravityBridge.Native.Full40.BoostContact
/-! # The guarded complete four-group longitudinal target -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
def fourGroupValue (groups : Fin 4 → K) : K := ∑ j, groups j
def normalizedTarget (j rho d4 : K) (groups : Fin 4 → K) : K :=
  -fourGroupValue groups / (j * rho * d4)
end Artform.Scores.GravityBridge.Native.Full40
