import ArtformScores.GravityBridge.Native.Full40.BoostContactDefs
/-! # The original temporal boost quarter-contact -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:temporal-boost-quarter-contact**
(the original temporal boost quarter-contact). -/
@[ledger "GAC2:temporal-boost-quarter-contact"]
def boostContactLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (n : Fin 3 → K) (a : K),
    coordinateLorentz (lowerThirdJet n a) =
      ![n 0 * a / 2, n 1 * a / 2, n 2 * a / 2, 0, 0, 0]) ∧
    (∀ (n : Fin 3 → K) (a : K),
    temporalBoostContact n a = ![n 0 * a / 4, n 1 * a / 4, n 2 * a / 4, 0, 0, 0]) ∧
    (∀ (n : Fin 3 → K) (_hn : ∃ j, n j ≠ 0) (a : K),
    temporalBoostContact n a = 0 ↔ a = 0) ∧
    (∀ (h : K) (n : Fin 3 → K) (a : K),
    -h • temporalBoostContact n a =
      ![-h * n 0 * a / 4, -h * n 1 * a / 4, -h * n 2 * a / 4, 0, 0, 0]) ∧
    (∀ (E C : Biv K →ₗ[K] Biv K) (z : Biv K) (_hz : z = 0)
    (n : Fin 3 → K) (a kappa : K),
    temporalBoostContact n a - (2 * kappa) • E (C z) = temporalBoostContact n a)
end Artform.Scores.GravityBridge.Native.Full40.Statement
