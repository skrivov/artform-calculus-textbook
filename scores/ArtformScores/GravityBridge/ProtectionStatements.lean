import ArtformScores.GravityBridge.ProtectionDefs
/-! # Specified axis exchange and response protection -/
namespace Artform.Scores.GravityBridge.Statement
/-- **GAC:axis-exchange-protection** (specified axis exchange and response protection). -/
@[ledger "GAC:axis-exchange-protection"]
def protectionLaw : Prop :=
  (∀ (ct cs : ℚ),
    (∀ k, quadraticKinetic ![ct, cs, cs, cs] 0 (kineticSwap01 k) =
      quadraticKinetic ![ct, cs, cs, cs] 0 k) ↔ ct = cs) ∧
  (∀ (c : ℚ) (i : Fin 4),
    loopResponse c c i = loopResponse c c 0)
end Artform.Scores.GravityBridge.Statement
