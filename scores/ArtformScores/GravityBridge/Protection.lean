import ArtformScores.GravityBridge.ProtectionStatements
/-! # Specified axis exchange and response protection -/
namespace Artform.Scores.GravityBridge
noncomputable section
lemma axis_exchange_coefficient_iff (ct cs : ℚ) :
    (∀ k, quadraticKinetic ![ct, cs, cs, cs] 0 (kineticSwap01 k) =
      quadraticKinetic ![ct, cs, cs, cs] 0 k) ↔ ct = cs := by
  constructor
  · intro h
    have he := h ![1, 0, 0, 0]
    simpa [kineticSwap01, quadraticKinetic] using he.symm
  · rintro rfl k
    dsimp [kineticSwap01, quadraticKinetic]
    ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The finite sixteen-mode rational response expands all four axis permutations.
lemma full_axis_response (c : ℚ) (i : Fin 4) :
    loopResponse c c i = loopResponse c c 0 := by
  fin_cases i <;>
    norm_num [loopResponse, modePrecision, momentumAxis, Fin.sum_univ_succ, Nat.testBit] <;> ring
/-- **GAC:axis-exchange-protection** (specified axis exchange and response protection). -/
@[ledger "GAC:axis-exchange-protection"]
theorem protectionLaw : Statement.protectionLaw := by
  exact ⟨axis_exchange_coefficient_iff, full_axis_response⟩
/-! ## Non-vacuity -/
example : loopResponse 1 1 0 = loopResponse 1 1 3 ∧
    loopResponse 2 1 0 - loopResponse 2 1 1 = -11 / 30 := by
  refine ⟨(full_axis_response 1 3).symm, ?_⟩
  rw [anisotropic_loop_response.1, anisotropic_loop_response.2]
  norm_num
end
end Artform.Scores.GravityBridge
