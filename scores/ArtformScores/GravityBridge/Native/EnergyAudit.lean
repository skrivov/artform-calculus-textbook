import ArtformScores.GravityBridge.Native.Preparation
import ArtformScores.GravityBridge.Memory

/-! # D08: scoped algebra checks for a failed reservoir-energy transfer

These are tests of the existing signed action and score data. Neither action
values nor a conserved quadratic are thereby a coercive physical Hamiltonian.
-/

namespace Artform.Scores.GravityBridge.Native

example : completeConnectionAction 1 (connectionPreparation 1) = -2 / 103 ∧
    completeConnectionAction 1 (connectionPreparation 1) < 0 ∧
    connectionAction 1 (connectionPreparation 1) = 4 / 10403 := by
  rw [completeConnectionAction_prepared, connectionAction_prepared]
  norm_num

end Artform.Scores.GravityBridge.Native

namespace Artform.Scores.GravityBridge

-- A conserved quadratic of an actual reversible score need not be bounded below.
example (p : ℚ × ℚ) :
    -((quarterTurn p).1 ^ 2 + (quarterTurn p).2 ^ 2) = -(p.1 ^ 2 + p.2 ^ 2) := by
  simp [quarterTurn]
  ring

example (n : ℕ) : -(((n + 1 : ℚ), 0) : ℚ × ℚ).1 ^ 2 < 0 := by
  have hn : (0 : ℚ) < n + 1 := by positivity
  nlinarith [sq_pos_of_pos hn]

example : ¬ ∃ M : ℚ, ∀ n : ℕ, M ≤ -(n + 1 : ℚ) ^ 2 := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (|M| + 1)
  have hb := hM n
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith [neg_abs_le M, abs_nonneg M]

end Artform.Scores.GravityBridge
