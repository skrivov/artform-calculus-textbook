import ArtformScores.GravityBridge.StateTransportStatements

/-! # State pullback preserves positivity in the declared algebraic class -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma state_pullback_invariant {A B : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] (s : AlgebraicPositiveState A)
    (f : B →⋆ₐ[ℂ] A) (alpha : A →⋆ₐ[ℂ] A) (beta : B →⋆ₐ[ℂ] B)
    (hs : ∀ a, s.functional (alpha a) = s.functional a)
    (hf : ∀ b, f (beta b) = alpha (f b)) (b : B) :
    (s.pullback f).functional (beta b) = (s.pullback f).functional b := by
  change s.functional (f (beta b)) = s.functional (f b)
  rw [hf, hs]

lemma finite_matrix_no_ccr (n : ℕ) (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℂ) :
    A * B - B * A ≠ Complex.I • 1 := by
  intro h
  have ht := congrArg Matrix.trace h
  simp only [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at ht
  have him := congrArg Complex.im ht
  norm_num at him
  exact (Nat.ne_of_gt hn) (by exact_mod_cast him.symm)

lemma pulled_swap_state :
    (zeroVectorState.pullback binarySwapAut).functional binaryZ = -1 := by
  change (binaryX * binaryZ * binaryX.conjTranspose) 0 0 = -1
  norm_num [binaryX, binaryZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- **GAC:algebraic-state-transport** (actual algebraic pullback, with a domain scope test). -/
@[ledger "GAC:algebraic-state-transport"]
theorem stateTransportLaw : Statement.stateTransportLaw := by
  refine ⟨?_, ?_, pulled_swap_state, finite_matrix_no_ccr⟩
  · intro A B _ _ _ _ _ _ s f
    exact ⟨(s.pullback f).normalized, (s.pullback f).positive⟩
  · intro A B _ _ _ _ _ _ s f alpha beta hs hf b
    exact state_pullback_invariant s f alpha beta hs hf b

/-! ## Non-vacuity -/

example : zeroVectorState.functional binaryX = 0 ∧ zeroVectorState.functional binaryZ = 1 := by
  change binaryX 0 0 = 0 ∧ binaryZ 0 0 = 1
  norm_num [binaryX, binaryZ]

end

end Artform.Scores.GravityBridge
