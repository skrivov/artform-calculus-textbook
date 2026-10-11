import ArtformTextbook.Ch05.Statements

/-!
# Reversing a tick of two steps (Section 5.18)

Proposition 5.39, by the book's chain of rewrites, in the group of
permutations of the states, where `f * g` is `f ∘ g`.
-/

namespace Artform

-- ANCHOR: lreversalproof
/-- **Proposition 5.39** (reversing a tick of two steps). Let a tick be
`F = S₁ ∘ S₀`, and let an involution `R` of the states undo each step:
`R ∘ S₀ ∘ R = S₀⁻¹` and `R ∘ S₁ ∘ R = S₁⁻¹`. Then `I₀ = R ∘ S₀` and
`I₁ = S₁ ∘ R` are involutions, and each reverses the tick:
`I₀ ∘ F ∘ I₀ = F⁻¹ = I₁ ∘ F ∘ I₁`. -/
@[book "prop:two-step-reversal"]
theorem twoStepReversal : Statement.twoStepReversal := by
  intro S S₀ S₁ R hR h₀ h₁
  -- From `R ∘ Sᵢ ∘ R = Sᵢ⁻¹` follows `Sᵢ ∘ R ∘ Sᵢ = R`.
  have k₀ : S₀ * R * S₀ = R := by
    have h : R * (S₀ * R * S₀) = 1 := by
      rw [← mul_assoc, ← mul_assoc, h₀, inv_mul_cancel]
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hR]
  have k₁ : S₁ * R * S₁ = R := by
    have h : R * (S₁ * R * S₁) = 1 := by
      rw [← mul_assoc, ← mul_assoc, h₁, inv_mul_cancel]
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hR]
  -- `F⁻¹ = S₀⁻¹ ∘ S₁⁻¹ = (R ∘ S₀ ∘ R) ∘ (R ∘ S₁ ∘ R) = R ∘ S₀ ∘ S₁ ∘ R`.
  have hF : R * S₀ * S₁ * R = (S₁ * S₀)⁻¹ := by
    calc R * S₀ * S₁ * R = R * S₀ * (R * R) * S₁ * R := by rw [hR, mul_one]
      _ = (R * S₀ * R) * (R * S₁ * R) := by simp only [mul_assoc]
      _ = (S₁ * S₀)⁻¹ := by rw [h₀, h₁, mul_inv_rev]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `I₀ ∘ I₀ = (R ∘ S₀ ∘ R) ∘ S₀ = S₀⁻¹ ∘ S₀`
    rw [← mul_assoc, h₀, inv_mul_cancel]
  · -- `I₁ ∘ I₁ = S₁ ∘ (R ∘ S₁ ∘ R) = S₁ ∘ S₁⁻¹`
    calc S₁ * R * (S₁ * R) = S₁ * (R * S₁ * R) := by simp only [mul_assoc]
      _ = 1 := by rw [h₁, mul_inv_cancel]
  · -- `I₀ ∘ F ∘ I₀ = R ∘ S₀ ∘ S₁ ∘ (S₀ ∘ R ∘ S₀) = R ∘ S₀ ∘ S₁ ∘ R`
    calc R * S₀ * (S₁ * S₀) * (R * S₀) = R * S₀ * S₁ * (S₀ * R * S₀) := by
          simp only [mul_assoc]
      _ = (S₁ * S₀)⁻¹ := by rw [k₀, hF]
  · -- `I₁ ∘ F ∘ I₁ = (S₁ ∘ R ∘ S₁) ∘ S₀ ∘ S₁ ∘ R = R ∘ S₀ ∘ S₁ ∘ R`
    calc S₁ * R * (S₁ * S₀) * (S₁ * R) = (S₁ * R * S₁) * S₀ * S₁ * R := by
          simp only [mul_assoc]
      _ = (S₁ * S₀)⁻¹ := by rw [k₁, hF]
-- ANCHOR_END: lreversalproof

/-! ## Non-vacuity -/

/-- The hypotheses of Proposition 5.39 met with a flip that is not the
identity: the two-shear step of Figure 5.43 on `ℤ/8 × ℤ/8`, with the kick
`K(p, q) = (p + q, q)` as `S₀`, the move `M(p, q) = (p, q + 2p)` as `S₁`, and
the flip `R(p, q) = (-p, q)`, which undoes each of the two shears
(Section 5.18). -/
example : ∃ K M R : Equiv.Perm (ZMod 8 × ZMod 8),
    (∀ p q, K (p, q) = (p + q, q)) ∧ (∀ p q, M (p, q) = (p, q + 2 * p)) ∧
    (∀ p q, R (p, q) = (-p, q)) ∧ R ≠ 1 ∧
    R * R = 1 ∧ R * K * R = K⁻¹ ∧ R * M * R = M⁻¹ := by
  refine ⟨⟨fun x => (x.1 + x.2, x.2), fun x => (x.1 - x.2, x.2), fun x => by simp,
      fun x => by simp⟩,
    ⟨fun x => (x.1, x.2 + 2 * x.1), fun x => (x.1, x.2 - 2 * x.1), fun x => by simp,
      fun x => by simp⟩,
    Equiv.prodCongr (Equiv.neg _) (Equiv.refl _), fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · -- `R(1, 0) = (7, 0)`
    intro h
    have h1 := congrArg (fun f : Equiv.Perm (ZMod 8 × ZMod 8) => (f (1, 0)).1) h
    exact absurd h1 (by decide)
  · ext x <;> simp
  · -- `R(K(R(p, q))) = (p - q, q) = K⁻¹(p, q)`
    ext x
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      ring
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  · -- `R(M(R(p, q))) = (p, q - 2p) = M⁻¹(p, q)`
    ext x
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      ring

end Artform
