import ArtformStages.WeylKind

/-!
# The energy likeness

The research ledger's proposal R4 reads the likeness A17 on energies: the quantum tick of light is
the Trotter step of the classical law's energy, each count read by its value of least size (finding
484 of the ledger). On one cell its kick is the signed kick of `WeylKind.lean`,
`exp(-π i κ s(b)² / n)`, at every real weight `κ`. Here R4 is read as a likeness with the classical
law over the real numbers, and that likeness is shown to force the signed kick.

* `RealLike` and `signedPhase_realLike` (ER1): at every count `b` but the top `n / 2`, the
  signed kick carries the move of one click to the move times the turn by the real number
  `κ s(b)` and the number `exp(π i κ / n)`: the classical kick read on the real values;
* `eq_signedPhase_of_realLike` (ER2): a phase that is `1` at `0` and is so like the classical
  kick at every count but the top is the signed kick: the likeness away from the wrap forces it;
* `signedPhase_eq_dialPhase_of_even` (ER3): on an odd dial at an even whole weight the signed
  kick is the dial's own phase, the quantum kick of `QuantumLight.lean` on one cell;
* `signedPhase_norm`, `signedPhase_sum_sq` (ER4): the signed kick has size `1` at every count,
  and so keeps the sum of the squares of a wave.

None of this is new: it is Villain's form of the magnetic energy, read as a phase.
-/

open Complex
open scoped Real

namespace Artform.Stages

section EnergyTick

variable {n : ℕ} [NeZero n]

/-- The top of the dial, `n / 2`: the one count at which the next count wraps. -/
def dialTop (n : ℕ) [NeZero n] : ZMod n := ((n / 2 : ℕ) : ZMod n)

/-- **Like the classical kick** of weight `κ`, read on the real values, at the count `b`: the phase
`φ` carries the move of one click to the move times the turn by the real number `κ s(b)` and the
number `exp(π i κ / n)`. -/
def RealLike (κ : ℝ) (φ : ZMod n → ℂ) (b : ZMod n) : Prop :=
  φ b = exp (π * I / n * κ) * exp (π * I / n * (2 * (κ * ((b.valMinAbs : ℤ) : ℂ)))) * φ (b + 1)

/-- At every count but the top, the next count does not wrap. -/
theorem valMinAbs_add_one_of_ne_top (b : ZMod n) (hb : b ≠ dialTop n) :
    (b + 1).valMinAbs = b.valMinAbs + 1 := by
  rcases valMinAbs_add_one b with h | h
  · exact h
  · exfalso
    apply hb
    have h1 := (b + 1).valMinAbs_mem_Ioc
    have h2 := b.valMinAbs_mem_Ioc
    simp only [Set.mem_Ioc] at h1 h2
    rw [h] at h1
    have hs : b.valMinAbs = ((n / 2 : ℕ) : ℤ) := by omega
    rw [dialTop, ← ZMod.coe_valMinAbs b, hs, Int.cast_natCast]

/-- ER1. **The signed kick is like the classical kick** at every count but the top. -/
theorem signedPhase_realLike (κ : ℝ) (b : ZMod n) (hb : b ≠ dialTop n) :
    RealLike κ (signedPhase n κ) b := by
  unfold RealLike signedPhase
  rw [valMinAbs_add_one_of_ne_top b hb, ← exp_add, ← exp_add, ← mul_add, ← mul_add]
  congr 2
  push_cast
  ring

/-- The counts `0, 1, …, n / 2 - 1` are not the top. -/
theorem natCast_ne_top {j : ℕ} (hj : j < n / 2) : (j : ZMod n) ≠ dialTop n := by
  intro h
  have := congrArg ZMod.val h
  rw [dialTop, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne n)) (by norm_num))] at this
  omega

/-- The counts `-1, -2, …` down to `-(n - n / 2 - 1)` are not the top. -/
theorem neg_natCast_ne_top {j : ℕ} (hj0 : 0 < j) (hj : j < n - n / 2) :
    -(j : ZMod n) ≠ dialTop n := by
  intro h
  have h0 : ((j + n / 2 : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_add, ← dialTop, ← h, add_neg_cancel]
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) h0

/-- ER2. **The likeness forces the signed kick**: on every dial, a phase that is `1` at `0` and is
like the classical kick of weight `κ` at every count but the top is the signed kick. -/
theorem eq_signedPhase_of_realLike (κ : ℝ) (φ : ZMod n → ℂ) (h0 : φ 0 = 1)
    (h : ∀ b, b ≠ dialTop n → RealLike κ φ b) : φ = signedPhase n κ := by
  set r : ZMod n → ℂ := fun b => φ b * (signedPhase n κ b)⁻¹ with hr
  -- the ratio to the signed kick does not change from a count to the next, but at the top
  have hstep : ∀ b, b ≠ dialTop n → r b = r (b + 1) := by
    intro b hb
    have h1 := h b hb
    have h2 := signedPhase_realLike κ b hb
    unfold RealLike at h1 h2
    simp only [hr]
    rw [h1, h2]
    have hC : exp (π * I / n * κ) * exp (π * I / n * (2 * (κ * ((b.valMinAbs : ℤ) : ℂ)))) ≠ 0 :=
      mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
    have hs := signedPhase_ne_zero (n := n) κ (b + 1)
    field_simp
  have hr0 : r 0 = 1 := by
    simp only [hr, h0, one_mul]
    rw [show signedPhase n κ 0 = 1 by simp [signedPhase], inv_one]
  -- forward: `0, 1, …, n / 2`
  have hfwd : ∀ j : ℕ, j ≤ n / 2 → r (j : ZMod n) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using hr0
    | succ j ih =>
      intro hj
      rw [Nat.cast_succ, ← hstep _ (natCast_ne_top (by omega)), ih (by omega)]
  -- backward: `0, -1, …, -(n - n / 2 - 1)`
  have hbwd : ∀ j : ℕ, j < n - n / 2 → r (-(j : ZMod n)) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using hr0
    | succ j ih =>
      intro hj
      have hne := neg_natCast_ne_top (n := n) (j := j + 1) (by omega) hj
      rw [hstep _ hne, show -((j + 1 : ℕ) : ZMod n) + 1 = -(j : ZMod n) by push_cast; ring,
        ih (by omega)]
  funext b
  have hb : r b = 1 := by
    by_cases hv : b.val ≤ n / 2
    · rw [← ZMod.natCast_zmod_val b]
      exact hfwd _ hv
    · have hlt := ZMod.val_lt b
      have heq : b = -((n - b.val : ℕ) : ZMod n) := by
        rw [Nat.cast_sub hlt.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub, neg_neg]
      rw [heq]
      exact hbwd _ (by omega)
  have hs := signedPhase_ne_zero (n := n) κ b
  simp only [hr] at hb
  field_simp at hb
  exact hb

/-- ER3. **R4 agrees with R1 at even weights**: on an odd dial, for an even whole weight `k`, the
signed kick is the dial's own phase `χ(-half · k · b²)`, the quantum kick of `QuantumLight.lean` on
one cell. -/
theorem signedPhase_eq_dialPhase_of_even (hodd : Odd n) {k : ℤ} (hk : Even k) (b : ZMod n) :
    signedPhase n k b = (ZMod.stdAddChar (-(half n * ((k : ZMod n) * (b * b)))) : ℂ) := by
  rw [dialPhase_eq_signedPhase hodd k b]
  obtain ⟨m, rfl⟩ := hk
  have : exp (π * I * ((m + m : ℤ) : ℂ) * ((b.valMinAbs : ℤ) : ℂ)) = 1 := by
    rw [show π * I * ((m + m : ℤ) : ℂ) * ((b.valMinAbs : ℤ) : ℂ) =
        ((m * b.valMinAbs : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

/-- ER4. **The signed kick has size `1`** at every count. -/
theorem signedPhase_norm (κ : ℝ) (b : ZMod n) : ‖signedPhase n κ b‖ = 1 := by
  rw [signedPhase, show π * I / n * (-((κ : ℂ) * ((b.valMinAbs : ℤ) : ℂ) ^ 2)) =
      ((-(π * κ * (b.valMinAbs : ℝ) ^ 2 / n) : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- ER4. So the signed kick keeps the sum of the squares of every wave of one cell. -/
theorem signedPhase_sum_sq (κ : ℝ) (ψ : ZMod n → ℂ) :
    ∑ b, ‖cellPhase (signedPhase n κ) ψ b‖ ^ 2 = ∑ b, ‖ψ b‖ ^ 2 := by
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [cellPhase, signedPhase_norm]

end EnergyTick

end Artform.Stages
