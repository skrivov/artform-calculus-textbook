import ArtformStages.QuantumLight

/-!
# The Weyl kind, and light in the plane and in space

The quantum law of light that the research ledger's reading R1 forces carries every Weyl operation
to a multiple of a Weyl operation (finding 474, `QuantumLight.lean`): it is of the *Weyl kind*.
Here it is asked whether a tick of that kind can carry light where light has waves, in the plane
and in space (finding 483 of the ledger).

A kick is a phase on the configurations of a cell. Its *signed* form of weight `κ`, a real
number, multiplies the wave at `b` by `exp(-π i κ s(b)² / n)`, where `s(b)` is the value of least
size of `b`, Mathlib's `ZMod.valMinAbs`: the book's signed flux. The dial's own form multiplies it
by the turn `χ(-half · κ · b²)`, the quantum kick of `QuantumLight.lean` on one cell.

* `valMinAbs_add_one` (WK1): the value of least size of `b + 1` is that of `b` plus one, or plus
  one less `n`;
* `signedPhase_carries_iff` (WK2): on a dial of at least `3`, there are `c` and `e` with
  `φ b = c · χ(e · b) · φ (b + 1)` for every `b`, `φ` the signed kick of weight `κ`, exactly when
  `κ` is a whole number `k` with `k n` even;
* `cellPhase_carries_iff` (WK3): on one cell a phase that is nowhere `0` carries the move of one
  click to a multiple of a Weyl operation exactly when such `c` and `e` exist;
  `signedPhase_half_not_carries` and `signedPhase_one_not_carries`: so the signed kick of weight
  `1/2` is of no Weyl kind on any dial of at least `3`, nor that of weight `1` on an odd dial;
* `dialPhase_eq_signedPhase` (WK4): on an odd dial the dial's own phase of a whole weight `k` is the
  signed kick of weight `k` times `exp(π i k s(b))`, which is `(-1)` to the power `k s(b)`;
* `pair_one_mode`, `modeTick_grows`, `corner_pull`, `corner_grows` (WK5): Pair on one mode is the
  table `modeTick κ ℓ g`, of determinant `1` and trace `2 - κℓg`, with `ℓ` the drift's weight; it
  multiplies some state other than `0` by a real number of size greater than `1` when `κℓ ≥ 1` and
  `g ≥ 8`, or `κℓ < 0` and `g > 0`; the corner of the zone in `d` dimensions has the pull `4d`; so
  for whole weights with `κℓ ≠ 0`, in two dimensions or more, the corner wave grows at every tick.

None of this is new: it is the arithmetic of the signed lift on a cyclic group, the Clifford
condition for a diagonal phase, and the instability of the leapfrog past Courant's limit.
-/

open Complex Matrix
open scoped Real

namespace Artform.Stages

section WeylKind

variable {n : ℕ} [NeZero n]

/-- WK1. The value of least size of `b + 1` is that of `b` plus one, or plus one less `n`. -/
theorem valMinAbs_add_one (b : ZMod n) :
    (b + 1).valMinAbs = b.valMinAbs + 1 ∨ (b + 1).valMinAbs = b.valMinAbs + 1 - n := by
  have h1 := b.valMinAbs_mem_Ioc
  have h2 := (b + 1).valMinAbs_mem_Ioc
  simp only [Set.mem_Ioc] at h1 h2
  have hc : (((b + 1).valMinAbs - b.valMinAbs - 1 : ℤ) : ZMod n) = 0 := by
    push_cast [ZMod.coe_valMinAbs]
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨m, hm⟩ := hc
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hlt : (n : ℤ) * m < n := by nlinarith
  have hgt : -(2 * (n : ℤ)) < n * m := by nlinarith
  have hm1 : m < 1 := by
    by_contra h
    have h' : 1 ≤ m := not_lt.mp h
    nlinarith
  have hm2 : -2 < m := by
    by_contra h
    have h' : m ≤ -2 := not_lt.mp h
    nlinarith
  have : m = 0 ∨ m = -1 := by omega
  rcases this with rfl | rfl
  · left
    linarith
  · right
    linarith

/-- **The signed kick** of weight `κ` on one cell: at `b`, the number `exp(-π i κ s(b)² / n)`, with
`s(b)` the value of least size of `b`. -/
noncomputable def signedPhase (n : ℕ) [NeZero n] (κ : ℝ) (b : ZMod n) : ℂ :=
  exp (π * I / n * (-(κ * ((b.valMinAbs : ℤ) : ℂ) ^ 2)))

/-- The signed kick is nowhere `0`. -/
theorem signedPhase_ne_zero (κ : ℝ) (b : ZMod n) : signedPhase n κ b ≠ 0 :=
  exp_ne_zero _

/-- The turn by a whole number `j` is `exp(π i / n · 2 j)`. -/
theorem turn_intCast (j : ℤ) :
    (ZMod.stdAddChar ((j : ℤ) : ZMod n) : ℂ) = exp (π * I / n * (2 * j)) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  ring

/-- Exponents that differ by `2 n m`, in the unit `π i / n`, give the same number. -/
theorem exp_theta_eq {P Q : ℂ} (m : ℤ) (h : P = Q + 2 * n * m) :
    exp (π * I / n * P) = exp (π * I / n * Q) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨m, by rw [h]; field_simp⟩

/-- Exponents, in the unit `π i / n`, of the same number differ by `2 n m` for a whole `m`. -/
theorem exists_of_exp_theta_eq {P Q : ℂ} (h : exp (π * I / n * P) = exp (π * I / n * Q)) :
    ∃ m : ℤ, P = Q + 2 * n * m := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hθ : (π * I / n : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero) hn0
  obtain ⟨m, hm⟩ := exp_eq_exp_iff_exists_int.1 h
  refine ⟨m, mul_left_cancel₀ hθ ?_⟩
  rw [hm]
  field_simp

omit [NeZero n] in
/-- The value of least size of `1` on a dial of at least `3`. -/
theorem valMinAbs_one (hn : 3 ≤ n) : (1 : ZMod n).valMinAbs = 1 := by
  have := ZMod.valMinAbs_natCast_of_le_half (n := n) (a := 1) (by omega)
  simpa using this

omit [NeZero n] in
/-- The value of least size of `-1` on a dial of at least `3`. -/
theorem valMinAbs_neg_one (hn : 3 ≤ n) : (-1 : ZMod n).valMinAbs = -1 := by
  have hv : (1 : ZMod n).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [ZMod.valMinAbs_neg_of_ne_half (by omega), valMinAbs_one hn]

/-- The top of the dial, `n / 2`, is its own value of least size. -/
theorem valMinAbs_top (n : ℕ) [NeZero n] : ((n / 2 : ℕ) : ZMod n).valMinAbs = (n / 2 : ℕ) :=
  ZMod.valMinAbs_natCast_of_le_half le_rfl

omit [NeZero n] in
/-- The count after the top wraps: its value of least size is `n / 2 + 1 - n`. -/
theorem valMinAbs_top_add_one (hn : 3 ≤ n) :
    (((n / 2 : ℕ) : ZMod n) + 1).valMinAbs = (n / 2 : ℕ) + 1 - n := by
  have h := ZMod.valMinAbs_natCast_of_half_lt (n := n) (a := n / 2 + 1) (by omega) (by omega)
  have hc : ((n / 2 : ℕ) : ZMod n) + 1 = ((n / 2 + 1 : ℕ) : ZMod n) := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hc, h]
  simp only [Nat.cast_add, Nat.cast_one]

omit [NeZero n] in
/-- From `1 = c · exp(θ (-κ))`: `c = exp(θ κ)`, in the unit `θ = π i / n`. -/
theorem eq_exp_of_one_eq_mul {c : ℂ} {κ : ℂ} (h : 1 = c * exp (π * I / n * -κ)) :
    c = exp (π * I / n * κ) := by
  calc c = c * exp (π * I / n * -κ + π * I / n * κ) := by
        rw [show π * I / n * -κ + π * I / n * κ = (0 : ℂ) by ring, exp_zero, mul_one]
    _ = c * exp (π * I / n * -κ) * exp (π * I / n * κ) := by rw [exp_add, mul_assoc]
    _ = exp (π * I / n * κ) := by rw [← h, one_mul]

/-- WK2. **The signed kick and the Weyl kind**: on a dial of at least `3`, the signed kick `φ` of
weight `κ` has `φ b = c · χ(e · b) · φ (b + 1)` for every `b`, for some `c` and `e`, exactly
when `κ` is a whole number `k` with `k n` even. -/
theorem signedPhase_carries_iff (hn : 3 ≤ n) (κ : ℝ) :
    (∃ c : ℂ, ∃ e : ZMod n, ∀ b : ZMod n,
        signedPhase n κ b = c * ZMod.stdAddChar (e * b) * signedPhase n κ (b + 1)) ↔
      ∃ k : ℤ, (k : ℝ) = κ ∧ Even (k * n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hs0 : signedPhase n κ 0 = 1 := by simp [signedPhase]
  have hs1 : signedPhase n κ 1 = exp (π * I / n * -(κ : ℂ)) := by
    rw [signedPhase, valMinAbs_one hn]
    congr 2
    push_cast
    ring
  have hsm1 : signedPhase n κ (-1) = exp (π * I / n * -(κ : ℂ)) := by
    rw [signedPhase, valMinAbs_neg_one hn]
    congr 2
    push_cast
    ring
  constructor
  · rintro ⟨c, e, h⟩
    set v : ℤ := e.valMinAbs with hv
    have he : e = (v : ZMod n) := (ZMod.coe_valMinAbs e).symm
    -- at `b = 0`: `c = exp(θ κ)`
    have h0 := h 0
    rw [zero_add, mul_zero, AddChar.map_zero_eq_one, mul_one, hs0, hs1] at h0
    have hc := eq_exp_of_one_eq_mul h0
    -- at `b = -1`: `exp(θ (-κ)) = exp(θ (κ - 2 v))`
    have hm1 := h (-1)
    have hturn : (ZMod.stdAddChar (e * -1) : ℂ) = exp (π * I / n * (2 * ((-v : ℤ) : ℂ))) := by
      rw [he, show ((v : ZMod n) * -1) = ((-v : ℤ) : ZMod n) by push_cast; ring, turn_intCast]
    rw [neg_add_cancel, hs0, mul_one, hsm1, hturn, hc, ← exp_add, ← mul_add] at hm1
    obtain ⟨m, hm⟩ := exists_of_exp_theta_eq hm1
    -- so `κ = v - n m`, a whole number
    have hκ : (κ : ℂ) = ((v - n * m : ℤ) : ℂ) := by
      push_cast at hm ⊢
      linear_combination -hm / 2
    set k : ℤ := v - n * m with hk
    have hκr : (k : ℝ) = κ := by exact_mod_cast hκ.symm
    refine ⟨k, hκr, ?_⟩
    -- at the top of the dial the count wraps: `k n` is even
    have htop := h ((n / 2 : ℕ) : ZMod n)
    set s : ℤ := ((n / 2 : ℕ) : ℤ) with hs
    have hturn2 : (ZMod.stdAddChar (e * ((n / 2 : ℕ) : ZMod n)) : ℂ) =
        exp (π * I / n * (2 * ((v * s : ℤ) : ℂ))) := by
      rw [he, hs, ← turn_intCast]
      congr 1
      rw [Int.cast_mul, Int.cast_natCast]
    have htopL : signedPhase n κ ((n / 2 : ℕ) : ZMod n) =
        exp (π * I / n * (-((κ : ℂ) * (s : ℂ) ^ 2))) := by
      rw [signedPhase, valMinAbs_top]
    have htopR : signedPhase n κ (((n / 2 : ℕ) : ZMod n) + 1) =
        exp (π * I / n * (-((κ : ℂ) * ((s + 1 - n : ℤ) : ℂ) ^ 2))) := by
      rw [signedPhase, valMinAbs_top_add_one hn]
    rw [htopL, htopR, hturn2, hc, ← exp_add, ← exp_add, ← mul_add, ← mul_add] at htop
    obtain ⟨j, hj⟩ := exists_of_exp_theta_eq htop
    have hvk : (v : ℂ) = k + n * m := by rw [hk]; push_cast; ring
    rw [hκ] at hj
    push_cast at hj
    rw [hvk] at hj
    have hzero : (n : ℂ) * (2 * m * s + 2 * k * (s + 1) - k * n + 2 * j) = 0 := by
      linear_combination -hj
    have hz := (mul_eq_zero.1 hzero).resolve_left hn0
    refine ⟨m * s + k * (s + 1) + j, ?_⟩
    have : ((k * n : ℤ) : ℂ) = ((m * s + k * (s + 1) + j + (m * s + k * (s + 1) + j) : ℤ) : ℂ) := by
      push_cast
      linear_combination -hz
    exact_mod_cast this
  · rintro ⟨k, rfl, j, hj⟩
    refine ⟨exp (π * I / n * (k : ℂ)), (k : ZMod n), fun b => ?_⟩
    set s : ℤ := b.valMinAbs with hs
    have hb : b = (s : ZMod n) := (ZMod.coe_valMinAbs b).symm
    have hturn : (ZMod.stdAddChar ((k : ZMod n) * b) : ℂ) =
        exp (π * I / n * (2 * ((k * s : ℤ) : ℂ))) := by
      rw [← turn_intCast, hb]
      push_cast
      rfl
    have hjC : (k : ℂ) * n = j + j := by exact_mod_cast hj
    rw [hturn, signedPhase, signedPhase, ← exp_add, ← exp_add, ← mul_add, ← mul_add, ← hs]
    rcases valMinAbs_add_one b with ht | ht
    · refine exp_theta_eq 0 ?_
      rw [ht, ← hs]
      push_cast
      ring
    · refine exp_theta_eq (j - k * (s + 1)) ?_
      rw [ht, ← hs]
      push_cast
      linear_combination (n : ℂ) * hjC

/-- The multiplication of a wave of one cell, a complex number at every count, by `φ`. -/
def cellPhase (φ : ZMod n → ℂ) : Module.End ℂ (ZMod n → ℂ) where
  toFun ψ := φ * ψ
  map_add' := mul_add φ
  map_smul' c ψ := mul_smul_comm c φ ψ

/-- **A Weyl operation of one cell** `W(b0, e0)`: at `b`, the turn by `e0 · b` of the wave at
`b + b0`; the Weyl operation of `QuantumLight.lean` on a single cell. -/
noncomputable def cellWeyl (b0 e0 : ZMod n) : Module.End ℂ (ZMod n → ℂ) where
  toFun ψ b := ZMod.stdAddChar (e0 * b) * ψ (b + b0)
  map_add' ψ φ := by
    funext b
    simp only [Pi.add_apply, mul_add]
  map_smul' c ψ := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- WK3. **One cell**: a phase `φ` that is nowhere `0` carries the move of one click `W(1, 0)` to a
multiple of a Weyl operation exactly when `φ b = c · χ(e · b) · φ (b + 1)` for some `c`, `e` and
every `b`; the Weyl operation is then `W(1, e)`. -/
theorem cellPhase_carries_iff (φ : ZMod n → ℂ) (hφ : ∀ b, φ b ≠ 0) :
    (∃ c : ℂ, ∃ b0 e0 : ZMod n,
        cellPhase φ * cellWeyl 1 0 = c • (cellWeyl b0 e0 * cellPhase φ)) ↔
      ∃ c : ℂ, ∃ e : ZMod n, ∀ b : ZMod n, φ b = c * ZMod.stdAddChar (e * b) * φ (b + 1) := by
  classical
  constructor
  · rintro ⟨c, b0, e0, h⟩
    have hb : ∀ b, φ b * (Pi.single (b + 1) 1 : ZMod n → ℂ) (b + 1) =
        c * (ZMod.stdAddChar (e0 * b) * (φ (b + b0) *
          (Pi.single (b + 1) 1 : ZMod n → ℂ) (b + b0))) := by
      intro b
      have := congrArg (fun M => M (Pi.single (b + 1) 1) b) h
      simpa [cellPhase, cellWeyl, Module.End.mul_apply] using this
    -- the move is by one click
    have h1 : b0 = 1 := by
      by_contra hne
      have h0 := hb 0
      rw [zero_add, zero_add, Pi.single_eq_same, mul_one] at h0
      have hz : (Pi.single (1 : ZMod n) (1 : ℂ) : ZMod n → ℂ) b0 = 0 := Pi.single_eq_of_ne hne 1
      rw [hz] at h0
      simp only [mul_zero] at h0
      exact hφ 0 h0
    subst h1
    refine ⟨c, e0, fun b => ?_⟩
    have := hb b
    simp only [Pi.single_eq_same, mul_one] at this
    rw [this]
    ring
  · rintro ⟨c, e, h⟩
    refine ⟨c, 1, e, LinearMap.ext fun ψ => funext fun b => ?_⟩
    simp only [Module.End.mul_apply, cellPhase, cellWeyl, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.mul_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
      AddChar.map_zero_eq_one, one_mul]
    rw [h b]
    ring

/-- WK3, the case `κ = 1/2`: on a dial of at least `3` the signed kick of weight `1/2` carries the
move of one click to no multiple of a Weyl operation. -/
theorem signedPhase_half_not_carries (hn : 3 ≤ n) :
    ¬ ∃ c : ℂ, ∃ b0 e0 : ZMod n,
      cellPhase (signedPhase n (1 / 2)) * cellWeyl 1 0 =
        c • (cellWeyl b0 e0 * cellPhase (signedPhase n (1 / 2))) := by
  rw [cellPhase_carries_iff _ (signedPhase_ne_zero _), signedPhase_carries_iff hn]
  rintro ⟨k, hk, -⟩
  have h2 : (2 * k : ℝ) = 1 := by rw [hk]; norm_num
  have : (2 * k : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- WK3, the case `κ = 1` on an odd dial: the signed kick of weight `1` carries the move of one
click to no multiple of a Weyl operation. -/
theorem signedPhase_one_not_carries (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∃ c : ℂ, ∃ b0 e0 : ZMod n,
      cellPhase (signedPhase n 1) * cellWeyl 1 0 =
        c • (cellWeyl b0 e0 * cellPhase (signedPhase n 1)) := by
  rw [cellPhase_carries_iff _ (signedPhase_ne_zero _), signedPhase_carries_iff hn]
  rintro ⟨k, hk, hev⟩
  have : k = 1 := by exact_mod_cast hk
  subst this
  rw [one_mul] at hev
  exact (Int.not_even_iff_odd.2 (by exact_mod_cast hodd)) hev

/-- WK4. **The dial's own phase on an odd dial**: for a whole weight `k`, `χ(-half · k · b²)` is the
signed kick of weight `k` times `exp(π i k s(b))`, which is `(-1)` to the power `k s(b)`. -/
theorem dialPhase_eq_signedPhase (hodd : Odd n) (k : ℤ) (b : ZMod n) :
    (ZMod.stdAddChar (-(half n * ((k : ZMod n) * (b * b)))) : ℂ) =
      signedPhase n k b * exp (π * I * k * (b.valMinAbs : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  obtain ⟨h, hh⟩ := hodd
  set s : ℤ := b.valMinAbs with hs
  have hb : b = (s : ZMod n) := (ZMod.coe_valMinAbs b).symm
  have hhalf : half n = ((h + 1 : ℤ) : ZMod n) := by
    simp only [half, hh, show (2 * h + 1 + 1) / 2 = h + 1 by omega]
    push_cast
    rfl
  have harg : -(half n * ((k : ZMod n) * (b * b))) = ((-((h + 1) * k * (s * s)) : ℤ) : ZMod n) := by
    rw [hhalf, hb]
    push_cast
    ring
  have hexp : π * I * k * (s : ℂ) = π * I / n * (n * k * s) := by
    field_simp
  rw [harg, turn_intCast, signedPhase, ← hs, hexp, ← exp_add, ← mul_add]
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self s
  have hjC : (s : ℂ) * (s + 1) = j + j := by exact_mod_cast hj
  have hnC : (n : ℂ) = 2 * h + 1 := by exact_mod_cast hh
  refine exp_theta_eq (-(k * j)) ?_
  push_cast
  rw [hnC]
  linear_combination (-(2 * (h : ℂ) + 1) * k) * hjC

/-- **Pair on one mode**: the table `modeTick κ l g` on `(a, e)`, with the kick of weight `κ g` and
the drift of weight `l`. -/
def modeTick (κ l g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - κ * l * g, -l; κ * g, 1]

/-- WK5. Pair over the real numbers on one mode, with the kick `S = (κ g)` and the drift `L = (l)`,
is `modeTick κ l g` on the line of the mode and its dual line. -/
theorem pair_one_mode (κ l g : ℝ) (x : LightState ℝ (Fin 1)) :
    ![(pair !![κ * g] !![l] x).1 0, (pair !![κ * g] !![l] x).2 0] =
      modeTick κ l g *ᵥ ![x.1 0, x.2 0] := by
  ext i
  fin_cases i
  · simp [pair, modeTick, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead]
    ring
  · simp [pair, modeTick, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead]
    ring

/-- The determinant and the trace of `modeTick`. -/
theorem modeTick_det (κ l g : ℝ) : (modeTick κ l g).det = 1 := by
  simp [modeTick, Matrix.det_fin_two]
  ring

theorem modeTick_trace (κ l g : ℝ) : (modeTick κ l g).trace = 2 - κ * l * g := by
  simp [modeTick, Matrix.trace_fin_two]
  ring

/-- WK5. **The mode grows** past the limit: when `κl ≥ 1` and `g ≥ 8`, or `κl < 0` and `g > 0`, the
table `modeTick κ l g` multiplies some state other than `0` by a real number of size greater than
`1`. -/
theorem modeTick_grows (κ l g : ℝ) (h : (1 ≤ κ * l ∧ 8 ≤ g) ∨ (κ * l < 0 ∧ 0 < g)) :
    ∃ z : ℝ, 1 < |z| ∧ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ modeTick κ l g *ᵥ v = z • v := by
  set t := 2 - κ * l * g with ht
  have hl : l ≠ 0 := by
    rintro rfl
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
    linarith
  have hdisc : 0 ≤ t ^ 2 - 4 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : t ≤ -6 := by nlinarith
      nlinarith
    · have : 2 < t := by nlinarith
      nlinarith
  set r := Real.sqrt (t ^ 2 - 4) with hr
  have hr2 : r ^ 2 = t ^ 2 - 4 := Real.sq_sqrt hdisc
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- a root of `z² - t z + 1` is a multiplier, with the state `(-l, z - (1 - κlg))`
  have root : ∀ z : ℝ, z ^ 2 - t * z + 1 = 0 →
      modeTick κ l g *ᵥ ![-l, z - (1 - κ * l * g)] = z • ![-l, z - (1 - κ * l * g)] := by
    intro z hz
    ext i
    fin_cases i
    · simp [modeTick, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [modeTick, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [ht] at hz
      linear_combination -hz
  have hv : ∀ z : ℝ, (![-l, z - (1 - κ * l * g)] : Fin 2 → ℝ) ≠ 0 := fun z hv0 =>
    hl (by simpa using congrFun hv0 0)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have htle : t ≤ -6 := by nlinarith
    refine ⟨(t - r) / 2, ?_, _, hv _, root _ (by nlinarith)⟩
    rw [abs_of_neg (by linarith)]
    linarith
  · have htgt : 2 < t := by nlinarith
    refine ⟨(t + r) / 2, ?_, _, hv _, root _ (by nlinarith)⟩
    rw [abs_of_pos (by linarith)]
    linarith

/-- The pull of the corner of the zone, `k = (π, …, π)`, in `d` dimensions:
`∑ 4 sin²(π/2) = 4 d`. -/
theorem corner_pull (d : ℕ) : ∑ _j : Fin d, 4 * Real.sin (π / 2) ^ 2 = 4 * (d : ℝ) := by
  simp only [Real.sin_pi_div_two, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- WK5. **The corner grows**: for whole weights `κ` and `l` with `κl ≠ 0`, in two dimensions or
more, Pair at the corner of the zone multiplies some state other than `0` by a real number of size
greater than `1`. -/
theorem corner_grows (κ l : ℤ) (h : κ * l ≠ 0) (d : ℕ) (hd : 2 ≤ d) :
    ∃ z : ℝ, 1 < |z| ∧ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ modeTick κ l (4 * d) *ᵥ v = z • v := by
  apply modeTick_grows
  have hd' : (8 : ℝ) ≤ 4 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rcases lt_or_gt_of_ne h with hneg | hpos
  · right
    refine ⟨?_, by linarith⟩
    have : ((κ * l : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
    simpa using this
  · left
    refine ⟨?_, hd'⟩
    have : (1 : ℝ) ≤ ((κ * l : ℤ) : ℝ) := by exact_mod_cast hpos
    simpa using this

end WeylKind

end Artform.Stages
