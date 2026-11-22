import ArtformStages.Pair
import ArtformStages.FillingWaves
import ArtformStages.KindOfNumber

/-!
# The quantum law of light

The classical law of light of the research ledger on a layered universe is Pair, `pair S L`, with
symmetric tables `S` and `L`, read here over the dial `ℤ/n`, with its pairing `omega`
(`Pair.lean`). Here it is carried up to the waves (finding 474 of the ledger). A *wave* is a
complex number on every configuration `b : V → ZMod n` of a finite set of cells `V`; the dial is
odd, so that it has a half, `(n + 1) / 2`; the turn is the dial's standard character `χ`
(`ZMod.stdAddChar`), faithful by `stdAddChar_faithful` (`KindOfNumber.lean`). A *Weyl operation*
`W(b0, e0)` is named by a state `(b0, e0)` of the classical field: its value at `b` is
`χ(e0 ⬝ b)` times the wave's value at `b + b0`. The *quantum kick* of `S` multiplies the value at
`b` by `χ(-half · b ⬝ S b)`; the *quantum drift* of `A` is the table that multiplies the electric
pattern `b ↦ χ(-(e ⬝ b))` by `χ(half · e ⬝ A e)` (`qdrift_pattern`, `eq_qdrift_of_pattern`); the
*quantum tick* is the drift of `-L` after the kick of `S`. The classical law acts on the names:

* `fourier_write`, `fourier_read` (QL0): the Fourier transform `ψ ↦ (b ↦ ∑ c, χ(-(b ⬝ c)) ψ c)`
  takes the write of a line of `FillingWaves.lean` to the turn by that line's count taken the
  other way round, which is the reading undone, and the reading of the line to its write;
* `weyl`, `weyl_comm` (QL1): `W(u) W(v) = χ(omega u v) W(v) W(u)`;
* `qkick`, `qkick_weyl` (QL2): the kick, after `W(b0, e0)`, after the kick undone, is
  `χ(half · b0 ⬝ S b0) W(b0, e0 + S b0)`;
* `qdrift`, `qdrift_weyl` (QL3): the drift, after `W(b0, e0)`, after the drift undone, is
  `χ(half · e0 ⬝ A e0) W(b0 + A e0, e0)`;
* `qtick`, `qtick_weyl` (QL4): the tick, after `W(v)`, after the tick undone, is the turn by
  `qtickTurn S L v` times `W(pair S L v)`;
* `commute_weyl_iff` (QL5): a linear map of the waves passes every `W(v)` exactly when it is a
  multiple of `1`;
* `qtick_unique`, `qtick_unique_upto_weyl` (QL6): an invertible map that carries every `W(v)` to
  the same multiple of `W(pair S L v)` as the tick is the tick times a nonzero number; one that
  carries every `W(v)` to some multiple of `W(pair S L v)` is the tick times a Weyl operation and
  a nonzero number;
* `phase_quadratic_of_carries` (QL7): a phase `φ`, nowhere `0`, that carries every Weyl operation
  to a multiple of a Weyl operation has `φ b = φ 0 · χ(-half · b ⬝ S b + β ⬝ b)` for a symmetric
  table `S` and a configuration `β`;
* `qtick_pow_weyl_iff` (QL8): the power `t` of the tick is a Weyl operation times a number exactly
  when the power `t` of `pair S L` is the identity on the dial's states.

The proofs read each table on a few waves. A map that passes the diagonal Weyl operations keeps
the wave of each configuration, since the turns tell configurations apart; passing the moves makes
its numbers equal. Every function of the configurations that takes sums to products is a turn
against one configuration (`exists_turn_of_mul`), since its Fourier transform is not `0` at some
point. None of this is new: these are the Weyl operations of a finite phase space, Schur's lemma
for them, and the quadratic phases of their symmetries.
-/

open Matrix

namespace Artform.Stages

section QuantumLight

variable {V : Type*} [Fintype V] {n : ℕ} [NeZero n]

/-- A wave of light: a complex number on every configuration `b : V → ZMod n` of the cells. -/
abbrev LightWave (V : Type*) (n : ℕ) := (V → ZMod n) → ℂ

/-- The half of the dial, `(n + 1) / 2`. -/
def half (n : ℕ) : ZMod n := ((n + 1) / 2 : ℕ)

omit [NeZero n] in
/-- On an odd dial the half is the inverse of `2`. -/
theorem two_mul_half (hn : Odd n) : 2 * half n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h0 : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
  simp only [half, hk]
  push_cast at h0 ⊢
  linear_combination h0

/-- Two turns are the turn of the sum. -/
theorem turn_mul_turn (x y : ZMod n) :
    ZMod.stdAddChar x * ZMod.stdAddChar y = (ZMod.stdAddChar (x + y) : ℂ) :=
  (AddChar.map_add_eq_mul _ x y).symm

/-- Two turns are the turn of the sum, in front of a number. -/
theorem turn_mul_turn_mul (x y : ZMod n) (z : ℂ) :
    ZMod.stdAddChar x * (ZMod.stdAddChar y * z) = (ZMod.stdAddChar (x + y) : ℂ) * z := by
  rw [← mul_assoc, turn_mul_turn]

/-- A turn is never `0`. -/
theorem turn_ne_zero (x : ZMod n) : (ZMod.stdAddChar x : ℂ) ≠ 0 := by
  intro h
  have h1 := turn_mul_turn x (-x)
  rw [h, zero_mul, add_neg_cancel, AddChar.map_zero_eq_one] at h1
  exact zero_ne_one h1

/-- The turn of `x` is `1` only at `x = 0`: the dial's turn is faithful (`stdAddChar_faithful`,
wave D3). -/
theorem turn_eq_one_iff (x : ZMod n) : (ZMod.stdAddChar x : ℂ) = 1 ↔ x = 0 :=
  ⟨stdAddChar_faithful x, fun h => h ▸ AddChar.map_zero_eq_one _⟩

/-- Two equal turns are turns by one count. -/
theorem turn_injective {x y : ZMod n} (h : (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar y) :
    x = y := by
  have h1 : (ZMod.stdAddChar (x - y) : ℂ) = 1 := by
    rw [AddChar.map_sub_eq_div, h, div_self (turn_ne_zero y)]
  exact sub_eq_zero.mp ((turn_eq_one_iff _).mp h1)

/-- Two configurations with the same turns against every configuration are equal. -/
theorem eq_of_turn_dotProduct {x y : V → ZMod n}
    (h : ∀ b : V → ZMod n, (ZMod.stdAddChar (x ⬝ᵥ b) : ℂ) = ZMod.stdAddChar (y ⬝ᵥ b)) :
    x = y := by
  classical
  funext i
  have hi := turn_injective (h (Pi.single i 1))
  simpa [dotProduct_single] using hi

/-- **A Weyl operation** `W(b0, e0)`, named by a state `v = (b0, e0)` of the classical field on
the dial: its value at `b` is the turn by `e0 ⬝ b` of the wave's value at `b + b0`. -/
noncomputable def weyl (v : LightState (ZMod n) V) : Module.End ℂ (LightWave V n) where
  toFun ψ b := ZMod.stdAddChar (v.2 ⬝ᵥ b) * ψ (b + v.1)
  map_add' ψ φ := by
    funext b
    simp only [Pi.add_apply, mul_add]
  map_smul' c ψ := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A Weyl operation, read at `b`. -/
@[simp] theorem weyl_apply (v : LightState (ZMod n) V) (ψ : LightWave V n) (b : V → ZMod n) :
    weyl v ψ b = ZMod.stdAddChar (v.2 ⬝ᵥ b) * ψ (b + v.1) := rfl

/-- Two Weyl operations make one: `W(u) W(v)` is the turn by `v.2 ⬝ u.1` times `W(u + v)`. -/
theorem weyl_mul_weyl (u v : LightState (ZMod n) V) :
    weyl u * weyl v = (ZMod.stdAddChar (v.2 ⬝ᵥ u.1) : ℂ) • weyl (u + v) := by
  refine LinearMap.ext fun ψ => funext fun b => ?_
  simp only [Module.End.mul_apply, weyl_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    Prod.fst_add, Prod.snd_add, turn_mul_turn_mul, add_assoc]
  congr 2
  rw [dotProduct_add, add_dotProduct]
  ring

/-- The Weyl operation named by the state `0` is `1`. -/
theorem weyl_zero : weyl (0 : LightState (ZMod n) V) = 1 := by
  refine LinearMap.ext fun ψ => funext fun b => ?_
  simp

/-- QL1. **Weyl operations pass up to the classical pairing**:
`W(u) W(v) = χ(omega u v) W(v) W(u)`, with `omega` Pair's pairing over the dial. -/
theorem weyl_comm (u v : LightState (ZMod n) V) :
    weyl u * weyl v = (ZMod.stdAddChar (omega u v) : ℂ) • (weyl v * weyl u) := by
  rw [weyl_mul_weyl, weyl_mul_weyl, smul_smul, turn_mul_turn, add_comm v u]
  congr 2
  simp only [omega]
  rw [dotProduct_comm v.2 u.1]
  ring

section Carry

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- From `U X = c (Y U)`, with `U` invertible: `U X U⁻¹ = c Y`. -/
theorem conj_eq_of_mul_eq (U : Aˣ) {X Y : A} {c : ℂ} (h : ↑U * X = c • (Y * ↑U)) :
    ↑U * X * ↑U⁻¹ = c • Y := by
  rw [Units.mul_inv_eq_iff_eq_mul, h, smul_mul_assoc]

/-- From `U X U⁻¹ = c Y`: `U X = c (Y U)`. -/
theorem mul_eq_of_conj_eq (U : Aˣ) {X Y : A} {c : ℂ} (h : ↑U * X * ↑U⁻¹ = c • Y) :
    ↑U * X = c • (Y * ↑U) := by
  rw [Units.mul_inv_eq_iff_eq_mul, smul_mul_assoc] at h
  exact h

/-- Carrying twice: from `U X = c (Y U)` and `U' Y = c' (Z U')`, `(U' U) X = c c' (Z (U' U))`. -/
theorem mul_carry (U U' : Aˣ) {X Y Z : A} {c c' : ℂ} (h : ↑U * X = c • (Y * ↑U))
    (h' : ↑U' * Y = c' • (Z * ↑U')) : ↑(U' * U) * X = (c * c') • (Z * ↑(U' * U)) := by
  rw [Units.val_mul, mul_assoc, h, mul_smul_comm, ← mul_assoc, h', smul_mul_assoc, smul_smul,
    mul_assoc]

/-- Carrying back: from `U X = c (Y U)` with `c ≠ 0`, `U⁻¹ Y = c⁻¹ (X U⁻¹)`. -/
theorem inv_carry (U : Aˣ) {X Y : A} {c : ℂ} (hc : c ≠ 0) (h : ↑U * X = c • (Y * ↑U)) :
    ↑U⁻¹ * Y = c⁻¹ • (X * ↑U⁻¹) := by
  have h1 : X * ↑U⁻¹ = c • (↑U⁻¹ * Y) := by
    calc X * ↑U⁻¹ = ↑U⁻¹ * (↑U * X) * ↑U⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = c • (↑U⁻¹ * Y) := by
        rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Carry

/-- The map that multiplies the value of a wave at each configuration `b` by `φ b`. -/
def phaseMul (φ : (V → ZMod n) → ℂ) : Module.End ℂ (LightWave V n) where
  toFun ψ := φ * ψ
  map_add' := mul_add φ
  map_smul' c ψ := mul_smul_comm c φ ψ

omit [Fintype V] [NeZero n] in
/-- The multiplication by `φ`, read at `b`. -/
@[simp] theorem phaseMul_apply (φ : (V → ZMod n) → ℂ) (ψ : LightWave V n) (b : V → ZMod n) :
    phaseMul φ ψ b = φ b * ψ b := rfl

/-- The invertible map that multiplies the value of a wave at each `b` by the turn by `θ b`. -/
noncomputable def turnMul (θ : (V → ZMod n) → ZMod n) : (Module.End ℂ (LightWave V n))ˣ where
  val := phaseMul fun b => ZMod.stdAddChar (θ b)
  inv := phaseMul fun b => ZMod.stdAddChar (-θ b)
  val_inv := LinearMap.ext fun ψ => funext fun b => by
    simp [turn_mul_turn_mul]
  inv_val := LinearMap.ext fun ψ => funext fun b => by
    simp [turn_mul_turn_mul]

/-- **The quantum kick** of a table `S`: the value of a wave at `b` times the turn by
`-half · b ⬝ S b`. -/
noncomputable def qkick (S : Matrix V V (ZMod n)) : (Module.End ℂ (LightWave V n))ˣ :=
  turnMul fun b => -(half n * (b ⬝ᵥ (S *ᵥ b)))

/-- The quantum kick, read at `b`. -/
theorem qkick_apply (S : Matrix V V (ZMod n)) (ψ : LightWave V n) (b : V → ZMod n) :
    (qkick S : Module.End ℂ (LightWave V n)) ψ b =
      ZMod.stdAddChar (-(half n * (b ⬝ᵥ (S *ᵥ b)))) * ψ b := rfl

/-- The kick carries `W(b0, e0)` to a turn times `W(b0, e0 + S b0)`, read without inverses. -/
theorem qkick_mul_weyl (hn : Odd n) {S : Matrix V V (ZMod n)} (hS : Sᵀ = S)
    (b0 e0 : V → ZMod n) :
    (qkick S : Module.End ℂ (LightWave V n)) * weyl (b0, e0) =
      (ZMod.stdAddChar (half n * (b0 ⬝ᵥ (S *ᵥ b0))) : ℂ) •
        (weyl (b0, e0 + S *ᵥ b0) * ↑(qkick S)) := by
  refine LinearMap.ext fun ψ => funext fun b => ?_
  simp only [Module.End.mul_apply, weyl_apply, qkick_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, turn_mul_turn_mul]
  congr 2
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, add_dotProduct,
    dotProduct_comm (S *ᵥ b0) b, dotProduct_mulVec_symm S hS b0 b]
  linear_combination (b ⬝ᵥ (S *ᵥ b0)) * two_mul_half hn

/-- QL2. **The kick carries names by the classical kick**: the quantum kick of `S`, after
`W(b0, e0)`, after the kick undone, is `χ(half · b0 ⬝ S b0)` times `W(b0, e0 + S b0)`. -/
theorem qkick_weyl (hn : Odd n) {S : Matrix V V (ZMod n)} (hS : Sᵀ = S) (b0 e0 : V → ZMod n) :
    ↑(qkick S) * weyl (b0, e0) * ↑(qkick S)⁻¹ =
      (ZMod.stdAddChar (half n * (b0 ⬝ᵥ (S *ᵥ b0))) : ℂ) • weyl (b0, e0 + S *ᵥ b0) :=
  conj_eq_of_mul_eq _ (qkick_mul_weyl hn hS b0 e0)

/-- The turn by which the quantum tick carries `W(v)` to `W(pair S L v)`:
`half · b0 ⬝ S b0 - half · e' ⬝ L e'`, with `e' = e0 + S b0` the field after the kick. -/
def qtickTurn (S L : Matrix V V (ZMod n)) (v : LightState (ZMod n) V) : ZMod n :=
  half n * (v.1 ⬝ᵥ (S *ᵥ v.1)) - half n * ((v.2 + S *ᵥ v.1) ⬝ᵥ (L *ᵥ (v.2 + S *ᵥ v.1)))

/-- A diagonal Weyl operation multiplies the wave of one configuration `c` by its turn. -/
theorem weyl_diag_single (e c : V → ZMod n) :
    weyl (0, e) (Pi.single c 1 : LightWave V n) =
      (ZMod.stdAddChar (e ⬝ᵥ c) : ℂ) • Pi.single c 1 := by
  funext b
  by_cases hb : b = c
  · subst hb
    simp
  · simp [hb]

/-- The move by `c` takes the wave of the configuration `c` to the wave of `0`. -/
theorem weyl_shift_single (c : V → ZMod n) :
    weyl (c, 0) (Pi.single c 1 : LightWave V n) = Pi.single 0 1 := by
  funext b
  by_cases hb : b = 0
  · subst hb
    simp
  · have hbc : b + c ≠ c := fun h => hb (add_eq_right.mp h)
    simp [hb, hbc]

/-- A move takes the constant wave to itself. -/
theorem weyl_shift_const (b0 : V → ZMod n) :
    weyl (b0, 0) (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext b
  simp

/-- `W(-w) W(w)` is the turn by `-(w.2 ⬝ w.1)`. -/
theorem weyl_neg_mul_weyl (w : LightState (ZMod n) V) :
    weyl (-w) * weyl w = (ZMod.stdAddChar (-(w.2 ⬝ᵥ w.1)) : ℂ) • 1 := by
  rw [weyl_mul_weyl, neg_add_cancel, weyl_zero, Prod.fst_neg, dotProduct_neg]

/-- A Weyl operation is not `0`. -/
theorem weyl_ne_zero (v : LightState (ZMod n) V) : weyl v ≠ 0 := by
  intro h
  have h' := congrFun (LinearMap.congr_fun h fun _ => 1) 0
  simp at h'

omit [Fintype V] [NeZero n] in
/-- An invertible map takes a wave other than `0` to a wave other than `0`. -/
theorem units_apply_ne_zero (M : (Module.End ℂ (LightWave V n))ˣ) {ψ : LightWave V n}
    (hψ : ψ ≠ 0) : (M : Module.End ℂ (LightWave V n)) ψ ≠ 0 := by
  intro h
  apply hψ
  have h' := congrArg (↑M⁻¹ : Module.End ℂ (LightWave V n)) h
  rwa [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, map_zero] at h'

/-- A multiple of `W(v)` other than `0` is a multiple of `W(w)` only when `v = w`. -/
theorem eq_of_smul_weyl_eq {a b : ℂ} {v w : LightState (ZMod n) V} (ha : a ≠ 0)
    (h : a • weyl v = b • weyl w) : v = w := by
  classical
  have h1 := congrFun (LinearMap.congr_fun h (Pi.single 0 1)) (-v.1)
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, weyl_apply, neg_add_cancel,
    Pi.single_eq_same, mul_one] at h1
  have hw1 : w.1 = v.1 := by
    by_contra hne
    have h0 : -v.1 + w.1 ≠ 0 := fun h0 => hne (neg_add_eq_zero.mp h0).symm
    rw [Pi.single_eq_of_ne h0, mul_zero, mul_zero] at h1
    exact mul_ne_zero ha (turn_ne_zero _) h1
  have h2 : ∀ x, a * ZMod.stdAddChar (v.2 ⬝ᵥ x) = b * ZMod.stdAddChar (w.2 ⬝ᵥ x) := by
    intro x
    have h3 := congrFun (LinearMap.congr_fun h fun _ => 1) x
    simpa using h3
  have hab : a = b := by simpa using h2 0
  have hw2 : v.2 = w.2 :=
    eq_of_turn_dotProduct fun x => mul_left_cancel₀ ha (by rw [h2 x, hab])
  exact Prod.ext hw1.symm hw2

/-- The core of QL5: a map that passes every diagonal Weyl operation and every move is a
multiple of `1`. -/
theorem eq_smul_one_of_commute (M : Module.End ℂ (LightWave V n))
    (h1 : ∀ e, M * weyl (0, e) = weyl (0, e) * M)
    (h2 : ∀ b0, M * weyl (b0, 0) = weyl (b0, 0) * M) :
    ∃ c : ℂ, M = c • 1 := by
  classical
  have hA : ∀ c b : V → ZMod n, b ≠ c → M (Pi.single c 1) b = 0 := by
    intro c b hbc
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra h
      push Not at h
      exact hbc (funext h)
    have h := congrFun (LinearMap.congr_fun (h1 (Pi.single i 1)) (Pi.single c 1)) b
    simp only [Module.End.mul_apply, weyl_diag_single, map_smul, weyl_apply, Pi.smul_apply,
      smul_eq_mul, add_zero, single_dotProduct, one_mul] at h
    by_contra hne
    exact hi (turn_injective (mul_right_cancel₀ hne h)).symm
  have hB : ∀ c : V → ZMod n, M (Pi.single c 1) = M (Pi.single c 1) c • Pi.single c 1 := by
    intro c
    funext b
    by_cases hb : b = c
    · subst hb
      simp
    · rw [hA c b hb, Pi.smul_apply, Pi.single_eq_of_ne hb, smul_zero]
  have hC : ∀ c : V → ZMod n, M (Pi.single c 1) c = M (Pi.single 0 1) 0 := by
    intro c
    have h := congrFun (LinearMap.congr_fun (h2 c) (Pi.single c 1)) 0
    simp only [Module.End.mul_apply, weyl_shift_single, weyl_apply, zero_add, dotProduct_zero,
      AddChar.map_zero_eq_one, one_mul] at h
    exact h.symm
  refine ⟨M (Pi.single 0 1) 0, (Pi.basisFun ℂ (V → ZMod n)).ext fun c => ?_⟩
  rw [Pi.basisFun_apply, LinearMap.smul_apply, Module.End.one_apply, ← hC c]
  exact hB c

/-- QL5. **Only multiples of `1` pass every Weyl operation**: a linear map of the waves passes
every `W(v)` exactly when it is a multiple of `1`. -/
theorem commute_weyl_iff (M : Module.End ℂ (LightWave V n)) :
    (∀ v : LightState (ZMod n) V, Commute M (weyl v)) ↔ ∃ c : ℂ, M = c • 1 := by
  constructor
  · intro h
    exact eq_smul_one_of_commute M (fun e => (h (0, e)).eq) fun b0 => (h (b0, 0)).eq
  · rintro ⟨c, rfl⟩ v
    exact (Commute.one_left _).smul_left c

/-- The electric pattern of `e`: the wave `b ↦ χ(-(e ⬝ b))`. -/
noncomputable def electricPattern (e : V → ZMod n) : LightWave V n :=
  fun b => ZMod.stdAddChar (-(e ⬝ᵥ b))

section Fourier

variable [DecidableEq V]

/-- The sum over the configurations of the turns against `x`: the number of configurations if
`x = 0`, and `0` otherwise. -/
theorem sum_turn_dotProduct (x : V → ZMod n) :
    ∑ c : V → ZMod n, (ZMod.stdAddChar (c ⬝ᵥ x) : ℂ) =
      if x = 0 then (Fintype.card (V → ZMod n) : ℂ) else 0 := by
  split_ifs with hx
  · subst hx
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    have hshift : ∑ c : V → ZMod n, (ZMod.stdAddChar (c ⬝ᵥ x) : ℂ) =
        ZMod.stdAddChar (x i) * ∑ c : V → ZMod n, (ZMod.stdAddChar (c ⬝ᵥ x) : ℂ) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight (Pi.single i 1)) _ _ fun c => ?_
      rw [Equiv.subRight_apply, turn_mul_turn, sub_dotProduct, single_dotProduct, one_mul,
        add_sub_cancel]
    have hne : (ZMod.stdAddChar (x i) : ℂ) ≠ 1 := fun h => hi ((turn_eq_one_iff _).mp h)
    have h2 : (1 - ZMod.stdAddChar (x i)) *
        ∑ c : V → ZMod n, (ZMod.stdAddChar (c ⬝ᵥ x) : ℂ) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h

/-- The number of configurations is not `0`. -/
theorem card_config_ne_zero : (Fintype.card (V → ZMod n) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The Fourier transform of the waves: at `k`, the sum over `c` of the turn by `-(k ⬝ c)` times
the value at `c`. -/
noncomputable def fourierMap : Module.End ℂ (LightWave V n) where
  toFun ψ k := ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ψ c
  map_add' ψ φ := by
    funext k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a ψ := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_left_comm _ _ _

/-- The Fourier transform undone: at `b`, the mean over `k` of the turn by `b ⬝ k` times the
value at `k`. -/
noncomputable def fourierInvMap : Module.End ℂ (LightWave V n) where
  toFun ψ b := (Fintype.card (V → ZMod n) : ℂ)⁻¹ * ∑ k, ZMod.stdAddChar (b ⬝ᵥ k) * ψ k
  map_add' ψ φ := by
    funext b
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a ψ := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring

/-- The Fourier transform, read at `k`. -/
theorem fourierMap_apply (ψ : LightWave V n) (k : V → ZMod n) :
    fourierMap ψ k = ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ψ c := rfl

/-- The Fourier transform undone, read at `b`. -/
theorem fourierInvMap_apply (ψ : LightWave V n) (b : V → ZMod n) :
    fourierInvMap ψ b =
      (Fintype.card (V → ZMod n) : ℂ)⁻¹ * ∑ k, ZMod.stdAddChar (b ⬝ᵥ k) * ψ k := rfl

/-- The inverse transform undoes the transform. -/
theorem fourierInv_fourier :
    fourierInvMap * fourierMap = (1 : Module.End ℂ (LightWave V n)) := by
  refine LinearMap.ext fun ψ => funext fun b => ?_
  rw [Module.End.mul_apply, fourierInvMap_apply, Module.End.one_apply]
  have h : ∀ c, ∑ k : V → ZMod n,
      ZMod.stdAddChar (b ⬝ᵥ k) * (ZMod.stdAddChar (-(k ⬝ᵥ c)) * ψ c) =
        (if b - c = 0 then (Fintype.card (V → ZMod n) : ℂ) else 0) * ψ c := by
    intro c
    rw [← sum_turn_dotProduct (b - c), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [turn_mul_turn_mul, dotProduct_sub, dotProduct_comm b k, sub_eq_add_neg]
  have key : ∑ k, ZMod.stdAddChar (b ⬝ᵥ k) * fourierMap ψ k =
      (Fintype.card (V → ZMod n) : ℂ) * ψ b := by
    simp only [fourierMap_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [h, sub_eq_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [key, inv_mul_cancel_left₀ card_config_ne_zero]

/-- The transform undoes the inverse transform. -/
theorem fourier_fourierInv :
    fourierMap * fourierInvMap = (1 : Module.End ℂ (LightWave V n)) := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  rw [Module.End.mul_apply, fourierMap_apply, Module.End.one_apply]
  have h : ∀ j, ∑ c : V → ZMod n,
      ZMod.stdAddChar (-(k ⬝ᵥ c)) * (ZMod.stdAddChar (c ⬝ᵥ j) * ψ j) =
        (if j - k = 0 then (Fintype.card (V → ZMod n) : ℂ) else 0) * ψ j := by
    intro j
    rw [← sum_turn_dotProduct (j - k), Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [turn_mul_turn_mul, dotProduct_sub, dotProduct_comm k c]
    ring_nf
  have key : ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ∑ j, ZMod.stdAddChar (c ⬝ᵥ j) * ψ j =
      (Fintype.card (V → ZMod n) : ℂ) * ψ k := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [h, sub_eq_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hpull : ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * fourierInvMap ψ c =
      (Fintype.card (V → ZMod n) : ℂ)⁻¹ *
        ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ∑ j, ZMod.stdAddChar (c ⬝ᵥ j) * ψ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [fourierInvMap_apply]; ring
  rw [hpull, key, inv_mul_cancel_left₀ card_config_ne_zero]

/-- The Fourier transform, an invertible map of the waves. -/
noncomputable def waveFourier : (Module.End ℂ (LightWave V n))ˣ where
  val := fourierMap
  inv := fourierInvMap
  val_inv := fourier_fourierInv
  inv_val := fourierInv_fourier

/-- The Fourier transform carries `W(b0, e0)` to a turn times `W(-e0, b0)`: the names cross
over. -/
theorem fourier_mul_weyl (b0 e0 : V → ZMod n) :
    (waveFourier (V := V) (n := n) : Module.End ℂ (LightWave V n)) * weyl (b0, e0) =
      (ZMod.stdAddChar (-(e0 ⬝ᵥ b0)) : ℂ) •
        (weyl (-e0, b0) * ↑(waveFourier (V := V) (n := n))) := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  change ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * (ZMod.stdAddChar (e0 ⬝ᵥ c) * ψ (c + b0)) =
    ZMod.stdAddChar (-(e0 ⬝ᵥ b0)) * (ZMod.stdAddChar (b0 ⬝ᵥ k) *
      ∑ c, ZMod.stdAddChar (-((k + -e0) ⬝ᵥ c)) * ψ c)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight b0) _ _ fun c => ?_
  rw [Equiv.coe_addRight, turn_mul_turn_mul, turn_mul_turn_mul, turn_mul_turn_mul]
  congr 2
  rw [add_dotProduct, dotProduct_add, dotProduct_add, neg_dotProduct, neg_dotProduct,
    dotProduct_comm b0 k]
  ring

/-- The inverse transform carries `W(p, q)` to a turn times `W(q, -p)`. -/
theorem fourierInv_mul_weyl (p q : V → ZMod n) :
    (↑(waveFourier (V := V) (n := n))⁻¹ : Module.End ℂ (LightWave V n)) * weyl (p, q) =
      (ZMod.stdAddChar (-(p ⬝ᵥ q)) : ℂ) • (weyl (q, -p) * ↑(waveFourier (V := V) (n := n))⁻¹) := by
  have h := fourier_mul_weyl (V := V) (n := n) q (-p)
  rw [neg_neg, neg_dotProduct, neg_neg] at h
  rw [inv_carry waveFourier (turn_ne_zero _) h, AddChar.map_neg_eq_inv]

/-- The transform loses nothing. -/
theorem fourierMap_injective :
    Function.Injective (fourierMap : Module.End ℂ (LightWave V n)) := by
  intro ψ φ h
  have h' := congrArg fourierInvMap h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, fourierInv_fourier] at h'

omit [DecidableEq V] in
/-- A function of the configurations that is `1` at `0` and takes sums to products is the turn
against one configuration `β`: every character of the configurations is a turn. -/
theorem exists_turn_of_mul (ρ : (V → ZMod n) → ℂ) (h0 : ρ 0 = 1)
    (hmul : ∀ x y, ρ (x + y) = ρ x * ρ y) :
    ∃ β : V → ZMod n, ∀ b, ρ b = ZMod.stdAddChar (β ⬝ᵥ b) := by
  classical
  have hρ : fourierMap ρ ≠ 0 := by
    intro h
    have h' : fourierMap ρ = fourierMap (0 : LightWave V n) := by rw [h, map_zero]
    have h1 := congrFun (fourierMap_injective h') 0
    rw [h0] at h1
    exact one_ne_zero h1
  obtain ⟨k, hk⟩ : ∃ k, fourierMap ρ k ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ (funext h)
  refine ⟨k, fun b0 => ?_⟩
  have hshift : fourierMap ρ k = ZMod.stdAddChar (-(k ⬝ᵥ b0)) * ρ b0 * fourierMap ρ k := by
    rw [fourierMap_apply, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight b0) _ _ fun c => ?_
    rw [Equiv.subRight_apply]
    have hc : ρ c = ρ (c - b0) * ρ b0 := by rw [← hmul, sub_add_cancel]
    have hx : -(k ⬝ᵥ c) = -(k ⬝ᵥ b0) + -(k ⬝ᵥ (c - b0)) := by rw [dotProduct_sub]; ring
    rw [hc, hx, ← turn_mul_turn]
    ring
  have h1 : ZMod.stdAddChar (-(k ⬝ᵥ b0)) * ρ b0 = 1 :=
    mul_right_cancel₀ hk (hshift.symm.trans (one_mul _).symm)
  calc ρ b0 = ZMod.stdAddChar (k ⬝ᵥ b0) * (ZMod.stdAddChar (-(k ⬝ᵥ b0)) * ρ b0) := by
        rw [turn_mul_turn_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
    _ = ZMod.stdAddChar (k ⬝ᵥ b0) := by rw [h1, mul_one]

omit [DecidableEq V] in
/-- An invertible map that carries every `W(v)` to a multiple of `W(v)` is a nonzero number times
one Weyl operation. -/
theorem exists_eq_smul_weyl (M : (Module.End ℂ (LightWave V n))ˣ)
    (h : ∀ v : LightState (ZMod n) V, ∃ c : ℂ, ↑M * weyl v = c • (weyl v * ↑M)) :
    ∃ (c : ℂ) (w : LightState (ZMod n) V), c ≠ 0 ∧
      (M : Module.End ℂ (LightWave V n)) = c • weyl w := by
  classical
  choose d hd using h
  -- the diagonal operations, read on the wave of the configuration `0`
  have hM0 : (M : Module.End ℂ (LightWave V n)) (Pi.single 0 1) ≠ 0 := by
    refine units_apply_ne_zero M fun h0 => ?_
    have h1 := congrFun h0 0
    simp at h1
  obtain ⟨bs, hbs⟩ : ∃ bs, (M : Module.End ℂ (LightWave V n)) (Pi.single 0 1) bs ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hM0 (funext hc)
  have hdiag : ∀ e, d (0, e) * ZMod.stdAddChar (bs ⬝ᵥ e) = 1 := by
    intro e
    have h1 := congrFun (LinearMap.congr_fun (hd (0, e)) (Pi.single 0 1)) bs
    simp only [Module.End.mul_apply, weyl_diag_single, dotProduct_zero, AddChar.map_zero_eq_one,
      one_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, weyl_apply, add_zero] at h1
    rw [← mul_assoc, dotProduct_comm e bs] at h1
    exact mul_right_cancel₀ hbs (h1.symm.trans (one_mul _).symm)
  -- the moves, read on the constant wave
  obtain ⟨φ, hφ⟩ : ∃ φ : LightWave V n, (M : Module.End ℂ (LightWave V n)) (fun _ => 1) = φ :=
    ⟨_, rfl⟩
  have hrel : ∀ b0 b, φ b = d (b0, 0) * φ (b + b0) := by
    intro b0 b
    have h1 := congrFun (LinearMap.congr_fun (hd (b0, 0)) fun _ => 1) b
    simp only [Module.End.mul_apply, weyl_shift_const, hφ, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, weyl_apply, zero_dotProduct, AddChar.map_zero_eq_one, one_mul] at h1
    exact h1
  have hφ0 : φ 0 ≠ 0 := by
    intro h0
    refine units_apply_ne_zero M (ψ := fun _ => 1) (fun h1 => one_ne_zero (congrFun h1 0)) ?_
    rw [hφ]
    funext b
    rw [hrel (-b) b, add_neg_cancel, h0, mul_zero, Pi.zero_apply]
  have hkey : ∀ x y, φ (x + y) * φ 0 = φ x * φ y := by
    intro x y
    have e1 := hrel y 0
    rw [zero_add] at e1
    rw [hrel y x, e1]
    ring
  obtain ⟨β, hβ⟩ := exists_turn_of_mul (fun b => φ b / φ 0) (div_self hφ0) fun x y => by
    rw [div_mul_div_comm, div_eq_div_iff hφ0 (mul_ne_zero hφ0 hφ0)]
    linear_combination (φ 0) * hkey x y
  have hβ' : ∀ b, φ b / φ 0 = ZMod.stdAddChar (β ⬝ᵥ b) := hβ
  have htrans : ∀ b0, d (b0, 0) * ZMod.stdAddChar (β ⬝ᵥ b0) = 1 := by
    intro b0
    have e1 := hrel b0 0
    rw [zero_add] at e1
    rw [← hβ' b0, mul_div_assoc', ← e1, div_self hφ0]
  -- one Weyl operation carries both kinds back
  have hcomm : ∀ v, d v * ZMod.stdAddChar (omega (bs, -β) v) = 1 →
      weyl (bs, -β) * ↑M * weyl v = weyl v * (weyl (bs, -β) * ↑M) := by
    intro v hv
    rw [mul_assoc, hd v, mul_smul_comm, ← mul_assoc, weyl_comm (bs, -β) v, smul_mul_assoc,
      smul_smul, hv, one_smul, mul_assoc]
  have hc1 : ∀ e, d (0, e) * ZMod.stdAddChar (omega (bs, -β) (0, e)) = 1 := by
    intro e
    simp only [omega, dotProduct_zero, sub_zero]
    exact hdiag e
  have hc2 : ∀ b0, d (b0, 0) * ZMod.stdAddChar (omega (bs, -β) (b0, 0)) = 1 := by
    intro b0
    simp only [omega, dotProduct_zero, zero_sub, neg_dotProduct, neg_neg]
    exact htrans b0
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute (weyl (bs, -β) * (M : Module.End ℂ (LightWave V n)))
    (fun e => hcomm _ (hc1 e)) fun b0 => hcomm _ (hc2 b0)
  have h1 : weyl (-(bs, -β)) * (weyl (bs, -β) * ↑M) =
      (ZMod.stdAddChar (-((bs, -β).2 ⬝ᵥ (bs, -β).1)) : ℂ) •
        (M : Module.End ℂ (LightWave V n)) := by
    rw [← mul_assoc, weyl_neg_mul_weyl, smul_mul_assoc, one_mul]
  rw [hc, mul_smul_comm, mul_one] at h1
  refine ⟨ZMod.stdAddChar ((bs, -β).2 ⬝ᵥ (bs, -β).1) * c, -(bs, -β), ?_, ?_⟩
  · intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact turn_ne_zero _ h0
    · rw [h0, zero_smul] at h1
      rcases smul_eq_zero.mp h1.symm with h2 | h2
      · exact turn_ne_zero _ h2
      · exact Units.ne_zero M h2
  · rw [mul_smul, h1, smul_smul, turn_mul_turn, add_neg_cancel, AddChar.map_zero_eq_one,
      one_smul]

omit [DecidableEq V] in
/-- QL7. **A phase that carries names is quadratic**: a map that multiplies the value at each `b`
by a nonzero number `φ b`, and that carries every Weyl operation to a multiple of a Weyl
operation, has `φ b = φ 0 · χ(-half · b ⬝ S b + β ⬝ b)` for some symmetric table `S` and some
configuration `β`. -/
theorem phase_quadratic_of_carries (hn : Odd n) (φ : (V → ZMod n) → ℂ) (hφ : ∀ b, φ b ≠ 0)
    (h : ∀ v : LightState (ZMod n) V, ∃ (c : ℂ) (w : LightState (ZMod n) V),
      phaseMul φ * weyl v * phaseMul φ⁻¹ = c • weyl w) :
    ∃ (S : Matrix V V (ZMod n)) (β : V → ZMod n), Sᵀ = S ∧
      ∀ b, φ b = φ 0 * ZMod.stdAddChar (-(half n * (b ⬝ᵥ (S *ᵥ b))) + β ⬝ᵥ b) := by
  classical
  choose c w hw using fun b0 : V → ZMod n => h (b0, 0)
  -- the moves, read on the constant wave
  have hrel : ∀ b0 b, φ b * (φ (b + b0))⁻¹ = c b0 * ZMod.stdAddChar ((w b0).2 ⬝ᵥ b) := by
    intro b0 b
    have h1 := congrFun (LinearMap.congr_fun (hw b0) fun _ => 1) b
    simp only [Module.End.mul_apply, phaseMul_apply, weyl_apply, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, Pi.inv_apply, mul_one, zero_dotProduct,
      AddChar.map_zero_eq_one, one_mul] at h1
    exact h1
  have hR : ∀ b0 b, φ (b + b0) * φ 0 = φ b * φ b0 * ZMod.stdAddChar (-(w b0).2 ⬝ᵥ b) := by
    intro b0 b
    have e0 := hrel b0 0
    rw [zero_add, dotProduct_zero, AddChar.map_zero_eq_one, mul_one] at e0
    have e1' : φ b = c b0 * ZMod.stdAddChar ((w b0).2 ⬝ᵥ b) * φ (b + b0) := by
      rw [← hrel b0 b, mul_assoc, inv_mul_cancel₀ (hφ _), mul_one]
    have e0' : φ 0 = c b0 * φ b0 := by
      rw [← e0, mul_assoc, inv_mul_cancel₀ (hφ _), mul_one]
    have hχ : ZMod.stdAddChar ((w b0).2 ⬝ᵥ b) * ZMod.stdAddChar (-(w b0).2 ⬝ᵥ b) = (1 : ℂ) := by
      rw [turn_mul_turn, neg_dotProduct, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [e1', e0']
    linear_combination (-(c b0 * φ (b + b0) * φ b0)) * hχ
  -- the phase relative to its value at `0`, and the linear form of each move
  obtain ⟨μ, hμ⟩ : ∃ μ : (V → ZMod n) → (V → ZMod n), ∀ b0, μ b0 = -(w b0).2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (V → ZMod n) → ℂ, ∀ b, ψ b = φ b / φ 0 := ⟨_, fun _ => rfl⟩
  have hψ0 : ∀ b, ψ b ≠ 0 := fun b => by
    rw [hψ]
    exact div_ne_zero (hφ b) (hφ 0)
  have hψR : ∀ b0 b, ψ (b + b0) = ψ b * ψ b0 * ZMod.stdAddChar (μ b0 ⬝ᵥ b) := by
    intro b0 b
    rw [hψ, hψ, hψ, hμ, div_mul_div_comm, div_mul_eq_mul_div, ← hR b0 b,
      mul_div_mul_right _ _ (hφ 0)]
  -- the linear form is symmetric
  have hsym : ∀ b b0, μ b0 ⬝ᵥ b = μ b ⬝ᵥ b0 := by
    intro b b0
    have h2 := hψR b b0
    rw [add_comm b0 b, hψR b0 b] at h2
    apply turn_injective
    have h3 : ψ b * ψ b0 * ZMod.stdAddChar (μ b0 ⬝ᵥ b) =
        ψ b * ψ b0 * ZMod.stdAddChar (μ b ⬝ᵥ b0) := by
      rw [h2]
      ring
    exact mul_left_cancel₀ (mul_ne_zero (hψ0 b) (hψ0 b0)) h3
  -- and it adds
  have hadd : ∀ b0 b1, μ (b0 + b1) = μ b0 + μ b1 := by
    intro b0 b1
    apply eq_of_turn_dotProduct
    intro b
    have h1 := hψR (b0 + b1) b
    rw [← add_assoc, hψR b1 (b + b0), hψR b0 b, hψR b1 b0, dotProduct_add,
      ← turn_mul_turn] at h1
    rw [add_dotProduct, ← turn_mul_turn]
    have hne : ψ b * ψ b0 * ψ b1 * ZMod.stdAddChar (μ b1 ⬝ᵥ b0) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (hψ0 b) (hψ0 b0)) (hψ0 b1)) (turn_ne_zero _)
    apply mul_left_cancel₀ hne
    linear_combination (-1 : ℂ) * h1
  -- so it is a symmetric table
  obtain ⟨M, hM⟩ : ∃ M : Matrix V V (ZMod n), ∀ b0, M *ᵥ b0 = μ b0 :=
    ⟨LinearMap.toMatrix' ((AddMonoidHom.mk' μ hadd).toZModLinearMap n), fun b0 =>
      LinearMap.toMatrix'_mulVec _ b0⟩
  have hMsym : Mᵀ = M := by
    ext i j
    rw [transpose_apply]
    have h1 := hsym (Pi.single i 1) (Pi.single j 1)
    rw [← hM, ← hM, dotProduct_single, dotProduct_single, mul_one, mul_one, mulVec_single_one,
      mulVec_single_one, col_apply, col_apply] at h1
    exact h1.symm
  -- the phase less its quadratic part is a character
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (V → ZMod n) → ℂ,
      ∀ b, ρ b = ψ b * ZMod.stdAddChar (-(half n * (b ⬝ᵥ (M *ᵥ b)))) := ⟨_, fun _ => rfl⟩
  have hρ0 : ρ 0 = 1 := by
    rw [hρ, hψ, div_self (hφ 0), mulVec_zero, dotProduct_zero, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, mul_one]
  have hρmul : ∀ x y, ρ (x + y) = ρ x * ρ y := by
    intro x y
    have he : μ y ⬝ᵥ x + -(half n * ((x + y) ⬝ᵥ (M *ᵥ (x + y)))) =
        -(half n * (x ⬝ᵥ (M *ᵥ x))) + -(half n * (y ⬝ᵥ (M *ᵥ y))) := by
      rw [← hM, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
        dotProduct_comm (M *ᵥ y) x, dotProduct_mulVec_symm M hMsym y x]
      linear_combination (-(x ⬝ᵥ (M *ᵥ y))) * two_mul_half hn
    rw [hρ, hρ, hρ, hψR y x, mul_assoc (ψ x * ψ y), turn_mul_turn, he, ← turn_mul_turn]
    ring
  obtain ⟨β, hβ⟩ := exists_turn_of_mul ρ hρ0 hρmul
  refine ⟨-M, β, by rw [transpose_neg, hMsym], fun b => ?_⟩
  have hψb : ψ b = ZMod.stdAddChar (β ⬝ᵥ b) * ZMod.stdAddChar (half n * (b ⬝ᵥ (M *ᵥ b))) := by
    rw [← hβ b, hρ, mul_assoc, turn_mul_turn, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  have hφb : φ b = φ 0 * ψ b := by
    rw [hψ, mul_div_assoc', mul_div_cancel_left₀ _ (hφ 0)]
  rw [hφb, hψb, turn_mul_turn]
  congr 2
  rw [neg_mulVec, dotProduct_neg]
  ring

/-- **The quantum drift** of a table `A`: the Fourier transform undone, after the kick of `-A`,
after the transform. It multiplies the electric pattern of `e` by `χ(half · e ⬝ A e)`
(`qdrift_pattern`), and it is the only table that does (`eq_qdrift_of_pattern`). -/
noncomputable def qdrift (A : Matrix V V (ZMod n)) : (Module.End ℂ (LightWave V n))ˣ :=
  waveFourier⁻¹ * (qkick (-A) * waveFourier)

omit [DecidableEq V] in
/-- The electric pattern of `e`, read at `b`. -/
theorem electricPattern_apply (e b : V → ZMod n) :
    electricPattern e b = ZMod.stdAddChar (-(e ⬝ᵥ b)) := rfl

/-- The drift is the table that multiplies the electric pattern of `e` by `χ(half · e ⬝ A e)`:
the quantum drift of the registration. -/
theorem qdrift_pattern (A : Matrix V V (ZMod n)) (e : V → ZMod n) :
    (qdrift A : Module.End ℂ (LightWave V n)) (electricPattern e) =
      (ZMod.stdAddChar (half n * (e ⬝ᵥ (A *ᵥ e))) : ℂ) • electricPattern e := by
  have hF : fourierMap (electricPattern e) =
      (Fintype.card (V → ZMod n) : ℂ) • (Pi.single (-e) 1 : LightWave V n) := by
    funext k
    rw [fourierMap_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ∀ c, (ZMod.stdAddChar (-(k ⬝ᵥ c)) : ℂ) * electricPattern e c =
        ZMod.stdAddChar (c ⬝ᵥ (-(k + e))) := by
      intro c
      rw [electricPattern_apply, turn_mul_turn, dotProduct_neg, dotProduct_add,
        dotProduct_comm c k, dotProduct_comm c e, neg_add]
    rw [Finset.sum_congr rfl fun c _ => h1 c, sum_turn_dotProduct]
    by_cases hk : k = -e
    · subst hk
      simp
    · have hk' : -(k + e) ≠ 0 := fun h0 => hk (eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h0))
      rw [ite_eq_right hk', Pi.single_eq_of_ne hk, mul_zero]
  have hK : (qkick (-A) : Module.End ℂ (LightWave V n)) (Pi.single (-e) 1) =
      (ZMod.stdAddChar (half n * (e ⬝ᵥ (A *ᵥ e))) : ℂ) • Pi.single (-e) 1 := by
    funext k
    rw [qkick_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = -e
    · subst hk
      rw [Pi.single_eq_same, neg_mulVec, mulVec_neg, neg_neg, neg_dotProduct, mul_neg, neg_neg]
    · rw [Pi.single_eq_of_ne hk, mul_zero, mul_zero]
  have hFi : fourierInvMap (Pi.single (-e) 1 : LightWave V n) =
      (Fintype.card (V → ZMod n) : ℂ)⁻¹ • electricPattern e := by
    funext b
    rw [fourierInvMap_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_eq_single (-e)]
    · rw [Pi.single_eq_same, mul_one, electricPattern_apply, dotProduct_neg, dotProduct_comm]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change fourierInvMap ((qkick (-A) : Module.End ℂ (LightWave V n))
    (fourierMap (electricPattern e))) = _
  rw [hF, map_smul, hK, map_smul, map_smul, hFi, smul_smul, smul_smul,
    mul_comm _ (ZMod.stdAddChar _), mul_assoc, mul_inv_cancel₀ card_config_ne_zero, mul_one]

/-- Every wave is a sum of electric patterns: the transform undone, read at `b`. -/
theorem eq_sum_electricPattern (ψ : LightWave V n) :
    ψ = ∑ k, ((Fintype.card (V → ZMod n) : ℂ)⁻¹ * fourierMap ψ k) • electricPattern (-k) := by
  have h := LinearMap.congr_fun fourierInv_fourier ψ
  rw [Module.End.mul_apply, Module.End.one_apply] at h
  conv_lhs => rw [← h]
  funext b
  rw [fourierInvMap_apply, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, electricPattern_apply, neg_dotProduct, neg_neg, dotProduct_comm]
  ring

/-- The drift is the only table that multiplies each electric pattern of `e` by
`χ(half · e ⬝ A e)`. -/
theorem eq_qdrift_of_pattern (A : Matrix V V (ZMod n)) (M : Module.End ℂ (LightWave V n))
    (hM : ∀ e, M (electricPattern e) =
      (ZMod.stdAddChar (half n * (e ⬝ᵥ (A *ᵥ e))) : ℂ) • electricPattern e) :
    M = qdrift A := by
  refine LinearMap.ext fun ψ => ?_
  rw [eq_sum_electricPattern ψ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, hM, qdrift_pattern]

/-- The drift carries `W(b0, e0)` to a turn times `W(b0 + A e0, e0)`, read without inverses. -/
theorem qdrift_mul_weyl (hn : Odd n) {A : Matrix V V (ZMod n)} (hA : Aᵀ = A)
    (b0 e0 : V → ZMod n) :
    (qdrift A : Module.End ℂ (LightWave V n)) * weyl (b0, e0) =
      (ZMod.stdAddChar (half n * (e0 ⬝ᵥ (A *ᵥ e0))) : ℂ) •
        (weyl (b0 + A *ᵥ e0, e0) * ↑(qdrift A)) := by
  have hA' : (-A)ᵀ = -A := by rw [transpose_neg, hA]
  have h := mul_carry _ _ (mul_carry _ _ (fourier_mul_weyl b0 e0)
    (qkick_mul_weyl hn hA' (-e0) b0)) (fourierInv_mul_weyl (-e0) (b0 + (-A) *ᵥ -e0))
  have hq : ((b0 + (-A) *ᵥ -e0, - -e0) : LightState (ZMod n) V) = (b0 + A *ᵥ e0, e0) := by
    rw [neg_mulVec, mulVec_neg, neg_neg, neg_neg]
  have hph : -(e0 ⬝ᵥ b0) + half n * (-e0 ⬝ᵥ ((-A) *ᵥ -e0)) + -(-e0 ⬝ᵥ (b0 + (-A) *ᵥ -e0)) =
      half n * (e0 ⬝ᵥ (A *ᵥ e0)) := by
    rw [neg_mulVec, mulVec_neg, neg_neg, neg_dotProduct, neg_dotProduct, dotProduct_add]
    linear_combination (-(e0 ⬝ᵥ (A *ᵥ e0))) * two_mul_half hn
  rw [hq, turn_mul_turn, turn_mul_turn, hph] at h
  exact h

/-- QL3. **The drift carries names by the classical drift**: the quantum drift of `A`, after
`W(b0, e0)`, after the drift undone, is `χ(half · e0 ⬝ A e0)` times `W(b0 + A e0, e0)`. -/
theorem qdrift_weyl (hn : Odd n) {A : Matrix V V (ZMod n)} (hA : Aᵀ = A) (b0 e0 : V → ZMod n) :
    ↑(qdrift A) * weyl (b0, e0) * ↑(qdrift A)⁻¹ =
      (ZMod.stdAddChar (half n * (e0 ⬝ᵥ (A *ᵥ e0))) : ℂ) • weyl (b0 + A *ᵥ e0, e0) :=
  conj_eq_of_mul_eq _ (qdrift_mul_weyl hn hA b0 e0)

/-- **The quantum tick** of the tables `S` and `L`: the drift of `-L` after the kick of `S`. -/
noncomputable def qtick (S L : Matrix V V (ZMod n)) : (Module.End ℂ (LightWave V n))ˣ :=
  qdrift (-L) * qkick S

/-- The tick carries `W(v)` to a turn times `W(pair S L v)`, read without inverses. -/
theorem qtick_mul_weyl (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S) (hL : Lᵀ = L)
    (v : LightState (ZMod n) V) :
    (qtick S L : Module.End ℂ (LightWave V n)) * weyl v =
      (ZMod.stdAddChar (qtickTurn S L v) : ℂ) • (weyl (pair S L v) * ↑(qtick S L)) := by
  obtain ⟨b0, e0⟩ := v
  have hL' : (-L)ᵀ = -L := by rw [transpose_neg, hL]
  have h := mul_carry _ _ (qkick_mul_weyl hn hS b0 e0) (qdrift_mul_weyl hn hL' b0 (e0 + S *ᵥ b0))
  have hname : pair S L (b0, e0) = (b0 + (-L) *ᵥ (e0 + S *ᵥ b0), e0 + S *ᵥ b0) := by
    rw [neg_mulVec, ← sub_eq_add_neg]
    rfl
  have hturn : qtickTurn S L (b0, e0) = half n * (b0 ⬝ᵥ (S *ᵥ b0)) +
      half n * ((e0 + S *ᵥ b0) ⬝ᵥ ((-L) *ᵥ (e0 + S *ᵥ b0))) := by
    rw [neg_mulVec, dotProduct_neg, mul_neg, ← sub_eq_add_neg]
    rfl
  rw [hname, hturn, ← turn_mul_turn]
  exact h

/-- QL4. **The quantum tick carries names by Pair**: for symmetric `S` and `L`, the quantum tick,
after `W(v)`, after the tick undone, is a turn times `W(pair S L v)`. -/
theorem qtick_weyl (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S) (hL : Lᵀ = L)
    (v : LightState (ZMod n) V) :
    ↑(qtick S L) * weyl v * ↑(qtick S L)⁻¹ =
      (ZMod.stdAddChar (qtickTurn S L v) : ℂ) • weyl (pair S L v) :=
  conj_eq_of_mul_eq _ (qtick_mul_weyl hn hS hL v)

/-- The power `t` of the tick carries `W(v)` to a number times `W((pair S L)^[t] v)`. -/
theorem qtick_pow_mul_weyl (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S)
    (hL : Lᵀ = L) (t : ℕ) (v : LightState (ZMod n) V) :
    ∃ c : ℂ, (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n)) * weyl v =
      c • (weyl ((pair S L)^[t] v) * (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n))) := by
  induction t with
  | zero => exact ⟨1, by simp⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * ZMod.stdAddChar (qtickTurn S L ((pair S L)^[t] v)), ?_⟩
    rw [pow_succ', Function.iterate_succ_apply']
    exact mul_carry _ _ hc (qtick_mul_weyl hn hS hL _)

/-- QL6(a). **The quantum tick is unique**: an invertible map `U` that carries every `W(v)` to the
same multiple of `W(pair S L v)` as the quantum tick does is the quantum tick times one nonzero
number. -/
theorem qtick_unique (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S) (hL : Lᵀ = L)
    (U : (Module.End ℂ (LightWave V n))ˣ)
    (hU : ∀ v : LightState (ZMod n) V, ↑U * weyl v * ↑U⁻¹ =
      (ZMod.stdAddChar (qtickTurn S L v) : ℂ) • weyl (pair S L v)) :
    ∃ c : ℂ, c ≠ 0 ∧ (U : Module.End ℂ (LightWave V n)) = c • ↑(qtick S L) := by
  obtain ⟨M, hMdef⟩ : ∃ M : (Module.End ℂ (LightWave V n))ˣ, M = (qtick S L)⁻¹ * U :=
    ⟨_, rfl⟩
  have hM : ∀ v : LightState (ZMod n) V,
      (M : Module.End ℂ (LightWave V n)) * weyl v = weyl v * ↑M := by
    intro v
    have h := mul_carry _ _ (mul_eq_of_conj_eq U (hU v))
      (inv_carry (qtick S L) (turn_ne_zero _) (qtick_mul_weyl hn hS hL v))
    rw [mul_inv_cancel₀ (turn_ne_zero _), one_smul, ← hMdef] at h
    exact h
  obtain ⟨c, hc⟩ := (commute_weyl_iff _).mp fun v => hM v
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hc
    exact Units.ne_zero _ hc
  · calc (U : Module.End ℂ (LightWave V n)) = ↑(qtick S L) * ↑M := by
          rw [hMdef, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
      _ = c • ↑(qtick S L) := by rw [hc, mul_smul_comm, mul_one]

/-- QL6(b). An invertible map `U` that carries every `W(v)` to some multiple of
`W(pair S L v)` is the quantum tick times one Weyl operation and one nonzero number. -/
theorem qtick_unique_upto_weyl (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S)
    (hL : Lᵀ = L) (U : (Module.End ℂ (LightWave V n))ˣ)
    (hU : ∀ v : LightState (ZMod n) V, ∃ c : ℂ, ↑U * weyl v * ↑U⁻¹ = c • weyl (pair S L v)) :
    ∃ (c : ℂ) (w : LightState (ZMod n) V), c ≠ 0 ∧
      (U : Module.End ℂ (LightWave V n)) = c • (↑(qtick S L) * weyl w) := by
  obtain ⟨M, hMdef⟩ : ∃ M : (Module.End ℂ (LightWave V n))ˣ, M = (qtick S L)⁻¹ * U :=
    ⟨_, rfl⟩
  have hM : ∀ v : LightState (ZMod n) V,
      ∃ c : ℂ, (M : Module.End ℂ (LightWave V n)) * weyl v = c • (weyl v * ↑M) := by
    intro v
    obtain ⟨c, hc⟩ := hU v
    rw [hMdef]
    exact ⟨_, mul_carry _ _ (mul_eq_of_conj_eq U hc)
      (inv_carry (qtick S L) (turn_ne_zero _) (qtick_mul_weyl hn hS hL v))⟩
  obtain ⟨c, w, hc0, hcw⟩ := exists_eq_smul_weyl _ hM
  refine ⟨c, w, hc0, ?_⟩
  calc (U : Module.End ℂ (LightWave V n)) = ↑(qtick S L) * ↑M := by
        rw [hMdef, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    _ = c • (↑(qtick S L) * weyl w) := by rw [hcw, mul_smul_comm]

/-- QL8. **The period**: the power `t` of the quantum tick is a Weyl operation times a number
exactly when the power `t` of `pair S L` is the identity on the dial's states. -/
theorem qtick_pow_weyl_iff (hn : Odd n) {S L : Matrix V V (ZMod n)} (hS : Sᵀ = S)
    (hL : Lᵀ = L) (t : ℕ) :
    (∃ (c : ℂ) (w : LightState (ZMod n) V),
        (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n)) = c • weyl w) ↔
      (pair S L)^[t] = id := by
  constructor
  · rintro ⟨c, w, hcw⟩
    funext v
    obtain ⟨d, hd⟩ := qtick_pow_mul_weyl hn hS hL t v
    have h1 : (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n)) * weyl v =
        (ZMod.stdAddChar (omega w v) : ℂ) •
          (weyl v * (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n))) := by
      rw [hcw, smul_mul_assoc, weyl_comm, mul_smul_comm, smul_comm c]
    rw [h1] at hd
    have h2 : (ZMod.stdAddChar (omega w v) : ℂ) • weyl v = d • weyl ((pair S L)^[t] v) := by
      have h3 := congrArg (· * (↑(qtick S L ^ t)⁻¹ : Module.End ℂ (LightWave V n))) hd
      simp only [smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one] at h3
      exact h3
    exact (eq_of_smul_weyl_eq (turn_ne_zero _) h2).symm
  · intro ht
    have hM : ∀ v : LightState (ZMod n) V,
        ∃ c : ℂ, (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n)) * weyl v =
        c • (weyl v * (↑(qtick S L ^ t) : Module.End ℂ (LightWave V n))) := by
      intro v
      obtain ⟨d, hd⟩ := qtick_pow_mul_weyl hn hS hL t v
      rw [ht, id] at hd
      exact ⟨d, hd⟩
    obtain ⟨c, w, -, hcw⟩ := exists_eq_smul_weyl _ hM
    exact ⟨c, w, hcw⟩

end Fourier

section Fillings

variable {α : Type*} [Fintype α] [DecidableEq α] (S : Stage α) [Fintype S.World]
  [DecidableEq S.World] (n : ℕ) [NeZero n]

/-- The Fourier transform after D2's write of `ℓ` is the turn by minus the count on `ℓ` after the
transform. -/
theorem fourier_mul_write (ℓ : α × S.World) :
    (waveFourier (V := α × S.World) (n := n) : Module.End ℂ (S.Wave n)) * S.waveWrite n ℓ =
      phaseMul (fun k : α × S.World → ZMod n => ZMod.stdAddChar (-(k ℓ))) *
        ↑(waveFourier (V := α × S.World) (n := n)) := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  change ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ψ (c - Pi.single ℓ 1) =
    ZMod.stdAddChar (-(k ℓ)) * ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * ψ c
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight (Pi.single ℓ 1)) _ _ fun c => ?_
  rw [Equiv.subRight_apply, turn_mul_turn_mul, dotProduct_sub, dotProduct_single, mul_one]
  congr 2
  ring

/-- The Fourier transform after D2's reading of `ℓ` is D2's write of `ℓ` after the transform. -/
theorem fourier_mul_read (ℓ : α × S.World) :
    (waveFourier (V := α × S.World) (n := n) : Module.End ℂ (S.Wave n)) * S.waveRead n ℓ =
      S.waveWrite n ℓ * ↑(waveFourier (V := α × S.World) (n := n)) := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  change ∑ c, ZMod.stdAddChar (-(k ⬝ᵥ c)) * (ZMod.stdAddChar (c ℓ) * ψ c) =
    ∑ c, ZMod.stdAddChar (-((k - Pi.single ℓ 1) ⬝ᵥ c)) * ψ c
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [turn_mul_turn_mul, sub_dotProduct, single_dotProduct, one_mul]
  congr 2
  ring

omit [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World] in
/-- The turn by minus the count on `ℓ` is D2's reading of `ℓ` undone. -/
theorem phaseMul_neg_count_mul_read (ℓ : α × S.World) :
    phaseMul (fun k : α × S.World → ZMod n => ZMod.stdAddChar (-(k ℓ))) * S.waveRead n ℓ = 1 := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  rw [Module.End.mul_apply, phaseMul_apply, Stage.waveRead_apply, turn_mul_turn_mul,
    neg_add_cancel, AddChar.map_zero_eq_one, one_mul, Module.End.one_apply]

/-- QL0. **The Fourier transform takes D2's write of a line to the turn by that line's count**,
taken the other way round, which is D2's reading undone (`phaseMul_neg_count_mul_read`): the
transform, after the write of `ℓ`, after the transform undone, multiplies the value at `k` by the
turn by `-(k ℓ)`. -/
theorem fourier_write (ℓ : α × S.World) :
    (waveFourier (V := α × S.World) (n := n) : Module.End ℂ (S.Wave n)) * S.waveWrite n ℓ *
        (↑(waveFourier (V := α × S.World) (n := n))⁻¹ : Module.End ℂ (S.Wave n)) =
      phaseMul fun k : α × S.World → ZMod n => ZMod.stdAddChar (-(k ℓ)) := by
  rw [Units.mul_inv_eq_iff_eq_mul]
  exact fourier_mul_write S n ℓ

/-- QL0. **The Fourier transform takes D2's reading of a line to a move by one on that line**:
the transform, after the reading of `ℓ`, after the transform undone, is D2's write of `ℓ`. The
names cross over. -/
theorem fourier_read (ℓ : α × S.World) :
    (waveFourier (V := α × S.World) (n := n) : Module.End ℂ (S.Wave n)) * S.waveRead n ℓ *
        (↑(waveFourier (V := α × S.World) (n := n))⁻¹ : Module.End ℂ (S.Wave n)) =
      S.waveWrite n ℓ := by
  rw [Units.mul_inv_eq_iff_eq_mul]
  exact fourier_mul_read S n ℓ

end Fillings

end QuantumLight

end Artform.Stages
