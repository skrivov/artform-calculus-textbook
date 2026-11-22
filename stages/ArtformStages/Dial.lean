import ArtformStages.Maxwell
import ArtformStages.Waves

/-!
# The book's tick on the dial of eight

The baseline of the research ledger on a layered universe has, as its TE1, the Maxwell tick on a
grid of squares with two dials of eight on every edge: the kick adds a face's sum round it, and
the drift takes the new count from the potential. It is Pair over `ZMod 8` with the kick `Cᵀ C`
and the drift `1`. With a board's maps read over every ring, the laws proved over every
commutative ring hold for it (finding 448 of the ledger):

* `Board.incidenceR_mul_gaugeR`, `Board.incidenceR_real`, `Board.gaugeR_real` (DL1): `C G = 0`
  over every ring, and over the real numbers the maps are those of `Board`;
* `Board.bookTick_charge`, `Board.bookTick_gauge` (DL2, DL3): Gauss's law, and the gauge;
* `Board.bookTick_omega`, `Board.bookTick_qstar` (DL4): the kept forms, on the dial;
* `Board.bookTick_unpair`, `Board.bookTick_wave` (DL5): undone by `unpair`, and the wave equation;
* `Board.bookTick_continuity` (DL6): with a current, continuity;
* `Board.bookTick_returns` (DL7): on a finite board every light returns.
-/

open Matrix

namespace Artform.Stages

namespace Board

variable {f e v : Type*} (B : Board f e v) (R : Type*) [CommRing R]

/-- The sign of a side over a ring `R`: `1` along the turn of its square, `-1` against it. -/
def turnSignR (b : Bool) : R := if b then 1 else -1

/-- The incidence of a board over a ring `R`. -/
def incidenceR [DecidableEq e] : Matrix f e R :=
  Matrix.of fun σ ℓ => ∑ i, if B.side σ i = ℓ then turnSignR R (B.along σ i) else 0

/-- The gauge of a board over a ring `R`. -/
def gaugeR [DecidableEq v] : Matrix e v R :=
  Matrix.of fun ℓ w => (if B.head ℓ = w then 1 else 0) - (if B.tail ℓ = w then 1 else 0)

/-- DL1. Over the real numbers, the incidence over a ring is the board's incidence. -/
theorem incidenceR_real [DecidableEq e] : B.incidenceR ℝ = B.incidence := rfl

/-- DL1. Over the real numbers, the gauge over a ring is the board's gauge. -/
theorem gaugeR_real [DecidableEq v] : B.gaugeR ℝ = B.gauge := rfl

/-- DL1. Over every commutative ring, the sides of each square close up: `C G = 0`. -/
theorem incidenceR_mul_gaugeR [DecidableEq e] [DecidableEq v] [Fintype e] :
    B.incidenceR R * B.gaugeR R = 0 := by
  ext σ w
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [incidenceR, Matrix.of_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h2 : ∀ i, turnSignR R (B.along σ i) * B.gaugeR R (B.side σ i) w =
      (if B.corner σ (i + 1) = w then 1 else 0) - (if B.corner σ i = w then 1 else 0) := by
    intro i
    simp only [gaugeR, Matrix.of_apply, B.tail_side, B.head_side]
    cases B.along σ i <;> simp [turnSignR]
  simp only [h2, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

/-- The book's kick on the dial of `N`: `Cᵀ C`, a face's sum round it, read back on its sides. -/
def bookKick [DecidableEq e] [DecidableEq f] [Fintype f] (N : ℕ) : Matrix e e (ZMod N) :=
  (B.incidenceR (ZMod N))ᵀ * (1 : Matrix f f (ZMod N)) * B.incidenceR (ZMod N)

/-- The book's tick on the dial of `N`: Pair over `ZMod N` with the kick `Cᵀ C` and the drift
`1`. With `N = 8` it is the baseline's TE1. -/
def bookTick [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ) :
    LightState (ZMod N) e → LightState (ZMod N) e :=
  pair (B.bookKick N) 1

theorem bookKick_symm [DecidableEq e] [DecidableEq f] [Fintype f] (N : ℕ) :
    (B.bookKick N)ᵀ = B.bookKick N := by
  simp [bookKick, Matrix.transpose_mul]

/-- DL2. The book's tick keeps Gauss's law. -/
theorem bookTick_charge [DecidableEq e] [DecidableEq f] [DecidableEq v] [Fintype e] [Fintype f]
    (N : ℕ) (x : LightState (ZMod N) e) :
    (B.gaugeR (ZMod N))ᵀ *ᵥ (B.bookTick N x).2 = (B.gaugeR (ZMod N))ᵀ *ᵥ x.2 :=
  charge_pair _ _ 1 1 (B.incidenceR_mul_gaugeR (ZMod N)) x

/-- DL3. The book's tick passes the gauge. -/
theorem bookTick_gauge [DecidableEq e] [DecidableEq f] [DecidableEq v] [Fintype e] [Fintype f]
    [Fintype v] (N : ℕ) (A E : e → ZMod N) (g : v → ZMod N) :
    B.bookTick N (A + B.gaugeR (ZMod N) *ᵥ g, E) =
      ((B.bookTick N (A, E)).1 + B.gaugeR (ZMod N) *ᵥ g, (B.bookTick N (A, E)).2) :=
  _root_.Artform.Stages.pair_gauge _ _ 1 1 (B.incidenceR_mul_gaugeR (ZMod N)) A E g

/-- DL4. The book's tick keeps the alternating pairing, on the dial. -/
theorem bookTick_omega [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ)
    (x y : LightState (ZMod N) e) : omega (B.bookTick N x) (B.bookTick N y) = omega x y :=
  omega_pair _ _ (B.bookKick_symm N) (Matrix.transpose_one) x y

/-- DL4. The book's tick keeps the staggered form `Q⋆`, on the dial. -/
theorem bookTick_qstar [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ)
    (x : LightState (ZMod N) e) :
    qstar (B.bookKick N) 1 (B.bookTick N x) = qstar (B.bookKick N) 1 x :=
  qstar_pair _ _ (B.bookKick_symm N) (Matrix.transpose_one) x

/-- DL5. The book's tick is undone by `unpair`. -/
theorem bookTick_unpair [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ)
    (x : LightState (ZMod N) e) :
    unpair (B.bookKick N) 1 (B.bookTick N x) = x :=
  unpair_pair _ _ x

/-- DL5. The book's tick obeys the wave equation in steps. -/
theorem bookTick_wave [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ)
    (x : LightState (ZMod N) e) :
    (B.bookTick N (B.bookTick N x)).1 - (B.bookTick N x).1 =
      ((B.bookTick N x).1 - x.1) -
        (1 : Matrix e e (ZMod N)) *ᵥ (B.bookKick N *ᵥ (B.bookTick N x).1) :=
  pair_wave _ _ x

/-- DL6. With a current on the dial, the divergence of `E` falls by that of the current. -/
theorem bookTick_continuity [DecidableEq e] [DecidableEq f] [DecidableEq v] [Fintype e]
    [Fintype f] (N : ℕ) (J : e → ZMod N) (x : LightState (ZMod N) e) :
    divergence (B.gaugeR (ZMod N))
        (pairWith (B.bookKick N) 1 J x).2 =
      divergence (B.gaugeR (ZMod N)) x.2 - divergence (B.gaugeR (ZMod N)) J :=
  divergence_pairWith _ _ 1 1 (B.incidenceR_mul_gaugeR (ZMod N)) J x

/-- DL7. On a finite board every light returns: some number of ticks brings every state back. -/
theorem bookTick_returns [DecidableEq e] [DecidableEq f] [Fintype e] [Fintype f] (N : ℕ)
    [NeZero N] : ∃ p : ℕ, 0 < p ∧ ∀ x, (B.bookTick N)^[p] x = x := by
  let σ : Equiv.Perm (LightState (ZMod N) e) :=
    { toFun := B.bookTick N
      invFun := unpair (B.bookKick N) 1
      left_inv := fun x => unpair_pair _ _ x
      right_inv := fun y => pair_unpair _ _ y }
  refine ⟨orderOf σ, orderOf_pos σ, fun x => ?_⟩
  have h : (σ ^ orderOf σ) x = x := by
    rw [pow_orderOf_eq_one]
    rfl
  rw [Equiv.Perm.coe_pow] at h
  exact h

end Board

end Artform.Stages
