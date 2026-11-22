import ArtformStages.EnergyTick

/-!
# One square: its charge-free field and its mode

The square's four lines go round its face (finding 485 of the research ledger). With no charge, a
filling of them is one count, the loop, whose partner is the face's flux; and at the weights
`κ = λ = 1/2`, below Courant's limit, Pair on that mode turns by `π / 3` at every tick.

* `squareEnds`, `squareEnds_eq_zero_iff`, `squareLoops`, `card_square_neutral` (SQ1): a filling of
  the four lines whose ends are `0` at the four corners has the same count on every line, and there
  are exactly `n` of them on the dial of `n`;
* `square_mode_trace`, `square_mode_pow_three`, `square_mode_pow_six` (SQ2): Pair on the square's
  mode, `modeTick (1/2) (1/2) 4`, has trace `1 = 2 cos(π/3)`; its third power is `-1` and its sixth
  is `1`: the classical law turns the mode by `π / 3`.

None of this is new: it is the cycle of four and the leapfrog of one oscillator.
-/

open scoped Real

namespace Artform.Stages

section OneSquare

variable {n : ℕ}

/-- **The ends of a filling of the square.** Its lines `0, 1, 2, 3` go round the face, the line `i`
from the corner `i` to the corner `i + 1`; at the corner `i` the end is what the line `i - 1` brings
less what the line `i` takes away. -/
def squareEnds (E : ZMod 4 → ZMod n) : ZMod 4 → ZMod n := fun i => E (i - 1) - E i

/-- SQ1. **No charge, one count**: the ends are `0` at all four corners exactly when every line
carries the count of the line `0`. -/
theorem squareEnds_eq_zero_iff (E : ZMod 4 → ZMod n) :
    squareEnds E = 0 ↔ ∀ i, E i = E 0 := by
  constructor
  · intro h
    have h1 : ∀ i, E (i - 1) = E i := fun i => sub_eq_zero.1 (congrFun h i)
    have e1 : E 1 = E 0 := by
      have := h1 1
      rw [sub_self] at this
      exact this.symm
    have e2 : E 2 = E 0 := by
      have := h1 2
      rw [show (2 : ZMod 4) - 1 = 1 by decide] at this
      rw [← this, e1]
    have e3 : E 3 = E 0 := by
      have := h1 3
      rw [show (3 : ZMod 4) - 1 = 2 by decide] at this
      rw [← this, e2]
    intro i
    fin_cases i
    · rfl
    · exact e1
    · exact e2
    · exact e3
  · intro h
    funext i
    simp [squareEnds, h (i - 1), h i]

/-- The charge-free fillings of the square are its loops, one count each. -/
def squareLoops : {E : ZMod 4 → ZMod n // squareEnds E = 0} ≃ ZMod n where
  toFun E := E.1 0
  invFun e := ⟨fun _ => e, by funext i; simp [squareEnds]⟩
  left_inv E := by
    ext i
    exact ((squareEnds_eq_zero_iff E.1).1 E.2 i).symm
  right_inv _ := rfl

/-- SQ1. On the dial of `n` the square has exactly `n` charge-free fillings. -/
theorem card_square_neutral [NeZero n] :
    Fintype.card {E : ZMod 4 → ZMod n // squareEnds E = 0} = n := by
  rw [Fintype.card_congr squareLoops, ZMod.card]

/-- SQ2. **The square's mode at `κ = λ = 1/2`**: Pair on one mode of pull `4` has trace
`1 = 2 cos(π/3)`. -/
theorem square_mode_trace : (modeTick (1 / 2) (1 / 2) 4).trace = 2 * Real.cos (π / 3) := by
  rw [modeTick_trace, Real.cos_pi_div_three]
  norm_num

/-- SQ2. Its third power is `-1`: the classical law turns the mode by `π` in three ticks. -/
theorem square_mode_pow_three : modeTick (1 / 2) (1 / 2) 4 ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modeTick, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- SQ2. Its sixth power is `1`: the mode comes back after six ticks, a turn of `π / 3` each. -/
theorem square_mode_pow_six : modeTick (1 / 2) (1 / 2) 4 ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, square_mode_pow_three]
  simp

end OneSquare

end Artform.Stages
