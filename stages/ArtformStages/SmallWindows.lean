import ArtformStages.OneSquare

/-!
# Small windows: the modes of light on two squares

The window of two squares has seven lines and six corners (finding 486 of the research ledger).
With no charge its field is the sum of the two faces' loops; its electric energy is a form on
them, and that form's table, the faces' table `C Cᵀ`, has the classical modes of light on the
window as its eigenvectors.

* `dominoEnds`, `dominoLoop`, `dominoEnds_eq_zero_iff`, `dominoLoops`, `card_domino_neutral`
  (SW1): a filling whose ends are `0` at every corner is the sum of the two loops, `a` on the left
  and `b` on the right, and there are exactly `n ^ 2` of them on the dial of `n`;
* `domino_energy`, `dominoFaces`, `domino_energy_eq_form`, `dominoFaces_sym`,
  `dominoFaces_anti`, `domino_mode_traces` (SW2): the sum of the squares of the loops' filling is
  `4 a² + 4 b² - 2 a b`, the form of the faces' table with `4` on its diagonal and `-1` off it; that
  table takes `(1, 1)` to `3` times itself and `(1, -1)` to `5` times itself, so the classical
  modes have `ω² = 3` and `5`; at `κ = λ = 1/2` Pair on them has the traces `5/4` and `3/4`.

None of this is new: it is the cycle space of a graph and the normal modes of two coupled loops.
-/

open Matrix

namespace Artform.Stages

section SmallWindows

variable {n : ℕ}

/-- **The ends of a filling of the window of two squares.** The corners `0, 1, 2` run along the
bottom and `3, 4, 5` along the top; the lines are `0` (from `0` to `1`), `1` (`1` to `2`), `2`
(`3` to `4`), `3` (`4` to `5`), `4` (`0` to `3`), `5` (`1` to `4`) and `6` (`2` to `5`). At a
corner the end is what comes in less what goes out. -/
def dominoEnds (E : Fin 7 → ZMod n) : Fin 6 → ZMod n :=
  ![-E 0 - E 4, E 0 - E 1 - E 5, E 1 - E 6, E 4 - E 2, E 2 + E 5 - E 3, E 3 + E 6]

/-- **The two faces' loops**: `a` round the left face and `b` round the right one, each the way
of the hands of a clock turned round; the middle line carries `a - b`. -/
def dominoLoop {R : Type*} [CommRing R] (a b : R) : Fin 7 → R :=
  ![a, b, -a, -b, -a, a - b, b]

/-- SW1. **No charge, two loops**: the ends are `0` at every corner exactly when the filling is
the sum of the two loops, with the counts of the lines `0` and `1`. -/
theorem dominoEnds_eq_zero_iff (E : Fin 7 → ZMod n) :
    dominoEnds E = 0 ↔ E = dominoLoop (E 0) (E 1) := by
  constructor
  · intro h
    have h0 : -E 0 - E 4 = 0 := by simpa [dominoEnds] using congrFun h 0
    have h1 : E 0 - E 1 - E 5 = 0 := by simpa [dominoEnds] using congrFun h 1
    have h2 : E 1 - E 6 = 0 := by simpa [dominoEnds] using congrFun h 2
    have h3 : E 4 - E 2 = 0 := by simpa [dominoEnds] using congrFun h 3
    have h5 : E 3 + E 6 = 0 := by simpa [dominoEnds] using congrFun h 5
    funext i
    fin_cases i
    · simp [dominoLoop]
    · simp [dominoLoop]
    · simp only [dominoLoop]
      simp
      linear_combination -h3 - h0
    · simp only [dominoLoop]
      simp
      linear_combination h5 + h2
    · simp only [dominoLoop]
      simp
      linear_combination -h0
    · simp only [dominoLoop]
      simp
      linear_combination -h1
    · simp only [dominoLoop]
      simp
      linear_combination -h2
  · intro h
    rw [h]
    funext j
    fin_cases j <;> simp [dominoEnds, dominoLoop]
    ring

/-- The charge-free fillings of the window are the pairs of loops. -/
def dominoLoops : {E : Fin 7 → ZMod n // dominoEnds E = 0} ≃ ZMod n × ZMod n where
  toFun E := (E.1 0, E.1 1)
  invFun p := ⟨dominoLoop p.1 p.2, by
    rw [dominoEnds_eq_zero_iff]
    simp [dominoLoop]⟩
  left_inv E := by
    ext i
    have := congrFun ((dominoEnds_eq_zero_iff E.1).1 E.2) i
    simp only at this ⊢
    rw [← this]
  right_inv p := by
    simp [dominoLoop]

/-- SW1. On the dial of `n` the window of two squares has exactly `n ^ 2` charge-free fillings. -/
theorem card_domino_neutral [NeZero n] :
    Fintype.card {E : Fin 7 → ZMod n // dominoEnds E = 0} = n ^ 2 := by
  rw [Fintype.card_congr dominoLoops, Fintype.card_prod, ZMod.card, sq]

/-- SW2. **The loops' electric energy**: the sum of the squares is `4 a² + 4 b² - 2 a b`. -/
theorem domino_energy {R : Type*} [CommRing R] (a b : R) :
    ∑ i, dominoLoop a b i ^ 2 = 4 * a ^ 2 + 4 * b ^ 2 - 2 * a * b := by
  simp [dominoLoop, Fin.sum_univ_succ]
  ring

/-- **The faces' table** `C Cᵀ` of the window of two squares. -/
def dominoFaces : Matrix (Fin 2) (Fin 2) ℝ := !![4, -1; -1, 4]

/-- SW2. The loops' energy is the form of the faces' table. -/
theorem domino_energy_eq_form (a b : ℝ) :
    ∑ i, dominoLoop a b i ^ 2 = ![a, b] ⬝ᵥ (dominoFaces *ᵥ ![a, b]) := by
  rw [domino_energy]
  simp [dominoFaces, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- SW2. The faces' table takes `(1, 1)` to `3` times itself. -/
theorem dominoFaces_sym : dominoFaces *ᵥ ![1, 1] = (3 : ℝ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp [dominoFaces, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- SW2. The faces' table takes `(1, -1)` to `5` times itself. -/
theorem dominoFaces_anti : dominoFaces *ᵥ ![1, -1] = (5 : ℝ) • ![1, -1] := by
  ext i
  fin_cases i <;> simp [dominoFaces, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- SW2. At `κ = λ = 1/2` Pair on the modes of pull `3` and `5` has the traces `5/4` and `3/4`: both
swing. -/
theorem domino_mode_traces :
    (modeTick (1 / 2) (1 / 2) 3).trace = 5 / 4 ∧ (modeTick (1 / 2) (1 / 2) 5).trace = 3 / 4 := by
  constructor <;> rw [modeTick_trace] <;> norm_num

end SmallWindows

end Artform.Stages
