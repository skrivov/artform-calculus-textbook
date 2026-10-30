import ArtformScores.Statements

/-!
# The caller's cut

T14 of the algebra of scores, its exact part: the two orders of the dimension
split have the same phase and opposite cuts `±h²(gx - gy)/2`, so a caller's
mean tick has the cut `(2q - 1) h²(gx - gy)/2`. A fair caller (`q = 1/2`)
cancels it; the book's caller, which turns on the pattern `11` of two response
cells (`q = 1/4`), leaves `-h²(gx - gy)/4`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

variable {K : Type*} [Field K]

/-- The entries of the dimension split. -/
theorem splitTick_mat (xFirst : Bool) (h gx gy : K) :
    (splitTick xFirst h gx gy : Matrix (Fin 2) (Fin 2) K) =
      let g₁ := if xFirst then gx else gy
      let g₂ := if xFirst then gy else gx
      (Step.kick (h / 4)).mat * (Step.move (-(h * g₂))).mat * (Step.kick (h / 2)).mat *
        (Step.move (-(h * g₁))).mat * (Step.kick (h / 4)).mat := by
  simp [splitTick, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

/-- **T14** (the caller's cut). -/
theorem callerCut : Statement.callerCut := by
  intro K _ _ h gx gy q
  have hcut : ∀ (A B : Matrix (Fin 2) (Fin 2) K) (r : K),
      cut (r • A + (1 - r) • B) = r * cut A + (1 - r) * cut B := by
    intro A B r
    simp only [cut, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h1 : cut (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) = h ^ 2 * (gx - gy) / 2 := by
    rw [splitTick_mat]
    simp [cut, Step.mat]
    ring
  have h2 : cut (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K) =
      -(h ^ 2 * (gx - gy) / 2) := by
    rw [splitTick_mat]
    simp [cut, Step.mat]
    ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [splitTick_mat, splitTick_mat]
    simp [Step.mat, Matrix.trace_fin_two]
    ring
  · rw [hcut, h1, h2]
    ring

/-! ## Non-vacuity

The ledger's values (finding 080): `h = 1/5`, `gx = 1`, `gy = 1/4` over `ℚ`, and
the book's caller, `q = 1/4`. -/

/-- The book's caller leaves the cut `-h²(gx - gy)/4` on the ledger's mode. -/
example : cut ((1 / 4 : ℚ) •
      (splitTick true (1 / 5 : ℚ) 1 (1 / 4) : Matrix (Fin 2) (Fin 2) ℚ) +
    (1 - 1 / 4 : ℚ) • (splitTick false (1 / 5 : ℚ) 1 (1 / 4) : Matrix (Fin 2) (Fin 2) ℚ)) =
      -((1 / 5 : ℚ) ^ 2 * (1 - 1 / 4) / 4) := by
  rw [(callerCut ℚ (1 / 5) 1 (1 / 4) (1 / 4)).2.2.2]
  norm_num

end Artform.Scores
