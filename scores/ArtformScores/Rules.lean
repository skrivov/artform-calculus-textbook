import ArtformScores.Statements

/-!
# The rules are sound

The rules R1, R3, R4 and R5 of the algebra of scores hold for the laws, over every
commutative ring, and T2: no score realizes a chiral mover.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

variable {S : Type*} [CommRing S]

/-- The law of the Whitehead word `w(u)` is `[[0, u], [-u⁻¹, 0]]`. -/
theorem whitehead_mat (u : Sˣ) :
    (realize (whitehead u) : Matrix (Fin 2) (Fin 2) S) = !![0, ↑u; -↑u⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [whitehead, Step.mat, Matrix.SpecialLinearGroup.coe_mul]

/-- The balanced pair `h(u)` is the law `diag(u, u⁻¹)`. -/
theorem balanced_mat (u : Sˣ) :
    (balanced u : Matrix (Fin 2) (Fin 2) S) = !![↑u, 0; 0, ↑u⁻¹] := by
  ext i j
  simp only [balanced, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    whitehead_mat, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

/-- **R1** (merging). Two kicks in a row are one kick with the summed stencil, and
two moves in a row are one move. -/
@[ledger "R1"]
theorem merging : Statement.merging := by
  intro S _ f g
  constructor
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Step.mat, Matrix.SpecialLinearGroup.coe_mul]
    all_goals ring

/-- **R3** (Whitehead's rule). -/
@[ledger "R3"]
theorem whiteheadRule : Statement.whiteheadRule := by
  intro S _ u f
  refine ⟨whitehead_mat u, ?_, ?_⟩
  all_goals
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      whitehead_mat, Step.coe_sl, Step.mat, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp
    all_goals ring

/-- **R4** (balanced movers). -/
@[ledger "R4"]
theorem balancedRule : Statement.balancedRule := by
  intro S _ u v
  refine ⟨balanced_mat u, ?_⟩
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, balanced_mat, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- **R5** (time reversal). -/
@[ledger "R5"]
theorem timeReversal : Statement.timeReversal := by
  intro S _ w
  induction w with
  | nil => simp [Score.reverse]
  | cons s w ih =>
    simp only [Score.reverse, List.map_cons, List.reverse_cons] at ih ⊢
    rw [realize_append, ih, realize_singleton, Step.sl_neg, realize_cons, mul_inv_rev]

/-- **T2** (the index). No score realizes a chiral mover `diag(a, 1)`, `a ≠ 1`. -/
@[ledger "T2"]
theorem index : Statement.index := by
  intro S _ a ha w h
  have hdet := Matrix.SpecialLinearGroup.det_coe (realize w)
  rw [h, Matrix.det_fin_two_of] at hdet
  exact ha (by simpa using hdet)

/-! ## Non-vacuity

The statements on the running example: the book's tick `K(1) M(-3)` over `F₇`
(κ = 1, λg = 3), the unit `3` of `F₇`, and the shift `x` of the Laurent ring
`F₇[x, 1/x]`. -/

/-- Merging on `F₇`: the kicks `K(1) K(2)` are the kick `K(3)`. -/
example : realize [Step.kick (1 : ZMod 7), Step.kick 2] = realize [Step.kick 3] := by
  have h := (merging (ZMod 7) 1 2).1
  rwa [show (1 : ZMod 7) + 2 = 3 by decide] at h

/-- Whitehead's word for the unit `3` of `F₇`, whose inverse is `5`. -/
example : (realize (whitehead (⟨3, 5, by decide, by decide⟩ : (ZMod 7)ˣ)) :
    Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![0, 3; -5, 0] :=
  (whiteheadRule (ZMod 7) ⟨3, 5, by decide, by decide⟩ 1).1

/-- The balanced movers of the units `3` and `5` of `F₇` multiply. -/
example : balanced (⟨3, 5, by decide, by decide⟩ : (ZMod 7)ˣ) *
    balanced ⟨5, 3, by decide, by decide⟩ =
      balanced ((⟨3, 5, by decide, by decide⟩ : (ZMod 7)ˣ) * ⟨5, 3, by decide, by decide⟩) :=
  (balancedRule (ZMod 7) _ _).2

/-- Time reversal of the book's tick `K(1) M(-3)` over `F₇`. -/
example : realize (Score.reverse [Step.kick (1 : ZMod 7), Step.move (-3)]) =
    (realize [Step.kick (1 : ZMod 7), Step.move (-3)])⁻¹ :=
  timeReversal (ZMod 7) _

/-- The shift `x` of `F₇[x, 1/x]` is not `1`: the hypothesis of the index holds
for the chiral mover `diag(x, 1)`. -/
theorem shift_ne_one : (LaurentPolynomial.T 1 : LaurentPolynomial (ZMod 7)) ≠ 1 := by
  rw [← LaurentPolynomial.T_zero]
  intro h
  have h0 := congrArg (fun f : LaurentPolynomial (ZMod 7) => f.coeff 0) h
  simp only [LaurentPolynomial.T_apply] at h0
  exact absurd h0 (by decide)

/-- The index: no score over `F₇[x, 1/x]` realizes the chiral mover `diag(x, 1)`. -/
example (w : Score (LaurentPolynomial (ZMod 7))) :
    (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 7))) ≠
      !![LaurentPolynomial.T 1, 0; 0, 1] :=
  index _ _ shift_ne_one w

end Artform.Scores
