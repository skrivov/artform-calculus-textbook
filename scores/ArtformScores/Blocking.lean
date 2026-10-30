import ArtformScores.Statements

/-!
# Blocking: red-black as a law on the blocked artform

R6 of the algebra of scores, and the red-black scheme on an index-2 blocking.
- `block` is multiplicative, because `Algebra.leftMulMatrix` is a ring homomorphism.
  The placed steps of a blocked step never feed one another, so they multiply to the
  blocked step. Hence the realizer commutes with blocking (R6).
- On an index-2 blocking with the places red (`1`) and black (`x`, `x² = d`), the
  blocked shift by `x` exchanges red and black, so it turns the red-black tick into the
  black-red tick. A blocked law of the artform commutes with the shift, so red-black is
  one only if the two ticks agree. Their entries at (`e` black, `b` red) are `κ² β` and
  `0`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

section Proofs

variable {S' S : Type*} [CommRing S'] [CommRing S] [Algebra S' S] {m : ℕ}

theorem block_mul (bs : Module.Basis (Fin m) S' S) (T U : Matrix (Fin 2) (Fin 2) S) :
    block bs (T * U) = block bs T * block bs U := by
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [block, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem block_one (bs : Module.Basis (Fin m) S' S) : block bs 1 = 1 := by
  ext ⟨i, s⟩ ⟨j, t⟩
  by_cases hij : i = j
  · subst hij
    simp [block, Matrix.one_apply]
  · simp [block, Matrix.one_apply, hij]

theorem realizePlaced_append (u v : List (PStep S' m)) :
    realizePlaced (u ++ v) = realizePlaced v * realizePlaced u := by
  induction u with
  | nil => simp [realizePlaced]
  | cons s u ih => simp [realizePlaced, ih, mul_assoc]

/-- Placed steps whose targets are never sources multiply to `1` plus the sum of their
shears. -/
theorem realizePlaced_orth (L : List (PStep S' m)) (hL : ∀ s ∈ L, ∀ t ∈ L, s.β ≠ t.α) :
    realizePlaced L = 1 + (L.map fun s => Matrix.single s.α s.β s.g).sum := by
  induction L with
  | nil => simp [realizePlaced]
  | cons s L ih =>
    rw [realizePlaced, ih fun a ha b hb => hL a (by simp [ha]) b (by simp [hb]), PStep.mat]
    have h0 : (L.map fun s => Matrix.single s.α s.β s.g).sum * Matrix.single s.α s.β s.g = 0 := by
      rw [← List.sum_map_mul_right]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact Matrix.single_mul_single_of_ne (h := hL a (by simp [ha]) s (by simp)) ..
    rw [List.map_cons, List.sum_cons, add_mul, one_mul, mul_add, mul_one, h0, add_zero]
    abel

theorem list_sum_flatMap {α β : Type*} [AddMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_block_singles (F : Matrix (Fin m) (Fin m) S') (i₀ j₀ : Fin 2) :
    (((List.finRange m).flatMap fun s => (List.finRange m).map fun t =>
        (⟨(i₀, s), (j₀, t), F s t⟩ : PStep S' m)).map fun p => Matrix.single p.α p.β p.g).sum =
      Matrix.of fun p q => if i₀ = p.1 ∧ j₀ = q.1 then F p.2 q.2 else 0 := by
  rw [List.map_flatMap, list_sum_flatMap]
  simp only [List.map_map, Function.comp_def]
  rw [← Fin.sum_univ_def]
  simp only [← Fin.sum_univ_def]
  ext ⟨i, a⟩ ⟨j, c⟩
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.of_apply, Prod.mk.injEq]
  by_cases hi : i₀ = i <;> by_cases hj : j₀ = j <;> simp [hi, hj, ite_and, Finset.sum_ite_eq']

/-- A blocked step: its placed steps multiply to the blocked law of the step. -/
theorem realizePlaced_block (bs : Module.Basis (Fin m) S' S) (s : Step S) :
    realizePlaced (s.block bs) = block bs s.mat := by
  rw [realizePlaced_orth]
  · cases s with
    | kick f =>
      rw [Step.block, sum_block_singles]
      ext ⟨i, a⟩ ⟨j, c⟩
      fin_cases i <;> fin_cases j <;> simp [block, Step.mat, Matrix.one_apply]
    | move f =>
      rw [Step.block, sum_block_singles]
      ext ⟨i, a⟩ ⟨j, c⟩
      fin_cases i <;> fin_cases j <;> simp [block, Step.mat, Matrix.one_apply]
  · cases s <;> simp only [Step.block, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and] <;>
    · rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
      simp

/-- The realizer commutes with blocking. -/
theorem block_realize (bs : Module.Basis (Fin m) S' S) (w : Score S) :
    block bs (realize w : Matrix (Fin 2) (Fin 2) S) = realizePlaced (blockScore bs w) := by
  induction w with
  | nil => simp [block_one, blockScore, realizePlaced]
  | cons s w ih =>
    rw [realize_cons, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, block_mul, ih,
      ← realizePlaced_block]
    simp only [blockScore, List.flatMap_cons, realizePlaced_append]

section RedBlack

variable {bs : Module.Basis (Fin 2) S' S} {x : S} {d : S'ˣ}

theorem repr_mul_x (hb0 : bs 0 = 1) (hb1 : bs 1 = x) (hx : x * x = algebraMap S' S d) (h : S) :
    bs.repr (h * x) 0 = d * bs.repr h 1 ∧ bs.repr (h * x) 1 = bs.repr h 0 := by
  have hh : h = bs.repr h 0 • bs 0 + bs.repr h 1 • bs 1 := by
    have := bs.sum_repr h
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have e : h * x = (d * bs.repr h 1) • bs 0 + bs.repr h 0 • bs 1 := by
    conv_lhs => rw [hh]
    rw [hb0, hb1, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hx, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]
    ring
  rw [e]
  simp

theorem leftMulMatrix_eq (hb0 : bs 0 = 1) (hb1 : bs 1 = x) (hx : x * x = algebraMap S' S d)
    (h : S) :
    Algebra.leftMulMatrix bs h = !![bs.repr h 0, d * bs.repr h 1; bs.repr h 1, bs.repr h 0] := by
  obtain ⟨h0, h1⟩ := repr_mul_x hb0 hb1 hx h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, h0, h1]

theorem realizePlaced_singleton (s : PStep S' m) : realizePlaced [s] = s.mat := by
  simp [realizePlaced]

theorem redBlackTick_eq (κ : S') (h : S) :
    redBlackTick bs κ h = block bs (Step.move h).mat * ((blackKick κ).mat *
      (block bs (Step.move h).mat * (redKick κ).mat)) := by
  simp only [redBlackTick, realizePlaced_append, realizePlaced_singleton, realizePlaced_block]

theorem blackRedTick_eq (κ : S') (h : S) :
    blackRedTick bs κ h = block bs (Step.move h).mat * ((redKick κ).mat *
      (block bs (Step.move h).mat * (blackKick κ).mat)) := by
  simp only [blackRedTick, realizePlaced_append, realizePlaced_singleton, realizePlaced_block]

theorem block_smul_one_comm (y : S) (T : Matrix (Fin 2) (Fin 2) S) :
    block bs (y • 1) * block bs T = block bs T * block bs (y • 1) := by
  rw [← block_mul, ← block_mul, Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one]

theorem redBlack_of (hb0 : bs 0 = 1) (hb1 : bs 1 = x) (hx : x * x = algebraMap S' S d)
    (κ : S') (h : S) :
    realizePlaced [redKick κ, blackKick κ] = block bs (Step.kick (algebraMap S' S κ)).mat ∧
    block bs (x • 1) * redBlackTick bs κ h = blackRedTick bs κ h * block bs (x • 1) ∧
    ((∃ T : Matrix (Fin 2) (Fin 2) S, block bs T = redBlackTick bs κ h) →
      κ * κ * bs.repr h 1 = 0) := by
  have hrx : bs.repr x 0 = 0 ∧ bs.repr x 1 = 1 := by
    rw [← hb1]; simp
  have hX : Algebra.leftMulMatrix bs x = !![0, (d : S'); 1, 0] := by
    rw [leftMulMatrix_eq hb0 hb1 hx, hrx.1, hrx.2]; simp
  have hκ : Algebra.leftMulMatrix bs (algebraMap S' S κ) = κ • 1 := by
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  have hH := leftMulMatrix_eq hb0 hb1 hx h
  set P := block bs (x • 1) with hP
  set Bm := block bs (Step.move h).mat with hBm
  set Kr := (redKick κ).mat with hKr
  set Kk := (blackKick κ).mat with hKk
  have hPB : P * Bm = Bm * P := block_smul_one_comm x _
  have hPKr : P * Kr = Kk * P := by
    ext ⟨i, a⟩ ⟨j, c⟩
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases c <;>
      simp [hP, hKr, hKk, block, PStep.mat, redKick, blackKick, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, hX]
  have hPKk : P * Kk = Kr * P := by
    ext ⟨i, a⟩ ⟨j, c⟩
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases c <;>
      simp [hP, hKr, hKk, block, PStep.mat, redKick, blackKick, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, hX,
        mul_comm]
  have hconj : P * redBlackTick bs κ h = blackRedTick bs κ h * P := by
    rw [redBlackTick_eq, blackRedTick_eq, ← hBm, ← hKr, ← hKk]
    calc P * (Bm * (Kk * (Bm * Kr)))
        = Bm * (P * (Kk * (Bm * Kr))) := by rw [← mul_assoc, hPB, mul_assoc]
      _ = Bm * (Kr * (P * (Bm * Kr))) := by rw [← mul_assoc P Kk, hPKk, mul_assoc]
      _ = Bm * (Kr * (Bm * (P * Kr))) := by rw [← mul_assoc P Bm, hPB, mul_assoc]
      _ = Bm * (Kr * (Bm * (Kk * P))) := by rw [hPKr]
      _ = Bm * (Kr * (Bm * Kk)) * P := by simp only [mul_assoc]
  refine ⟨?_, hconj, ?_⟩
  · rw [realizePlaced_orth _ (by simp [redKick, blackKick])]
    ext ⟨i, a⟩ ⟨j, c⟩
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases c <;>
      simp [block, Step.mat, redKick, blackKick, hκ]
  · rintro ⟨T, hT⟩
    have hcomm : P * redBlackTick bs κ h = redBlackTick bs κ h * P := by
      rw [← hT]; exact block_smul_one_comm x T
    have hinv : P * block bs ((x * algebraMap S' S ↑d⁻¹) • 1) = 1 := by
      rw [hP, ← block_mul, smul_one_mul, smul_smul, ← mul_assoc, hx, ← map_mul, Units.mul_inv,
        map_one, one_smul, block_one]
    have heq : blackRedTick bs κ h = redBlackTick bs κ h := by
      calc blackRedTick bs κ h
          = blackRedTick bs κ h * P * block bs ((x * algebraMap S' S ↑d⁻¹) • 1) := by
            rw [mul_assoc, hinv, mul_one]
        _ = redBlackTick bs κ h * P * block bs ((x * algebraMap S' S ↑d⁻¹) • 1) := by
            rw [← hconj, ← hcomm]
        _ = redBlackTick bs κ h := by rw [mul_assoc, hinv, mul_one]
    have e := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) S' => M (1, 1) (0, 0)) heq
    simp only [redBlackTick_eq, blackRedTick_eq] at e
    simp [block, Step.mat, redKick, blackKick, PStep.mat, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, hH] at e
    linear_combination -e

end RedBlack

end Proofs

/-- **R6** (blocking). -/
@[ledger "R6"]
theorem blocking : Statement.blocking := fun _ _ _ _ _ _ bs w => block_realize bs w

/-- **R6** (red-black on the blocked artform). -/
@[ledger "R6"]
theorem redBlack : Statement.redBlack := fun _ _ _ _ _ _ _ _ hb0 hb1 hx κ h =>
  redBlack_of hb0 hb1 hx κ h

/-! ## Non-vacuity

Both statements on the running example's line `F₇[x, 1/x]`, blocked by its even and odd
cells: `F₇[x, 1/x] = F₇[u, 1/u][x]/(x² - u)` with `u = x²`, on the basis `1, x`. Red is
the even cells, and black the odd ones. -/

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open Polynomial in
/-- The polynomial `x² - u` over the even stencils `F₇[u, 1/u]`. -/
noncomputable abbrev lineG : (LaurentPolynomial (ZMod 7))[X] := X ^ 2 - C (LaurentPolynomial.T 1)

theorem lineG_monic : lineG.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)

theorem lineG_dim : (AdjoinRoot.powerBasis' lineG_monic).dim = 2 := by
  simp [AdjoinRoot.powerBasis']

/-- The places of the line: the basis `1, x` of its stencils over the even stencils. -/
noncomputable def lineBasis :
    Module.Basis (Fin 2) (LaurentPolynomial (ZMod 7)) (AdjoinRoot lineG) :=
  (AdjoinRoot.powerBasis' lineG_monic).basis.reindex (finCongr lineG_dim)

theorem lineBasis_zero : lineBasis 0 = 1 := by
  simp [lineBasis]

theorem lineBasis_one : lineBasis 1 = AdjoinRoot.root lineG := by
  rw [lineBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have : (((finCongr lineG_dim).symm 1 : Fin _) : ℕ) = 1 := rfl
  rw [this, pow_one]
  rfl

/-- The square `u = x²` of the odd shift, a unit of the even stencils. -/
noncomputable def lineD : (LaurentPolynomial (ZMod 7))ˣ :=
  (LaurentPolynomial.isUnit_T (R := ZMod 7) 1).unit

theorem lineRoot_sq : AdjoinRoot.root lineG * AdjoinRoot.root lineG =
    algebraMap (LaurentPolynomial (ZMod 7)) (AdjoinRoot lineG)
      (lineD : LaurentPolynomial (ZMod 7)) := by
  have h := AdjoinRoot.eval₂_root lineG
  simp only [lineG, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [lineD, IsUnit.unit_spec, AdjoinRoot.algebraMap_eq, ← sq]
  exact sub_eq_zero.mp h

/-- R6 on the book's tick `K(1) M(-3)`, blocked by the even and odd cells. -/
example : block lineBasis (realize [Step.kick (1 : AdjoinRoot lineG), Step.move (-3)] :
      Matrix (Fin 2) (Fin 2) (AdjoinRoot lineG)) =
    realizePlaced (blockScore lineBasis [Step.kick (1 : AdjoinRoot lineG), Step.move (-3)]) :=
  blocking _ _ _ lineBasis _

/-- Red-black on the line, with `κ = 1` and the move `M(x)`, whose stencil `x` is black, is
a law of the blocked artform and the blocking of no law of the line. -/
example : ¬ ∃ T : Matrix (Fin 2) (Fin 2) (AdjoinRoot lineG),
    block lineBasis T = redBlackTick lineBasis 1 (AdjoinRoot.root lineG) := by
  intro hT
  have := (redBlack _ _ lineBasis _ lineD lineBasis_zero lineBasis_one lineRoot_sq 1
    (AdjoinRoot.root lineG)).2.2 hT
  rw [← lineBasis_one] at this
  simp at this

end Artform.Scores
