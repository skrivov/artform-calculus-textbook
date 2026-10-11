import ArtformTextbook.Ch12.EdgeSector
import ArtformTextbook.Ch11.ThereAndBack

/-!
# The operators of the models, as words for the kernel

Each operator of Chapter 12 on the occupations of one edge, written as an integer combination of
words in creations and annihilations (`FockCalc.Op`), in the book's order of the modes:

* `A_{cc'}` and `A_{cc'}†`, and `3 Ω = Σ (A† A + A A†) + m Σ (A A + A† A†)` (`Edge.tally3Op`);
* `S₊`, `S₋ = S₊†`, and the diagonal operators `2 S_z`, the parity `(-1)^{N_x}` and the sign
  `(-1)^{N_↑}` of the hole map, read off the masks (`FockCalc.diagonal_mulVec_toFock`);
* the six factors `a ± a†` of the hole map.

Then an operator that carries each product of a basis to an integer combination of products
carries a combination of products to the combination given by its matrix
(`SpecCert.mulVec_linearCombination`).
-/

namespace Artform

open scoped Matrix ComplexConjugate

open FockCalc Spin

namespace FockCalc

variable {M : Type*} [Fintype M] [DecidableEq M] {code : M → ℕ}

/-- A diagonal operator read off the masks: `d(decode k) = f k`. -/
theorem diagonal_mulVec_toFock (d : Finset M → ℂ) (f : ℕ → ℤ)
    (hf : ∀ k, d (decode code k) = f k) (v : Vec) :
    Matrix.diagonal d *ᵥ Vec.toFock code v =
      Vec.toFock code (v.map fun p => (p.1, f p.1 * p.2)) := by
  induction v with
  | nil => simp [Vec.toFock]
  | cons p v ih =>
    rw [Vec.toFock_cons, Matrix.mulVec_add, ih, List.map_cons, Vec.toFock_cons,
      Matrix.mulVec_smul, Vertex.diagonal_mulVec_ket, hf, smul_smul]
    push_cast
    ring_nf

end FockCalc

namespace Edge

/-- The modes of one edge with two slots. -/
abbrev EM : Type := Mode (Fin 3) (Fin 2)

/-- The three colours, as a list. -/
def colours : List (Fin 3) := [0, 1, 2]

theorem sum_colours {β : Type*} [AddCommMonoid β] (f : Fin 3 → β) :
    ∑ c, f c = (colours.map f).sum := by
  rw [Fin.sum_univ_three]
  simp [colours, add_assoc]

/-- `A_{cc'} = Σ_s a†_{ycs} a_{xc's}` as words. -/
def hopAOp (c c' : Fin 3) : Op EM :=
  [(1, [⟨true, Sum.inr (c, 0)⟩, ⟨false, Sum.inl (c', 0)⟩]),
    (1, [⟨true, Sum.inr (c, 1)⟩, ⟨false, Sum.inl (c', 1)⟩])]

/-- `A_{cc'}† = Σ_s a†_{xc's} a_{ycs}` as words. -/
def hopAdOp (c c' : Fin 3) : Op EM :=
  [(1, [⟨true, Sum.inl (c', 0)⟩, ⟨false, Sum.inr (c, 0)⟩]),
    (1, [⟨true, Sum.inl (c', 1)⟩, ⟨false, Sum.inr (c, 1)⟩])]

theorem two_word_toMat (a b : Letter EM) :
    wordMat bookOrd [a, b] = a.toMat bookOrd * b.toMat bookOrd := by
  simp [wordMat]

theorem hopAOp_toMat (c c' : Fin 3) : Op.toMat bookOrd (hopAOp c c') = hopA bookOrd c c' := by
  simp [Op.toMat, hopAOp, hopA, wordMat, Letter.toMat, Fin.sum_univ_two]

theorem hopAdOp_toMat (c c' : Fin 3) :
    Op.toMat bookOrd (hopAdOp c c') = (hopA bookOrd c c')ᴴ := by
  rw [ThereAndBack.hopA_conjTranspose]
  simp [Op.toMat, hopAdOp, wordMat, Letter.toMat, Fin.sum_univ_two]

/-- An operator scaled by an integer. -/
def Op.scale {M : Type*} (a : ℤ) (O : Op M) : Op M := O.map fun t => (a * t.1, t.2)

theorem Op.toMat_scale {M : Type*} [Fintype M] [DecidableEq M] (ord : LinearOrder M) (a : ℤ)
    (O : Op M) : Op.toMat ord (Op.scale a O) = (a : ℂ) • Op.toMat ord O := by
  induction O with
  | nil => simp [Op.scale, Op.toMat]
  | cons t O ih =>
    have e : Op.scale a (t :: O) = (a * t.1, t.2) :: Op.scale a O := rfl
    rw [e, Op.toMat_cons, Op.toMat_cons, ih, smul_add, smul_smul]
    push_cast
    rfl

theorem Op.toMat_flatMap {M : Type*} [Fintype M] [DecidableEq M] (ord : LinearOrder M)
    {ι : Type*} (l : List ι) (f : ι → Op M) :
    Op.toMat ord (l.flatMap f) = (l.map fun i => Op.toMat ord (f i)).sum := by
  induction l with
  | nil => simp [Op.toMat]
  | cons i l ih => rw [List.flatMap_cons, Op.toMat_append, ih, List.map_cons, List.sum_cons]

/-- `3 Ω = Σ_{c,c'} (A† A + A A†) + m Σ_{c,c'} (A A + A† A†)` as words. -/
def tally3Op (m : ℤ) : Op EM :=
  colours.flatMap fun c => colours.flatMap fun c' =>
    Op.mul (hopAdOp c c') (hopAOp c c') ++ Op.mul (hopAOp c c') (hopAdOp c c') ++
      Op.scale m (Op.mul (hopAOp c c') (hopAOp c c') ++ Op.mul (hopAdOp c c') (hopAdOp c c'))

theorem tally3Op_toMat (m : ℕ) :
    Op.toMat bookOrd (tally3Op m) = (3 : ℂ) • tally bookOrd m := by
  have h : Op.toMat bookOrd (tally3Op m) = ∑ c : Fin 3, ∑ c' : Fin 3,
      ((hopA bookOrd c c')ᴴ * hopA bookOrd c c' + hopA bookOrd c c' * (hopA bookOrd c c')ᴴ +
        (m : ℂ) • (hopA bookOrd c c' * hopA bookOrd c c' +
          (hopA bookOrd c c')ᴴ * (hopA bookOrd c c')ᴴ)) := by
    rw [tally3Op, Op.toMat_flatMap, ← sum_colours]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Op.toMat_flatMap, ← sum_colours]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [Op.toMat_append, Op.toMat_scale, Op.toMat_mul, hopAOp_toMat, hopAdOp_toMat]
    push_cast
    rfl
  rw [h, tally]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, smul_smul]
  rw [show (3 : ℂ) * (1 / 3) = 1 by norm_num, show (3 : ℂ) * ((m : ℂ) / 3) = m by ring]
  simp only [one_smul]

/-! ### Spin -/

/-- `S₊ = Σ_{v,c} a†_{vc↑} a_{vc↓}` as words. -/
def spinPlusOp : Op EM :=
  colours.flatMap fun c =>
    [(1, [⟨true, Sum.inl (c, 0)⟩, ⟨false, Sum.inl (c, 1)⟩]),
      (1, [⟨true, Sum.inr (c, 0)⟩, ⟨false, Sum.inr (c, 1)⟩])]

/-- `S₋ = Σ_{v,c} a†_{vc↓} a_{vc↑}` as words. -/
def spinMinusOp : Op EM :=
  colours.flatMap fun c =>
    [(1, [⟨true, Sum.inl (c, 1)⟩, ⟨false, Sum.inl (c, 0)⟩]),
      (1, [⟨true, Sum.inr (c, 1)⟩, ⟨false, Sum.inr (c, 0)⟩])]

theorem spinPlusOp_toMat : Op.toMat bookOrd spinPlusOp = spinPlus bookOrd := by
  rw [spinPlusOp, Op.toMat_flatMap, spinPlus, sum_colours]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp [Op.toMat, wordMat, Letter.toMat]

theorem spinMinusOp_toMat : Op.toMat bookOrd spinMinusOp = (spinPlus bookOrd)ᴴ := by
  rw [spinMinusOp, Op.toMat_flatMap, spinPlus, Matrix.conjTranspose_sum, sum_colours]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp [Op.toMat, wordMat, Letter.toMat, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Fock.conjTranspose_creation, ThereAndBack.annihilation_conjTranspose]

/-- The number of up quarks minus the number of down quarks of a mask, `2 S_z`. -/
def spinZ2 (k : ℕ) : ℤ :=
  ((decode code k).filter fun m => spinOf m = up).card -
    ((decode code k).filter fun m => spinOf m = down).card

theorem two_spinZ : (2 : ℂ) • spinZ = Matrix.diagonal fun n =>
    (((n.filter fun m => spinOf m = up).card : ℂ) - (n.filter fun m => spinOf m = down).card) := by
  rw [spinZ, ← Matrix.diagonal_smul]
  congr 1
  funext n
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem spinZ2_spec (k : ℕ) :
    (fun n : Finset EM => (((n.filter fun m => spinOf m = up).card : ℂ) -
      (n.filter fun m => spinOf m = down).card)) (decode code k) = (spinZ2 k : ℂ) := by
  simp [spinZ2]

/-- `(-1)^{N_x}` of a mask. -/
def parityF (k : ℕ) : ℤ := (-1) ^ (decode code k).toLeft.card

theorem parityF_spec (k : ℕ) :
    (fun n : Finset EM => (-1 : ℂ) ^ n.toLeft.card) (decode code k) = (parityF k : ℂ) := by
  simp [parityF]

/-- `(-1)^{N_↑}` of a mask. -/
def upSignF (k : ℕ) : ℤ := (-1) ^ ((decode code k).filter fun m => spinOf m = up).card

theorem upSignF_spec (k : ℕ) :
    (fun n : Finset EM => (-1 : ℂ) ^ (n.filter fun m => spinOf m = up).card) (decode code k) =
      (upSignF k : ℂ) := by
  simp [upSignF]

/-! ### The hole map -/

/-- `a_m + ε a†_m` as words. -/
def majOp (m : EM) (ε : ℤ) : Op EM := [(1, [⟨false, m⟩]), (ε, [⟨true, m⟩])]

theorem majOp_toMat (m : EM) (ε : ℤ) :
    Op.toMat bookOrd (majOp m ε) =
      Fock.annihilation bookOrd m + (ε : ℂ) • Fock.creation bookOrd m := by
  simp [Op.toMat, majOp, wordMat, Letter.toMat]

/-- The six factors of the hole map, `(a - a†)` at the up modes of `y` for colours `3, 2, 1`, then
`(a + a†)` at the up modes of `x` for colours `3, 2, 1`, as one operator. -/
def holeWordsOp : Op EM :=
  Op.mul (majOp (Sum.inr (2, 0)) (-1)) (Op.mul (majOp (Sum.inr (1, 0)) (-1))
    (Op.mul (majOp (Sum.inr (0, 0)) (-1)) (Op.mul (majOp (Sum.inl (2, 0)) 1)
      (Op.mul (majOp (Sum.inl (1, 0)) 1) (majOp (Sum.inl (0, 0)) 1)))))

theorem holeMap_eq : holeMap bookOrd =
    Matrix.diagonal (fun n : Finset EM => (-1 : ℂ) ^ (n.filter fun m => spinOf m = up).card) *
      Op.toMat bookOrd holeWordsOp := by
  simp only [holeMap, holeWordsOp, Op.toMat_mul, majOp_toMat, Int.cast_neg, Int.cast_one,
    neg_smul, one_smul, ← sub_eq_add_neg, mul_assoc]

end Edge

namespace SpecCert

/-- A combination of vectors given by a sparse list with indices below `n ≤ 2^d`. -/
theorem sum_entries_vec {N : Type*} {d n : ℕ} (hn : n ≤ 2 ^ d) (hn0 : 0 < n) (B : Fin n → N → ℂ)
    (l : Vec) (hl : keysLt n l = true) :
    (l.map fun p => (p.2 : ℂ) • B ⟨p.1 % n, Nat.mod_lt _ hn0⟩).sum =
      ∑ i : Fin n, (Vec.sumAt d i l : ℂ) • B i := by
  induction l with
  | nil => simp [Vec.sumAt]
  | cons p v ih =>
    simp only [keysLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2]
    simp only [sumAt_cons, Int.cast_add, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨p.1, hl.1⟩]
    · simp [Nat.mod_eq_of_lt hl.1]
    · intro i _ hi
      rw [ite_eq_right]
      · simp
      · intro h
        apply hi
        apply Fin.ext
        rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hl.1 hn),
          Nat.mod_eq_of_lt (lt_of_lt_of_le i.2 hn)] at h
        exact h.symm
    · simp

/-- An operator `X` that carries each vector `B j` of a basis to the combination of the `B i` with
the coefficients of the column `j` of `K` carries `Σ a_j B j` to `Σ (K a)_i B i`. -/
theorem mulVec_linearCombination {N : Type*} [Fintype N] {d n : ℕ} (hn : n ≤ 2 ^ d)
    (hn0 : 0 < n) (X : Matrix N N ℂ) (B : Fin n → N → ℂ) (cols : List Vec)
    (hk : ∀ j : Fin n, keysLt n (cols.getD j []) = true)
    (hX : ∀ j : Fin n, X *ᵥ B j = ((cols.getD j []).map fun p =>
      (p.2 : ℂ) • B ⟨p.1 % n, Nat.mod_lt _ hn0⟩).sum)
    (a : Fin n → ℂ) :
    X *ᵥ Fintype.linearCombination ℂ B a =
      Fintype.linearCombination ℂ B (colMat d n cols *ᵥ a) := by
  simp only [Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hX,
    sum_entries_vec hn hn0 B _ (hk _), Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end SpecCert

end Artform
