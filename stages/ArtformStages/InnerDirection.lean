import ArtformStages.Basic

/-!
# The inner direction

Finding 475 of the research ledger on a layered universe: a charge that moves needs an inner
direction, and the least inner direction is a spinor.

* `scalar_reach_one_unitary_iff` (ID1): on the ring of `N ≥ 5` places, with `S` the shift, the
  table `a S⁻¹ + b + c S` keeps the sum of the squares of the sizes of every wave exactly when
  `|a|² + |b|² + |c|² = 1` and two of `a`, `b` and `c` are `0`: it shifts rigidly, or it stands
  and turns.
* `pauli_anticommute`, `dirac_anticommute`, `no_anticommuting_odd`, `no_four_anticommuting_two`
  (ID2): two and three anticommuting involutions exist of size 2, and four of size 4; there are no
  two of any odd size, so none of size 1, and no four of size 2.
* `turnA`, `turnB`, `turnC`, `turn_relations`, `turnA_moves`, `turnB_moves` (ID3): the quarter,
  third and half turns of the cube on the half part, with `A⁴ = B³ = C² = A B C = -1`; `A` moves
  `σx` to `σy`, and `B` moves `σx` to `σy` to `σz` to `σx`.
* `spinor_no_rescaling` (ID4): no numbers `x`, `y`, `w` make `(x A)⁴`, `(y B)³`, `(w C)²` and
  `(x A) (y B) (w C)` all `1`.
* `rowsStage`, `halfPart_hom`, `halfPart_anticommute` (ID7): in the stage of `m` rows that pass up
  to a kept sign, every family of anticommuting involutions gives a map of the world into the
  invertible matrices that sends the kept sign to `-1`, and every such map sends the rows to
  anticommuting involutions.

None of this is new: ID1 is Meyer's theorem on scalar quantum cellular automata (1996), ID2 the
least sizes of the representations of Clifford algebras, ID3 and ID4 the binary octahedral group.
-/

open Matrix Complex ComplexConjugate
open scoped Kronecker

namespace Artform.Stages

/-! ### ID1: no motion without an inner direction -/

section Ring

variable {N : ℕ}

/-- The shift `S` of the ring of `N` places: it moves a wave by one place. -/
def ringShift (ψ : ZMod N → ℂ) : ZMod N → ℂ := fun x => ψ (x - 1)

/-- The shift undone, `S⁻¹`. -/
def ringUnshift (ψ : ZMod N → ℂ) : ZMod N → ℂ := fun x => ψ (x + 1)

/-- A table of reach 1, the same at every place, on waves of plain numbers: `a S⁻¹ + b + c S`. -/
def reachOne (a b c : ℂ) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  a • ringUnshift ψ + b • ψ + c • ringShift ψ

theorem reachOne_apply (a b c : ℂ) (ψ : ZMod N → ℂ) (x : ZMod N) :
    reachOne a b c ψ x = a * ψ (x + 1) + b * ψ x + c * ψ (x - 1) := rfl

theorem reachOne_add (a b c : ℂ) (φ ψ : ZMod N → ℂ) :
    reachOne a b c (φ + ψ) = reachOne a b c φ + reachOne a b c ψ := by
  funext x
  simp only [reachOne_apply, Pi.add_apply]
  ring

theorem reachOne_sub (a b c : ℂ) (φ ψ : ZMod N → ℂ) :
    reachOne a b c (φ - ψ) = reachOne a b c φ - reachOne a b c ψ := by
  funext x
  simp only [reachOne_apply, Pi.sub_apply]
  ring

theorem reachOne_smul (a b c t : ℂ) (ψ : ZMod N → ℂ) :
    reachOne a b c (t • ψ) = t • reachOne a b c ψ := by
  funext x
  simp only [reachOne_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The pairing of two waves, `∑ conj (φ x) ψ x`. -/
def ringPair [NeZero N] (φ ψ : ZMod N → ℂ) : ℂ := ∑ x, conj (φ x) * ψ x

theorem ringPair_self [NeZero N] (φ : ZMod N → ℂ) :
    ringPair φ φ = ((∑ x, ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ringPair, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]

/-- The pairing is read off the sums of squares. -/
theorem ringPair_polar [NeZero N] (φ ψ : ZMod N → ℂ) :
    4 * ringPair φ ψ = ringPair (φ + ψ) (φ + ψ) - ringPair (φ - ψ) (φ - ψ)
      - I * ringPair (φ + I • ψ) (φ + I • ψ) + I * ringPair (φ - I • ψ) (φ - I • ψ) := by
  simp only [ringPair, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul,
    Complex.conj_I]
  linear_combination (2 * conj (φ x) * ψ x - 2 * conj (ψ x) * φ x) * Complex.I_sq

theorem ringPair_add_left [NeZero N] (f g h : ZMod N → ℂ) :
    ringPair (f + g) h = ringPair f h + ringPair g h := by
  simp [ringPair, add_mul, Finset.sum_add_distrib]

theorem ringPair_add_right [NeZero N] (f g h : ZMod N → ℂ) :
    ringPair f (g + h) = ringPair f g + ringPair f h := by
  simp [ringPair, mul_add, Finset.sum_add_distrib]

theorem ringPair_smul_left [NeZero N] (t : ℂ) (f g : ZMod N → ℂ) :
    ringPair (t • f) g = conj t * ringPair f g := by
  simp [ringPair, Finset.mul_sum, mul_assoc]

theorem ringPair_smul_right [NeZero N] (t : ℂ) (f g : ZMod N → ℂ) :
    ringPair f (t • g) = t * ringPair f g := by
  simp [ringPair, Finset.mul_sum, mul_left_comm]

/-- A table that keeps the sum of squares of every wave keeps the pairing. -/
theorem ringPair_reachOne [NeZero N] {a b c : ℂ}
    (h : ∀ ψ : ZMod N → ℂ, ∑ x, ‖reachOne a b c ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2)
    (φ ψ : ZMod N → ℂ) :
    ringPair (reachOne a b c φ) (reachOne a b c ψ) = ringPair φ ψ := by
  have hQ : ∀ f : ZMod N → ℂ, ringPair (reachOne a b c f) (reachOne a b c f) = ringPair f f :=
    fun f => by rw [ringPair_self, ringPair_self, h]
  have h4 := ringPair_polar (reachOne a b c φ) (reachOne a b c ψ)
  rw [← reachOne_smul, ← reachOne_add, ← reachOne_add, ← reachOne_sub, ← reachOne_sub, hQ, hQ,
    hQ, hQ, ← ringPair_polar] at h4
  linear_combination h4 / 4

/-- The wave that is `1` at the place `p` and `0` elsewhere. -/
def ringDelta (p : ZMod N) : ZMod N → ℂ := fun x => if x = p then 1 else 0

theorem reachOne_delta (a b c : ℂ) (p : ZMod N) :
    reachOne a b c (ringDelta p) =
      a • ringDelta (p - 1) + b • ringDelta p + c • ringDelta (p + 1) := by
  funext x
  simp only [reachOne_apply, ringDelta, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ← eq_sub_iff_add_eq, sub_eq_iff_eq_add]

theorem ringPair_delta [NeZero N] (p q : ZMod N) :
    ringPair (ringDelta p) (ringDelta q) = if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst hpq
    simp [ringPair, ringDelta, apply_ite (starRingEnd ℂ)]
  · simp [ringPair, ringDelta, apply_ite (starRingEnd ℂ), hpq, Ne.symm hpq]

theorem zmod_natCast_ne_zero {k : ℕ} (hk : 0 < k) (hkN : k < N) : (k : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd hk h) (by omega)

theorem sum_norm_sq_shift [NeZero N] (t : ℂ) (ht : ‖t‖ ^ 2 = 1) (k : ZMod N)
    (ψ : ZMod N → ℂ) : ∑ x, ‖t * ψ (x + k)‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  simp only [norm_mul, mul_pow, ht, one_mul]
  exact Equiv.sum_comp (Equiv.addRight k) (fun x => ‖ψ x‖ ^ 2)

/-- **ID1** (Meyer's theorem). On the ring of `N ≥ 5` places the table `a S⁻¹ + b + c S` keeps
the sum of the squares of the sizes of every wave exactly when `|a|² + |b|² + |c|² = 1` and two
of `a`, `b` and `c` are `0`. -/
theorem scalar_reach_one_unitary_iff [NeZero N] (hN : 5 ≤ N) (a b c : ℂ) :
    (∀ ψ : ZMod N → ℂ, ∑ x, ‖reachOne a b c ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2) ↔
      ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 = 1 ∧ (a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 ∨ b = 0 ∧ c = 0) := by
  constructor
  · intro h
    have h1 : (1 : ZMod N) ≠ 0 := by exact_mod_cast zmod_natCast_ne_zero (k := 1) one_pos (by omega)
    have h2 : (2 : ZMod N) ≠ 0 := by exact_mod_cast zmod_natCast_ne_zero (k := 2) two_pos (by omega)
    have h3 : (3 : ZMod N) ≠ 0 := by
      exact_mod_cast zmod_natCast_ne_zero (k := 3) (by norm_num) (by omega)
    have h4 : (4 : ZMod N) ≠ 0 := by
      exact_mod_cast zmod_natCast_ne_zero (k := 4) (by norm_num) (by omega)
    have f1 : (-1 : ZMod N) ≠ 0 := fun e => h1 (by linear_combination -e)
    have f2 : (-1 : ZMod N) ≠ 1 := fun e => h2 (by linear_combination -e)
    have f3 : (-1 : ZMod N) ≠ 2 := fun e => h3 (by linear_combination -e)
    have f4 : (-1 : ZMod N) ≠ 3 := fun e => h4 (by linear_combination -e)
    have f5 : (0 : ZMod N) ≠ -1 := fun e => h1 (by linear_combination e)
    have f6 : (0 : ZMod N) ≠ 1 := fun e => h1 (by linear_combination -e)
    have f7 : (0 : ZMod N) ≠ 2 := fun e => h2 (by linear_combination -e)
    have f8 : (0 : ZMod N) ≠ 3 := fun e => h3 (by linear_combination -e)
    have f9 : (1 : ZMod N) ≠ -1 := fun e => h2 (by linear_combination e)
    have f11 : (1 : ZMod N) ≠ 2 := fun e => h1 (by linear_combination -e)
    have f12 : (1 : ZMod N) ≠ 3 := fun e => h2 (by linear_combination -e)
    have p1 : (0 : ZMod N) - 1 = -1 := zero_sub 1
    have p2 : (0 : ZMod N) + 1 = 1 := zero_add 1
    have p3 : (1 : ZMod N) - 1 = 0 := sub_self 1
    have p4 : (1 : ZMod N) + 1 = 2 := one_add_one_eq_two
    have p5 : (2 : ZMod N) - 1 = 1 := by ring
    have p6 : (2 : ZMod N) + 1 = 3 := by ring
    have e00 := ringPair_reachOne h (ringDelta 0) (ringDelta 0)
    have e01 := ringPair_reachOne h (ringDelta 0) (ringDelta 1)
    have e02 := ringPair_reachOne h (ringDelta 0) (ringDelta 2)
    simp only [reachOne_delta, p1, p2, p3, p4, p5, p6, ringPair_add_left, ringPair_add_right,
      ringPair_smul_left, ringPair_smul_right, ringPair_delta, f1, f2, f3, f4, f5, f6, f7, f8, f9,
      h1, f11, f12, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at e00 e01 e02
    refine ⟨?_, ?_⟩
    · rw [Complex.mul_conj', Complex.mul_conj', Complex.mul_conj'] at e00
      exact_mod_cast e00
    · have e02' : a = 0 ∨ c = 0 := by simpa using e02
      rcases e02' with rfl | rfl
      · have e01' : b = 0 ∨ c = 0 := by simpa using e01
        rcases e01' with rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · have e01' : a = 0 ∨ b = 0 := by simpa using e01
        rcases e01' with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro ⟨hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ ψ
    · have hc : ‖c‖ ^ 2 = 1 := by simpa using hn
      have e : ∀ x, reachOne 0 0 c ψ x = c * ψ (x + -1) := fun x => by
        simp [reachOne_apply, sub_eq_add_neg]
      simp only [e]
      exact sum_norm_sq_shift c hc (-1) ψ
    · have hb : ‖b‖ ^ 2 = 1 := by simpa using hn
      have e : ∀ x, reachOne 0 b 0 ψ x = b * ψ (x + 0) := fun x => by simp [reachOne_apply]
      simp only [e]
      exact sum_norm_sq_shift b hb 0 ψ
    · have ha : ‖a‖ ^ 2 = 1 := by simpa using hn
      have e : ∀ x, reachOne a 0 0 ψ x = a * ψ (x + 1) := fun x => by simp [reachOne_apply]
      simp only [e]
      exact sum_norm_sq_shift a ha 1 ψ

end Ring

/-! ### ID2: the half part of two, three and four rows -/

section HalfPart

/-- Anticommuting involutions: tables `γ i` with `γ i γ i = 1`, any two of which give opposite
products in their two orders. -/
def AnticommutingInvolutions {ι n : Type*} [Fintype n] [DecidableEq n] (γ : ι → Matrix n n ℂ) :
    Prop :=
  (∀ i, γ i * γ i = 1) ∧ ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i)

/-- The first row's table `σx`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The second row's table `σy`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The third row's table `σz`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_pauliY : pauliX * pauliY = -(pauliY * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_pauliZ : pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_pauliZ : pauliY * pauliZ = -(pauliZ * pauliY) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem anticomm_symm {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (h : A * B = -(B * A)) :
    B * A = -(A * B) := by
  rw [h, neg_neg]

/-- **ID2(a)**, two and three rows: the Pauli tables are anticommuting involutions of size 2. -/
theorem pauli_anticommute :
    AnticommutingInvolutions ![pauliX, pauliY] ∧
      AnticommutingInvolutions ![pauliX, pauliY, pauliZ] := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ⟨fun i => ?_, fun i j hij => ?_⟩⟩
  · fin_cases i
    exacts [pauliX_mul_self, pauliY_mul_self]
  · fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, pauliX_pauliY, anticomm_symm pauliX_pauliY, absurd rfl hij]
  · fin_cases i
    exacts [pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self]
  · fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, pauliX_pauliY, pauliX_pauliZ, anticomm_symm pauliX_pauliY,
      absurd rfl hij, pauliY_pauliZ, anticomm_symm pauliX_pauliZ, anticomm_symm pauliY_pauliZ,
      absurd rfl hij]

theorem kronecker_neg_left' {m n : Type*} (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp

theorem kronecker_neg_right' {m n : Type*} (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp

/-- The doubling of a family of tables of size `n`: `σy ⊗ 1` and the `σx ⊗ γᵢ`, of size `2 n`. -/
def doubleFamily {k : ℕ} {n : Type*} [DecidableEq n] (γ : Fin k → Matrix n n ℂ) :
    Fin (k + 1) → Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  Fin.cons (pauliY ⊗ₖ (1 : Matrix n n ℂ)) fun i => pauliX ⊗ₖ γ i

/-- The doubling of anticommuting involutions is one more of them, of twice the size. -/
theorem AnticommutingInvolutions.double {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    {γ : Fin k → Matrix n n ℂ} (h : AnticommutingInvolutions γ) :
    AnticommutingInvolutions (doubleFamily γ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      simp only [doubleFamily, Fin.cons_zero]
      rw [← mul_kronecker_mul, pauliY_mul_self, Matrix.one_mul, one_kronecker_one]
    | succ i =>
      simp only [doubleFamily, Fin.cons_succ]
      rw [← mul_kronecker_mul, pauliX_mul_self, h.1 i, one_kronecker_one]
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        simp only [doubleFamily, Fin.cons_zero, Fin.cons_succ]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, anticomm_symm pauliX_pauliY,
          Matrix.one_mul, Matrix.mul_one, kronecker_neg_left']
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [doubleFamily, Fin.cons_zero, Fin.cons_succ]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, pauliX_pauliY, Matrix.one_mul,
          Matrix.mul_one, kronecker_neg_left']
      | succ j =>
        simp only [doubleFamily, Fin.cons_succ]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, pauliX_mul_self,
          h.2 i j fun e => hij (by rw [e]), kronecker_neg_right']

/-- A map of rings sends anticommuting involutions to anticommuting involutions. -/
theorem AnticommutingInvolutions.map {ι n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix n' n' ℂ)]
    [RingHomClass F (Matrix n n ℂ) (Matrix n' n' ℂ)] (f : F) {γ : ι → Matrix n n ℂ}
    (h : AnticommutingInvolutions γ) : AnticommutingInvolutions fun i => f (γ i) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← map_mul, h.1 i, map_one]
  · rw [← map_mul, ← map_mul, h.2 i j hij, map_neg]

/-- Four tables of size 4: the doubling of the three Pauli tables, read on `Fin 4`. -/
def diracGamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun i =>
  reindexAlgEquiv ℂ ℂ (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
    (doubleFamily ![pauliX, pauliY, pauliZ] i)

/-- **ID2(a)**, four rows: four anticommuting involutions of size 4. -/
theorem dirac_anticommute : AnticommutingInvolutions diracGamma :=
  pauli_anticommute.2.double.map
    (reindexAlgEquiv ℂ ℂ (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4))

/-- **ID2(b)**, odd sizes: there are no two anticommuting involutions of an odd size. -/
theorem no_anticommuting_odd {d : ℕ} (hd : Odd d) :
    ¬ ∃ γ : Fin 2 → Matrix (Fin d) (Fin d) ℂ, AnticommutingInvolutions γ := by
  rintro ⟨γ, h1, h2⟩
  have hdet : ∀ i, (γ i).det ^ 2 = 1 := fun i => by rw [sq, ← det_mul, h1 i, det_one]
  have e := congrArg det (h2 0 1 (by decide))
  rw [det_neg, det_mul, det_mul, Fintype.card_fin, hd.neg_one_pow] at e
  have e0 : (γ 0).det * (γ 1).det = 0 := by linear_combination e / 2
  have e1 : (1 : ℂ) = 0 := by
    linear_combination -((γ 1).det ^ 2) * hdet 0 - hdet 1 + ((γ 0).det * (γ 1).det) * e0
  exact one_ne_zero e1

/-- So there are no two anticommuting involutions of size 1. -/
theorem no_anticommuting_one :
    ¬ ∃ γ : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ, AnticommutingInvolutions γ :=
  no_anticommuting_odd odd_one

/-- Two traceless tables of size 2 anticommute up to the trace of their product. -/
theorem traceless_anticomm (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : trace A = 0)
    (hB : trace B = 0) : A * B + B * A = trace (A * B) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [trace_fin_two] at hA hB
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two]
    linear_combination B 0 0 * hA - A 1 1 * hB
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination B 0 1 * hA + A 0 1 * hB
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination B 1 0 * hA + A 1 0 * hB
  · simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two]
    linear_combination A 1 1 * hB - B 0 0 * hA

/-- A table that anticommutes with an involution has trace `0`. -/
theorem trace_eq_zero_of_anticomm {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hB : B * B = 1) (h : A * B = -(B * A)) : trace A = 0 := by
  have e : trace A = -trace A := by
    calc trace A = trace (A * B * B) := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
      _ = trace (-(B * A) * B) := by rw [h]
      _ = -trace (B * A * B) := by rw [Matrix.neg_mul, trace_neg]
      _ = -trace (A * B * B) := by rw [Matrix.mul_assoc, trace_mul_comm]
      _ = -trace A := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  linear_combination e / 2

/-- The product of two anticommuting tables has trace `0`. -/
theorem trace_mul_eq_zero_of_anticomm {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (h : A * B = -(B * A)) : trace (A * B) = 0 := by
  have e : trace (A * B) = -trace (A * B) := by
    calc trace (A * B) = trace (-(B * A)) := by rw [h]
      _ = -trace (A * B) := by rw [trace_neg, trace_mul_comm]
  linear_combination e / 2

/-- **ID2(b)**, four rows: there are no four anticommuting involutions of size 2. -/
theorem no_four_anticommuting_two :
    ¬ ∃ γ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ, AnticommutingInvolutions γ := by
  rintro ⟨γ, h1, h2⟩
  have t0 : trace (γ 0) = 0 := trace_eq_zero_of_anticomm (h1 1) (h2 0 1 (by decide))
  have t1 : trace (γ 1) = 0 := trace_eq_zero_of_anticomm (h1 0) (h2 1 0 (by decide))
  have t01 : trace (γ 0 * γ 1) = 0 := trace_mul_eq_zero_of_anticomm (h2 0 1 (by decide))
  set X := γ 2 * γ 3 with hXdef
  have tX : trace X = 0 := trace_mul_eq_zero_of_anticomm (h2 2 3 (by decide))
  have passes : ∀ k, k ≠ 2 → k ≠ 3 → X * γ k = γ k * X := fun k hk2 hk3 => by
    rw [hXdef, Matrix.mul_assoc, h2 3 k hk3.symm, Matrix.mul_neg, ← Matrix.mul_assoc,
      h2 2 k hk2.symm, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have half : ∀ k, k ≠ 2 → k ≠ 3 → trace (γ k) = 0 →
      (2 : ℂ) • X = trace (X * γ k) • γ k := fun k hk2 hk3 tk => by
    have e := traceless_anticomm X (γ k) tX tk
    rw [← passes k hk2 hk3] at e
    calc (2 : ℂ) • X = (X * γ k + X * γ k) * γ k := by
          rw [← two_smul ℂ (X * γ k), Matrix.smul_mul, Matrix.mul_assoc, h1 k, Matrix.mul_one]
      _ = trace (X * γ k) • γ k := by rw [e, Matrix.smul_mul, Matrix.one_mul]
  have e0 := half 0 (by decide) (by decide) t0
  have e1 := half 1 (by decide) (by decide) t1
  have e2 : trace (X * γ 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      trace (X * γ 1) • (γ 0 * γ 1) := by
    have e := congrArg (γ 0 * ·) (e0.symm.trans e1)
    simp only [Matrix.mul_smul, h1 0] at e
    exact e
  have e3 := congrArg trace e2
  rw [trace_smul, trace_smul, trace_one, t01, Fintype.card_fin, smul_zero, smul_eq_mul] at e3
  have e4 : trace (X * γ 0) = 0 := by
    have : trace (X * γ 0) * 2 = 0 := by exact_mod_cast e3
    simpa using this
  rw [e4, zero_smul] at e0
  have hX : X = 0 := (smul_eq_zero.mp e0).resolve_left two_ne_zero
  have hXX : X * X = -1 := by
    rw [hXdef, Matrix.mul_assoc, ← Matrix.mul_assoc (γ 3), h2 3 2 (by decide), Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (γ 2), h1 2, Matrix.one_mul, h1 3]
  rw [hX, Matrix.zero_mul] at hXX
  have := congrFun (congrFun hXX 0) 0
  simp at this

end HalfPart

/-! ### ID3, ID4: the cube's turns on the half part -/

section Turns

/-- The quarter turn about the third axis: `diag((1 - i)/√2, (1 + i)/√2)`. -/
noncomputable def turnA : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1 - I, 0; 0, 1 + I]

/-- The third turn about the diagonal: `(1 - i (σx + σy + σz)) / 2`. -/
noncomputable def turnB : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • !![1 - I, -1 - I; 1 - I, 1 + I]

/-- The half turn about the line through the middles of two opposite edges:
`-i (σy + σz) / √2`. -/
noncomputable def turnC : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![-I, -1; 1, I]

theorem sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sqrt_two_inv_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 2⁻¹ := by
  rw [inv_pow, sqrt_two_sq]

theorem turnB_eq_pauli : turnB = (2 : ℂ)⁻¹ • (1 - I • (pauliX + pauliY + pauliZ)) := by
  rw [turnB]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ] <;> ring_nf <;>
    simp [Complex.ext_iff]

theorem turnA_pow_four : turnA ^ 4 = -1 := by
  have e : (!![1 - I, 0; 0, 1 + I] : Matrix (Fin 2) (Fin 2) ℂ) ^ 4 = (-4 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num
  rw [turnA, smul_pow, e, smul_smul, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt_two_inv_sq]
  norm_num

theorem turnB_pow_three : turnB ^ 3 = -1 := by
  have e : (!![1 - I, -1 - I; 1 - I, 1 + I] : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = (-8 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num
  rw [turnB, smul_pow, e, smul_smul]
  norm_num

theorem turnC_pow_two : turnC ^ 2 = -1 := by
  have e : (!![-I, -1; 1, I] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = (-2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num
  rw [turnC, smul_pow, e, smul_smul, sqrt_two_inv_sq]
  norm_num

theorem turnA_turnB_turnC : turnA * turnB * turnC = -1 := by
  have e : (!![1 - I, 0; 0, 1 + I] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![1 - I, -1 - I; 1 - I, 1 + I] * !![-I, -1; 1, I] = (-4 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num
  rw [turnA, turnB, turnC, smul_mul_smul_comm, smul_mul_smul_comm, e, smul_smul]
  convert neg_one_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) using 2
  linear_combination (-2 : ℂ) * sqrt_two_inv_sq

/-- **ID3**, the relations: `A⁴ = B³ = C² = A B C = -1`. -/
theorem turn_relations :
    turnA ^ 4 = -1 ∧ turnB ^ 3 = -1 ∧ turnC ^ 2 = -1 ∧ turnA * turnB * turnC = -1 :=
  ⟨turnA_pow_four, turnB_pow_three, turnC_pow_two, turnA_turnB_turnC⟩

/-- The half turn is `-(A B)⁻¹`. -/
theorem turnC_eq : turnC = -(turnA * turnB)⁻¹ := by
  have e : turnA * turnB * -turnC = 1 := by rw [Matrix.mul_neg, turnA_turnB_turnC, neg_neg]
  rw [Matrix.inv_eq_right_inv e, neg_neg]

/-- A table with a power `-1` has a right inverse. -/
theorem mul_inv_of_pow_eq_neg_one {M : Matrix (Fin 2) (Fin 2) ℂ} {k : ℕ} (h : M ^ (k + 1) = -1) :
    M * M⁻¹ = 1 := by
  have h1 : M * -(M ^ k) = 1 := by rw [Matrix.mul_neg, ← pow_succ', h, neg_neg]
  rw [Matrix.inv_eq_right_inv h1, h1]

theorem turnA_pauliX : turnA * pauliX = pauliY * turnA := by
  rw [turnA, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

theorem turnB_pauli :
    turnB * pauliX = pauliY * turnB ∧ turnB * pauliY = pauliZ * turnB ∧
      turnB * pauliZ = pauliX * turnB := by
  simp only [turnB, Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- **ID3**, the quarter turn moves the first row's table to the second: `A σx A⁻¹ = σy`. -/
theorem turnA_moves : turnA * pauliX * turnA⁻¹ = pauliY := by
  rw [turnA_pauliX, Matrix.mul_assoc, mul_inv_of_pow_eq_neg_one (k := 3) turnA_pow_four,
    Matrix.mul_one]

/-- **ID3**, the third turn moves the three rows' tables round: `σx` to `σy` to `σz` to `σx`. -/
theorem turnB_moves :
    turnB * pauliX * turnB⁻¹ = pauliY ∧ turnB * pauliY * turnB⁻¹ = pauliZ ∧
      turnB * pauliZ * turnB⁻¹ = pauliX := by
  have hB := mul_inv_of_pow_eq_neg_one (k := 2) turnB_pow_three
  obtain ⟨e1, e2, e3⟩ := turnB_pauli
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Matrix.mul_assoc, hB, Matrix.mul_one]
  · rw [e2, Matrix.mul_assoc, hB, Matrix.mul_one]
  · rw [e3, Matrix.mul_assoc, hB, Matrix.mul_one]

/-- **ID4**: no rescaling of the three turns makes all four relations `1`; the turns act on the
half part only up to a sign. -/
theorem spinor_no_rescaling :
    ¬ ∃ x y w : ℂ, (x • turnA) ^ 4 = 1 ∧ (y • turnB) ^ 3 = 1 ∧ (w • turnC) ^ 2 = 1 ∧
      (x • turnA) * (y • turnB) * (w • turnC) = 1 := by
  rintro ⟨x, y, w, h1, h2, h3, h4⟩
  rw [smul_pow, turnA_pow_four] at h1
  rw [smul_pow, turnB_pow_three] at h2
  rw [smul_pow, turnC_pow_two] at h3
  rw [smul_mul_smul_comm, smul_mul_smul_comm, turnA_turnB_turnC] at h4
  have entry : ∀ t : ℂ, t • (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 → t = -1 := fun t ht => by
    have := congrFun (congrFun ht 0) 0
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_neg, mul_one] at this
    linear_combination -this
  have ex := entry _ h1
  have ey := entry _ h2
  have ew := entry _ h3
  have exyw := entry _ h4
  have e12 : (x * y * w) ^ 12 = x ^ 12 * y ^ 12 * w ^ 12 := by ring
  rw [exyw, show x ^ 12 = (x ^ 4) ^ 3 by ring, show y ^ 12 = (y ^ 3) ^ 4 by ring,
    show w ^ 12 = (w ^ 2) ^ 6 by ring, ex, ey, ew] at e12
  norm_num at e12

end Turns

/-! ### ID7: the half part is the stage's kept sign at `-1` -/

section RowsStage

/-- The stage of `m` rows that pass up to a kept sign (charter D1): the acts `some i`, the row
`gᵢ`, and `none`, the kept sign `z`, with the rules: each `gᵢ` made twice is rest; `z` made twice
is rest; `z` passes every `gᵢ`; and for `i ≠ j`, `gᵢ gⱼ gᵢ⁻¹ gⱼ⁻¹` is `z`. -/
def rowsStage (m : ℕ) : Stage (Option (Fin m)) :=
  ⟨{r : FreeGroup (Option (Fin m)) |
    (∃ i, r = FreeGroup.of (some i) * FreeGroup.of (some i)) ∨
    r = FreeGroup.of none * FreeGroup.of none ∨
    (∃ i, r = FreeGroup.of none * FreeGroup.of (some i) * (FreeGroup.of none)⁻¹ *
      (FreeGroup.of (some i))⁻¹) ∨
    ∃ i j, i ≠ j ∧ r = FreeGroup.of (some i) * FreeGroup.of (some j) *
      (FreeGroup.of (some i))⁻¹ * (FreeGroup.of (some j))⁻¹ * (FreeGroup.of none)⁻¹}⟩

/-- Two involutions whose product made twice is `-1` anticommute. -/
theorem anticomm_of_mul_four {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A * A = 1) (hB : B * B = 1) (h : A * B * A * B = -1) : A * B = -(B * A) := by
  calc A * B = A * B * A * (B * B) * A := by
        rw [hB, Matrix.mul_one, Matrix.mul_assoc, hA, Matrix.mul_one]
    _ = A * B * A * B * (B * A) := by simp only [Matrix.mul_assoc]
    _ = -(B * A) := by rw [h, neg_one_mul]

/-- **ID7(a)**: every family of anticommuting involutions of size `d` gives a map of the world of
the rows' stage into the invertible `d × d` matrices, `gᵢ ↦ γᵢ` and `z ↦ -1`. -/
theorem halfPart_hom {m d : ℕ} (γ : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hγ : AnticommutingInvolutions γ) :
    ∃ φ : (rowsStage m).World →* (Matrix (Fin d) (Fin d) ℂ)ˣ,
      (∀ i, (φ ((rowsStage m).law (FreeGroup.of (some i))) : Matrix (Fin d) (Fin d) ℂ) = γ i) ∧
      (φ ((rowsStage m).law (FreeGroup.of none)) : Matrix (Fin d) (Fin d) ℂ) = -1 := by
  let u : Fin m → (Matrix (Fin d) (Fin d) ℂ)ˣ := fun i => ⟨γ i, γ i, hγ.1 i, hγ.1 i⟩
  have huu : ∀ i, u i * u i = 1 := fun i => Units.ext (hγ.1 i)
  have hu : ∀ i, (u i)⁻¹ = u i := fun i => inv_eq_of_mul_eq_one_right (huu i)
  have hanti : ∀ i j, i ≠ j → u i * u j * u i * u j = -1 := fun i j hij => by
    apply Units.ext
    change γ i * γ j * γ i * γ j = -1
    rw [Matrix.mul_assoc (γ i), hγ.2 j i hij.symm, Matrix.mul_neg, Matrix.neg_mul,
      ← Matrix.mul_assoc, hγ.1 i, Matrix.one_mul, hγ.1 j]
  let f : Option (Fin m) → (Matrix (Fin d) (Fin d) ℂ)ˣ := fun o => o.elim (-1) u
  have hf : ∀ r ∈ (rowsStage m).rules, FreeGroup.lift f r = 1 := by
    rintro r (⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simp [f, huu]
    · simp [f]
    · simp [f, hu, huu]
    · simp [f, hu, hanti i j hij]
  exact ⟨PresentedGroup.toGroup hf, fun i => congrArg Units.val (PresentedGroup.toGroup.of hf),
    congrArg Units.val (PresentedGroup.toGroup.of hf)⟩

/-- **ID7(b)**: every map of the world of the rows' stage into the invertible `d × d` matrices
that sends the kept sign to `-1` sends the rows to anticommuting involutions. -/
theorem halfPart_anticommute {m d : ℕ} (φ : (rowsStage m).World →* (Matrix (Fin d) (Fin d) ℂ)ˣ)
    (hz : (φ ((rowsStage m).law (FreeGroup.of none)) : Matrix (Fin d) (Fin d) ℂ) = -1) :
    AnticommutingInvolutions
      fun i => (φ ((rowsStage m).law (FreeGroup.of (some i))) : Matrix (Fin d) (Fin d) ℂ) := by
  have hrule : ∀ r ∈ (rowsStage m).rules, φ ((rowsStage m).law r) = 1 := fun r hr => by
    rw [(rowsStage m).law_eq_one_iff.mpr ((rowsStage m).rules_subset_rest hr), map_one]
  have hgg : ∀ i, φ ((rowsStage m).law (FreeGroup.of (some i))) *
      φ ((rowsStage m).law (FreeGroup.of (some i))) = 1 := fun i => by
    have := hrule _ (Or.inl ⟨i, rfl⟩)
    rwa [map_mul, map_mul] at this
  have hval : ∀ i, (φ ((rowsStage m).law (FreeGroup.of (some i))) : Matrix (Fin d) (Fin d) ℂ) *
      φ ((rowsStage m).law (FreeGroup.of (some i))) = 1 := fun i => by
    rw [← Units.val_mul, hgg i, Units.val_one]
  refine ⟨hval, fun i j hij => ?_⟩
  have hinv : ∀ k, (φ ((rowsStage m).law (FreeGroup.of (some k))))⁻¹ =
      φ ((rowsStage m).law (FreeGroup.of (some k))) := fun k =>
    inv_eq_of_mul_eq_one_right (hgg k)
  have h1 := hrule _ (Or.inr (Or.inr (Or.inr ⟨i, j, hij, rfl⟩)))
  simp only [map_mul, map_inv] at h1
  rw [mul_inv_eq_one, hinv, hinv] at h1
  have h2 := congrArg Units.val h1
  simp only [Units.val_mul] at h2
  rw [hz] at h2
  exact anticomm_of_mul_four (hval i) (hval j) h2

end RowsStage

end Artform.Stages
