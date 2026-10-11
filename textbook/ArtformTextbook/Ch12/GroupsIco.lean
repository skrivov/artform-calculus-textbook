import ArtformTextbook.Ch12.ColourGroupsCheck
import ArtformTextbook.Ch12.GroupsSU3

/-!
# The icosahedral group and `C₃ × A₅` as finite colour groups

The sixty rotations `Icosahedron.R k` enumerate the icosahedral group; their product is read
from the table `a5At`, which the kernel checked on the base edge, and a rotation is fixed by
the images of the base edge. From the exact traces of the rotations come the classes, the
values of the character table and the averages over the group; from the product, the orders
and the exponent. `C₃ × A₅` follows.
-/

namespace Artform.ColourGroups

open Exact Icosahedron Matrix

/-! ### Two general tools -/

/-- The search `ordAux` finds the order: if `f` carries the product `mul x ·` to the product by
`f x` on a set `S` of codes, and `f y = 1` only for `y = one`, then from `acc = x^n` the search
returns, within its fuel, an `r` with `f x ^ r = 1` and no power `f x ^ m ≠ 1` in between. -/
theorem ordAux_spec {M : Type*} [Monoid M] (mul : ℕ → ℕ → ℕ) (one x : ℕ) (f : ℕ → M)
    (S : Set ℕ) (hS : ∀ y ∈ S, mul x y ∈ S) (hmul : ∀ y ∈ S, f (mul x y) = f x * f y)
    (hone : f one = 1) (hinj : ∀ y ∈ S, f y = 1 → y = one) :
    ∀ fuel acc n, acc ∈ S → f acc = f x ^ n → ordAux mul one x fuel acc n < n + fuel →
      f x ^ ordAux mul one x fuel acc n = 1 ∧
        ∀ m, n ≤ m → m < ordAux mul one x fuel acc n → f x ^ m ≠ 1 := by
  intro fuel
  induction fuel with
  | zero => intro acc n _ _ h; simp [ordAux] at h
  | succ fuel ih =>
    intro acc n hS' hacc h
    by_cases h1 : acc = one
    · simp only [ordAux, h1, ite_true] at h ⊢
      refine ⟨?_, fun m hm1 hm2 => absurd hm2 (not_lt.mpr hm1)⟩
      rw [← hacc, h1, hone]
    · simp only [ordAux, h1, ite_false] at h ⊢
      have hacc' : f (mul x acc) = f x ^ (n + 1) := by rw [hmul acc hS', hacc, pow_succ']
      obtain ⟨h2, h3⟩ := ih (mul x acc) (n + 1) (hS acc hS') hacc' (by omega)
      refine ⟨h2, fun m hm1 hm2 => ?_⟩
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · have : m = n := by omega
        subst this
        rw [← hacc]
        exact fun h4 => h1 (hinj acc hS' h4)
      · exact h3 m hm hm2

/-- The order of `f x`, found by the search started at `mul x one`. -/
theorem orderOf_eq_ordAux {M : Type*} [Monoid M] (mul : ℕ → ℕ → ℕ) (one x : ℕ) (f : ℕ → M)
    (S : Set ℕ) (hS : ∀ y ∈ S, mul x y ∈ S) (hone' : one ∈ S)
    (hmul : ∀ y ∈ S, f (mul x y) = f x * f y) (hone : f one = 1)
    (hinj : ∀ y ∈ S, f y = 1 → y = one) (fuel : ℕ)
    (hlt : ordAux mul one x fuel (mul x one) 1 < 1 + fuel) :
    orderOf (f x) = ordAux mul one x fuel (mul x one) 1 := by
  have h1 : f (mul x one) = f x ^ 1 := by rw [hmul one hone', hone, mul_one, pow_one]
  obtain ⟨h2, h3⟩ := ordAux_spec mul one x f S hS hmul hone hinj fuel (mul x one) 1
    (hS one hone') h1 hlt
  have hpos : 0 < ordAux mul one x fuel (mul x one) 1 := by
    rcases Nat.eq_zero_or_pos (ordAux mul one x fuel (mul x one) 1) with h | h
    · exfalso
      have key : ∀ fuel acc n, 1 ≤ n → 1 ≤ ordAux mul one x fuel acc n := by
        intro fuel
        induction fuel with
        | zero => intro acc n hn; simpa [ordAux] using hn
        | succ fuel ih =>
          intro acc n hn
          simp only [ordAux]
          split_ifs
          · exact hn
          · exact ih _ _ (by omega)
      have := key fuel (mul x one) 1 le_rfl
      omega
    · exact h
  rw [orderOf_eq_iff hpos]
  exact ⟨h2, fun m hm hm0 => h3 m hm0 hm⟩

/-- A sum in `ℤ[ω, φ]` by recursion: `zsum f m = f (m - 1) + ⋯ + f 0`. -/
def zsum (f : ℕ → ZOP) : ℕ → ZOP
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 => f n + zsum f n

theorem toComplex_zsum (f : ℕ → ZOP) (m : ℕ) :
    ZOP.toComplex (zsum f m) = ∑ n ∈ Finset.range m, ZOP.toComplex (f n) := by
  induction m with
  | zero => simp [zsum, ZOP.toComplex]
  | succ m ih => rw [zsum, ZOP.toComplex_add, ih, Finset.sum_range_succ, add_comm]

/-- Reading a check by recursion at one point. -/
theorem allBelow_at {P : ℕ → Bool} {m : ℕ} (h : allBelow P m = true) {n : ℕ} (hn : n < m) :
    P n = true :=
  (allBelow_iff P m).mp h n hn

/-! ### The product of rotations -/

/-- The product of two rotations, as an index. -/
def a5Mul (k l : Fin 60) : Fin 60 :=
  ⟨a5At k l, by
    have h := allBelow_at (allBelow_at a5At_check k.2) l.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1⟩

theorem perm_a5Mul (k l : Fin 60) :
    perm (a5Mul k l) 0 = perm k (perm l 0) ∧ perm (a5Mul k l) 4 = perm k (perm l 4) := by
  have h := allBelow_at (allBelow_at a5At_check k.2) l.2
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨_, h0⟩, h4⟩ := h
  have e : ∀ (a : Fin 60) (i : Fin 12), permAt a i = perm a i := permAt_eq
  constructor
  · apply Fin.ext
    have := e (a5Mul k l) 0
    rw [← this, ← e k (perm l 0), ← e l 0]
    exact h0
  · apply Fin.ext
    have := e (a5Mul k l) 4
    rw [← this, ← e k (perm l 4), ← e l 4]
    exact h4

/-- The base edge `(vR 0, vR 4)` is an edge of the icosahedron. -/
theorem base_edge_real : vR 0 ⬝ᵥ vR 4 = Real.goldenRatio := (vR_dot_eq_phi_iff 0 4).2 base_edge

theorem vR_mem (i : Fin 12) : vR i ∈ icoVertices := by
  rw [icoVertices_eq]
  exact ⟨i, rfl⟩

/-- The table gives the product of rotations. -/
theorem R_a5Mul (k l : Fin 60) : R (a5Mul k l) = R k * R l := by
  obtain ⟨h0, h4⟩ := perm_a5Mul k l
  refine determined (vR 0) (vR_mem 0) (vR 4) (vR_mem 4) base_edge_real _ (R_mem _) _
    (mul_mem_icoRotations (R_mem k) (R_mem l)) ?_ ?_
  · rw [R_mulVec, ← mulVec_mulVec, R_mulVec, R_mulVec, h0]
  · rw [R_mulVec, ← mulVec_mulVec, R_mulVec, R_mulVec, h4]

theorem R_one : R 1 = 1 := by
  have h := congrArg M3.toRealHalf (show gE 1 = ⟨⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩,
      ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩⟩ from rfl)
  rw [R, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3.toRealHalf, ZPhi.toReal]

/-! ### The icosahedral group, enumerated -/

/-- Rotation `k`, read as a complex matrix. -/
noncomputable def rotC (k : Fin 60) : Matrix (Fin 3) (Fin 3) ℂ := (R k).map (fun x : ℝ => (x : ℂ))

theorem rotC_mem (k : Fin 60) : rotC k ∈ specialUnitaryGroup (Fin 3) ℂ :=
  map_ofReal_mem_specialUnitaryGroup (R_mem_SO k)

/-- Rotation `k` as an element of the icosahedral group. -/
noncomputable def icoElt (k : Fin 60) : icoGroup :=
  ⟨⟨rotC k, rotC_mem k⟩, R k, R_mem k, rfl⟩

theorem rotC_a5Mul (k l : Fin 60) : rotC (a5Mul k l) = rotC k * rotC l := by
  rw [rotC, R_a5Mul, map_ofReal_mul]
  rfl

theorem rotC_one : rotC 1 = 1 := by
  rw [rotC, R_one]
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

theorem icoElt_mul (k l : Fin 60) : icoElt (a5Mul k l) = icoElt k * icoElt l := by
  apply Subtype.ext
  apply Subtype.ext
  exact rotC_a5Mul k l

theorem icoElt_one : icoElt 1 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact rotC_one

theorem rotC_injective : Function.Injective rotC := by
  intro k l h
  apply R_injective
  ext i j
  have := congrFun (congrFun h i) j
  simpa [rotC] using this

theorem icoElt_injective : Function.Injective icoElt := by
  intro k l h
  apply rotC_injective
  have := congrArg (fun g : icoGroup => ((g : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ)) h
  exact this

theorem icoElt_surjective : Function.Surjective icoElt := by
  rintro ⟨g, R', hR', hg⟩
  rw [icoRotations_eq] at hR'
  obtain ⟨k, rfl⟩ := hR'
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  exact hg.symm

/-- The sixty rotations, as the elements of the icosahedral group. -/
noncomputable def icoEquiv : Fin 60 ≃ icoGroup :=
  Equiv.ofBijective icoElt ⟨icoElt_injective, icoElt_surjective⟩

theorem card_icoGroup : Nat.card icoGroup = 60 := by
  rw [← Nat.card_congr icoEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

noncomputable instance : Fintype icoGroup := Fintype.ofEquiv _ icoEquiv

theorem finsum_icoGroup (f : icoGroup → ℂ) : ∑ᶠ g, f g = ∑ k : Fin 60, f (icoElt k) := by
  rw [← finsum_comp_equiv icoEquiv, finsum_eq_sum_of_fintype]
  rfl

/-! ### Orders and the exponent -/

theorem a5At_lt' (k l : ℕ) (hk : k < 60) (hl : l < 60) : a5At k l < 60 := (a5Mul ⟨k, hk⟩ ⟨l, hl⟩).2

/-- Rotation `n` as an element of the icosahedral group, for a natural number `n`. -/
noncomputable def icoEltN (n : ℕ) : icoGroup := icoElt ⟨n % 60, Nat.mod_lt _ (by norm_num)⟩

theorem icoEltN_mul (k l : ℕ) (hk : k < 60) (hl : l < 60) :
    icoEltN (a5At k l) = icoEltN k * icoEltN l := by
  have e := icoElt_mul ⟨k, hk⟩ ⟨l, hl⟩
  simp only [icoEltN, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt (a5At_lt' k l hk hl)]
  exact e

theorem orderOf_icoElt (k : Fin 60) : orderOf (icoElt k) = ordA5 k := by
  have h := allBelow_at ordA5_check k.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have e : icoElt k = icoEltN k := by simp [icoEltN, Nat.mod_eq_of_lt k.2]
  rw [e]
  refine orderOf_eq_ordAux a5At 1 k icoEltN {y | y < 60} (fun y hy => a5At_lt' _ _ k.2 hy)
    (by norm_num) (fun y hy => icoEltN_mul _ _ k.2 hy) ?_ ?_ 60 (by unfold ordA5 at h; omega)
  · simp [icoEltN, icoElt_one]
  · intro y hy h1
    have : icoEltN y = icoElt 1 := by rw [h1, icoElt_one]
    simp only [icoEltN, Nat.mod_eq_of_lt hy] at this
    have := icoElt_injective this
    simpa using congrArg Fin.val this

theorem exponent_icoGroup : Monoid.exponent icoGroup = 30 := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    obtain ⟨k, rfl⟩ := icoElt_surjective g
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_icoElt]
    have h := allBelow_at ordA5_check k.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · obtain ⟨h2, h3, h5⟩ := ordA5_gens
    have d2 : 2 ∣ Monoid.exponent icoGroup := by
      have := Monoid.order_dvd_exponent (icoElt ⟨a5GenA, a5Gen_lt.1⟩)
      rwa [orderOf_icoElt, h2] at this
    have d3 : 3 ∣ Monoid.exponent icoGroup := by
      have := Monoid.order_dvd_exponent (icoElt ⟨a5GenB, a5Gen_lt.2⟩)
      rwa [orderOf_icoElt, h3] at this
    have d5 : 5 ∣ Monoid.exponent icoGroup := by
      have := Monoid.order_dvd_exponent (icoElt 0)
      rwa [orderOf_icoElt, show ((0 : Fin 60) : ℕ) = 0 from rfl, h5] at this
    have d6 : 6 ∣ Monoid.exponent icoGroup :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 d3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d6 d5


/-! ### Characters of the icosahedral group -/

/-- The doubled trace of rotation `n`, exactly. -/
def trA5 (n : ℕ) : ZOP := M3Z.trace (gAt n)

/-- The class of a rotation, read off its doubled trace: `6`, `-2`, `0`, `2φ` or `2 - 2φ`. -/
def a5ClassZ (t : ZOP) : A5Class :=
  if t = ⟨6, 0, 0, 0⟩ then .identity else if t = ⟨-2, 0, 0, 0⟩ then .halfTurn
  else if t = ⟨0, 0, 0, 0⟩ then .thirdTurn else if t = ⟨0, 2, 0, 0⟩ then .fifthTurn
  else .twoFifthsTurn

/-- The character table of the icosahedral group, exactly, `φ = ⟨0, 1, 0, 0⟩`. -/
def a5TabZ : A5Block → A5Class → ZOP
  | .one, _ => ⟨1, 0, 0, 0⟩
  | .three, .identity => ⟨3, 0, 0, 0⟩
  | .three, .halfTurn => ⟨-1, 0, 0, 0⟩
  | .three, .thirdTurn => ⟨0, 0, 0, 0⟩
  | .three, .fifthTurn => ⟨0, 1, 0, 0⟩
  | .three, .twoFifthsTurn => ⟨1, -1, 0, 0⟩
  | .three', .identity => ⟨3, 0, 0, 0⟩
  | .three', .halfTurn => ⟨-1, 0, 0, 0⟩
  | .three', .thirdTurn => ⟨0, 0, 0, 0⟩
  | .three', .fifthTurn => ⟨1, -1, 0, 0⟩
  | .three', .twoFifthsTurn => ⟨0, 1, 0, 0⟩
  | .four, .identity => ⟨4, 0, 0, 0⟩
  | .four, .halfTurn => ⟨0, 0, 0, 0⟩
  | .four, .thirdTurn => ⟨1, 0, 0, 0⟩
  | .four, .fifthTurn => ⟨-1, 0, 0, 0⟩
  | .four, .twoFifthsTurn => ⟨-1, 0, 0, 0⟩
  | .five, .identity => ⟨5, 0, 0, 0⟩
  | .five, .halfTurn => ⟨1, 0, 0, 0⟩
  | .five, .thirdTurn => ⟨-1, 0, 0, 0⟩
  | .five, .fifthTurn => ⟨0, 0, 0, 0⟩
  | .five, .twoFifthsTurn => ⟨0, 0, 0, 0⟩

theorem a5CharTable_eq (ρ : A5Block) (c : A5Class) :
    a5CharTable ρ c = ZOP.toComplex (a5TabZ ρ c) := by
  cases ρ <;> cases c <;> simp [a5CharTable, a5TabZ, ZOP.toComplex] <;> ring

theorem trA5_eq (k : Fin 60) : trA5 k = ZOP.ofZPhi (gE k).trace := by
  rw [trA5, gAt_eq]
  rfl

theorem char_icoElt (k : Fin 60) :
    colourChar icoGroup (icoElt k) = ZOP.toComplex (trA5 k) / 2 := by
  have h : colourChar icoGroup (icoElt k) = ((R k).trace : ℂ) := by
    simp [colourChar, icoElt, rotC, Matrix.trace_fin_three]
  rw [h, R_trace, trA5_eq, ZOP.toComplex_ofZPhi]
  push_cast
  ring

theorem conj_char_icoElt (k : Fin 60) :
    (starRingEnd ℂ) (colourChar icoGroup (icoElt k)) = colourChar icoGroup (icoElt k) := by
  rw [char_icoElt, trA5_eq, ZOP.toComplex_ofZPhi, map_div₀, Complex.conj_ofReal, map_ofNat]

theorem one_lt_phi : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio

theorem phi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two

theorem a5ClassOf_icoElt (k : Fin 60) : a5ClassOf (icoElt k) = a5ClassZ (trA5 k) := by
  have h1 := one_lt_phi
  have h2 := phi_lt_two
  have v : ∀ a b : ℤ,
      ZOP.toComplex (ZOP.ofZPhi ⟨a, b⟩) / 2 = ((a + b * Real.goldenRatio) / 2 : ℂ) := by
    intro a b
    rw [ZOP.toComplex_ofZPhi, ZPhi.toReal]
    push_cast
    ring
  rw [a5ClassOf, char_icoElt, trA5_eq]
  rcases gE_trace_cases k with h | h | h | h | h <;> rw [h, v] <;> simp only [a5ClassZ]
  · rw [ite_eq_left (by norm_num)]
    rfl
  · rw [ite_eq_right (by norm_num), ite_eq_left (by norm_num)]
    rfl
  · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), ite_eq_left (by norm_num)]
    rfl
  · have e : (((0 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Real.goldenRatio) / 2 = (Real.goldenRatio : ℂ) := by
      push_cast; ring
    rw [e, ite_eq_right (by exact_mod_cast (show Real.goldenRatio ≠ 3 by linarith)),
      ite_eq_right (by exact_mod_cast (show Real.goldenRatio ≠ -1 by linarith)),
      ite_eq_right (by exact_mod_cast (show Real.goldenRatio ≠ 0 by linarith)),
      ite_eq_left rfl]
    rfl
  · have e : (((2 : ℤ) : ℂ) + ((-2 : ℤ) : ℂ) * Real.goldenRatio) / 2 =
        ((1 - Real.goldenRatio : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, ite_eq_right (by exact_mod_cast (show 1 - Real.goldenRatio ≠ 3 by linarith)),
      ite_eq_right (by exact_mod_cast (show 1 - Real.goldenRatio ≠ -1 by linarith)),
      ite_eq_right (by exact_mod_cast (show 1 - Real.goldenRatio ≠ 0 by linarith)),
      ite_eq_right (by exact_mod_cast (show 1 - Real.goldenRatio ≠ Real.goldenRatio by linarith))]
    rfl

theorem a5Char_icoElt (ρ : A5Block) (k : Fin 60) :
    a5Char ρ (icoElt k) = ZOP.toComplex (a5TabZ ρ (a5ClassZ (trA5 k))) := by
  rw [a5Char, a5ClassOf_icoElt, a5CharTable_eq]


/-! ### Sums over the icosahedral group -/

theorem icoEltN_val (k : Fin 60) : icoEltN k = icoElt k := by
  simp [icoEltN, Nat.mod_eq_of_lt k.2]

theorem groupAvg_icoGroup (f : icoGroup → ℂ) :
    groupAvg icoGroup f = (60 : ℂ)⁻¹ * ∑ n ∈ Finset.range 60, f (icoEltN n) := by
  rw [groupAvg, card_icoGroup, finsum_icoGroup,
    ← Fin.sum_univ_eq_sum_range (fun n => f (icoEltN n))]
  simp only [icoEltN_val]
  norm_num

theorem icoEltN_eq (n : ℕ) (hn : n < 60) : icoEltN n = icoElt ⟨n, hn⟩ := by
  simp [icoEltN, Nat.mod_eq_of_lt hn]

/-- The class of rotation `n`, exactly. -/
def clsA5 (n : ℕ) : A5Class := a5ClassZ (trA5 n)

/-- The square of the doubled trace is four times the sum of the columns `1`, `3` and `5`,
and the doubled trace is twice the column `3`, at each of the sixty rotations. -/
theorem a5_columns : allBelow (fun n =>
    decide (trA5 n * trA5 n = ⟨4, 0, 0, 0⟩ *
      (a5TabZ .one (clsA5 n) + a5TabZ .three (clsA5 n) + a5TabZ .five (clsA5 n))) &&
    decide (trA5 n = ⟨2, 0, 0, 0⟩ * a5TabZ .three (clsA5 n))) 60 = true := by
  decide +kernel

/-- `Σ (2χ)⁴ = 2880` over the sixty rotations. -/
theorem a5_fourth : zsum (fun n => trA5 n ^ 4) 60 = ⟨2880, 0, 0, 0⟩ := by
  decide +kernel

/-- The columns `1`, `3` and `5` of the character table are orthonormal. -/
theorem a5_orthonormal : ∀ ρ ∈ [A5Block.one, .three, .five], ∀ σ ∈ [A5Block.one, .three, .five],
    zsum (fun n => a5TabZ ρ (clsA5 n) * ZOP.conj (a5TabZ σ (clsA5 n))) 60 =
      if ρ = σ then ⟨60, 0, 0, 0⟩ else ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem toComplex_four (x : ZOP) : ZOP.toComplex (⟨4, 0, 0, 0⟩ * x) = 4 * ZOP.toComplex x := by
  rw [ZOP.toComplex_mul]
  simp [ZOP.toComplex]

theorem toComplex_two (x : ZOP) : ZOP.toComplex (⟨2, 0, 0, 0⟩ * x) = 2 * ZOP.toComplex x := by
  rw [ZOP.toComplex_mul]
  simp [ZOP.toComplex]

theorem a5_sq (g : icoGroup) :
    colourChar icoGroup g ^ 2 = a5Char .one g + a5Char .three g + a5Char .five g := by
  obtain ⟨k, rfl⟩ := icoElt_surjective g
  have h := allBelow_at a5_columns k.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := congrArg ZOP.toComplex h.1
  rw [ZOP.toComplex_mul, toComplex_four, ZOP.toComplex_add, ZOP.toComplex_add] at h1
  rw [char_icoElt, a5Char_icoElt, a5Char_icoElt, a5Char_icoElt]
  simp only [clsA5] at h1
  linear_combination h1 / 4

theorem a5_three (g : icoGroup) : colourChar icoGroup g = a5Char .three g := by
  obtain ⟨k, rfl⟩ := icoElt_surjective g
  have h := allBelow_at a5_columns k.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := congrArg ZOP.toComplex h.2
  rw [toComplex_two] at h2
  rw [char_icoElt, a5Char_icoElt]
  simp only [clsA5] at h2
  linear_combination h2 / 2

theorem conj_colourChar_ico (g : icoGroup) :
    (starRingEnd ℂ) (colourChar icoGroup g) = colourChar icoGroup g := by
  obtain ⟨k, rfl⟩ := icoElt_surjective g
  exact conj_char_icoElt k

theorem a5_alt (g : icoGroup) : altSqChar (colourChar icoGroup) g = a5Char .three g := by
  rw [SU3.altSqChar_colourChar, conj_colourChar_ico, a5_three]

theorem a5_sym (g : icoGroup) :
    symSqChar (colourChar icoGroup) g = a5Char .one g + a5Char .five g := by
  rw [SU3.symSqChar_colourChar, conj_colourChar_ico, a5_sq, ← a5_three]
  ring

theorem a5Char_icoEltN (ρ : A5Block) (n : ℕ) (hn : n < 60) :
    a5Char ρ (icoEltN n) = ZOP.toComplex (a5TabZ ρ (clsA5 n)) := by
  rw [icoEltN_eq n hn, a5Char_icoElt]
  rfl

theorem a5_pairing (ρ σ : A5Block) (hρ : ρ ∈ [A5Block.one, .three, .five])
    (hσ : σ ∈ [A5Block.one, .three, .five]) :
    classPairing icoGroup (a5Char ρ) (a5Char σ) = if ρ = σ then 1 else 0 := by
  rw [classPairing, groupAvg_icoGroup]
  have e : ∑ n ∈ Finset.range 60, a5Char ρ (icoEltN n) * (starRingEnd ℂ) (a5Char σ (icoEltN n)) =
      ZOP.toComplex (zsum (fun n => a5TabZ ρ (clsA5 n) * ZOP.conj (a5TabZ σ (clsA5 n))) 60) := by
    rw [toComplex_zsum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [a5Char_icoEltN ρ n hn, a5Char_icoEltN σ n hn, ZOP.toComplex_mul, ZOP.toComplex_conj]
  rw [e, a5_orthonormal ρ hρ σ hσ]
  split_ifs <;> simp [ZOP.toComplex]

theorem a5_avg_fourth : groupAvg icoGroup (fun g => colourChar icoGroup g ^ 4) = 3 := by
  rw [groupAvg_icoGroup]
  have e : ∑ n ∈ Finset.range 60, colourChar icoGroup (icoEltN n) ^ 4 =
      ZOP.toComplex (zsum (fun n => trA5 n ^ 4) 60) / 16 := by
    rw [toComplex_zsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [icoEltN_eq n hn, char_icoElt, ZOP.toComplex_pow]
    ring
  rw [e, a5_fourth]
  simp [ZOP.toComplex]
  norm_num

/-! ### `C₃ × A₅` -/

theorem card_C3A5 : Nat.card C3A5 = 180 := by
  rw [Nat.card_prod, card_icoGroup, Nat.card_eq_fintype_card]
  rfl

theorem char_C3A5 (x : C3A5) :
    C3A5.char x = Exact.omega ^ (Multiplicative.toAdd x.1).val * colourChar icoGroup x.2 := by
  simp [C3A5.char, C3A5.triplet, colourChar, Matrix.trace_smul]

theorem normSq_char_C3A5 (x : C3A5) :
    C3A5.char x * (starRingEnd ℂ) (C3A5.char x) = colourChar icoGroup x.2 ^ 2 := by
  rw [char_C3A5, map_mul, conj_colourChar_ico]
  have h : Exact.omega ^ (Multiplicative.toAdd x.1).val *
      (starRingEnd ℂ) (Exact.omega ^ (Multiplicative.toAdd x.1).val) = 1 := by
    rw [map_pow, ← mul_pow, Exact.omega_mul_conj, one_pow]
  linear_combination (colourChar icoGroup x.2 ^ 2) * h

theorem groupAvg_C3A5 (f : icoGroup → ℂ) :
    groupAvg C3A5 (fun x => f x.2) = groupAvg icoGroup f := by
  rw [groupAvg, groupAvg, card_C3A5, card_icoGroup, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card (Multiplicative (ZMod 3)) = 3 from rfl, nsmul_eq_mul]
  push_cast
  ring

theorem exponent_C3A5 : Monoid.exponent C3A5 = 30 := by
  rw [Monoid.exponent_prod, Monoid.exponent_multiplicative, ZMod.exponent, exponent_icoGroup]
  rfl


theorem a5Char_one (g : icoGroup) : a5Char .one g = 1 := by
  simp [a5Char, a5CharTable]

theorem C3A5_fourth :
    groupAvg C3A5 (fun x => C3A5.char x ^ 2 * (starRingEnd ℂ) (C3A5.char x) ^ 2) = 3 := by
  have e : (fun x : C3A5 => C3A5.char x ^ 2 * (starRingEnd ℂ) (C3A5.char x) ^ 2) =
      fun x => colourChar icoGroup x.2 ^ 4 := by
    funext x
    rw [← mul_pow, normSq_char_C3A5]
    ring
  rw [e, groupAvg_C3A5 (fun g => colourChar icoGroup g ^ 4), a5_avg_fourth]

theorem C3A5_eight (x : C3A5) :
    C3A5.char x * (starRingEnd ℂ) (C3A5.char x) - 1 = a5Char .three x.2 + a5Char .five x.2 := by
  rw [normSq_char_C3A5, a5_sq, a5Char_one]
  ring

theorem C3A5_pairing (ρ σ : A5Block) (hρ : ρ ∈ [A5Block.one, .three, .five])
    (hσ : σ ∈ [A5Block.one, .three, .five]) :
    classPairing C3A5 (fun x => a5Char ρ x.2) (fun x => a5Char σ x.2) =
      if ρ = σ then 1 else 0 := by
  rw [classPairing, groupAvg_C3A5 (fun g => a5Char ρ g * (starRingEnd ℂ) (a5Char σ g))]
  exact a5_pairing ρ σ hρ hσ

end Artform.ColourGroups
