import ArtformTextbook.Ch12.GroupsIco

/-!
# The cube group

The twenty-four matrices `cubeE k` of the certificate are exactly the signed permutation
matrices of determinant one, so they enumerate the cube group. Their traces, whether they are
diagonal, their characters and their powers are computed exactly.
-/

namespace Artform.ColourGroups

open Exact Matrix

/-! ### The enumeration -/

/-- The entry `(i, j)` of the signed permutation matrix of `σ` and `s`, exactly. -/
def spE (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) (i j : Fin 3) : ZOP :=
  if j = σ i then ⟨((s i : ℤˣ) : ℤ), 0, 0, 0⟩ else ⟨0, 0, 0, 0⟩

/-- The signed permutation matrix of `σ` and `s`, exactly. -/
def spZ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) : M3Z :=
  ⟨spE σ s 0 0, spE σ s 0 1, spE σ s 0 2, spE σ s 1 0, spE σ s 1 1, spE σ s 1 2,
   spE σ s 2 0, spE σ s 2 1, spE σ s 2 2⟩

theorem toComplex_spE (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) (i j : Fin 3) :
    ZOP.toComplex (spE σ s i j) = signedPermMatrix σ s i j := by
  unfold spE signedPermMatrix
  rw [of_apply]
  split_ifs <;> simp [ZOP.toComplex]

theorem toMat_spZ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) :
    M3Z.toMat (spZ σ s) = signedPermMatrix σ s := by
  ext i j
  fin_cases i <;> fin_cases j <;> exact toComplex_spE σ s _ _

theorem cubeE_signed : ∀ k : Fin 24, ∃ σ : Equiv.Perm (Fin 3), ∃ s : Fin 3 → ℤˣ,
    spZ σ s = cubeE k := by
  decide +kernel

theorem signed_cubeE : ∀ σ : Equiv.Perm (Fin 3), ∀ s : Fin 3 → ℤˣ, M3Z.det (spZ σ s) = 1 →
    ∃ k : Fin 24, cubeE k = spZ σ s := by
  decide +kernel

theorem cubeMat_mem (k : Fin 24) : M3Z.toMat (cubeE k) ∈ specialUnitaryGroup (Fin 3) ℂ := by
  obtain ⟨hU, hD⟩ := cubeE_unitary k
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have e := congrArg M3Z.toMat hU
    rw [M3Z.toMat_mul, M3Z.toMat_star, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul] at e
    rw [star_eq_conjTranspose, e]
  · rw [M3Z.toMat_det, hD, ZOP.toComplex_one]

/-- The `k`-th rotation of the cube, as an element of the cube group. -/
noncomputable def cubeElt (k : Fin 24) : cubeGroup :=
  ⟨⟨M3Z.toMat (cubeE k), cubeMat_mem k⟩, by
    obtain ⟨σ, s, h⟩ := cubeE_signed k
    refine ⟨σ, s, ?_⟩
    change M3Z.toMat (cubeE k) = signedPermMatrix σ s
    rw [← h, toMat_spZ]⟩

theorem cubeElt_injective : Function.Injective cubeElt := by
  intro k l h
  have := congrArg (fun g : cubeGroup => ((g : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ)) h
  exact cubeE_injective k l (M3Z.toMat_injective this)

theorem cubeElt_surjective : Function.Surjective cubeElt := by
  rintro ⟨g, σ, s, hg⟩
  have hdet : M3Z.det (spZ σ s) = 1 := by
    apply ZOP.toComplex_injective
    rw [← M3Z.toMat_det, toMat_spZ, ← hg, ZOP.toComplex_one]
    exact (mem_specialUnitaryGroup_iff.mp g.2).2
  obtain ⟨k, hk⟩ := signed_cubeE σ s hdet
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  change M3Z.toMat (cubeE k) = (g : Matrix (Fin 3) (Fin 3) ℂ)
  rw [hk, toMat_spZ, hg]

/-- The twenty-four matrices, as the elements of the cube group. -/
noncomputable def cubeEquiv : Fin 24 ≃ cubeGroup :=
  Equiv.ofBijective cubeElt ⟨cubeElt_injective, cubeElt_surjective⟩

noncomputable instance : Fintype cubeGroup := Fintype.ofEquiv _ cubeEquiv

theorem card_cubeGroup : Nat.card cubeGroup = 24 := by
  rw [← Nat.card_congr cubeEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem groupAvg_cubeGroup (f : cubeGroup → ℂ) :
    groupAvg cubeGroup f = (24 : ℂ)⁻¹ * ∑ k : Fin 24, f (cubeElt k) := by
  rw [groupAvg, card_cubeGroup, ← finsum_comp_equiv cubeEquiv, finsum_eq_sum_of_fintype]
  push_cast
  rfl

/-! ### Classes and characters -/

/-- Whether an exact matrix is diagonal. -/
def isDiagZ (A : M3Z) : Bool :=
  A.e01 == 0 && A.e02 == 0 && A.e10 == 0 && A.e12 == 0 && A.e20 == 0 && A.e21 == 0

/-- The class of a rotation of the cube, read off its exact trace and whether it is diagonal. -/
def cubeClassZ (A : M3Z) : CubeClass :=
  if M3Z.trace A = ⟨3, 0, 0, 0⟩ then .identity
  else if M3Z.trace A = ⟨-1, 0, 0, 0⟩ then (if isDiagZ A then .faceHalfTurn else .edgeHalfTurn)
  else if M3Z.trace A = ⟨0, 0, 0, 0⟩ then .vertexThirdTurn
  else .faceQuarterTurn

/-- The character table of the cube group, exactly. -/
def cubeTabZ (ρ : CubeBlock) (c : CubeClass) : ZOP :=
  match ρ, c with
  | .one, _ => ⟨1, 0, 0, 0⟩
  | .sign, .identity => ⟨1, 0, 0, 0⟩
  | .sign, .edgeHalfTurn => ⟨-1, 0, 0, 0⟩
  | .sign, .faceHalfTurn => ⟨1, 0, 0, 0⟩
  | .sign, .vertexThirdTurn => ⟨1, 0, 0, 0⟩
  | .sign, .faceQuarterTurn => ⟨-1, 0, 0, 0⟩
  | .two, .identity => ⟨2, 0, 0, 0⟩
  | .two, .edgeHalfTurn => ⟨0, 0, 0, 0⟩
  | .two, .faceHalfTurn => ⟨2, 0, 0, 0⟩
  | .two, .vertexThirdTurn => ⟨-1, 0, 0, 0⟩
  | .two, .faceQuarterTurn => ⟨0, 0, 0, 0⟩
  | .threeS, .identity => ⟨3, 0, 0, 0⟩
  | .threeS, .edgeHalfTurn => ⟨1, 0, 0, 0⟩
  | .threeS, .faceHalfTurn => ⟨-1, 0, 0, 0⟩
  | .threeS, .vertexThirdTurn => ⟨0, 0, 0, 0⟩
  | .threeS, .faceQuarterTurn => ⟨-1, 0, 0, 0⟩
  | .threeR, .identity => ⟨3, 0, 0, 0⟩
  | .threeR, .edgeHalfTurn => ⟨-1, 0, 0, 0⟩
  | .threeR, .faceHalfTurn => ⟨-1, 0, 0, 0⟩
  | .threeR, .vertexThirdTurn => ⟨0, 0, 0, 0⟩
  | .threeR, .faceQuarterTurn => ⟨1, 0, 0, 0⟩

theorem cubeCharTable_eq (ρ : CubeBlock) (c : CubeClass) :
    cubeCharTable ρ c = ZOP.toComplex (cubeTabZ ρ c) := by
  cases ρ <;> cases c <;> simp [cubeCharTable, cubeTabZ, ZOP.toComplex]

theorem char_cubeElt (k : Fin 24) :
    colourChar cubeGroup (cubeElt k) = ZOP.toComplex (M3Z.trace (cubeE k)) := by
  rw [colourChar, ← M3Z.toMat_trace]
  rfl

theorem isDiag_toMat (A : M3Z) : (M3Z.toMat A).IsDiag ↔ isDiagZ A = true := by
  have h0 : ∀ x : ZOP, ZOP.toComplex x = 0 ↔ x = 0 := fun x => by
    rw [← ZOP.toComplex_zero, ZOP.toComplex_inj]
  simp only [isDiagZ, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> rw [← h0]
    · exact h (i := 0) (j := 1) (by decide)
    · exact h (i := 0) (j := 2) (by decide)
    · exact h (i := 1) (j := 0) (by decide)
    · exact h (i := 1) (j := 2) (by decide)
    · exact h (i := 2) (j := 0) (by decide)
    · exact h (i := 2) (j := 1) (by decide)
  · rintro ⟨⟨⟨⟨⟨h01, h02⟩, h10⟩, h12⟩, h20⟩, h21⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [M3Z.toMat, ZOP.toComplex_zero]

theorem cubeClassOf_cubeElt (k : Fin 24) : cubeClassOf (cubeElt k) = cubeClassZ (cubeE k) := by
  have e : ∀ (x : ZOP) (n : ℤ), ZOP.toComplex x = n ↔ x = ⟨n, 0, 0, 0⟩ := fun x n => by
    rw [show (n : ℂ) = ZOP.toComplex ⟨n, 0, 0, 0⟩ by simp [ZOP.toComplex], ZOP.toComplex_inj]
  have e3 := e (M3Z.trace (cubeE k)) 3
  have e1 := e (M3Z.trace (cubeE k)) (-1)
  have e0 := e (M3Z.trace (cubeE k)) 0
  push_cast at e3 e1 e0
  have ed : Matrix.IsDiag ((cubeElt k : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) ↔ isDiagZ (cubeE k) = true := isDiag_toMat (cubeE k)
  rw [cubeClassOf, cubeClassZ, char_cubeElt]
  simp only [e3, e1, e0]
  split_ifs <;> simp_all

theorem cubeChar_cubeElt (ρ : CubeBlock) (k : Fin 24) :
    cubeChar ρ (cubeElt k) = ZOP.toComplex (cubeTabZ ρ (cubeClassZ (cubeE k))) := by
  rw [cubeChar, cubeClassOf_cubeElt, cubeCharTable_eq]

/-! ### Exact checks on the twenty-four -/

/-- The trace, its square less itself, and the columns `1`, `2`, `3_s`. -/
theorem cube_sym : ∀ k : Fin 24,
    M3Z.trace (cubeE k) * M3Z.trace (cubeE k) - M3Z.trace (cubeE k) =
      cubeTabZ .one (cubeClassZ (cubeE k)) + cubeTabZ .two (cubeClassZ (cubeE k)) +
        cubeTabZ .threeS (cubeClassZ (cubeE k)) ∧
    ZOP.conj (M3Z.trace (cubeE k)) = M3Z.trace (cubeE k) := by
  decide +kernel

/-- The columns `1`, `2` and `3_s` are orthonormal. -/
theorem cube_orthonormal : ∀ ρ ∈ [CubeBlock.one, .two, .threeS],
    ∀ σ ∈ [CubeBlock.one, .two, .threeS],
    ∑ k : Fin 24,
      cubeTabZ ρ (cubeClassZ (cubeE k)) * ZOP.conj (cubeTabZ σ (cubeClassZ (cubeE k))) =
      if ρ = σ then ⟨24, 0, 0, 0⟩ else ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem cube_fourth : ∑ k : Fin 24, M3Z.trace (cubeE k) ^ 4 = ⟨96, 0, 0, 0⟩ := by
  decide +kernel

/-- The twelfth power of each of the twenty-four is the identity. -/
theorem cube_pow : ∀ k : Fin 24,
    let A2 := M3Z.mul (cubeE k) (cubeE k)
    let A4 := M3Z.mul A2 A2
    M3Z.mul (M3Z.mul A4 A4) A4 = M3Z.scalar 1 := by
  decide +kernel

/-- A quarter-turn and a third-turn. -/
theorem cube_orders : M3Z.mul (cubeE 4) (cubeE 4) ≠ M3Z.scalar 1 ∧
    M3Z.mul (M3Z.mul (cubeE 4) (cubeE 4)) (M3Z.mul (cubeE 4) (cubeE 4)) = M3Z.scalar 1 ∧
    cubeE 12 ≠ M3Z.scalar 1 ∧
    M3Z.mul (M3Z.mul (cubeE 12) (cubeE 12)) (cubeE 12) = M3Z.scalar 1 := by
  decide +kernel


/-! ### The claims about the cube group -/

theorem toComplex_sum (f : Fin 24 → ZOP) :
    ZOP.toComplex (∑ k, f k) = ∑ k, ZOP.toComplex (f k) :=
  map_sum ZOP.toComplexHom f Finset.univ

theorem cube_sym_char (g : cubeGroup) :
    symSqChar (colourChar cubeGroup) g =
      cubeChar .one g + cubeChar .two g + cubeChar .threeS g := by
  obtain ⟨k, rfl⟩ := cubeElt_surjective g
  obtain ⟨h1, h2⟩ := cube_sym k
  rw [SU3.symSqChar_colourChar, char_cubeElt, cubeChar_cubeElt, cubeChar_cubeElt,
    cubeChar_cubeElt, ← ZOP.toComplex_conj, h2, ← ZOP.toComplex_add, ← ZOP.toComplex_add, ← h1,
    ZOP.toComplex_sub, ZOP.toComplex_mul, sq]

theorem cube_pairing (ρ σ : CubeBlock) (hρ : ρ ∈ [CubeBlock.one, .two, .threeS])
    (hσ : σ ∈ [CubeBlock.one, .two, .threeS]) :
    classPairing cubeGroup (cubeChar ρ) (cubeChar σ) = if ρ = σ then 1 else 0 := by
  rw [classPairing, groupAvg_cubeGroup]
  have e : ∑ k : Fin 24, cubeChar ρ (cubeElt k) * (starRingEnd ℂ) (cubeChar σ (cubeElt k)) =
      ZOP.toComplex (∑ k : Fin 24,
        cubeTabZ ρ (cubeClassZ (cubeE k)) * ZOP.conj (cubeTabZ σ (cubeClassZ (cubeE k)))) := by
    rw [toComplex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cubeChar_cubeElt, cubeChar_cubeElt, ZOP.toComplex_mul, ZOP.toComplex_conj]
  rw [e, cube_orthonormal ρ hρ σ hσ]
  split_ifs <;> simp [ZOP.toComplex]

theorem cube_avg_fourth : groupAvg cubeGroup (fun g => colourChar cubeGroup g ^ 4) = 4 := by
  rw [groupAvg_cubeGroup]
  have e : ∑ k : Fin 24, colourChar cubeGroup (cubeElt k) ^ 4 =
      ZOP.toComplex (∑ k : Fin 24, M3Z.trace (cubeE k) ^ 4) := by
    rw [toComplex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [char_cubeElt, ZOP.toComplex_pow]
  rw [e, cube_fourth]
  simp [ZOP.toComplex]
  norm_num

theorem exponent_cubeGroup : Monoid.exponent cubeGroup = 12 := by
  have hpow : ∀ k : Fin 24, cubeElt k ^ 12 = 1 := by
    intro k
    have h := cube_pow k
    simp only at h
    apply Subtype.ext
    apply Subtype.ext
    have e := congrArg M3Z.toMat h
    simp only [M3Z.toMat_mul, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul] at e
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, OneMemClass.coe_one]
    rw [show (12 : ℕ) = 4 + 4 + 4 by norm_num, pow_add, pow_add,
      show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    change M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k) * (M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k)) *
      (M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k) * (M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k))) *
      (M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k) * (M3Z.toMat (cubeE k) * M3Z.toMat (cubeE k))) = 1
    exact e
  obtain ⟨h4a, h4b, h3a, h3b⟩ := cube_orders
  have o4 : orderOf (cubeElt 4) = 4 := by
    have hq : orderOf (cubeElt 4) = 2 ^ (1 + 1) := by
      apply orderOf_eq_prime_pow (p := 2)
      · intro h
        apply h4a
        apply M3Z.toMat_injective
        have := congrArg (fun g : cubeGroup => ((g : specialUnitaryGroup (Fin 3) ℂ) :
          Matrix (Fin 3) (Fin 3) ℂ)) h
        simp only [pow_one, pow_two, Subgroup.coe_mul, Submonoid.coe_mul, Subgroup.coe_one,
          OneMemClass.coe_one] at this
        rw [M3Z.toMat_mul, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul]
        exact this
      · apply Subtype.ext
        apply Subtype.ext
        have e := congrArg M3Z.toMat h4b
        simp only [M3Z.toMat_mul, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul] at e
        simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, OneMemClass.coe_one]
        rw [show (2 : ℕ) ^ (1 + 1 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
        exact e
    rw [hq]
    norm_num
  have o3 : orderOf (cubeElt 12) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      apply Subtype.ext
      have e := congrArg M3Z.toMat h3b
      simp only [M3Z.toMat_mul, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul] at e
      simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, OneMemClass.coe_one]
      rw [pow_succ, pow_two]
      exact e
    · intro h
      apply h3a
      apply M3Z.toMat_injective
      have := congrArg (fun g : cubeGroup => ((g : specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ)) h
      simp only [Subgroup.coe_one, OneMemClass.coe_one] at this
      rw [M3Z.toMat_scalar, ZOP.toComplex_one, one_smul]
      exact this
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    obtain ⟨k, rfl⟩ := cubeElt_surjective g
    exact hpow k
  · have d4 := Monoid.order_dvd_exponent (cubeElt 4)
    have d3 := Monoid.order_dvd_exponent (cubeElt 12)
    rw [o4] at d4
    rw [o3] at d3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d4 d3

end Artform.ColourGroups
