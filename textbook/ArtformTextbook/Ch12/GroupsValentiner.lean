import ArtformTextbook.Ch12.GroupsIco

/-!
# Valentiner's group `S(1080)`

The element coded by `x = j * 360 + k * 6 + i` is the matrix `vmat x = ω^j R_k c_i`. The
exact identities the kernel checked for the generators, carried along the trees of words,
give the products `c_i R_k` and `c_d c_i`, and with them `vmat (mulC x y) = vmat x * vmat y`.
The matrices `cᵀ c` tell the cosets apart, so that the 1080 codes give 1080 different matrices;
they form a group, which contains `C₃ × A₅` and `F`, and every one of them is a product of
those: Valentiner's group, as `valentiner` defines it, is exactly these 1080 matrices.
-/

namespace Artform.ColourGroups

open Exact Icosahedron Matrix

/-! ### The matrices of the codes -/

/-- Rotation `k` (modulo sixty) as a complex matrix. -/
noncomputable def rotN (k : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  rotC ⟨k % 60, Nat.mod_lt _ (by norm_num)⟩

/-- Half of an exact matrix, read in `ℂ`. -/
noncomputable def half (A : M3Z) : Matrix (Fin 3) (Fin 3) ℂ := (2 : ℂ)⁻¹ • M3Z.toMat A

/-- The coset representative `c_i` (`i` modulo six). -/
noncomputable def cosC (i : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := half (cosetAt i)

/-- The matrix of a code: `ω^j R_k c_i`. -/
noncomputable def vmat (x : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Exact.omega ^ jOf x • (rotN (kOf x) * cosC (iOf x))

theorem rotN_eq (k : ℕ) (hk : k < 60) : rotN k = half (gAt k) := by
  have h := gAt_eq ⟨k, hk⟩
  simp only [rotN, Nat.mod_eq_of_lt hk, rotC, R, half]
  rw [h, M3Z.map_toRealHalf]

theorem kOf_lt (x : ℕ) : kOf x < 60 := Nat.mod_lt _ (by norm_num)

theorem iOf_lt (x : ℕ) : iOf x < 6 := Nat.mod_lt _ (by norm_num)

theorem rotN_mul (k l : ℕ) (hk : k < 60) (hl : l < 60) :
    rotN (a5At k l) = rotN k * rotN l := by
  have h := rotC_a5Mul ⟨k, hk⟩ ⟨l, hl⟩
  simp only [rotN, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt (a5At_lt' k l hk hl)]
  exact h

theorem rotN_one : rotN 1 = 1 := by
  simp only [rotN]
  exact rotC_one

theorem half_mul_half (A B : M3Z) : half A * half B = (4 : ℂ)⁻¹ • M3Z.toMat (M3Z.mul A B) := by
  rw [half, half, M3Z.toMat_mul, smul_mul_smul_comm]
  norm_num

/-- An exact identity `A B = s (C D)` gives `(A/2)(B/2) = s (C/2)(D/2)`. -/
theorem half_identity {A B C D : M3Z} {s : ZOP} (h : M3Z.mul A B = M3Z.smul s (M3Z.mul C D)) :
    half A * half B = ZOP.toComplex s • (half C * half D) := by
  rw [half_mul_half, half_mul_half, h, M3Z.toMat_smul, smul_comm]

theorem toComplex_omegaZ (j : ℕ) : ZOP.toComplex (omegaZ j) = Exact.omega ^ j := by
  rw [omegaZ, ZOP.toComplex_omegaPow, Exact.omega_pow_mod]

theorem jOf_mkC (j k i : ℕ) (hk : k < 60) (hi : i < 6) : jOf (mkC j k i) = j := by
  simp only [jOf, mkC]
  omega

theorem kOf_mkC (j k i : ℕ) (hk : k < 60) (hi : i < 6) : kOf (mkC j k i) = k := by
  simp only [kOf, mkC]
  omega

theorem iOf_mkC (j k i : ℕ) (hi : i < 6) : iOf (mkC j k i) = i := by
  simp only [iOf, mkC]
  omega

theorem cosetAt_fin (i : Fin 6) : cosetAt i = cosetE i := by
  simp [cosetAt, Nat.mod_eq_of_lt i.2]

theorem cosC_zero : cosC 0 = 1 := by
  rw [cosC, half, show cosetAt 0 = cosetE 0 from rfl, cosetE_zero, M3Z.toMat_scalar]
  rw [smul_smul]
  simp [ZOP.toComplex, z]

/-! ### Products with the coset representatives -/

theorem a5Gen_spec (k : ℕ) (hk : k < 60) (h1 : k ≠ 1) :
    a5Par k < 60 ∧ a5Dep (a5Par k) < a5Dep k ∧ a5At (a5Gen k) (a5Par k) = k := by
  have h := allBelow_at a5Par_check hk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h h1
  · exact ⟨h.1.1, h.1.2, h.2⟩

theorem a5Gen_lt' (k : ℕ) : a5Gen k < 60 := by
  unfold a5Gen
  split_ifs
  · exact a5Gen_lt.1
  · exact a5Gen_lt.2

theorem gen_mat (i : ℕ) (hi : i < 6) (g : ℕ) (hg : g = a5GenA ∨ g = a5GenB) :
    cosC i * rotN g = Exact.omega ^ jOf (cRAt i g) •
      (rotN (kOf (cRAt i g)) * cosC (iOf (cRAt i g))) := by
  have hg60 : g < 60 := by
    rcases hg with rfl | rfl
    · exact a5Gen_lt.1
    · exact a5Gen_lt.2
  have h := gen_spec ⟨i, hi⟩ g (by rcases hg with rfl | rfl <;> simp)
  rw [cosC, rotN_eq g hg60, rotN_eq _ (kOf_lt _), cosC, ← toComplex_omegaZ]
  rw [show cosetAt i = cosetE ⟨i, hi⟩ from cosetAt_fin ⟨i, hi⟩]
  exact half_identity h

/-- `c_i R_k = ω^a R_b c_d` for `(a, b, d)` the code `cRAt i k`. -/
theorem cR_mat (k : ℕ) (hk : k < 60) : ∀ i < 6, cosC i * rotN k =
    Exact.omega ^ jOf (cRAt i k) • (rotN (kOf (cRAt i k)) * cosC (iOf (cRAt i k))) := by
  induction h : a5Dep k using Nat.strong_induction_on generalizing k with
  | _ n ih =>
  intro i hi
  have hc := allBelow_at (allBelow_at cR_check hi) hk
  by_cases h1 : k = 1
  · subst h1
    simp only [ite_true, beq_iff_eq] at hc
    rw [hc, jOf_mkC 0 1 i (by norm_num) hi, kOf_mkC 0 1 i (by norm_num) hi, iOf_mkC 0 1 i hi,
      pow_zero, one_smul, rotN_one, Matrix.mul_one, Matrix.one_mul]
  · simp only [h1, ite_false, beq_iff_eq] at hc
    obtain ⟨hp, hd, hk'⟩ := a5Gen_spec k hk h1
    set g := a5Gen k
    set p := a5Par k
    have hg : g = a5GenA ∨ g = a5GenB := by
      simp only [g, a5Gen]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    set r := cRAt i g
    set s := cRAt (iOf r) p
    have IH := ih (a5Dep p) (h ▸ hd) p hp rfl (iOf r) (iOf_lt r)
    rw [hc]
    conv_lhs => rw [← hk']
    rw [rotN_mul g p (a5Gen_lt' k) hp, ← Matrix.mul_assoc, gen_mat i hi g hg,
      smul_mul_assoc, Matrix.mul_assoc, IH, mul_smul_comm, smul_smul, ← Matrix.mul_assoc,
      ← rotN_mul _ _ (kOf_lt r) (kOf_lt s), comb,
      jOf_mkC _ _ _ (a5At_lt' _ _ (kOf_lt r) (kOf_lt s)) (iOf_lt s),
      kOf_mkC _ _ _ (a5At_lt' _ _ (kOf_lt r) (kOf_lt s)) (iOf_lt s), iOf_mkC _ _ _ (iOf_lt s),
      Exact.omega_pow_mod, pow_add]


/-- The generators of the tree of representatives as matrices: `F = c_1`, and the rotations
`a5GenA`, `a5GenB`. -/
noncomputable def genM (g : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  if g = 0 then cosC 1 else rotN (genRot g)

theorem parG_lt (i : ℕ) : parG i < 3 := (cosetParent ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩).2.2

theorem genRot_cases (g : ℕ) : genRot g = a5GenA ∨ genRot g = a5GenB := by
  unfold genRot
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem genRot_lt (g : ℕ) : genRot g < 60 := by
  rcases genRot_cases g with h | h <;> rw [h]
  · exact a5Gen_lt.1
  · exact a5Gen_lt.2

theorem cosC_parent (i : ℕ) (hi : i < 6) (hi0 : i ≠ 0) :
    parC i < i ∧ cosC i = cosC (parC i) * genM (parG i) := by
  have h := cosetParent_spec ⟨i, hi⟩
  rcases h with h | ⟨hlt, h⟩
  · exact absurd (congrArg Fin.val h) hi0
  have hp : parC i = (cosetParent ⟨i, hi⟩).1 := by simp [parC, Nat.mod_eq_of_lt hi]
  have hg : parG i = (cosetParent ⟨i, hi⟩).2 := by simp [parG, Nat.mod_eq_of_lt hi]
  refine ⟨by rw [hp]; exact hlt, ?_⟩
  have e := congrArg M3Z.toMat h
  rw [M3Z.toMat_smul, M3Z.toMat_mul] at e
  have hG : genM (parG i) = half (genZ (cosetParent ⟨i, hi⟩).2) := by
    rw [hg, genM]
    generalize (cosetParent ⟨i, hi⟩).2 = g
    fin_cases g
    · simp [genZ, cosC, ← cosetE_one]
      rfl
    · simp [genZ, genRot, rotN_eq _ a5Gen_lt.1]
    · simp [genZ, genRot, rotN_eq _ a5Gen_lt.2]
  rw [hG, cosC, cosC, hp, half, half, half, smul_mul_smul_comm,
    show cosetAt i = cosetE ⟨i, hi⟩ from cosetAt_fin ⟨i, hi⟩,
    show cosetAt ((cosetParent ⟨i, hi⟩).1 : ℕ) = cosetE (cosetParent ⟨i, hi⟩).1 from
      cosetAt_fin _, ← e, smul_smul]
  simp [ZOP.toComplex, z]

theorem cc1_mat (d : ℕ) (hd : d < 6) : cosC d * cosC 1 =
    Exact.omega ^ jOf (ccAt d 1) • (rotN (kOf (ccAt d 1)) * cosC (iOf (ccAt d 1))) := by
  have h := cc1_spec ⟨d, hd⟩
  rw [cosC, cosC, rotN_eq _ (kOf_lt _), cosC, ← toComplex_omegaZ,
    show cosetAt d = cosetE ⟨d, hd⟩ from cosetAt_fin ⟨d, hd⟩,
    show cosetAt 1 = cosetE 1 from rfl]
  exact half_identity h

theorem nextC_mat (m : ℕ) (hm : m < 6) (g : ℕ) : cosC m * genM g =
    Exact.omega ^ jOf (nextC m g) • (rotN (kOf (nextC m g)) * cosC (iOf (nextC m g))) := by
  unfold genM nextC
  split_ifs
  · exact cc1_mat m hm
  · exact cR_mat _ (genRot_lt g) m hm

/-- `c_d c_i = ω^a R_b c_m` for `(a, b, m)` the code `ccAt d i`. -/
theorem cc_mat (i : ℕ) (hi : i < 6) : ∀ d < 6, cosC d * cosC i =
    Exact.omega ^ jOf (ccAt d i) • (rotN (kOf (ccAt d i)) * cosC (iOf (ccAt d i))) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro d hd
  have hc := allBelow_at (allBelow_at cc_check hd) hi
  by_cases h0 : i = 0
  · subst h0
    simp only [ite_true, beq_iff_eq] at hc
    rw [hc, jOf_mkC 0 1 d (by norm_num) hd, kOf_mkC 0 1 d (by norm_num) hd, iOf_mkC 0 1 d hd,
      pow_zero, one_smul, rotN_one, Matrix.one_mul, cosC_zero, Matrix.mul_one]
  · simp only [h0, ite_false, beq_iff_eq] at hc
    obtain ⟨hp, hcp⟩ := cosC_parent i hi h0
    set p := parC i
    set g := parG i
    set r := ccAt d p
    set s := nextC (iOf r) g
    have IH := ih p hp (by omega) d hd
    rw [hc, hcp, ← Matrix.mul_assoc, IH, smul_mul_assoc, Matrix.mul_assoc,
      nextC_mat _ (iOf_lt r) g, mul_smul_comm, smul_smul, ← Matrix.mul_assoc,
      ← rotN_mul _ _ (kOf_lt r) (kOf_lt s), comb,
      jOf_mkC _ _ _ (a5At_lt' _ _ (kOf_lt r) (kOf_lt s)) (iOf_lt s),
      kOf_mkC _ _ _ (a5At_lt' _ _ (kOf_lt r) (kOf_lt s)) (iOf_lt s), iOf_mkC _ _ _ (iOf_lt s),
      Exact.omega_pow_mod, pow_add]

/-! ### The product of codes -/

theorem a5At_kOf (x y : ℕ) : a5At (kOf x) (kOf y) < 60 := a5At_lt' _ _ (kOf_lt x) (kOf_lt y)

theorem mulC_eq (x y : ℕ) : mulC x y = mkC ((jOf x + jOf y + jOf (cRAt (iOf x) (kOf y)) +
    jOf (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y))) % 3)
    (a5At (a5At (kOf x) (kOf (cRAt (iOf x) (kOf y))))
      (kOf (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y))))
    (iOf (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y))) := rfl

theorem mulC_lt (x y : ℕ) : mulC x y < 1080 := by
  rw [mulC_eq]
  have h1 := a5At_lt' _ _ (a5At_kOf x (cRAt (iOf x) (kOf y)))
    (kOf_lt (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y)))
  have h2 := iOf_lt (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y))
  have h3 := Nat.mod_lt (jOf x + jOf y + jOf (cRAt (iOf x) (kOf y)) +
    jOf (ccAt (iOf (cRAt (iOf x) (kOf y))) (iOf y))) (show 3 > 0 by norm_num)
  simp only [mkC]
  omega

/-- The matrix of a product of codes is the product of their matrices. -/
theorem vmat_mul (x y : ℕ) : vmat (mulC x y) = vmat x * vmat y := by
  set r := cRAt (iOf x) (kOf y)
  set s := ccAt (iOf r) (iOf y)
  have hk1 := a5At_kOf x r
  have hk := a5At_lt' _ _ hk1 (kOf_lt s)
  rw [mulC_eq, vmat, jOf_mkC _ _ _ hk (iOf_lt s), kOf_mkC _ _ _ hk (iOf_lt s),
    iOf_mkC _ _ _ (iOf_lt s), Exact.omega_pow_mod, rotN_mul _ _ hk1 (kOf_lt s),
    rotN_mul _ _ (kOf_lt x) (kOf_lt r), vmat, vmat, smul_mul_smul_comm]
  rw [show rotN (kOf x) * cosC (iOf x) * (rotN (kOf y) * cosC (iOf y)) =
      rotN (kOf x) * (cosC (iOf x) * rotN (kOf y)) * cosC (iOf y) by
    simp only [Matrix.mul_assoc]]
  rw [cR_mat _ (kOf_lt y) _ (iOf_lt x), mul_smul_comm, smul_mul_assoc,
    show rotN (kOf x) * (rotN (kOf r) * cosC (iOf r)) * cosC (iOf y) =
      rotN (kOf x) * rotN (kOf r) * (cosC (iOf r) * cosC (iOf y)) by
    simp only [Matrix.mul_assoc],
    cc_mat _ (iOf_lt y) _ (iOf_lt r), mul_smul_comm, smul_smul, smul_smul]
  rw [show rotN (kOf x) * rotN (kOf r) * (rotN (kOf s) * cosC (iOf s)) =
      rotN (kOf x) * rotN (kOf r) * rotN (kOf s) * cosC (iOf s) by
    simp only [Matrix.mul_assoc]]
  congr 1
  rw [pow_add, pow_add, pow_add]

theorem vmat_one : vmat oneC = 1 := by
  rw [vmat, show jOf oneC = 0 from rfl, show kOf oneC = 1 from rfl, show iOf oneC = 0 from rfl,
    rotN_one, cosC_zero, pow_zero, one_smul, Matrix.mul_one]


/-! ### Unitary matrices of determinant one -/

theorem cosC_mem (i : ℕ) : cosC i ∈ specialUnitaryGroup (Fin 3) ℂ := by
  have hi : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hU, hD⟩ := cosetE_unitary ⟨i % 6, hi⟩
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have e := congrArg M3Z.toMat hU
    rw [M3Z.toMat_mul, M3Z.toMat_star, M3Z.toMat_scalar] at e
    rw [cosC, half, cosetAt, star_eq_conjTranspose, conjTranspose_smul, smul_mul_smul_comm, e,
      smul_smul]
    simp [ZOP.toComplex, z]
    norm_num
  · have e := congrArg ZOP.toComplex hD
    rw [← M3Z.toMat_det] at e
    rw [cosC, half, cosetAt, det_smul, e]
    simp [ZOP.toComplex, z]
    norm_num

theorem rotN_mem (k : ℕ) : rotN k ∈ specialUnitaryGroup (Fin 3) ℂ := rotC_mem _

theorem vmat_mem (x : ℕ) : vmat x ∈ specialUnitaryGroup (Fin 3) ℂ :=
  omega_pow_smul_mem _ (Submonoid.mul_mem _ (rotN_mem _) (cosC_mem _))

/-- The element of `SU(3)` with code `x`. -/
noncomputable def vSU (x : ℕ) : specialUnitaryGroup (Fin 3) ℂ := ⟨vmat x, vmat_mem x⟩

theorem vSU_mul (x y : ℕ) : vSU (mulC x y) = vSU x * vSU y := Subtype.ext (vmat_mul x y)

theorem vSU_one : vSU oneC = 1 := Subtype.ext vmat_one

theorem vSU_inv (x : ℕ) (hx : x < 1080) : vSU (invAt x) = (vSU x)⁻¹ := by
  have h := allBelow_at inv_check hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have e : vSU x * vSU (invAt x) = 1 := by rw [← vSU_mul, h.2, vSU_one]
  exact (eq_inv_of_mul_eq_one_right e)

/-! ### The cosets told apart -/

theorem rotN_transpose_mul (k : ℕ) : (rotN k)ᵀ * rotN k = 1 := by
  have h := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (mem_specialOrthogonalGroup_iff.mp (R_mem_SO ⟨k % 60, Nat.mod_lt _ (by norm_num)⟩)).1
  rw [rotN, rotC, ← transpose_map, ← map_ofReal_mul, h]
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

theorem vmat_transpose_mul (x : ℕ) :
    (vmat x)ᵀ * vmat x = (Exact.omega ^ (2 * jOf x) * (4 : ℂ)⁻¹) •
      M3Z.toMat (qZ ⟨iOf x, iOf_lt x⟩) := by
  rw [vmat, transpose_smul, smul_mul_smul_comm, transpose_mul,
    show (cosC (iOf x))ᵀ * (rotN (kOf x))ᵀ * (rotN (kOf x) * cosC (iOf x)) =
      (cosC (iOf x))ᵀ * ((rotN (kOf x))ᵀ * rotN (kOf x)) * cosC (iOf x) by
      simp only [Matrix.mul_assoc],
    rotN_transpose_mul, Matrix.mul_one, cosC, half, transpose_smul, smul_mul_smul_comm,
    ← M3Z.toMat_transpose, ← M3Z.toMat_mul, smul_smul, qZ,
    show cosetAt (iOf x) = cosetE ⟨iOf x, iOf_lt x⟩ from cosetAt_fin ⟨iOf x, iOf_lt x⟩]
  congr 1
  rw [show 2 * jOf x = jOf x + jOf x by ring, pow_add]
  norm_num

theorem toComplex_omegaPow_two_mul (m : Fin 3) :
    ZOP.toComplex (ZOP.omegaPow (2 * m)) = Exact.omega ^ (2 * (m : ℕ)) := by
  rw [ZOP.toComplex_omegaPow, ← Exact.omega_pow_mod (2 * (m : ℕ)), Fin.val_mul]
  rfl

theorem code_eq (x : ℕ) : mkC (jOf x) (kOf x) (iOf x) = x := by
  simp only [mkC, jOf, kOf, iOf]
  omega

theorem vmat_injective (x y : ℕ) (hx : x < 1080) (hy : y < 1080) (h : vmat x = vmat y) :
    x = y := by
  have hjx : jOf x < 3 := by simp only [jOf]; omega
  have hjy : jOf y < 3 := by simp only [jOf]; omega
  have hq := congrArg (fun M => Mᵀ * M) h
  simp only [vmat_transpose_mul] at hq
  have hq' : M3Z.toMat (M3Z.smul (ZOP.omegaPow (2 * ⟨jOf x, hjx⟩)) (qZ ⟨iOf x, iOf_lt x⟩)) =
      M3Z.toMat (M3Z.smul (ZOP.omegaPow (2 * ⟨jOf y, hjy⟩)) (qZ ⟨iOf y, iOf_lt y⟩)) := by
    rw [M3Z.toMat_smul, M3Z.toMat_smul, toComplex_omegaPow_two_mul,
      toComplex_omegaPow_two_mul]
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    have := congrArg (fun M => (4 : ℂ) • M) hq
    simp only [smul_smul] at this
    rw [show (4 : ℂ) * (Exact.omega ^ (2 * jOf x) * 4⁻¹) = Exact.omega ^ (2 * jOf x) by
        field_simp,
      show (4 : ℂ) * (Exact.omega ^ (2 * jOf y) * 4⁻¹) = Exact.omega ^ (2 * jOf y) by
        field_simp] at this
    exact this
  obtain ⟨hj, hi⟩ := qZ_distinct _ _ _ _ (M3Z.toMat_injective hq')
  have hj' : jOf x = jOf y := congrArg Fin.val hj
  have hi' : iOf x = iOf y := congrArg Fin.val hi
  have hk' : kOf x = kOf y := by
    have h2 : rotN (kOf x) * cosC (iOf y) = rotN (kOf y) * cosC (iOf y) := by
      have := congrArg (fun M => (Exact.omega ^ jOf x)⁻¹ • M) h
      simp only [vmat, smul_smul, hj', hi'] at this
      rwa [inv_mul_cancel₀ (pow_ne_zero _ Exact.omega_ne_zero), one_smul, one_smul] at this
    have hc := (mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp (cosC_mem (iOf y))).1)
    have h3 : rotN (kOf x) = rotN (kOf y) := by
      have := congrArg (fun M => M * star (cosC (iOf y))) h2
      simpa only [Matrix.mul_assoc, hc, Matrix.mul_one] using this
    have := rotC_injective h3
    simpa [Nat.mod_eq_of_lt (kOf_lt x), Nat.mod_eq_of_lt (kOf_lt y)] using congrArg Fin.val this
  rw [← code_eq x, ← code_eq y, hj', hk', hi']


/-! ### Valentiner's group is the 1080 codes -/

theorem invAt_lt (x : ℕ) (hx : x < 1080) : invAt x < 1080 := by
  have h := allBelow_at inv_check hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The 1080 codes, as a subgroup of `SU(3)`. -/
noncomputable def codeGroup : Subgroup (specialUnitaryGroup (Fin 3) ℂ) where
  carrier := {g | ∃ x < 1080, vSU x = g}
  mul_mem' := by
    rintro _ _ ⟨x, -, rfl⟩ ⟨y, -, rfl⟩
    exact ⟨mulC x y, mulC_lt x y, vSU_mul x y⟩
  one_mem' := ⟨oneC, by norm_num [oneC], vSU_one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨invAt x, invAt_lt x hx, vSU_inv x hx⟩

theorem rotN_val (k : Fin 60) : rotN k = rotC k := by
  simp [rotN, Nat.mod_eq_of_lt k.2]

theorem triplet_eq (j : Multiplicative (ZMod 3)) (k : Fin 60) :
    C3A5.triplet (j, icoElt k) = vSU (mkC (Multiplicative.toAdd j).val k 0) := by
  have hj : (Multiplicative.toAdd j).val < 3 := ZMod.val_lt _
  apply Subtype.ext
  simp only [C3A5.triplet, MonoidHom.coe_mk, OneHom.coe_mk, vSU, vmat,
    jOf_mkC _ _ _ k.2 (by norm_num : 0 < 6), kOf_mkC _ _ _ k.2 (by norm_num : 0 < 6),
    iOf_mkC _ _ _ (by norm_num : 0 < 6), cosC_zero, Matrix.mul_one, rotN_val]
  rfl

theorem cosC_one_eq : cosC 1 = (valentinerF : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [cosC, show cosetAt 1 = cosetE 1 from rfl, cosetE_one, half]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3Z.toMat, fZ, z, valentinerF, ZOP.toComplex, Exact.omega_sq]
  ring

theorem F_eq : valentinerF = vSU genFC := by
  apply Subtype.ext
  change (valentinerF : Matrix (Fin 3) (Fin 3) ℂ) = vmat genFC
  rw [vmat, show jOf genFC = 0 from rfl, show kOf genFC = 1 from rfl,
    show iOf genFC = 1 from rfl, pow_zero, one_smul, rotN_one, Matrix.one_mul, cosC_one_eq]

theorem valentiner_le : valentiner ≤ codeGroup := by
  rw [valentiner, Subgroup.closure_le]
  rintro g (⟨⟨j, h⟩, rfl⟩ | hF)
  · obtain ⟨k, rfl⟩ := icoElt_surjective h
    rw [triplet_eq]
    refine ⟨_, ?_, rfl⟩
    have hj : (Multiplicative.toAdd j).val < 3 := ZMod.val_lt _
    simp only [mkC]
    omega
  · rw [Set.mem_singleton_iff] at hF
    rw [hF, F_eq]
    exact ⟨genFC, by decide, rfl⟩

theorem rot_mem_valentiner (k : Fin 60) :
    (⟨rotC k, rotC_mem k⟩ : specialUnitaryGroup (Fin 3) ℂ) ∈ valentiner := by
  apply Subgroup.subset_closure
  left
  refine ⟨(1, icoElt k), ?_⟩
  apply Subtype.ext
  simp [C3A5.triplet, icoElt]

/-- The generators of the tree of representatives, as elements of `SU(3)`. -/
noncomputable def genSU (g : ℕ) : specialUnitaryGroup (Fin 3) ℂ :=
  if g = 0 then valentinerF else ⟨rotC ⟨genRot g, genRot_lt g⟩, rotC_mem _⟩

theorem genSU_val (g : ℕ) : (genSU g : Matrix (Fin 3) (Fin 3) ℂ) = genM g := by
  unfold genSU genM
  split_ifs
  · exact cosC_one_eq.symm
  · exact (rotN_val ⟨genRot g, genRot_lt g⟩).symm

theorem genSU_mem (g : ℕ) : genSU g ∈ valentiner := by
  unfold genSU
  split_ifs
  · exact Subgroup.subset_closure (Or.inr rfl)
  · exact rot_mem_valentiner _

/-- The coset representative `c_i` as an element of `SU(3)`. -/
noncomputable def cosSU (i : ℕ) : specialUnitaryGroup (Fin 3) ℂ := ⟨cosC i, cosC_mem i⟩

theorem cos_mem_valentiner (i : ℕ) (hi : i < 6) : cosSU i ∈ valentiner := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  by_cases h0 : i = 0
  · subst h0
    have : cosSU 0 = 1 := Subtype.ext cosC_zero
    rw [this]
    exact Subgroup.one_mem _
  · obtain ⟨hp, hc⟩ := cosC_parent i hi h0
    have e : cosSU i = cosSU (parC i) * genSU (parG i) := by
      apply Subtype.ext
      rw [Submonoid.coe_mul, genSU_val]
      exact hc
    rw [e]
    exact Subgroup.mul_mem _ (ih _ hp (by omega)) (genSU_mem _)

theorem vSU_mem_valentiner (x : ℕ) : vSU x ∈ valentiner := by
  have e : vSU x = C3A5.triplet (Multiplicative.ofAdd (jOf x : ZMod 3),
      icoElt ⟨kOf x, kOf_lt x⟩) * cosSU (iOf x) := by
    apply Subtype.ext
    have hk : rotN (kOf x) = rotC ⟨kOf x, kOf_lt x⟩ := by
      simp [rotN, Nat.mod_eq_of_lt (kOf_lt x)]
    simp only [vSU, vmat, C3A5.triplet, MonoidHom.coe_mk, OneHom.coe_mk, Submonoid.coe_mul,
      toAdd_ofAdd, ZMod.val_natCast, Exact.omega_pow_mod, icoElt, smul_mul_assoc, hk, cosSU]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (cos_mem_valentiner (iOf x) (iOf_lt x))

theorem valentiner_eq : valentiner = codeGroup := by
  refine le_antisymm valentiner_le ?_
  rintro _ ⟨x, -, rfl⟩
  exact vSU_mem_valentiner x

/-- The element of Valentiner's group with code `x < 1080`. -/
noncomputable def vElt (x : Fin 1080) : valentiner := ⟨vSU x, vSU_mem_valentiner x⟩

theorem vElt_injective : Function.Injective vElt := by
  intro x y h
  have := congrArg (fun g : valentiner => ((g : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ)) h
  exact Fin.ext (vmat_injective x y x.2 y.2 this)

theorem vElt_surjective : Function.Surjective vElt := by
  rintro ⟨g, hg⟩
  rw [valentiner_eq] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The 1080 codes, as the elements of Valentiner's group. -/
noncomputable def vEquiv : Fin 1080 ≃ valentiner :=
  Equiv.ofBijective vElt ⟨vElt_injective, vElt_surjective⟩

noncomputable instance : Fintype valentiner := Fintype.ofEquiv _ vEquiv

theorem card_valentiner : Nat.card valentiner = 1080 := by
  rw [← Nat.card_congr vEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem finsum_valentiner (f : valentiner → ℂ) : ∑ᶠ g, f g = ∑ x : Fin 1080, f (vElt x) := by
  rw [← finsum_comp_equiv vEquiv, finsum_eq_sum_of_fintype]
  rfl

theorem vElt_mul (x y : Fin 1080) :
    vElt ⟨mulC x y, mulC_lt x y⟩ = vElt x * vElt y := Subtype.ext (vSU_mul x y)

/-- `C₃ × A₅` lies in Valentiner's group with index six. -/
theorem C3A5_index : C3A5.triplet.range ≤ valentiner ∧
    Nat.card C3A5.triplet.range * 6 = Nat.card valentiner := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  · have hinj : Function.Injective C3A5.triplet := by
      rintro ⟨j, g⟩ ⟨j', g'⟩ h
      obtain ⟨k, rfl⟩ := icoElt_surjective g
      obtain ⟨k', rfl⟩ := icoElt_surjective g'
      rw [triplet_eq, triplet_eq] at h
      have hj := ZMod.val_lt (Multiplicative.toAdd j)
      have hj' := ZMod.val_lt (Multiplicative.toAdd j')
      have h1 := vmat_injective _ _ (by simp only [mkC]; omega) (by simp only [mkC]; omega)
        (congrArg Subtype.val h)
      simp only [mkC] at h1
      have e1 : (Multiplicative.toAdd j).val = (Multiplicative.toAdd j').val := by omega
      have e2 : (k : ℕ) = k' := by omega
      rw [Prod.mk.injEq]
      exact ⟨by
        apply Multiplicative.toAdd.injective
        exact ZMod.val_injective _ e1, by rw [Fin.ext e2]⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_C3A5, card_valentiner]


/-! ### Conjugacy classes -/

/-- The element with code `n`, for any natural number `n` (taken modulo 1080). -/
noncomputable def vEltN (n : ℕ) : valentiner := vElt ⟨n % 1080, Nat.mod_lt _ (by norm_num)⟩

theorem vEltN_eq (n : ℕ) (hn : n < 1080) : vEltN n = vElt ⟨n, hn⟩ := by
  simp [vEltN, Nat.mod_eq_of_lt hn]

theorem vEltN_mul (x y : ℕ) (hx : x < 1080) (hy : y < 1080) :
    vEltN (mulC x y) = vEltN x * vEltN y := by
  rw [vEltN_eq _ (mulC_lt x y), vEltN_eq x hx, vEltN_eq y hy]
  exact Subtype.ext (vSU_mul x y)

theorem vEltN_inv (x : ℕ) (hx : x < 1080) : vEltN (invAt x) = (vEltN x)⁻¹ := by
  rw [vEltN_eq _ (invAt_lt x hx), vEltN_eq x hx]
  exact Subtype.ext (vSU_inv x hx)

/-- The code of an element of Valentiner's group. -/
noncomputable def codeOf (g : valentiner) : ℕ := (vEquiv.symm g : ℕ)

theorem codeOf_lt (g : valentiner) : codeOf g < 1080 := (vEquiv.symm g).2

theorem vEltN_codeOf (g : valentiner) : vEltN (codeOf g) = g := by
  rw [vEltN_eq _ (codeOf_lt g)]
  exact vEquiv.apply_symm_apply g

theorem codeOf_vEltN (x : ℕ) (hx : x < 1080) : codeOf (vEltN x) = x := by
  rw [vEltN_eq x hx]
  exact congrArg Fin.val (vEquiv.symm_apply_apply ⟨x, hx⟩)

/-- The row of the class table that holds the class of an element. -/
noncomputable def labG (g : valentiner) : ℕ := labAt (codeOf g)

theorem labAt_lt (x : ℕ) (hx : x < 1080) : labAt x < 17 := by
  have h := allBelow_at labA_check hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem labG_lt (g : valentiner) : labG g < 17 := labAt_lt _ (codeOf_lt g)

theorem labG_vEltN (x : ℕ) (hx : x < 1080) : labG (vEltN x) = labAt x := by
  rw [labG, codeOf_vEltN x hx]

/-- Conjugation by one of the three generators keeps the row. -/
theorem labG_conj_gen (t : ℕ) (ht : t = genAC ∨ t = genBC ∨ t = genFC) (g : valentiner) :
    labG (vEltN t * g * (vEltN t)⁻¹) = labG g := by
  have htl : t < 1080 := by
    rcases ht with rfl | rfl | rfl <;> decide
  obtain ⟨x, hx, rfl⟩ : ∃ x < 1080, vEltN x = g := ⟨codeOf g, codeOf_lt g, vEltN_codeOf g⟩
  rw [← vEltN_inv t htl, ← vEltN_mul t x htl hx, ← vEltN_mul _ _ (mulC_lt t x) (invAt_lt t htl),
    labG_vEltN _ (mulC_lt _ _), labG_vEltN x hx]
  have hA := allBelow_at labA_check hx
  have hB := allBelow_at labB_check hx
  have hF := allBelow_at labF_check hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hA hB hF
  rcases ht with rfl | rfl | rfl
  · exact hA.2
  · exact hB
  · exact hF

/-- The elements whose conjugation keeps every row. -/
noncomputable def keepLab : Subgroup valentiner where
  carrier := {h | ∀ g, labG (h * g * h⁻¹) = labG g}
  mul_mem' := by
    intro a b ha hb g
    rw [show a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ by group, ha, hb]
  one_mem' := by
    intro g
    simp
  inv_mem' := by
    intro a ha g
    have := ha (a⁻¹ * g * a⁻¹⁻¹)
    rw [show a * (a⁻¹ * g * a⁻¹⁻¹) * a⁻¹ = g by group] at this
    exact this.symm

theorem gen_mem_keepLab (t : ℕ) (ht : t = genAC ∨ t = genBC ∨ t = genFC) : vEltN t ∈ keepLab :=
  labG_conj_gen t ht

theorem central_mem_keepLab (j : ℕ) (hj : j < 3) : vEltN (mkC j 1 0) ∈ keepLab := by
  have hl : mkC j 1 0 < 1080 := by simp only [mkC]; omega
  intro g
  have hc : vEltN (mkC j 1 0) * g = g * vEltN (mkC j 1 0) := by
    rw [vEltN_eq _ hl]
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Submonoid.coe_mul, vElt, vSU, vmat,
      jOf_mkC j 1 0 (by norm_num) (by norm_num), kOf_mkC j 1 0 (by norm_num) (by norm_num),
      iOf_mkC j 1 0 (by norm_num), rotN_one, cosC_zero, Matrix.mul_one, smul_mul_assoc,
      mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  rw [hc, mul_inv_cancel_right]

theorem vEltN_mkC (j k i : ℕ) (hj : j < 3) (hk : k < 60) (hi : i < 6) :
    vEltN (mkC j k i) = vEltN (mkC j 1 0) * vEltN (mkC 0 k 0) * vEltN (mkC 0 1 i) := by
  have h1 : mkC j k i < 1080 := by simp only [mkC]; omega
  have h2 : mkC j 1 0 < 1080 := by simp only [mkC]; omega
  have h3 : mkC 0 k 0 < 1080 := by simp only [mkC]; omega
  have h4 : mkC 0 1 i < 1080 := by simp only [mkC]; omega
  rw [vEltN_eq _ h1, vEltN_eq _ h2, vEltN_eq _ h3, vEltN_eq _ h4]
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Submonoid.coe_mul, vElt, vSU, vmat,
    jOf_mkC _ _ _ hk hi, kOf_mkC _ _ _ hk hi, iOf_mkC _ _ _ hi,
    jOf_mkC j 1 0 (by norm_num) (by norm_num), kOf_mkC j 1 0 (by norm_num) (by norm_num),
    iOf_mkC j 1 0 (by norm_num), jOf_mkC 0 k 0 hk (by norm_num), kOf_mkC 0 k 0 hk (by norm_num),
    iOf_mkC 0 k 0 (by norm_num), jOf_mkC 0 1 i (by norm_num) hi, kOf_mkC 0 1 i (by norm_num) hi,
    rotN_one, cosC_zero, pow_zero, one_smul, Matrix.mul_one, Matrix.one_mul, smul_mul_assoc]

theorem rot_mem_keepLab (k : ℕ) (hk : k < 60) : vEltN (mkC 0 k 0) ∈ keepLab := by
  induction h : a5Dep k using Nat.strong_induction_on generalizing k with
  | _ n ih =>
  by_cases h1 : k = 1
  · subst h1
    have : vEltN (mkC 0 1 0) = 1 := by
      rw [vEltN_eq _ (by decide)]
      exact Subtype.ext (Subtype.ext vmat_one)
    rw [this]
    exact keepLab.one_mem
  · obtain ⟨hp, hd, hk'⟩ := a5Gen_spec k hk h1
    have hg : mkC 0 (a5Gen k) 0 = genAC ∨ mkC 0 (a5Gen k) 0 = genBC ∨
        mkC 0 (a5Gen k) 0 = genFC := by
      unfold a5Gen
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have e : vEltN (mkC 0 k 0) = vEltN (mkC 0 (a5Gen k) 0) * vEltN (mkC 0 (a5Par k) 0) := by
      have hgl : mkC 0 (a5Gen k) 0 < 1080 := by
        have := a5Gen_lt' k; simp only [mkC]; omega
      have hpl : mkC 0 (a5Par k) 0 < 1080 := by simp only [mkC]; omega
      have hkl : mkC 0 k 0 < 1080 := by simp only [mkC]; omega
      rw [vEltN_eq _ hkl, vEltN_eq _ hgl, vEltN_eq _ hpl]
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Submonoid.coe_mul, vElt, vSU, vmat,
        jOf_mkC 0 _ 0 hk (by norm_num), kOf_mkC 0 _ 0 hk (by norm_num), iOf_mkC 0 k 0 (by norm_num),
        jOf_mkC 0 _ 0 (a5Gen_lt' k) (by norm_num), kOf_mkC 0 _ 0 (a5Gen_lt' k) (by norm_num),
        iOf_mkC 0 (a5Gen k) 0 (by norm_num), jOf_mkC 0 _ 0 hp (by norm_num),
        kOf_mkC 0 _ 0 hp (by norm_num), iOf_mkC 0 (a5Par k) 0 (by norm_num), cosC_zero,
        pow_zero, one_smul, Matrix.mul_one]
      rw [show rotN k = rotN (a5At (a5Gen k) (a5Par k)) by rw [hk'],
        rotN_mul _ _ (a5Gen_lt' k) hp]
    rw [e]
    exact keepLab.mul_mem (gen_mem_keepLab _ hg) (ih _ (h ▸ hd) _ hp rfl)

theorem cos_mem_keepLab (i : ℕ) (hi : i < 6) : vEltN (mkC 0 1 i) ∈ keepLab := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  by_cases h0 : i = 0
  · subst h0
    have : vEltN (mkC 0 1 0) = 1 := by
      rw [vEltN_eq _ (by decide)]
      exact Subtype.ext (Subtype.ext vmat_one)
    rw [this]
    exact keepLab.one_mem
  · obtain ⟨hp, hc⟩ := cosC_parent i hi h0
    have hpl : mkC 0 1 (parC i) < 1080 := by simp only [mkC]; omega
    have hil : mkC 0 1 i < 1080 := by simp only [mkC]; omega
    have hgen : ∃ t, (t = genAC ∨ t = genBC ∨ t = genFC) ∧ t < 1080 ∧
        vmat t = genM (parG i) := by
      unfold genM
      split_ifs with hg
      · refine ⟨genFC, Or.inr (Or.inr rfl), by decide, ?_⟩
        rw [vmat, show jOf genFC = 0 from rfl, show kOf genFC = 1 from rfl,
          show iOf genFC = 1 from rfl, pow_zero, one_smul, rotN_one, Matrix.one_mul]
      · refine ⟨mkC 0 (genRot (parG i)) 0, ?_, ?_, ?_⟩
        · unfold genRot
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · have := genRot_lt (parG i); simp only [mkC]; omega
        · rw [vmat, jOf_mkC 0 _ 0 (genRot_lt _) (by norm_num),
            kOf_mkC 0 _ 0 (genRot_lt _) (by norm_num), iOf_mkC 0 _ 0 (by norm_num), pow_zero,
            one_smul, cosC_zero, Matrix.mul_one]
    obtain ⟨t, ht, htl, htm⟩ := hgen
    have e : vEltN (mkC 0 1 i) = vEltN (mkC 0 1 (parC i)) * vEltN t := by
      rw [vEltN_eq _ hil, vEltN_eq _ hpl, vEltN_eq _ htl]
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Submonoid.coe_mul, vElt, vSU, htm]
      rw [vmat, vmat, jOf_mkC 0 1 i (by norm_num) hi, kOf_mkC 0 1 i (by norm_num) hi,
        iOf_mkC 0 1 i hi, jOf_mkC 0 1 _ (by norm_num) (by omega),
        kOf_mkC 0 1 _ (by norm_num) (by omega), iOf_mkC 0 1 _ (by omega), pow_zero, one_smul,
        one_smul, rotN_one, Matrix.one_mul, Matrix.one_mul, hc]
    rw [e]
    exact keepLab.mul_mem (ih _ hp (by omega)) (gen_mem_keepLab t ht)

theorem keepLab_eq_top : keepLab = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [← vEltN_codeOf g, ← code_eq (codeOf g)]
  have hx := codeOf_lt g
  have hj : jOf (codeOf g) < 3 := by simp only [jOf]; omega
  rw [vEltN_mkC _ _ _ hj (kOf_lt _) (iOf_lt _)]
  exact keepLab.mul_mem (keepLab.mul_mem (central_mem_keepLab _ hj)
    (rot_mem_keepLab _ (kOf_lt _))) (cos_mem_keepLab _ (iOf_lt _))

/-- Conjugation keeps the row of the class table. -/
theorem labG_conj (h g : valentiner) : labG (h * g * h⁻¹) = labG g := by
  have : h ∈ keepLab := by rw [keepLab_eq_top]; trivial
  exact this g

/-- Every element is conjugate to the representative of its row. -/
theorem semiconj_rep (g : valentiner) :
    SemiconjBy (vEltN (conjAt (codeOf g))) g (vEltN (repAt (labG g))) := by
  have hx := codeOf_lt g
  have h := allBelow_at conj_check hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hr := allBelow_at rep_check (labG_lt g)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  have hr1 : repAt (labAt (codeOf g)) < 1080 := hr.1
  have e := congrArg vEltN h.2
  rw [vEltN_mul _ _ h.1 hx, vEltN_mul _ _ hr1 h.1, vEltN_codeOf] at e
  exact e

theorem isConj_of_semiconj {a x y : valentiner} (h : SemiconjBy a x y) : IsConj x y :=
  isConj_iff.mpr ⟨a, by rw [h.eq, mul_inv_cancel_right]⟩

theorem isConj_iff_labG (g h : valentiner) : IsConj g h ↔ labG g = labG h := by
  constructor
  · rw [isConj_iff]
    rintro ⟨c, rfl⟩
    rw [labG_conj]
  · intro e
    have h1 := isConj_of_semiconj (semiconj_rep g)
    have h2 := isConj_of_semiconj (semiconj_rep h)
    rw [e] at h1
    exact h1.trans h2.symm

theorem labG_rep (l : ℕ) (hl : l < 17) : labG (vEltN (repAt l)) = l := by
  have hr := allBelow_at rep_check hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  rw [labG_vEltN _ hr.1, hr.2]

/-- The conjugacy classes of Valentiner's group are the seventeen rows. -/
noncomputable def classEquiv : ConjClasses valentiner ≃ Fin 17 where
  toFun := Quotient.lift (fun g => (⟨labG g, labG_lt g⟩ : Fin 17))
    (fun g h hgh => Fin.ext ((isConj_iff_labG g h).mp hgh))
  invFun l := ConjClasses.mk (vEltN (repAt l))
  left_inv c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (vEltN (repAt (labG g))) = ConjClasses.mk g
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_labG, labG_rep _ (labG_lt g)]
  right_inv l := by
    change (⟨labG (vEltN (repAt l)), _⟩ : Fin 17) = l
    exact Fin.ext (labG_rep l l.2)

theorem classEquiv_mk (g : valentiner) : classEquiv (ConjClasses.mk g) = ⟨labG g, labG_lt g⟩ :=
  rfl

theorem mem_carrier_iff (c : ConjClasses valentiner) (g : valentiner) :
    g ∈ c.carrier ↔ labG g = classEquiv c := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ← classEquiv.apply_eq_iff_eq, classEquiv_mk, Fin.ext_iff]


/-! ### Traces and orders of the classes -/

theorem traceZ_eq (l : Fin 17) : ZOP.toComplex (traceZ l) = (s1080ClassTable l).trace := by
  fin_cases l <;> simp [traceZ, s1080ClassTable, z, ZOP.toComplex, Exact.omega_sq] <;> ring

theorem colourChar_conj (h g : valentiner) :
    colourChar valentiner (h * g * h⁻¹) = colourChar valentiner g := by
  simp only [colourChar, Subgroup.coe_mul, Subgroup.coe_inv, Submonoid.coe_mul]
  rw [Matrix.trace_mul_cycle, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    Matrix.one_mul]

theorem trace_vmat (x : ℕ) :
    (vmat x).trace = ZOP.toComplex (omegaZ (jOf x) *
      M3Z.trace (M3Z.mul (gAt (kOf x)) (cosetAt (iOf x)))) / 4 := by
  rw [vmat, Matrix.trace_smul, rotN_eq _ (kOf_lt x), cosC, half_mul_half, Matrix.trace_smul,
    M3Z.toMat_trace, ZOP.toComplex_mul, toComplex_omegaZ, smul_eq_mul, smul_eq_mul]
  ring

theorem char_rep (l : Fin 17) :
    colourChar valentiner (vEltN (repAt l)) = ZOP.toComplex (traceZ l) := by
  have hr := allBelow_at rep_check l.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  have h := congrArg ZOP.toComplex (rep_trace l)
  rw [vEltN_eq _ hr.1, colourChar]
  change (vmat (repAt l)).trace = _
  rw [trace_vmat, h, ZOP.toComplex_mul]
  simp [z, ZOP.toComplex]

/-- The row of an element, as an index of the table. -/
noncomputable def rowOf (g : valentiner) : Fin 17 := ⟨labG g, labG_lt g⟩

theorem char_eq_row (g : valentiner) :
    colourChar valentiner g = ZOP.toComplex (traceZ (rowOf g)) := by
  have hs := semiconj_rep g
  have e : vEltN (repAt (labG g)) =
      vEltN (conjAt (codeOf g)) * g * (vEltN (conjAt (codeOf g)))⁻¹ := by
    rw [hs.eq, mul_inv_cancel_right]
  rw [← char_rep (rowOf g)]
  change _ = colourChar valentiner (vEltN (repAt (labG g)))
  rw [e, colourChar_conj]

theorem orderOf_rep (l : Fin 17) : orderOf (vEltN (repAt l)) = (s1080ClassTable l).order := by
  have hr := allBelow_at rep_check l.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  have ho := rep_order l
  have hlt : (s1080ClassTable l).order < 61 := by
    have : ∀ l : Fin 17, (s1080ClassTable l).order < 61 := by decide +kernel
    exact this l
  rw [← ho]
  refine orderOf_eq_ordAux mulC oneC (repAt l) vEltN {y | y < 1080} (fun y _ => mulC_lt _ _)
    (by decide) (fun y hy => vEltN_mul _ _ hr.1 hy) ?_ ?_ 60 (by unfold ordC at ho; omega)
  · rw [vEltN_eq _ (by decide)]
    exact Subtype.ext (Subtype.ext vmat_one)
  · intro y hy h1
    have h2 : vEltN y = vEltN oneC := by
      rw [h1, vEltN_eq _ (by decide)]
      exact (Subtype.ext (Subtype.ext vmat_one)).symm
    rw [vEltN_eq _ hy, vEltN_eq _ (by decide)] at h2
    exact congrArg Fin.val (vElt_injective h2)

theorem orderOf_eq_row (g : valentiner) : orderOf g = (s1080ClassTable (rowOf g)).order := by
  rw [← orderOf_rep (rowOf g), (semiconj_rep g).orderOf_eq]
  rfl

/-! ### The sizes of the classes -/

theorem countBelow_eq_sum (P : ℕ → Bool) (m : ℕ) :
    countBelow P m = ∑ n ∈ Finset.range m, if P n then 1 else 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [countBelow, ih, Finset.sum_range_succ, add_comm]

theorem card_lab_fin (l : Fin 17) :
    (Finset.univ.filter fun x : Fin 1080 => labAt x = l).card = (s1080ClassTable l).size := by
  rw [← lab_count l, countBelow_eq_sum, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun n => if (labAt n == (l : ℕ)) = true then 1 else 0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [beq_iff_eq]

theorem labG_vElt (x : Fin 1080) : labG (vElt x) = labAt x := by
  rw [← vEltN_eq x x.2, labG_vEltN x x.2]

theorem card_row (l : Fin 17) :
    {g : valentiner | labG g = l}.ncard = (s1080ClassTable l).size := by
  have e : {g : valentiner | labG g = l} =
      vEquiv '' ((Finset.univ.filter fun x : Fin 1080 => labAt x = l : Finset (Fin 1080)) :
        Set (Fin 1080)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨vEquiv.symm g, ?_, vEquiv.apply_symm_apply g⟩
      rw [← h]
      rfl
    · rintro ⟨x, hx, rfl⟩
      change labG (vElt x) = l
      rw [labG_vElt, hx]
  rw [e, Set.ncard_image_of_injective _ vEquiv.injective, Set.ncard_coe_finset, card_lab_fin]


/-! ### The class table, the orders and the exponent -/

theorem class_table : ∃ e : ConjClasses valentiner ≃ Fin 17, ∀ c : ConjClasses valentiner,
    c.carrier.ncard = (s1080ClassTable (e c)).size ∧
    ∀ g ∈ c.carrier, colourChar valentiner g = (s1080ClassTable (e c)).trace ∧
      orderOf g = (s1080ClassTable (e c)).order := by
  refine ⟨classEquiv, fun c => ⟨?_, fun g hg => ?_⟩⟩
  · have : c.carrier = {g | labG g = classEquiv c} := Set.ext (mem_carrier_iff c)
    rw [this, card_row]
  · have hrow : rowOf g = classEquiv c := Fin.ext ((mem_carrier_iff c g).mp hg)
    rw [char_eq_row, orderOf_eq_row, hrow, traceZ_eq]
    exact ⟨rfl, rfl⟩

theorem order_of_trace (g h : valentiner)
    (e : colourChar valentiner g = colourChar valentiner h) : orderOf g = orderOf h := by
  rw [char_eq_row, char_eq_row] at e
  have key : ∀ l l' : Fin 17, traceZ l = traceZ l' →
      (s1080ClassTable l).order = (s1080ClassTable l').order := by decide +kernel
  rw [orderOf_eq_row, orderOf_eq_row]
  exact key _ _ (ZOP.toComplex_injective e)

/-- The number of rows of the table with order `n`. -/
theorem card_rows_order (n : ℕ) :
    (Finset.univ.filter fun l : Fin 17 => (s1080ClassTable l).order = n).card =
      if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 4 else if n = 4 then 1
      else if n = 5 then 2 else if n = 6 then 2 else if n = 12 then 2 else if n = 15 then 4
      else 0 := by
  rcases Nat.lt_or_ge n 16 with hn | hn
  · have key : ∀ n < 16,
        (Finset.univ.filter fun l : Fin 17 => (s1080ClassTable l).order = n).card =
          if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 4 else if n = 4 then 1
          else if n = 5 then 2 else if n = 6 then 2 else if n = 12 then 2 else if n = 15 then 4
          else 0 := by decide +kernel
    exact key n hn
  · have hle : ∀ l : Fin 17, (s1080ClassTable l).order ≤ 15 := by decide +kernel
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun l _ h => by
      have := hle l; omega)]
    split_ifs <;> omega

theorem order_count (n : ℕ) :
    {c : ConjClasses valentiner | ∃ g ∈ c.carrier, orderOf g = n}.ncard =
      if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 4 else if n = 4 then 1
      else if n = 5 then 2 else if n = 6 then 2 else if n = 12 then 2 else if n = 15 then 4
      else 0 := by
  have e : {c : ConjClasses valentiner | ∃ g ∈ c.carrier, orderOf g = n} =
      classEquiv.symm '' ((Finset.univ.filter fun l : Fin 17 =>
        (s1080ClassTable l).order = n : Finset (Fin 17)) : Set (Fin 17)) := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, hg, hgn⟩
      refine ⟨classEquiv c, ?_, classEquiv.symm_apply_apply c⟩
      have hrow : rowOf g = classEquiv c := Fin.ext ((mem_carrier_iff c g).mp hg)
      rw [← hgn, orderOf_eq_row, hrow]
    · rintro ⟨l, hl, rfl⟩
      refine ⟨vEltN (repAt l), ?_, ?_⟩
      · rw [mem_carrier_iff, Equiv.apply_symm_apply, labG_rep l l.2]
      · rw [orderOf_rep, hl]
  rw [e, Set.ncard_image_of_injective _ classEquiv.symm.injective, Set.ncard_coe_finset,
    card_rows_order]

theorem exponent_valentiner : Monoid.exponent valentiner = 60 := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_eq_row]
    have : ∀ l : Fin 17, (s1080ClassTable l).order ∣ 60 := by decide +kernel
    exact this _
  · have d12 : 12 ∣ Monoid.exponent valentiner := by
      have := Monoid.order_dvd_exponent (vEltN (repAt (11 : Fin 17)))
      rwa [orderOf_rep] at this
    have d15 : 15 ∣ Monoid.exponent valentiner := by
      have := Monoid.order_dvd_exponent (vEltN (repAt (13 : Fin 17)))
      rwa [orderOf_rep] at this
    exact Nat.lcm_dvd d12 d15

/-! ### Averages over the group -/

theorem labFin_eq (x : Fin 1080) : rowOf (vElt x) = ⟨labAt x, labAt_lt x x.2⟩ :=
  Fin.ext (labG_vElt x)

theorem sum_rows (F : ℂ → ℂ) :
    ∑ x : Fin 1080, F (colourChar valentiner (vElt x)) =
      ∑ l : Fin 17, ((s1080ClassTable l).size : ℂ) * F (ZOP.toComplex (traceZ l)) := by
  have e1 : ∀ x : Fin 1080, F (colourChar valentiner (vElt x)) =
      F (ZOP.toComplex (traceZ (⟨labAt x, labAt_lt x x.2⟩ : Fin 17))) := by
    intro x
    rw [char_eq_row, labFin_eq]
  rw [Finset.sum_congr rfl fun x _ => e1 x,
    ← Finset.sum_fiberwise Finset.univ (fun x : Fin 1080 => (⟨labAt x, labAt_lt x x.2⟩ : Fin 17))]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hf : (Finset.univ.filter fun x : Fin 1080 => (⟨labAt x, labAt_lt x x.2⟩ : Fin 17) = l) =
      Finset.univ.filter fun x : Fin 1080 => labAt x = l :=
    Finset.filter_congr fun x _ => Fin.ext_iff
  rw [Finset.sum_congr rfl (g := fun _ => F (ZOP.toComplex (traceZ l))) (fun x hx => by
    rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul, hf, card_lab_fin l]

theorem avg_valentiner (F : ℂ → ℂ) :
    groupAvg valentiner (fun g => F (colourChar valentiner g)) =
      (1080 : ℂ)⁻¹ * ∑ l : Fin 17, ((s1080ClassTable l).size : ℂ) *
        F (ZOP.toComplex (traceZ l)) := by
  rw [groupAvg, card_valentiner, finsum_valentiner, sum_rows]
  push_cast
  rfl

/-- A sum over the rows of the table, exactly: `Σ_l |C_l| F'(t_l)`. -/
noncomputable def classSum (F : ZOP → ZOP) : ZOP :=
  zsum (fun n => ⟨(s1080ClassTable ⟨n % 17, Nat.mod_lt _ (by norm_num)⟩).size, 0, 0, 0⟩ *
    F (traceZ ⟨n % 17, Nat.mod_lt _ (by norm_num)⟩)) 17

theorem classSum_eq (F : ZOP → ZOP) :
    ∑ l : Fin 17, ((s1080ClassTable l).size : ℂ) * ZOP.toComplex (F (traceZ l)) =
      ZOP.toComplex (classSum F) := by
  rw [classSum, toComplex_zsum, Finset.sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Nat.mod_eq_of_lt l.2, ZOP.toComplex_mul]
  simp [ZOP.toComplex]

theorem classSum_1 : classSum (fun t => t * ZOP.conj t) = ⟨1080, 0, 0, 0⟩ := by decide +kernel

theorem classSum_2 : classSum (fun t => (t * ZOP.conj t) * (t * ZOP.conj t)) =
    ⟨2160, 0, 0, 0⟩ := by decide +kernel

theorem classSum_3 : classSum (fun t => (t * ZOP.conj t - 1) * ZOP.conj (t * ZOP.conj t - 1)) =
    ⟨1080, 0, 0, 0⟩ := by decide +kernel

theorem classSum_4 : classSum (fun t => ZOP.conj t * ZOP.conj (ZOP.conj t)) =
    ⟨1080, 0, 0, 0⟩ := by decide +kernel

theorem classSum_5 : classSum (fun t => (t * t - ZOP.conj t) * ZOP.conj (t * t - ZOP.conj t)) =
    ⟨1080, 0, 0, 0⟩ := by decide +kernel

/-- An average over Valentiner's group of an exact function of the character. -/
theorem avg_exact (F : ℂ → ℂ) (F' : ZOP → ZOP)
    (hF : ∀ t, F (ZOP.toComplex t) = ZOP.toComplex (F' t))
    (c : ℕ) (hc : classSum F' = ⟨c, 0, 0, 0⟩) :
    groupAvg valentiner (fun g => F (colourChar valentiner g)) = (c : ℂ) / 1080 := by
  rw [avg_valentiner]
  simp only [hF]
  rw [classSum_eq, hc]
  simp [ZOP.toComplex]
  ring

end Artform.ColourGroups
