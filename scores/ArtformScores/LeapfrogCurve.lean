import ArtformScores.Classes
import ArtformScores.FaceLink

/-!
# The classes of the leapfrog phase: the normalization
-/

namespace Artform.Scores.Leapfrog

open Polynomial
open LaurentPolynomial (T T_add T_zero)

variable {F : Type*} [Field F] (q : F)

/-- The points of the `s`-line where `x` is `0` or `∞`, besides `s = ∞`: `s (s - 1) (s - q)`. -/
noncomputable def poles : F[X] := X * (X - 1) * (X - C q)

/-- The ring of the normalization: the `s`-line without `s = 0, 1, q, ∞`. -/
abbrev Norm := Localization.Away (poles q)

/-- The coordinate `s`. -/
noncomputable def sN : Norm q := algebraMap F[X] (Norm q) X

variable {q}

theorem poles_ne_zero : poles q ≠ 0 := by
  unfold poles
  have h1 : (X - 1 : F[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : F)
  exact mul_ne_zero (mul_ne_zero X_ne_zero h1) (X_sub_C_ne_zero q)

instance : IsDomain (Norm q) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors poles_ne_zero)

instance : IsPrincipalIdealRing (Norm q) := by
  constructor
  intro J
  have h := IsLocalization.map_under (Submonoid.powers (poles q)) (Norm q) J
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (Ideal.under F[X] J)
  refine ⟨algebraMap F[X] (Norm q) g, ?_⟩
  rw [← h, hg]
  exact (Ideal.map_span _ _).trans (by simp)

theorem isUnit_poles : IsUnit (algebraMap F[X] (Norm q) (poles q)) :=
  IsLocalization.Away.algebraMap_isUnit _

theorem factors_unit :
    IsUnit (sN q) ∧ IsUnit (sN q - 1) ∧ IsUnit (sN q - algebraMap F (Norm q) q) := by
  have h := isUnit_poles (q := q)
  have e : algebraMap F[X] (Norm q) (poles q) =
      sN q * (sN q - 1) * (sN q - algebraMap F (Norm q) q) := by
    simp only [poles, map_mul, map_sub, map_one, sN]
    rw [IsScalarTower.algebraMap_apply F F[X] (Norm q), algebraMap_eq]
  rw [e] at h
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h), isUnit_of_mul_isUnit_right h⟩

/-- The constant `q` in the normalization. -/
noncomputable abbrev qN (q : F) : Norm q := algebraMap F (Norm q) q

theorem map_C (a : F) : algebraMap F[X] (Norm q) (C a) = algebraMap F (Norm q) a := by
  rw [IsScalarTower.algebraMap_apply F F[X] (Norm q), algebraMap_eq]

variable (q) in
/-- The three unit factors, as units. -/
noncomputable def uS : (Norm q)ˣ := factors_unit.1.unit

variable (q) in
/-- The unit `s - 1`. -/
noncomputable def uS1 : (Norm q)ˣ := factors_unit.2.1.unit

variable (q) in
/-- The unit `s - q`. -/
noncomputable def uSq : (Norm q)ˣ := factors_unit.2.2.unit

theorem val_uS : (uS q : Norm q) = sN q := rfl
theorem val_uS1 : (uS1 q : Norm q) = sN q - 1 := rfl
theorem val_uSq : (uSq q : Norm q) = sN q - qN q := rfl

/-- The constant `q` as a unit. -/
noncomputable def uQ (hq0 : q ≠ 0) : (Norm q)ˣ :=
  Units.map (algebraMap F (Norm q)).toMonoidHom (Units.mk0 q hq0)

theorem val_uQ (hq0 : q ≠ 0) : (uQ hq0 : Norm q) = qN q := rfl

/-- The unit `x` as a function of `s`: `x = q (1 - s) / (s (s - q))`. -/
noncomputable def xU (hq0 : q ≠ 0) : (Norm q)ˣ :=
  -(uQ hq0 * uS1 q * (uS q * uSq q)⁻¹)

variable (hq0 : q ≠ 0)

/-- The defining relation of `x`. -/
theorem xU_rel : (xU hq0 : Norm q) * (sN q * (sN q - qN q)) = qN q * (1 - sN q) := by
  have h : ((uS q * uSq q)⁻¹ : (Norm q)ˣ).val * (sN q * (sN q - qN q)) = 1 := by
    have := Units.inv_mul (uS q * uSq q)
    rwa [Units.val_mul, val_uS, val_uSq] at this
  simp only [xU, Units.val_neg, Units.val_mul, val_uQ, val_uS1]
  linear_combination (-(qN q * (sN q - 1))) * h

/-- The defect `δ = x - 1` as a function of `s`. -/
noncomputable def deltaN : Norm q := (xU hq0 : Norm q) - 1

/-- The eigenvalue `λ = 1 + (x - 1) s`. -/
noncomputable def lamN : Norm q := 1 + deltaN hq0 * sN q

/-- `x s² = q λ`. -/
theorem x_sq_eq : (xU hq0 : Norm q) * (sN q * sN q) = qN q * lamN hq0 := by
  have h := xU_rel hq0
  simp only [lamN, deltaN]
  linear_combination h

/-- `(x - 1) s (s - q) = q - s²`. -/
theorem delta_rel : deltaN hq0 * (sN q * (sN q - qN q)) = qN q - sN q * sN q := by
  have h := xU_rel hq0
  simp only [deltaN]
  linear_combination h

/-- The inverse of `x`. -/
noncomputable def xInv : Norm q := ((xU hq0)⁻¹ : (Norm q)ˣ)

theorem x_mul_xInv : (xU hq0 : Norm q) * xInv hq0 = 1 := Units.mul_inv _

/-- The map from the stencils to the normalization: `x` goes to `xU`. -/
noncomputable def psi : LaurentPolynomial F →+* Norm q :=
  LaurentPolynomial.eval₂ (algebraMap F (Norm q)) (xU hq0)

theorem psi_C (r : F) : psi hq0 (LaurentPolynomial.C r) = algebraMap F (Norm q) r :=
  LaurentPolynomial.eval₂_C _ _ r

theorem psi_T_one : psi hq0 (T 1) = (xU hq0 : Norm q) := by
  have := LaurentPolynomial.eval₂_T (algebraMap F (Norm q)) (xU hq0) 1
  simp only [zpow_one] at this
  exact this

theorem psi_T_neg_one : psi hq0 (T (-1)) = xInv hq0 := by
  have := LaurentPolynomial.eval₂_T (algebraMap F (Norm q)) (xU hq0) (-1)
  simp only [Int.reduceNeg, zpow_neg, zpow_one] at this
  exact this

theorem psi_phase :
    psi hq0 (phaseT q) = 2 - qN q * (2 - (xU hq0 : Norm q) - xInv hq0) := by
  simp only [phaseT, stencilG, map_sub, map_mul, psi_C, psi_T_one, psi_T_neg_one, map_ofNat]

/-- `λ` is a root of `λ² - t λ + 1`. -/
theorem lam_root : lamN hq0 * lamN hq0 - psi hq0 (phaseT q) * lamN hq0 + 1 = 0 := by
  rw [psi_phase]
  have h1 := x_sq_eq hq0
  have h2 := x_mul_xInv hq0
  have hd : deltaN hq0 = (xU hq0 : Norm q) - 1 := rfl
  have hl : lamN hq0 = 1 + deltaN hq0 * sN q := rfl
  -- `(λ - 1)² = (t - 2) λ`
  have key : (deltaN hq0 * sN q) * (deltaN hq0 * sN q) =
      deltaN hq0 * deltaN hq0 * (xInv hq0 * (qN q * lamN hq0)) := by
    rw [← h1]
    linear_combination (-(deltaN hq0 * deltaN hq0 * (sN q * sN q))) * h2
  have key2 : deltaN hq0 * deltaN hq0 * xInv hq0 =
      (xU hq0 : Norm q) - 2 + xInv hq0 := by
    rw [hd]
    linear_combination ((xU hq0 : Norm q) - 2) * h2
  have hl' : lamN hq0 - 1 = deltaN hq0 * sN q := by rw [hl]; ring
  linear_combination (lamN hq0 - 1 + deltaN hq0 * sN q) * hl' + key + (qN q * lamN hq0) * key2


/-! ### The normalization as a module over the stencils -/

theorem psi_kap1 : psi hq0 (kap1 q) = qN q * (1 - xInv hq0) := by
  simp only [kap1, map_mul, map_sub, map_one, psi_C, psi_T_neg_one]

theorem psi_kap0 : psi hq0 (kap0 q) = qN q * xInv hq0 := by
  simp only [kap0, map_mul, psi_C, psi_T_neg_one]

/-- `s² = κ₁ s + κ₀`. -/
theorem s_sq : sN q * sN q = psi hq0 (kap1 q) * sN q + psi hq0 (kap0 q) := by
  rw [psi_kap1, psi_kap0]
  have h := xU_rel hq0
  have h2 := x_mul_xInv hq0
  linear_combination xInv hq0 * h + (-(sN q * (sN q - qN q))) * h2

theorem psi_T_mul : psi hq0 (T 1) * psi hq0 (T (-1)) = 1 := by
  rw [psi_T_one, psi_T_neg_one, x_mul_xInv]

/-- The elements `f + g s`, a subring of the normalization. -/
noncomputable def formSubring : Subring (Norm q) where
  carrier := {y | ∃ f g, y = psi hq0 f + psi hq0 g * sN q}
  mul_mem' := by
    rintro _ _ ⟨f, g, rfl⟩ ⟨f', g', rfl⟩
    refine ⟨f * f' + g * g' * kap0 q, f * g' + g * f' + g * g' * kap1 q, ?_⟩
    simp only [map_add, map_mul]
    linear_combination psi hq0 g * psi hq0 g' * s_sq hq0
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨f, g, rfl⟩ ⟨f', g', rfl⟩
    exact ⟨f + f', g + g', by simp only [map_add]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨f, g, rfl⟩
    exact ⟨-f, -g, by simp only [map_neg]; ring⟩

theorem const_mem (a : F) : algebraMap F (Norm q) a ∈ formSubring hq0 :=
  ⟨LaurentPolynomial.C a, 0, by simp [psi_C]⟩

theorem s_mem : sN q ∈ formSubring hq0 := ⟨0, 1, by simp⟩

theorem psi_mem (f : LaurentPolynomial F) : psi hq0 f ∈ formSubring hq0 := ⟨f, 0, by simp⟩

theorem poly_mem (P : F[X]) : algebraMap F[X] (Norm q) P ∈ formSubring hq0 := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine mul_mem ?_ (pow_mem (s_mem hq0) n)
    rw [map_C]
    exact const_mem hq0 a

variable (hq1 : q ≠ 1)

include hq1 in
theorem qm1_ne : algebraMap F (Norm q) (q - 1) ≠ 0 := by
  simpa [sub_eq_zero] using hq1

/-- The inverse of `s`, of the form `f + g s`. -/
theorem inv_s_mem : ∃ w ∈ formSubring hq0, sN q * w = 1 := by
  have h2 := x_mul_xInv hq0
  have hq : qN q * algebraMap F (Norm q) q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  refine ⟨algebraMap F (Norm q) q⁻¹ * (xU hq0 : Norm q) * (sN q - psi hq0 (kap1 q)),
    mul_mem (mul_mem (const_mem hq0 _) ?_) (sub_mem (s_mem hq0) (psi_mem hq0 _)), ?_⟩
  · rw [← psi_T_one]; exact psi_mem hq0 _
  · have h := s_sq hq0
    rw [psi_kap0] at h
    linear_combination (algebraMap F (Norm q) q⁻¹ * (xU hq0 : Norm q)) * h +
      (xU hq0 : Norm q) * xInv hq0 * hq + h2

include hq1 in
/-- The inverse of `s - 1`, of the form `f + g s`. -/
theorem inv_s1_mem : ∃ w ∈ formSubring hq0, (sN q - 1) * w = 1 := by
  have hq : algebraMap F (Norm q) (q - 1) * algebraMap F (Norm q) (q - 1)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hq1), map_one]
  refine ⟨algebraMap F (Norm q) (q - 1)⁻¹ * (sN q + 1 - psi hq0 (kap1 q)),
    mul_mem (const_mem hq0 _) (sub_mem (add_mem (s_mem hq0) (one_mem _)) (psi_mem hq0 _)), ?_⟩
  have h := s_sq hq0
  have hk : psi hq0 (kap1 q) + psi hq0 (kap0 q) = algebraMap F (Norm q) (q - 1) + 1 := by
    rw [psi_kap1, psi_kap0, map_sub, map_one]; ring
  linear_combination (algebraMap F (Norm q) (q - 1)⁻¹) * h +
    (algebraMap F (Norm q) (q - 1)⁻¹) * hk + hq

include hq1 in
/-- The inverse of `s - q`, of the form `f + g s`. -/
theorem inv_sq_mem : ∃ w ∈ formSubring hq0, (sN q - qN q) * w = 1 := by
  obtain ⟨w, hw, hw1⟩ := inv_s1_mem hq0 hq1
  have hq : qN q * algebraMap F (Norm q) q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  refine ⟨-(algebraMap F (Norm q) q⁻¹ * (xU hq0 : Norm q) * sN q * w),
    neg_mem (mul_mem (mul_mem (mul_mem (const_mem hq0 _) ?_) (s_mem hq0)) hw), ?_⟩
  · rw [← psi_T_one]; exact psi_mem hq0 _
  · have h := xU_rel hq0
    linear_combination (-(algebraMap F (Norm q) q⁻¹ * w)) * h +
      (-(w * (1 - sN q))) * hq + hw1

include hq1 in
/-- Every element of the normalization is `f + g s`, with `f` and `g` stencils. -/
theorem exists_form (y : Norm q) : ∃ f g, y = psi hq0 f + psi hq0 g * sN q := by
  obtain ⟨w₀, hw₀, h₀⟩ := inv_s_mem hq0
  obtain ⟨w₁, hw₁, h₁⟩ := inv_s1_mem hq0 hq1
  obtain ⟨w₂, hw₂, h₂⟩ := inv_sq_mem hq0 hq1
  have hp : algebraMap F[X] (Norm q) (poles q) =
      sN q * (sN q - 1) * (sN q - qN q) := by
    simp only [poles, map_mul, map_sub, map_one, sN, map_C]
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (poles q) y
  have hw : algebraMap F[X] (Norm q) (poles q) * (w₀ * w₁ * w₂) = 1 := by
    rw [hp]
    linear_combination ((sN q - 1) * w₁ * (sN q - qN q) * w₂) * h₀ +
      ((sN q - qN q) * w₂) * h₁ + h₂
  have hy : y = algebraMap F[X] (Norm q) a * (w₀ * w₁ * w₂) ^ n := by
    rw [← h, mul_assoc, ← mul_pow, hw, one_pow, mul_one]
  have hm : y ∈ formSubring hq0 := by
    rw [hy]
    exact mul_mem (poly_mem hq0 a) (pow_mem (mul_mem (mul_mem hw₀ hw₁) hw₂) n)
  exact hm

/-! ### The stencils embed in the normalization -/

/-- A homogeneous form in `A = q (1 - X)` and `B = X (X - q)` vanishes only when its coefficients
do, since `B` vanishes at `0` and `A` does not. -/
theorem hom_zero (A B : F[X]) (hB0 : B.eval 0 = 0) (hA0 : A.eval 0 ≠ 0) (hB : B ≠ 0) (d : ℕ) :
    ∀ a : ℕ → F, (∑ i ∈ Finset.range (d + 1), C (a i) * A ^ i * B ^ (d - i)) = 0 →
      ∀ i ≤ d, a i = 0 := by
  induction d with
  | zero =>
    intro a h i hi
    obtain rfl : i = 0 := by omega
    simpa using h
  | succ d ih =>
    intro a h
    rw [Finset.sum_range_succ] at h
    have hs : ∑ i ∈ Finset.range (d + 1), C (a i) * A ^ i * B ^ (d + 1 - i) =
        B * ∑ i ∈ Finset.range (d + 1), C (a i) * A ^ i * B ^ (d - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : d + 1 - i = d - i + 1 := by have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]
      ring
    rw [hs] at h
    have hlast : a (d + 1) = 0 := by
      have := congrArg (Polynomial.eval 0) h
      simp only [eval_add, eval_mul, hB0, zero_mul, eval_C, eval_pow, Nat.sub_self, pow_zero,
        mul_one, zero_add, eval_zero] at this
      exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hA0)
    rw [hlast] at h
    simp only [map_zero, zero_mul, add_zero] at h
    have hsum := (mul_eq_zero.mp h).resolve_left hB
    intro i hi
    rcases Nat.lt_or_ge i (d + 1) with hlt | hge
    · exact ih a hsum i (by omega)
    · obtain rfl : i = d + 1 := by omega
      exact hlast

theorem poly_injective : Function.Injective (algebraMap F[X] (Norm q)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (poles_ne_zero (q := q)))

/-- A polynomial in `x` vanishes on the normalization only if it is zero. -/
theorem eval_x_eq_zero (p : F[X])
    (h : Polynomial.eval₂ (algebraMap F (Norm q)) (xU hq0 : Norm q) p = 0) : p = 0 := by
  set A : F[X] := C q * (1 - X) with hA
  set B : F[X] := X * (X - C q) with hB
  have hB0 : B.eval 0 = 0 := by simp [hB]
  have hA0 : A.eval 0 ≠ 0 := by simpa [hA] using hq0
  have hBne : B ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero q)
  have hAB : (xU hq0 : Norm q) * algebraMap F[X] (Norm q) B = algebraMap F[X] (Norm q) A := by
    have hrel := xU_rel hq0
    simp only [hA, hB, map_mul, map_sub, map_one, map_C]
    exact hrel
  have key : (∑ i ∈ Finset.range (p.natDegree + 1),
      C (p.coeff i) * A ^ i * B ^ (p.natDegree - i)) = 0 := by
    apply poly_injective (q := q)
    rw [map_sum, map_zero]
    have h' : (∑ i ∈ Finset.range (p.natDegree + 1),
        algebraMap F (Norm q) (p.coeff i) * (xU hq0 : Norm q) ^ i) = 0 := by
      rw [← h, Polynomial.eval₂_eq_sum_range]
    calc _ = ∑ i ∈ Finset.range (p.natDegree + 1), algebraMap F[X] (Norm q) B ^ p.natDegree *
            (algebraMap F (Norm q) (p.coeff i) * (xU hq0 : Norm q) ^ i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : i ≤ p.natDegree := by have := Finset.mem_range.mp hi; omega
          rw [map_mul, map_mul, map_pow, map_pow, map_C, ← hAB, mul_pow]
          have hpow : algebraMap F[X] (Norm q) B ^ p.natDegree = algebraMap F[X] (Norm q) B ^ i *
              algebraMap F[X] (Norm q) B ^ (p.natDegree - i) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow]
          ring
      _ = 0 := by rw [← Finset.mul_sum, h', mul_zero]
  have hco := hom_zero A B hB0 hA0 hBne p.natDegree (fun i => p.coeff i) key
  ext i
  rw [coeff_zero]
  rcases Nat.lt_or_ge p.natDegree i with hlt | hge
  · exact coeff_eq_zero_of_natDegree_lt hlt
  · exact hco i hge

/-- The stencils embed in the normalization. -/
theorem psi_injective : Function.Injective (psi hq0) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have h0 : psi hq0 (Polynomial.toLaurent p) = 0 := by rw [hp, map_mul, hf, zero_mul]
  have h1 : Polynomial.eval₂ (algebraMap F (Norm q)) (xU hq0 : Norm q) p = 0 := by
    rw [← h0]
    exact (LaurentPolynomial.eval₂_toLaurent _ _ p).symm
  have hp0 := eval_x_eq_zero hq0 p h1
  rw [hp0, map_zero] at hp
  have hT : (T (n : ℤ) : LaurentPolynomial F) * T (-(n : ℤ)) = 1 := by rw [← T_add]; simp
  calc f = f * (T (n : ℤ) * T (-(n : ℤ))) := by rw [hT, mul_one]
    _ = 0 := by rw [← mul_assoc]; rw [← hp, zero_mul]

theorem T_one_ne_one : (T 1 : LaurentPolynomial F) ≠ 1 := by
  intro h
  have h' : (T 1 : LaurentPolynomial F) = T 0 := by rw [h, T_zero]
  have h'' := congrArg (fun f : LaurentPolynomial F => f.coeff 1) h'
  simp only [LaurentPolynomial.T_apply] at h''
  norm_num at h''

/-- `x` is not `1`. -/
theorem xU_ne_one : (xU hq0 : Norm q) ≠ 1 := by
  intro h
  have h0 : psi hq0 (T 1) = psi hq0 1 := by rw [psi_T_one, h, map_one]
  exact T_one_ne_one (psi_injective hq0 h0)

theorem deltaN_ne_zero : deltaN hq0 ≠ 0 := sub_ne_zero.mpr (xU_ne_one hq0)

/-- Two ring homomorphisms from the stencils that agree on the constants and on the shift agree. -/
theorem laurent_hom_ext {A : Type*} [CommRing A] (f g : LaurentPolynomial F →+* A)
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a)) (hT : f (T 1) = g (T 1)) :
    f = g := by
  have hTi : f (T (-1)) = g (T (-1)) := by
    have h1 : (T 1 : LaurentPolynomial F) * T (-1) = 1 := by rw [← T_add]; simp
    have hf := congrArg f h1
    have hg := congrArg g h1
    rw [map_mul, map_one] at hf hg
    rw [← hT] at hg
    calc f (T (-1)) = f (T (-1)) * (f (T 1) * g (T (-1))) := by rw [hg, mul_one]
      _ = (f (T 1) * f (T (-1))) * g (T (-1)) := by ring
      _ = g (T (-1)) := by rw [hf, one_mul]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on with
  | h_C a => exact hC a
  | h_add hp hq => rw [map_add, map_add, hp, hq]
  | h_C_mul_T n a h =>
    have e : (LaurentPolynomial.C a * T ((n : ℤ) + 1) : LaurentPolynomial F) =
        LaurentPolynomial.C a * T n * T 1 := by rw [T_add, mul_assoc]
    rw [e, map_mul, map_mul g, h, hT]
  | h_C_mul_T_Z n a h =>
    have e : (LaurentPolynomial.C a * T (-(n : ℤ) - 1) : LaurentPolynomial F) =
        LaurentPolynomial.C a * T (-(n : ℤ)) * T (-1) := by
      rw [mul_assoc, ← T_add]; rfl
    rw [e, map_mul, map_mul g, h, hTi]

/-! ### The involution `s ↦ (s - q)/(s - 1)` -/

variable (q) in
/-- The inverse of `s - 1`. -/
noncomputable def invS1 : Norm q := ((uS1 q)⁻¹ : (Norm q)ˣ)

theorem s1_mul_inv : (sN q - 1) * invS1 q = 1 := Units.mul_inv (uS1 q)

variable (q) in
/-- The value `s′ = (s - q)/(s - 1)` of the involution at `s`. -/
noncomputable def sP : Norm q := (sN q - qN q) * invS1 q

theorem sP_sub_one : sP q - 1 = (1 - qN q) * invS1 q := by
  simp only [sP]
  linear_combination s1_mul_inv (q := q)

theorem sP_sub_q : sP q - qN q = (1 - qN q) * (sN q * invS1 q) := by
  simp only [sP]
  linear_combination qN q * s1_mul_inv (q := q)

include hq1 in
theorem isUnit_one_sub_q : IsUnit (1 - qN q) := by
  have hne : (1 : F) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have : (1 - qN q) = algebraMap F (Norm q) (1 - q) := by rw [map_sub, map_one]
  rw [this]
  exact (IsUnit.mk0 _ hne).map _

theorem isUnit_invS1 : IsUnit (invS1 q) := ((uS1 q)⁻¹).isUnit

include hq1 in
theorem isUnit_poles_sP :
    IsUnit (Polynomial.eval₂RingHom (algebraMap F (Norm q)) (sP q) (poles q)) := by
  have e : Polynomial.eval₂RingHom (algebraMap F (Norm q)) (sP q) (poles q) =
      sP q * (sP q - 1) * (sP q - qN q) := by
    simp [poles, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C, eval₂_one]
  have h1 : IsUnit (sP q) := factors_unit.2.2.mul isUnit_invS1
  have h2 := isUnit_one_sub_q (q := q) hq1
  rw [e, sP_sub_one, sP_sub_q]
  exact (h1.mul (h2.mul isUnit_invS1)).mul (h2.mul (factors_unit.1.mul isUnit_invS1))

/-- The involution `σ` of the normalization: it fixes `x` and inverts `λ`. -/
noncomputable def sigma : Norm q →+* Norm q :=
  IsLocalization.Away.lift (poles q) (isUnit_poles_sP hq1)

theorem sigma_s : sigma hq1 (sN q) = sP q := by
  simp [sN, sigma]

theorem sigma_const (a : F) : sigma hq1 (algebraMap F (Norm q) a) = algebraMap F (Norm q) a := by
  have h := IsLocalization.Away.lift_eq (S := Norm q) (poles q) (isUnit_poles_sP hq1) (C a)
  rw [map_C] at h
  simpa [sigma] using h

theorem sigma_qN : sigma hq1 (qN q) = qN q := sigma_const hq1 q

theorem sigma_x : sigma hq1 (xU hq0 : Norm q) = (xU hq0 : Norm q) := by
  have h := congrArg (sigma hq1) (xU_rel hq0)
  simp only [map_mul, map_sub, map_one, sigma_s, sigma_qN] at h
  have hu : IsUnit (sP q * (sP q - qN q)) := by
    rw [sP_sub_q]
    exact (factors_unit.2.2.mul isUnit_invS1).mul
      ((isUnit_one_sub_q hq1).mul (factors_unit.1.mul isUnit_invS1))
  apply hu.mul_left_inj.mp
  rw [h]
  -- `x s′ (s′ - q) = q (1 - s′)`
  have hrel := xU_rel hq0
  have hi := s1_mul_inv (q := q)
  rw [sP_sub_q]
  simp only [sP]
  have hs1 : 1 - (sN q - qN q) * invS1 q = (qN q - 1) * invS1 q := by
    linear_combination (-1 : Norm q) * hi
  rw [hs1]
  linear_combination (-((1 - qN q) * invS1 q * invS1 q)) * hrel +
    ((1 - qN q) * qN q * invS1 q) * hi

/-- `σ` fixes the stencils. -/
theorem sigma_psi (f : LaurentPolynomial F) : sigma hq1 (psi hq0 f) = psi hq0 f := by
  have h := laurent_hom_ext ((sigma hq1).comp (psi hq0)) (psi hq0)
    (fun a => by simp only [RingHom.comp_apply, psi_C, sigma_const])
    (by simp only [RingHom.comp_apply, psi_T_one, sigma_x])
  exact RingHom.congr_fun h f

theorem s_ne_sP : sN q ≠ sP q := by
  intro h
  have hi := s1_mul_inv (q := q)
  have h1 : sN q * sN q - 2 * sN q + qN q = 0 := by
    rw [sP] at h
    linear_combination (sN q - 1) * h + (sN q - qN q) * hi
  have h2 : algebraMap F[X] (Norm q) (X ^ 2 - C 2 * X + C q) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_C, map_ofNat]
    rw [← h1]
    simp only [sN]
    ring
  have h3 := poly_injective (q := q) (h2.trans (map_zero _).symm)
  have h4 := congrArg (fun p : F[X] => p.coeff 2) h3
  simp [coeff_X_pow] at h4

include hq1 in
/-- `1` and `s` are independent over the stencils. -/
theorem form_eq_zero {f g : LaurentPolynomial F} (h : psi hq0 f + psi hq0 g * sN q = 0) :
    f = 0 ∧ g = 0 := by
  have h' := congrArg (sigma hq1) h
  simp only [map_add, map_mul, sigma_psi, sigma_s, map_zero] at h'
  have h1 : psi hq0 g * (sN q - sP q) = 0 := by linear_combination h - h'
  have hg : psi hq0 g = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr s_ne_sP)
  have hf : psi hq0 f = 0 := by simpa [hg] using h
  exact ⟨(injective_iff_map_eq_zero _).mp (psi_injective hq0) f hf,
    (injective_iff_map_eq_zero _).mp (psi_injective hq0) g hg⟩

/-- `λ (s - q) = s (1 - s)`. -/
theorem lam_mul : lamN hq0 * (sN q - qN q) = sN q * (1 - sN q) := by
  have h := delta_rel hq0
  simp only [lamN]
  linear_combination h

/-- `σ` inverts `λ`. -/
theorem sigma_lam : sigma hq1 (lamN hq0) * lamN hq0 = 1 := by
  have h := congrArg (sigma hq1) (lam_mul hq0)
  simp only [map_mul, map_sub, map_one, sigma_s, sigma_qN] at h
  rw [sP_sub_q] at h
  have hi := s1_mul_inv (q := q)
  have hl := lam_mul hq0
  have hs1 : sP q * (1 - sP q) = (sN q - qN q) * invS1 q * ((qN q - 1) * invS1 q) := by
    simp only [sP]; congr 1; linear_combination (-1 : Norm q) * hi
  rw [hs1] at h
  -- `σλ s = -(s - q) / (s - 1)`
  have h2 : sigma hq1 (lamN hq0) * sN q = -((sN q - qN q) * invS1 q) := by
    apply (isUnit_one_sub_q (q := q) hq1).mul_right_inj.mp
    linear_combination (sN q - 1) * h +
      (-(sigma hq1 (lamN hq0) * (1 - qN q) * sN q) + (qN q - 1) * (sN q - qN q) * invS1 q) * hi
  have hu : IsUnit (sN q * (sN q - qN q)) := factors_unit.1.mul factors_unit.2.2
  apply hu.mul_left_inj.mp
  linear_combination (lamN hq0 * (sN q - qN q)) * h2 +
    (-((sN q - qN q) * invS1 q)) * hl + (sN q * (sN q - qN q)) * hi

/-! ### The gluing data `E = F[r]/(r² - q)` -/

theorem rE_mul_self : (rE : Fib q) * rE = algebraMap F (Fib q) q := by
  ext <;> simp [rE]

theorem norm_rE : QuadraticAlgebra.norm (rE : Fib q) = -q := by
  simp [QuadraticAlgebra.norm_def, rE]

theorem norm_rE_sub_one : QuadraticAlgebra.norm ((rE : Fib q) - 1) = 1 - q := by
  simp only [QuadraticAlgebra.norm_def, rE, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]
  ring

theorem norm_rE_sub_q :
    QuadraticAlgebra.norm ((rE : Fib q) - algebraMap F (Fib q) q) = q * q - q := by
  simp [QuadraticAlgebra.norm_def, rE]

include hq0 in
theorem isUnit_rE : IsUnit (rE : Fib q) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_rE]
  exact (IsUnit.mk0 _ hq0).neg

include hq1 in
theorem isUnit_rE_sub_one : IsUnit ((rE : Fib q) - 1) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_rE_sub_one]
  exact IsUnit.mk0 _ (sub_ne_zero.mpr (Ne.symm hq1))

include hq0 hq1 in
theorem isUnit_rE_sub_q : IsUnit ((rE : Fib q) - algebraMap F (Fib q) q) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_rE_sub_q]
  refine IsUnit.mk0 _ ?_
  have : q * q - q = q * (q - 1) := by ring
  rw [this]
  exact mul_ne_zero hq0 (sub_ne_zero.mpr hq1)

include hq0 hq1 in
theorem isUnit_poles_rE :
    IsUnit (Polynomial.eval₂RingHom (algebraMap F (Fib q)) rE (poles q)) := by
  have e : Polynomial.eval₂RingHom (algebraMap F (Fib q)) rE (poles q) =
      rE * (rE - 1) * (rE - algebraMap F (Fib q) q) := by
    simp [poles, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C, eval₂_one]
  rw [e]
  exact ((isUnit_rE hq0).mul (isUnit_rE_sub_one hq1)).mul (isUnit_rE_sub_q hq0 hq1)

/-- The value on the fibre over the node. -/
noncomputable def eps : Norm q →+* Fib q :=
  IsLocalization.Away.lift (poles q) (isUnit_poles_rE hq0 hq1)

theorem eps_s : eps hq0 hq1 (sN q) = rE := by
  simp [sN, eps]

theorem eps_const (a : F) : eps hq0 hq1 (algebraMap F (Norm q) a) = algebraMap F (Fib q) a := by
  have h := IsLocalization.Away.lift_eq (S := Norm q) (poles q) (isUnit_poles_rE hq0 hq1) (C a)
  rw [map_C] at h
  simpa [eps] using h

theorem eps_qN : eps hq0 hq1 (qN q) = algebraMap F (Fib q) q := eps_const hq0 hq1 q

/-- `x` is `1` on the fibre. -/
theorem eps_x : eps hq0 hq1 (xU hq0 : Norm q) = 1 := by
  have h := congrArg (eps hq0 hq1) (xU_rel hq0)
  simp only [map_mul, map_sub, map_one, eps_s, eps_qN] at h
  have hu : IsUnit (rE * ((rE : Fib q) - algebraMap F (Fib q) q)) :=
    (isUnit_rE hq0).mul (isUnit_rE_sub_q hq0 hq1)
  apply hu.mul_left_inj.mp
  rw [h, one_mul]
  linear_combination (-1 : Fib q) * rE_mul_self (q := q)

/-- On the fibre a stencil is its value at the zero mode. -/
theorem eps_psi (f : LaurentPolynomial F) :
    eps hq0 hq1 (psi hq0 f) = algebraMap F (Fib q) (atZero F f) := by
  have h := laurent_hom_ext ((eps hq0 hq1).comp (psi hq0))
    ((algebraMap F (Fib q)).comp (atZero F))
    (fun a => by simp only [RingHom.comp_apply, psi_C, eps_const, atZero_C])
    (by simp only [RingHom.comp_apply, psi_T_one, eps_x, atZero_T, map_one])
  exact RingHom.congr_fun h f

theorem eps_delta : eps hq0 hq1 (deltaN hq0) = 0 := by
  simp [deltaN, eps_x]

theorem eps_lam : eps hq0 hq1 (lamN hq0) = 1 := by
  simp [lamN, eps_delta]

theorem elt_eq (z : Fib q) : z = algebraMap F (Fib q) z.re + algebraMap F (Fib q) z.im * rE := by
  ext <;> simp [rE]

theorem eps_surjective : Function.Surjective (eps hq0 hq1) := fun z =>
  ⟨algebraMap F (Norm q) z.re + algebraMap F (Norm q) z.im * sN q, by
    rw [map_add, map_mul, eps_const, eps_const, eps_s, ← elt_eq]⟩

/-- A stencil vanishing at the zero mode is a multiple of `x - 1`. -/
theorem dvd_of_atZero {f : LaurentPolynomial F} (hf : atZero F f = 0) :
    ∃ f', f = (T 1 - 1) * f' := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have h2 : atZero F (Polynomial.toLaurent p) = 0 := by
    rw [hp, map_mul, hf, zero_mul]
  have hroot : p.IsRoot 1 := (LaurentPolynomial.eval₂_toLaurent (RingHom.id F) 1 p).symm.trans h2
  obtain ⟨p₁, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨Polynomial.toLaurent p₁ * T (-(n : ℤ)), ?_⟩
  have hT : (T (n : ℤ) : LaurentPolynomial F) * T (-(n : ℤ)) = 1 := by rw [← T_add]; simp
  have hp' : Polynomial.toLaurent ((X - C 1) * p₁) = (T 1 - 1) * Polynomial.toLaurent p₁ := by
    simp
  calc f = f * (T (n : ℤ) * T (-(n : ℤ))) := by rw [hT, mul_one]
    _ = (f * T n) * T (-(n : ℤ)) := by rw [mul_assoc]
    _ = _ := by rw [← hp, hp', mul_assoc]

/-- The kernel of the value on the fibre is the multiples of `δ`. -/
theorem exists_delta_mul {y : Norm q} (hy : eps hq0 hq1 y = 0) : ∃ y', y = deltaN hq0 * y' := by
  obtain ⟨f, g, rfl⟩ := exists_form hq0 hq1 y
  have h : eps hq0 hq1 (psi hq0 f + psi hq0 g * sN q) =
      (⟨atZero F f, atZero F g⟩ : Fib q) := by
    rw [map_add, map_mul, eps_psi, eps_psi, eps_s]
    ext <;> simp [rE]
  rw [h] at hy
  have h1 : atZero F f = 0 := congrArg QuadraticAlgebra.re hy
  have h2 : atZero F g = 0 := congrArg QuadraticAlgebra.im hy
  obtain ⟨f', rfl⟩ := dvd_of_atZero h1
  obtain ⟨g', rfl⟩ := dvd_of_atZero h2
  refine ⟨psi hq0 f' + psi hq0 g' * sN q, ?_⟩
  have hd : psi hq0 (T 1 - 1) = deltaN hq0 := by
    rw [map_sub, psi_T_one, map_one, deltaN]
  simp only [map_mul, hd]
  ring

/-- On the fibre, `σ` is conjugation. -/
theorem eps_sigma (y : Norm q) : eps hq0 hq1 (sigma hq1 y) = star (eps hq0 hq1 y) := by
  have h : ((eps hq0 hq1).comp (sigma hq1)) = (starRingEnd (Fib q)).comp (eps hq0 hq1) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (poles q))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, map_C, sigma_const, eps_const, starRingEnd_apply]
      ext <;> simp
    · have hi := congrArg (eps hq0 hq1) (s1_mul_inv (q := q))
      simp only [map_mul, map_sub, map_one, eps_s] at hi
      have hX : algebraMap F[X] (Norm q) X = sN q := rfl
      simp only [RingHom.comp_apply, hX, sigma_s, eps_s, starRingEnd_apply, sP, map_mul, map_sub,
        eps_qN]
      have hs : star (rE : Fib q) = -rE := by ext <;> simp [rE]
      rw [hs]
      linear_combination (-(rE : Fib q)) * hi + eps hq0 hq1 (invS1 q) * rE_mul_self (q := q)
  exact RingHom.congr_fun h y

end Artform.Scores.Leapfrog
