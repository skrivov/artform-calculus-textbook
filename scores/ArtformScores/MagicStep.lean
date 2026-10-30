import ArtformScores.LeapfrogClasses
import ArtformScores.Steinberg

/-!
# The magic step

The ledger's T8 at `κλ = 1`, finding 057, Theorem S3.5. The phase is `x + 1/x`, so the curve is two
light cones `λ = x` and `λ = 1/x` crossing at `x = 1` and `x = -1`, and `t² - 4` is a square: the
correspondence with ideals of T7 does not apply. A left eigenvector of `x`, made primitive and
completed to a basis, brings every law to `[[x, 0], [w, 1/x]]`, and `w` matters only through its
values at the crossings, up to `(f, ±f)`.
-/

namespace Artform.Scores.Leapfrog

open Polynomial
open LaurentPolynomial (T T_add T_zero)
open Matrix (SpecialLinearGroup)

variable {F : Type*} [Field F]

theorem atPi_C (r : F) : atPi F (LaurentPolynomial.C r) = r := LaurentPolynomial.eval₂_C _ _ r

theorem atPi_T (n : ℤ) : atPi F (T n) = (((-1 : Fˣ) ^ n : Fˣ) : F) :=
  LaurentPolynomial.eval₂_T _ _ n

theorem atPi_T_one : atPi F (T 1) = -1 := by
  rw [atPi_T, zpow_one]
  simp

theorem atPi_T_neg_one : atPi F (T (-1)) = -1 := by
  rw [atPi_T, zpow_neg, zpow_one]
  simp

/-- A stencil vanishing at `x = -1` is a multiple of `x + 1`. -/
theorem dvd_of_atPi {f : LaurentPolynomial F} (hf : atPi F f = 0) :
    ∃ f', f = (T 1 + 1) * f' := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have h2 : atPi F (Polynomial.toLaurent p) = 0 := by
    rw [hp, map_mul, hf, zero_mul]
  have hroot : p.IsRoot (-1) :=
    (LaurentPolynomial.eval₂_toLaurent (RingHom.id F) (-1) p).symm.trans h2
  obtain ⟨p₁, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨Polynomial.toLaurent p₁ * T (-(n : ℤ)), ?_⟩
  have hT : (T (n : ℤ) : LaurentPolynomial F) * T (-(n : ℤ)) = 1 := by rw [← T_add]; simp
  have hp' : Polynomial.toLaurent ((X - C (-1)) * p₁) = (T 1 + 1) * Polynomial.toLaurent p₁ := by
    simp
  calc f = f * (T (n : ℤ) * T (-(n : ℤ))) := by rw [hT, mul_one]
    _ = (f * T n) * T (-(n : ℤ)) := by rw [mul_assoc]
    _ = _ := by rw [← hp, hp', mul_assoc]

/-- The two cones differ away from the crossings. -/
theorem T_sub_T_neg_ne : (T 1 - T (-1) : LaurentPolynomial F) ≠ 0 := by
  intro h
  have h' := congrArg (fun f : LaurentPolynomial F => f.coeff 1) (sub_eq_zero.mp h)
  simp only [LaurentPolynomial.T_apply] at h'
  norm_num at h'

theorem phaseT_one : phaseT (1 : F) = T 1 + T (-1) := by
  simp only [phaseT, stencilG, map_one, one_mul]
  ring

theorem phase_magicLaw (w : LaurentPolynomial F) : phase (magicLaw w) = phaseT (1 : F) := by
  rw [phaseT_one]
  simp [phase, magicLaw, Matrix.trace_fin_two]

/-- A nonzero pair over the stencils is a multiple of a primitive pair. -/
theorem exists_primitive {r0 r1 : LaurentPolynomial F} (h : r0 ≠ 0 ∨ r1 ≠ 0) :
    ∃ g u0 u1 α β : LaurentPolynomial F,
      g ≠ 0 ∧ r0 = g * u0 ∧ r1 = g * u1 ∧ α * u0 + β * u1 = 1 := by
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span {r0, r1})).principal
  have hg' : Ideal.span {r0, r1} = Ideal.span {g} := hg
  have h0 : r0 ∈ Ideal.span {g} := hg' ▸ Ideal.subset_span (by simp)
  have h1 : r1 ∈ Ideal.span {g} := hg' ▸ Ideal.subset_span (by simp)
  have hgm : g ∈ Ideal.span {r0, r1} := hg'.symm ▸ Ideal.mem_span_singleton_self g
  obtain ⟨u0, hu0⟩ := Ideal.mem_span_singleton'.mp h0
  obtain ⟨u1, hu1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨α, β, hab⟩ := Ideal.mem_span_pair.mp hgm
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hu0 hu1
    rcases h with h | h
    · exact h hu0.symm
    · exact h hu1.symm
  refine ⟨g, u0, u1, α, β, hg0, by rw [← hu0]; ring, by rw [← hu1]; ring, ?_⟩
  apply mul_left_cancel₀ hg0
  linear_combination α * hu0 + β * hu1 + hab

/-- Every law of the magic step is conjugate to the normal form. -/
theorem exists_magic (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F))
    (ht : phase L = phaseT (1 : F)) :
    ∃ (w : LaurentPolynomial F) (Pm Qm : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)),
      Pm * Qm = 1 ∧ L.1 = Pm * (magicLaw w).1 * Qm := by
  have hd := L.2
  rw [Matrix.det_fin_two] at hd
  have htr : L.1 0 0 + L.1 1 1 = T 1 + T (-1) := by
    rw [← phaseT_one, ← ht, phase, Matrix.trace_fin_two]
  have hxy := T_mul_T_neg (F := F)
  set a := L.1 0 0
  set b := L.1 0 1
  set c := L.1 1 0
  set d := L.1 1 1
  -- a row eigenvector of `x`
  obtain ⟨r0, r1, hr, he0, he1⟩ : ∃ r0 r1 : LaurentPolynomial F, (r0 ≠ 0 ∨ r1 ≠ 0) ∧
      r0 * a + r1 * c = T 1 * r0 ∧ r0 * b + r1 * d = T 1 * r1 := by
    by_cases hc : c = 0 ∧ a - T 1 = 0
    · refine ⟨d - T 1, -b, ?_, ?_, ?_⟩
      · by_contra hne
        simp only [not_or, not_not, neg_eq_zero] at hne
        -- `L = x I` would have determinant `x²`
        have ha : a = T 1 := sub_eq_zero.mp hc.2
        have hd' : d = T 1 := sub_eq_zero.mp hne.1
        rw [ha, hd', hne.2, zero_mul, sub_zero] at hd
        have h3 : (T 1 - T (-1) : LaurentPolynomial F) = 0 := by
          linear_combination T (-1) * hd - T 1 * hxy
        exact T_sub_T_neg_ne h3
      · linear_combination hd - T 1 * htr - hxy
      · ring
    · refine ⟨-c, a - T 1, ?_, ?_, ?_⟩
      · by_contra hne
        simp only [not_or, not_not, neg_eq_zero] at hne
        exact hc hne
      · ring
      · linear_combination hd - T 1 * htr - hxy
  obtain ⟨g, u0, u1, α, β, hg0, rfl, rfl, hab⟩ := exists_primitive hr
  have he0' : u0 * a + u1 * c = T 1 * u0 := by
    apply mul_left_cancel₀ hg0
    linear_combination he0
  have he1' : u0 * b + u1 * d = T 1 * u1 := by
    apply mul_left_cancel₀ hg0
    linear_combination he1
  have hAB : (-β * a + α * c) * u1 - (-β * b + α * d) * u0 = -T (-1) := by
    linear_combination α * he0' + β * he1' - (α * u0 + β * u1) * htr - T (-1) * hab
  refine ⟨(-β * a + α * c) * α + (-β * b + α * d) * β, !![α, -u1; β, u0], !![u0, u1; -β, α], ?_, ?_⟩
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    refine mat2_ext ?_ ?_ ?_ ?_
    · linear_combination hab
    · ring
    · ring
    · linear_combination hab
  · have hL : L.1 = !![a, b; c, d] := Matrix.eta_fin_two _
    have hPQ : !![α, -u1; β, u0] * !![u0, u1; -β, α] = (1 : Matrix (Fin 2) (Fin 2) _) := by
      rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      refine mat2_ext ?_ ?_ ?_ ?_
      · linear_combination hab
      · ring
      · ring
      · linear_combination hab
    have hQL : !![u0, u1; -β, α] * L.1 =
        (magicLaw ((-β * a + α * c) * α + (-β * b + α * d) * β)).1 * !![u0, u1; -β, α] := by
      rw [hL, magicLaw, Matrix.mul_fin_two, Matrix.mul_fin_two]
      refine mat2_ext ?_ ?_ ?_ ?_
      · linear_combination he0'
      · linear_combination he1'
      · linear_combination β * hAB - (-β * a + α * c) * hab
      · linear_combination (-α) * hAB - (-β * b + α * d) * hab
    rw [Matrix.mul_assoc, ← hQL, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]

theorem magic_val (w : LaurentPolynomial F) : (magicLaw w).1 = !![T 1, 0; w, T (-1)] := rfl

/-- Conjugate normal forms have values at the crossings related by `(f, ±f)`. -/
theorem magic_orbit {w w' : LaurentPolynomial F}
    {Pm Qm : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)} (hQP : Qm * Pm = 1)
    (h : (magicLaw w').1 = Pm * (magicLaw w).1 * Qm) :
    ∃ (f e : Fˣ), (e = 1 ∨ e = -1) ∧ atZero F w' = (f : F) * atZero F w ∧
      atPi F w' = (e : F) * (f : F) * atPi F w := by
  have hLP : (magicLaw w').1 * Pm = Pm * (magicLaw w).1 := by
    rw [h, Matrix.mul_assoc, hQP, Matrix.mul_one]
  have hP : Pm = !![Pm 0 0, Pm 0 1; Pm 1 0, Pm 1 1] := Matrix.eta_fin_two _
  generalize Pm 0 0 = p at hP
  generalize Pm 0 1 = r at hP
  generalize Pm 1 0 = s' at hP
  generalize Pm 1 1 = n at hP
  rw [magic_val, magic_val, hP, Matrix.mul_fin_two, Matrix.mul_fin_two] at hLP
  have e01 := congrFun (congrFun hLP 0) 1
  have e10 := congrFun (congrFun hLP 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.cons_val_fin_one, zero_mul, add_zero, mul_zero] at e01 e10
  have hr : r = 0 := by
    have h0 : r * (T 1 - T (-1)) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp h0).resolve_right T_sub_T_neg_ne
  -- `p` and `n` are units
  have hdet : Pm.det * Qm.det = 1 := by
    rw [← Matrix.det_mul, mul_eq_one_comm.mp hQP, Matrix.det_one]
  rw [hP, Matrix.det_fin_two_of, hr, zero_mul, sub_zero] at hdet
  have hpu : IsUnit p := IsUnit.of_mul_eq_one (n * Qm.det) (by rw [← mul_assoc]; exact hdet)
  have hnu : IsUnit n := IsUnit.of_mul_eq_one (p * Qm.det) (by
    rw [← mul_assoc, mul_comm n p]; exact hdet)
  obtain ⟨f₁, k₁, hp⟩ := units_laurent hpu.unit
  obtain ⟨f₂, k₂, hn⟩ := units_laurent hnu.unit
  rw [IsUnit.unit_spec] at hp hn
  have h1 := congrArg (atZero F) e10
  have h2 := congrArg (atPi F) e10
  simp only [map_add, map_mul, atZero_T, atPi_T_one, atPi_T_neg_one, mul_one, one_mul] at h1 h2
  rw [hp, hn] at h1 h2
  simp only [map_mul, atZero_C, atZero_T, atPi_C, atPi_T, mul_one] at h1 h2
  refine ⟨f₂ * f₁⁻¹, (-1) ^ (k₂ - k₁), ?_, ?_, ?_⟩
  · rcases Int.even_or_odd (k₂ - k₁) with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  · have hf₁ := f₁.ne_zero
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination h1
  · have hf₁ := f₁.ne_zero
    have he₁ := ((-1 : Fˣ) ^ k₁).ne_zero
    rw [zpow_sub, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val]
    field_simp
    linear_combination h2

/-- A stencil vanishing at both crossings is a multiple of `x - 1/x`. -/
theorem dvd_of_crossings (h2 : (2 : F) ≠ 0) {f : LaurentPolynomial F} (h1 : atZero F f = 0)
    (hm : atPi F f = 0) : ∃ f', f = f' * (T 1 - T (-1)) := by
  obtain ⟨f₁, rfl⟩ := dvd_of_atZero h1
  rw [map_mul, map_sub, map_one, atPi_T_one] at hm
  have h3 : atPi F f₁ = 0 := by
    have h4 : (-1 - 1 : F) ≠ 0 := by
      intro h5
      apply h2
      linear_combination -h5
    exact (mul_eq_zero.mp hm).resolve_left h4
  obtain ⟨f₂, rfl⟩ := dvd_of_atPi h3
  refine ⟨f₂ * T 1, ?_⟩
  linear_combination f₂ * T_mul_T_neg (F := F)

/-- Values related by `(f, ±f)` give conjugate normal forms. -/
theorem magic_conj (h2 : (2 : F) ≠ 0) {w w' : LaurentPolynomial F} (f e : Fˣ)
    (he : e = 1 ∨ e = -1) (h1 : atZero F w' = (f : F) * atZero F w)
    (hm : atPi F w' = (e : F) * (f : F) * atPi F w) :
    ∃ Pm Qm : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F),
      Pm * Qm = 1 ∧ (magicLaw w').1 = Pm * (magicLaw w).1 * Qm := by
  have hf : (f : F) * (f : F)⁻¹ = 1 := mul_inv_cancel₀ f.ne_zero
  have hxy := T_mul_T_neg (F := F)
  obtain ⟨a, b, hab, ha1, ham⟩ : ∃ a b : LaurentPolynomial F, a * b = 1 ∧
      atZero F a = (f : F) ∧ atPi F a = (e : F) * (f : F) := by
    rcases he with rfl | rfl
    · refine ⟨LaurentPolynomial.C (f : F), LaurentPolynomial.C (f : F)⁻¹, ?_, atZero_C _, ?_⟩
      · rw [← map_mul, hf, map_one]
      · rw [atPi_C, Units.val_one, one_mul]
    · refine ⟨LaurentPolynomial.C (f : F) * T 1, LaurentPolynomial.C (f : F)⁻¹ * T (-1), ?_, ?_, ?_⟩
      · have : LaurentPolynomial.C (f : F) * LaurentPolynomial.C (f : F)⁻¹ = 1 := by
          rw [← map_mul, hf, map_one]
        linear_combination T 1 * T (-1) * this + hxy
      · rw [map_mul, atZero_C, atZero_T, mul_one]
      · rw [map_mul, atPi_C, atPi_T_one, Units.val_neg, Units.val_one]
        ring
  obtain ⟨s', hs⟩ := dvd_of_crossings h2 (f := w' - a * w)
    (by rw [map_sub, map_mul, ha1, h1, sub_self])
    (by rw [map_sub, map_mul, ham, hm, sub_self])
  have hPQ : !![1, 0; s', a] * !![1, 0; -s' * b, b] = (1 : Matrix (Fin 2) (Fin 2) _) := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    refine mat2_ext ?_ ?_ ?_ ?_
    · ring
    · ring
    · linear_combination (-s') * hab
    · linear_combination hab
  have hLP : (magicLaw w').1 * !![1, 0; s', a] = !![1, 0; s', a] * (magicLaw w).1 := by
    rw [magic_val, magic_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine mat2_ext ?_ ?_ ?_ ?_
    · ring
    · ring
    · linear_combination hs
    · ring
  refine ⟨_, _, hPQ, ?_⟩
  rw [← hLP, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-! ### The classes -/

theorem mem_signs {x : Fˣ} : x ∈ signs F ↔ x = 1 ∨ x = -1 := by
  rw [signs, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem ofPair_inl {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    ofPair α β = Sum.inl ((Units.mk0 β hβ / Units.mk0 α hα : Fˣ) : Fˣ ⧸ signs F) := by
  simp only [ofPair, hα, hβ, ↓reduceDIte]

theorem ofPair_left {α : F} (hα : α ≠ 0) : ofPair α (0 : F) = Sum.inr 0 := by
  simp only [ofPair, hα, ↓reduceDIte]

theorem ofPair_right {β : F} (hβ : β ≠ 0) : ofPair (0 : F) β = Sum.inr 1 := by
  simp only [ofPair, hβ, ↓reduceDIte, ↓reduceIte]

theorem ofPair_zero : ofPair (0 : F) (0 : F) = Sum.inr 2 := by
  simp only [ofPair, ↓reduceDIte, ↓reduceIte]

theorem ofPair_orbit (α β : F) (f e : Fˣ) (he : e = 1 ∨ e = -1) :
    ofPair ((f : F) * α) ((e : F) * (f : F) * β) = ofPair α β := by
  have hf := f.ne_zero
  have hee := e.ne_zero
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0
    · subst hβ
      simp only [mul_zero]
    · have h2 : (e : F) * (f : F) * β ≠ 0 := mul_ne_zero (mul_ne_zero hee hf) hβ
      rw [mul_zero, ofPair_right h2, ofPair_right hβ]
  · have h1 : (f : F) * α ≠ 0 := mul_ne_zero hf hα
    by_cases hβ : β = 0
    · subst hβ
      rw [mul_zero, ofPair_left h1, ofPair_left hα]
    · have h2 : (e : F) * (f : F) * β ≠ 0 := mul_ne_zero (mul_ne_zero hee hf) hβ
      rw [ofPair_inl h1 h2, ofPair_inl hα hβ]
      refine congrArg Sum.inl (QuotientGroup.eq.mpr ?_)
      have hx : (Units.mk0 ((e : F) * (f : F) * β) h2 / Units.mk0 ((f : F) * α) h1)⁻¹ *
          (Units.mk0 β hβ / Units.mk0 α hα) = e⁻¹ := by
        ext
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val,
          Units.val_mk0]
        field_simp
      rw [hx]
      exact inv_mem (mem_signs.mpr he)

/-- Pairs with one class are related by `(f, ±f)`. -/
theorem orbit_of_ofPair {α β α' β' : F} (h : ofPair α β = ofPair α' β') :
    ∃ f e : Fˣ, (e = 1 ∨ e = -1) ∧ α' = (f : F) * α ∧ β' = (e : F) * (f : F) * β := by
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0
    · subst hβ
      rw [ofPair_zero] at h
      by_cases hα' : α' = 0
      · subst hα'
        by_cases hβ' : β' = 0
        · subst hβ'
          exact ⟨1, 1, Or.inl rfl, by simp, by simp⟩
        · rw [ofPair_right hβ'] at h
          exact absurd h (by simp)
      · by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_left hα'] at h
          exact absurd h (by simp)
        · rw [ofPair_inl hα' hβ'] at h
          exact absurd h (by simp)
    · rw [ofPair_right hβ] at h
      by_cases hα' : α' = 0
      · subst hα'
        by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_zero] at h
          exact absurd h (by simp)
        · refine ⟨Units.mk0 (β' / β) (div_ne_zero hβ' hβ), 1, Or.inl rfl, by simp, ?_⟩
          simp only [Units.val_one, one_mul, Units.val_mk0]
          field_simp
      · by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_left hα'] at h
          exact absurd h (by simp)
        · rw [ofPair_inl hα' hβ'] at h
          exact absurd h (by simp)
  · by_cases hβ : β = 0
    · subst hβ
      rw [ofPair_left hα] at h
      by_cases hα' : α' = 0
      · subst hα'
        by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_zero] at h
          exact absurd h (by simp)
        · rw [ofPair_right hβ'] at h
          exact absurd h (by simp)
      · by_cases hβ' : β' = 0
        · subst hβ'
          refine ⟨Units.mk0 (α' / α) (div_ne_zero hα' hα), 1, Or.inl rfl, ?_, by simp⟩
          simp only [Units.val_mk0]
          field_simp
        · rw [ofPair_inl hα' hβ'] at h
          exact absurd h (by simp)
    · rw [ofPair_inl hα hβ] at h
      by_cases hα' : α' = 0
      · subst hα'
        by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_zero] at h
          exact absurd h (by simp)
        · rw [ofPair_right hβ'] at h
          exact absurd h (by simp)
      · by_cases hβ' : β' = 0
        · subst hβ'
          rw [ofPair_left hα'] at h
          exact absurd h (by simp)
        · rw [ofPair_inl hα' hβ'] at h
          have hm := QuotientGroup.eq.mp (Sum.inl_injective h)
          have he := mem_signs.mp hm
          have hee : ∃ e : Fˣ, (e = 1 ∨ e = -1) ∧ (Units.mk0 β hβ / Units.mk0 α hα)⁻¹ *
              (Units.mk0 β' hβ' / Units.mk0 α' hα') = e := ⟨_, he, rfl⟩
          obtain ⟨e, he', hval⟩ := hee
          have hval' := congrArg (Units.val) hval
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val,
            Units.val_mk0] at hval'
          refine ⟨Units.mk0 (α' / α) (div_ne_zero hα' hα), e, he', ?_, ?_⟩
          · simp only [Units.val_mk0]
            field_simp
          · simp only [Units.val_mk0]
            rw [← hval']
            field_simp

/-- Every class is the class of a pair. -/
theorem ofPair_surjective (c : (Fˣ ⧸ signs F) ⊕ Fin 3) : ∃ α β : F, ofPair α β = c := by
  rcases c with c | c
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨1, x, ?_⟩
    rw [ofPair_inl one_ne_zero x.ne_zero]
    refine congrArg Sum.inl (congrArg _ ?_)
    ext
    simp
  · fin_cases c
    · exact ⟨1, 0, ofPair_left one_ne_zero⟩
    · exact ⟨0, 1, ofPair_right one_ne_zero⟩
    · exact ⟨0, 0, ofPair_zero⟩

/-- `L` is conjugate to the normal form of `w`. -/
def MagicOf (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F))
    (w : LaurentPolynomial F) : Prop :=
  ∃ Pm Qm : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F),
    Pm * Qm = 1 ∧ L.1 = Pm * (magicLaw w).1 * Qm

open Classical in
/-- The class of a law of the magic step. -/
noncomputable def magicMap (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) :
    (Fˣ ⧸ signs F) ⊕ Fin 3 :=
  if h : ∃ w, MagicOf L w then ofPair (atZero F h.choose) (atPi F h.choose) else Sum.inr 2

variable {L L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)}
  {w w' : LaurentPolynomial F}

/-- Two normal forms of one law have one class. -/
theorem magicOf_unique (h : MagicOf L w) (h' : MagicOf L w') :
    ofPair (atZero F w) (atPi F w) = ofPair (atZero F w') (atPi F w') := by
  obtain ⟨P, Q, hPQ, hL⟩ := h
  obtain ⟨P', Q', hPQ', hL'⟩ := h'
  have hQP := mul_eq_one_comm.mp hPQ
  have hQP' := mul_eq_one_comm.mp hPQ'
  -- `L_w = (Q P') L_w' (Q' P)`
  have h1 : (magicLaw w).1 = (Q * P') * (magicLaw w').1 * (Q' * P) := by
    calc (magicLaw w).1 = Q * (P * (magicLaw w).1 * Q) * P := by
          simp only [Matrix.mul_assoc]
          rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      _ = Q * (P' * (magicLaw w').1 * Q') * P := by rw [← hL, hL']
      _ = _ := by simp only [Matrix.mul_assoc]
  have hinv : (Q' * P) * (Q * P') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPQ, Matrix.one_mul, hQP']
  obtain ⟨f, e, he, h3, h4⟩ := magic_orbit hinv h1
  rw [h3, h4]
  exact ofPair_orbit _ _ f e he

theorem magicMap_eq (h : MagicOf L w) : magicMap L = ofPair (atZero F w) (atPi F w) := by
  have hex : ∃ w, MagicOf L w := ⟨w, h⟩
  have h1 : magicMap L = ofPair (atZero F hex.choose) (atPi F hex.choose) := by
    simp only [magicMap, hex, ↓reduceDIte]
  exact h1.trans (magicOf_unique hex.choose_spec h)

/-- Processing keeps the normal form. -/
theorem MagicOf.conj (h : MagicOf L w) (P Q : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))
    (hPQ : P * Q = 1) (hL : L'.1 = P * L.1 * Q) : MagicOf L' w := by
  obtain ⟨P₁, Q₁, h1, h2⟩ := h
  refine ⟨P * P₁, Q₁ * Q, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₁, h1, Matrix.one_mul, hPQ]
  · rw [hL, h2]
    simp only [Matrix.mul_assoc]

theorem magicMap_eq_iff (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT (1 : F))
    (ht' : phase L' = phaseT (1 : F)) :
    magicMap L = magicMap L' ↔
      ∃ P : GL (Fin 2) (LaurentPolynomial F), (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
        (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * L *
          ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
            Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) := by
  obtain ⟨w, Pm, Qm, hPQ, hL⟩ := exists_magic L ht
  obtain ⟨w', Pm', Qm', hPQ', hL'⟩ := exists_magic L' ht'
  have hm : MagicOf L w := ⟨Pm, Qm, hPQ, hL⟩
  have hm' : MagicOf L' w' := ⟨Pm', Qm', hPQ', hL'⟩
  constructor
  · intro h
    rw [magicMap_eq hm, magicMap_eq hm'] at h
    obtain ⟨f, e, he, h3, h4⟩ := orbit_of_ofPair h
    obtain ⟨P₂, Q₂, hPQ₂, hL₂⟩ := magic_conj h2 f e he h3 h4
    have hQP := mul_eq_one_comm.mp hPQ
    have hQP₂ := mul_eq_one_comm.mp hPQ₂
    have hQP' := mul_eq_one_comm.mp hPQ'
    -- `L' = (P' P₂ Q) L (P Q₂ Q')`
    have e1 : (Pm' * P₂ * Qm) * (Pm * Q₂ * Qm') = 1 := by
      calc (Pm' * P₂ * Qm) * (Pm * Q₂ * Qm') = Pm' * (P₂ * (Qm * Pm) * Q₂) * Qm' := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQP, Matrix.mul_one, hPQ₂, Matrix.mul_one, hPQ']
    have e2 : (Pm * Q₂ * Qm') * (Pm' * P₂ * Qm) = 1 := mul_eq_one_comm.mp e1
    refine ⟨⟨Pm' * P₂ * Qm, Pm * Q₂ * Qm', e1, e2⟩, ?_⟩
    change L'.1 = (Pm' * P₂ * Qm) * L.1 * (Pm * Q₂ * Qm')
    rw [hL', hL₂, hL]
    calc Pm' * (P₂ * (magicLaw w).1 * Q₂) * Qm' = Pm' * P₂ * (magicLaw w).1 * Q₂ * Qm' := by
          simp only [Matrix.mul_assoc]
      _ = Pm' * P₂ * (Qm * Pm) * (magicLaw w).1 * (Qm * Pm) * Q₂ * Qm' := by
          rw [hQP, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro ⟨P, hP⟩
    have hPQ₁ : (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) *
        ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
          Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [magicMap_eq hm, magicMap_eq (hm.conj _ _ hPQ₁ hP)]

/-- Every class is a law's. -/
theorem exists_magicLaw (h2 : (2 : F) ≠ 0) (c : (Fˣ ⧸ signs F) ⊕ Fin 3) :
    ∃ w : LaurentPolynomial F, ofPair (atZero F w) (atPi F w) = c := by
  obtain ⟨α, β, rfl⟩ := ofPair_surjective c
  refine ⟨LaurentPolynomial.C ((α + β) / 2) + LaurentPolynomial.C ((α - β) / 2) * T 1, ?_⟩
  congr 1
  · simp only [map_add, map_mul, atZero_C, atZero_T]
    field_simp
    ring
  · simp only [map_add, map_mul, atPi_C, atPi_T_one]
    field_simp
    ring

theorem magicMap_magicLaw (w : LaurentPolynomial F) :
    magicMap (magicLaw w) = ofPair (atZero F w) (atPi F w) :=
  magicMap_eq ⟨1, 1, by simp, by simp⟩

/-- The value of a law at a crossing is `± I` exactly when `w` vanishes there. -/
theorem map_eq_scalar_iff (φ : LaurentPolynomial F →+* F) (c : F) (hx : φ (T 1) = c)
    (hy : φ (T (-1)) = c) (h : MagicOf L w) :
    L.1.map φ = c • (1 : Matrix (Fin 2) (Fin 2) F) ↔ φ w = 0 := by
  obtain ⟨P, Q, hPQ, hL⟩ := h
  have hQP := mul_eq_one_comm.mp hPQ
  have hmap : ∀ A B : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F),
      (A * B).map φ = A.map φ * B.map φ := fun A B => Matrix.map_mul
  have hone : (1 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map φ = 1 :=
    map_one φ.mapMatrix
  have hP1 : P.map φ * Q.map φ = 1 := by rw [← hmap, hPQ, hone]
  have hQ1 : Q.map φ * P.map φ = 1 := by rw [← hmap, hQP, hone]
  have hLw : (magicLaw w).1.map φ = !![c, 0; φ w, c] := by
    rw [magic_val]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact hx
    · exact map_zero φ
    · rfl
    · exact hy
  have hLhat : L.1.map φ = P.map φ * (magicLaw w).1.map φ * Q.map φ := by
    rw [hL, hmap, hmap]
  constructor
  · intro h0
    have h1 : (magicLaw w).1.map φ = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc (magicLaw w).1.map φ = Q.map φ * (L.1.map φ) * P.map φ := by
            rw [hLhat]
            calc _ = (Q.map φ * P.map φ) * (magicLaw w).1.map φ * (Q.map φ * P.map φ) := by
                  rw [hQ1, Matrix.one_mul, Matrix.mul_one]
              _ = _ := by simp only [Matrix.mul_assoc]
        _ = c • (Q.map φ * P.map φ) := by
            rw [h0, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
        _ = _ := by rw [hQ1]
    rw [hLw] at h1
    simpa using congrFun (congrFun h1 1) 0
  · intro h0
    have h1 : (magicLaw w).1.map φ = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hLw, h0]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp
    rw [hLhat, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP1]

theorem atZero_one_iff (h : MagicOf L w) :
    L.1.map (atZero F) = (1 : Matrix (Fin 2) (Fin 2) F) ↔ atZero F w = 0 := by
  have := map_eq_scalar_iff (atZero F) 1 (atZero_T 1) (atZero_T (-1)) h
  rwa [one_smul] at this

theorem atPi_neg_one_iff (h : MagicOf L w) :
    L.1.map (atPi F) = -(1 : Matrix (Fin 2) (Fin 2) F) ↔ atPi F w = 0 := by
  have := map_eq_scalar_iff (atPi F) (-1) atPi_T_one atPi_T_neg_one h
  rwa [neg_smul, one_smul] at this

/-! ### The trivial class and the count -/

/-- The companion tick is the normal form of `w = 1`. -/
theorem magicOf_companion : MagicOf (companionLaw (1 : F)) 1 := by
  have hxy := T_mul_T_neg (F := F)
  refine ⟨!![1, -T 1; 0, 1], !![1, T 1; 0, 1], ?_, ?_⟩
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    refine mat2_ext ?_ ?_ ?_ ?_ <;> ring
  · rw [magic_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    change !![0, -1; 1, phaseT (1 : F)] = _
    rw [phaseT_one]
    refine mat2_ext ?_ ?_ ?_ ?_
    · ring
    · linear_combination hxy
    · ring
    · ring

/-- A cyclic vector conjugates a law to the companion tick. -/
theorem magicOf_of_cyclic (ht : phase L = phaseT (1 : F)) {v : Fin 2 → LaurentPolynomial F}
    (hv : IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det) :
    MagicOf L 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe L
  rw [Matrix.det_fin_two] at hdet
  have htr : (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 0 0 +
      (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 1 = phaseT (1 : F) := by
    rw [← ht, phase, Matrix.trace_fin_two]
  set Pm := cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v with hPm
  have hmat : (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * Pm =
      Pm * companion (phaseT (1 : F)) := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [hPm, cyclicMatrix, companion, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
    · linear_combination ((L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 0 0 * v 0 +
        (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 0 1 * v 1) * htr - v 0 * hdet
    · linear_combination ((L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 0 * v 0 +
        (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 1 * v 1) * htr - v 1 * hdet
  obtain ⟨Pu, hPu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hv
  have hPQ : Pm * ((Pu⁻¹ : (Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))ˣ) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) = 1 := by
    rw [← hPu, Units.mul_inv]
  refine magicOf_companion.conj Pm _ hPQ ?_
  change L.1 = Pm * companion (phaseT (1 : F)) * _
  rw [← hmat, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-- The class of the companion tick. -/
theorem magicMap_companion : magicMap (companionLaw (1 : F)) = Sum.inl 1 := by
  rw [magicMap_eq magicOf_companion, map_one, map_one, ofPair_inl one_ne_zero one_ne_zero]
  refine congrArg Sum.inl ?_
  have : (Units.mk0 (1 : F) one_ne_zero / Units.mk0 (1 : F) one_ne_zero : Fˣ) = 1 := by
    ext
    simp
  rw [this]
  rfl

theorem magicMap_eq_inl_one_iff (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT (1 : F)) :
    magicMap L = Sum.inl 1 ↔ ∃ v : Fin 2 → LaurentPolynomial F,
      IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det := by
  constructor
  · intro h
    have h1 : magicMap (companionLaw (1 : F)) = magicMap L := by rw [magicMap_companion, h]
    obtain ⟨P, hP⟩ := (magicMap_eq_iff h2 phase_companionLaw ht).mp h1
    exact cyclic_of_conj P hP
  · rintro ⟨v, hv⟩
    rw [magicMap_eq (magicOf_of_cyclic ht hv), map_one, map_one,
      ofPair_inl one_ne_zero one_ne_zero]
    refine congrArg Sum.inl ?_
    have : (Units.mk0 (1 : F) one_ne_zero / Units.mk0 (1 : F) one_ne_zero : Fˣ) = 1 := by
      ext
      simp
    rw [this]
    rfl

theorem card_signs (h2 : (2 : F) ≠ 0) : Nat.card (signs F) = 2 := by
  rw [signs, Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by simp) ?_
  intro h
  have h1 := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at h1
  apply h2
  linear_combination -h1

/-- On a dial there are `(p - 1) / 2 + 3` classes. -/
theorem card_magic_classes [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card ((Fˣ ⧸ signs F) ⊕ Fin 3) = (Nat.card F - 1) / 2 + 3 := by
  have h1 := Subgroup.card_mul_index (signs F)
  rw [card_signs h2, Nat.card_units F] at h1
  have h3 : (signs F).index = Nat.card (Fˣ ⧸ signs F) := rfl
  rw [h3] at h1
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, ← h1,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-! ### The theorems -/

/-- **T8** (the magic step). -/
@[ledger "T8"]
theorem magicClasses : Statement.magicClasses := by
  intro F _ h2
  refine ⟨magicMap, ?_, ?_, exists_magicLaw h2, ?_, ?_, ?_⟩
  · intro L L' ht ht'
    exact magicMap_eq_iff h2 ht ht'
  · exact fun w => ⟨phase_magicLaw w, magicMap_magicLaw w⟩
  · intro L ht
    obtain ⟨w, Pm, Qm, hPQ, hL⟩ := exists_magic L ht
    exact ⟨w, ⟨Pm, Qm, hPQ, mul_eq_one_comm.mp hPQ⟩, hL⟩
  · rintro L w ⟨P, hP⟩
    have h : MagicOf L w := ⟨P, ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)), by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one], hP⟩
    exact ⟨atZero_one_iff h, atPi_neg_one_iff h⟩
  · intro L ht
    exact magicMap_eq_inl_one_iff h2 ht

/-- **T8** (the count at the magic step). -/
@[ledger "T8"]
theorem magicCount : Statement.magicCount := by
  intro F _ _ h2
  rw [← card_magic_classes h2]
  let f : Quotient (processingSetoid (phaseT (1 : F))) → (Fˣ ⧸ signs F) ⊕ Fin 3 :=
    Quotient.lift (fun L => magicMap L.1) (fun L L' h => (magicMap_eq_iff h2 L.2 L'.2).mpr h)
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h L' =>
        intro h
        exact Quotient.sound ((magicMap_eq_iff h2 L.2 L'.2).mp h)
  · intro c
    obtain ⟨w, hw⟩ := exists_magicLaw h2 c
    exact ⟨Quotient.mk _ ⟨magicLaw w, phase_magicLaw w⟩, (magicMap_magicLaw w).trans hw⟩

/-- **T8** (the schemes at the magic step). -/
@[ledger "T8"]
theorem magicSchemes : Statement.magicSchemes := by
  intro F _ κ ℓ h2 hq
  have hκ : κ ≠ 0 := left_ne_zero_of_mul (by rw [hq]; exact one_ne_zero)
  have hℓ : ℓ ≠ 0 := right_ne_zero_of_mul (by rw [hq]; exact one_ne_zero)
  refine ⟨?_, rfl, ?_⟩
  · intro w hw
    have ht := phase_face h2 κ ℓ hw
    have ht' := phase_link h2 κ ℓ hw
    rw [hq] at ht ht'
    refine ⟨ht, cyclic_face h2 hκ ℓ hw, ht', ?_, ?_⟩
    · exact congrArg Subtype.val (link_at_zero κ ℓ w)
    · intro h0
      have hD : atPi F (diffD F) = 2 := by
        simp only [diffD, map_sub, map_one, atPi_T_one]
        ring
      have hDs : atPi F (diffDs F) = 2 := by
        simp only [diffDs, map_sub, map_one, atPi_T_neg_one]
        ring
      have hoff := offdiag_schemes (A := fun w => LaurentPolynomial.C (w * κ) * diffDs F)
        (B := fun w => LaurentPolynomial.C (-(w * ℓ)) * diffD F) (f := linkStep κ ℓ)
        (fun _ => rfl) (fun _ => rfl) hw
      rcases hoff with h1 | h1
      · have h3 := congrFun (congrFun h0 0) 1
        simp only [Matrix.map_apply, h1, Matrix.neg_apply, Matrix.one_apply_ne (zero_ne_one),
          neg_zero, map_mul, atPi_C, hD] at h3
        have h4 : -(1 * ℓ) * 2 ≠ 0 := by
          simpa using ⟨hℓ, h2⟩
        exact h4 h3
      · have h3 := congrFun (congrFun h0 1) 0
        simp only [Matrix.map_apply, h1, Matrix.neg_apply, Matrix.one_apply_ne (one_ne_zero),
          neg_zero, map_mul, atPi_C, hDs] at h3
        have h4 : (1 * κ) * 2 ≠ 0 := by
          simpa using ⟨hκ, h2⟩
        exact h4 h3
  · simp only [map_zero]
    exact ofPair_zero

end Artform.Scores.Leapfrog
