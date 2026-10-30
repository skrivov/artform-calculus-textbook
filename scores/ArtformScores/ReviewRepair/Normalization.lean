import ArtformScores.ReviewRepair.Statements

/-! # The integral birational normalization of the leapfrog curve -/

namespace Artform.Scores.Leapfrog
open Polynomial
open LaurentPolynomial (T)
variable {F : Type} [Field F] {q : F} (hq0 : q ≠ 0) (hq1 : q ≠ 1)

/-- The phase curve embedded in its proposed normalization. -/
noncomputable def normalizationMap : curveRing (phaseT q) →+* Norm q :=
  AdjoinRoot.lift (psi hq0) (lamN hq0) (by
    simpa only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul,
      eval₂_X, eval₂_C, eval₂_one, pow_two] using
      lam_root hq0)

@[simp] theorem normalizationMap_base (a : LaurentPolynomial F) :
    normalizationMap hq0 (algebraMap _ (curveRing (phaseT q)) a) = psi hq0 a := by
  exact AdjoinRoot.lift_of _

@[simp] theorem normalizationMap_eig : normalizationMap hq0 (eig (phaseT q)) = lamN hq0 :=
  AdjoinRoot.lift_root _

/-- The embedding is injective, not merely a parametrization on field points. -/
theorem normalizationMap_injective (hq1 : q ≠ 1) : Function.Injective (normalizationMap hq0) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨f, g, rfl⟩ := curve_decomp (phaseT q) a
  simp only [map_add, map_mul, normalizationMap_base, normalizationMap_eig] at ha
  have hf : psi hq0 (f + g) + psi hq0 (g * deltaS) * sN q = 0 := by
    simp only [map_add, map_mul, psi_delta', lamN] at ha ⊢
    linear_combination ha
  obtain ⟨hf0, hg0⟩ := form_eq_zero hq0 hq1 hf
  have hd : (deltaS : LaurentPolynomial F) ≠ 0 := sub_ne_zero.mpr T_one_ne_one
  have hg : g = 0 := (mul_eq_zero.mp hg0).resolve_right hd
  simp only [hg, add_zero] at hf0
  simp [hf0, hg]

/-- Every element of the proposed normalization is integral over the curve ring. -/
theorem normalizationMap_integral (hq1 : q ≠ 1) (z : Norm q) :
    ∃ p : Polynomial (curveRing (phaseT q)), p.Monic ∧
      eval₂ (normalizationMap hq0) z p = 0 := by
  obtain ⟨f, g, rfl⟩ := exists_form hq0 hq1 z
  let a := algebraMap (LaurentPolynomial F) (curveRing (phaseT q))
  refine ⟨X ^ 2 - C (a (2 * f + g * kap1 q)) * X +
    C (a (f ^ 2 + f * g * kap1 q - g ^ 2 * kap0 q)), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C, eval₂_mul]
  simp only [a, normalizationMap_base, map_add, map_mul, map_sub, map_pow, map_ofNat]
  linear_combination (psi hq0 g) ^ 2 * s_sq hq0

/-- Every element is a fraction of curve elements, with the common denominator
`x - 1`. Thus the integral embedding is birational. -/
theorem normalizationMap_fraction (hq1 : q ≠ 1) (z : Norm q) :
    ∃ a d : curveRing (phaseT q), d ≠ 0 ∧
      normalizationMap hq0 d * z = normalizationMap hq0 a := by
  obtain ⟨f, g, rfl⟩ := exists_form hq0 hq1 z
  let a := algebraMap (LaurentPolynomial F) (curveRing (phaseT q))
  refine ⟨a (deltaS * f - g) + a g * eig (phaseT q), a deltaS, ?_, ?_⟩
  · intro h
    have e := congrArg (normalizationMap hq0) h
    simp only [a, normalizationMap_base, map_zero] at e
    exact T_one_ne_one (sub_eq_zero.mp ((injective_iff_map_eq_zero _).mp
      (psi_injective hq0) _ e))
  · simp only [a, map_add, map_mul, normalizationMap_base, normalizationMap_eig,
      map_sub, lamN, ← psi_delta']
    ring

/-- The only singular point of the affine torus curve is `(1,1)`. The three
zero equations are the curve equation and its two formal partial derivatives. -/
theorem unique_singularity (hq0 : q ≠ 0) (hq1 : q ≠ 1) (h2 : (2 : F) ≠ 0)
    (x lam : F) (hx : x ≠ 0) (_hlam : lam ≠ 0) :
    (x * (lam - 1)^2 - q * (x - 1)^2 * lam = 0 ∧
     (lam - 1)^2 - 2 * q * (x - 1) * lam = 0 ∧
     2 * x * (lam - 1) - q * (x - 1)^2 = 0) ↔ x = 1 ∧ lam = 1 := by
  constructor
  · rintro ⟨hF, hX, hL⟩
    have hl : (lam - 1) * (lam + 1) = 0 := by
      apply (mul_eq_zero.mp (show x * ((lam - 1) * (lam + 1)) = 0 by
        linear_combination lam * hL - hF)).resolve_left hx
    rcases mul_eq_zero.mp hl with hl | hl
    · have hlam : lam = 1 := sub_eq_zero.mp hl
      subst lam
      have hs : (x - 1) * (x - 1) = 0 := by
        apply (mul_eq_zero.mp (show q * ((x - 1) * (x - 1)) = 0 by
          linear_combination -hF)).resolve_left hq0
      exact ⟨sub_eq_zero.mp (mul_self_eq_zero.mp hs), rfl⟩
    · have hlam : lam = -1 := by linear_combination hl
      subst lam
      have h4 : (2 * 2 : F) * (x + 1) = 0 := by
        linear_combination 2 * hF - (x - 1) * hX
      have hx1 : x = -1 := by
        have := (mul_eq_zero.mp h4).resolve_left (mul_ne_zero h2 h2)
        linear_combination this
      subst x
      have h4q : (2 * 2 : F) * (1 - q) = 0 := by linear_combination hX
      have hq : q = 1 := by
        have := (mul_eq_zero.mp h4q).resolve_left (mul_ne_zero h2 h2)
        linear_combination -this
      exact False.elim (hq1 hq)
  · rintro ⟨rfl, rfl⟩
    simp

end Artform.Scores.Leapfrog

namespace Artform.Scores

/-- **T8** (the actual normalization and the unique ordinary node). -/
@[ledger "T8"]
theorem leapfrogNormalization : Statement.leapfrogNormalization := by
  refine ⟨Leapfrog.leapfrogCurve, ?_⟩
  intro F _ q h2 hq0 hq1
  refine ⟨inferInstance, ⟨Leapfrog.normalizationMap hq0,
    Leapfrog.normalizationMap_injective hq0 hq1,
    Leapfrog.normalizationMap_integral hq0 hq1,
    Leapfrog.normalizationMap_fraction hq0 hq1, ?_⟩,
    Leapfrog.unique_singularity hq0 hq1 h2, (by intros; ring),
    Polynomial.separable_X_pow_sub_C q h2 hq0, ?_⟩
  · rw [Leapfrog.normalizationMap_eig, Leapfrog.normalizationMap_base]
    simp [Leapfrog.lamN, ← Leapfrog.psi_delta', Leapfrog.deltaS]
  · intro h hh
    have hh0 : h ≠ 0 := by
      intro e
      apply hq0
      rw [e, zero_mul] at hh
      exact hh.symm
    refine ⟨?_, fun u v => ?_⟩
    · intro e
      exact mul_ne_zero h2 hh0 (by linear_combination e)
    · rw [← hh]
      ring

/-! ## Non-vacuity -/

/-- At the running pull `q = 2` over the rationals the normalization exists
as an injective integral birational embedding in the specified localized line. -/
example : ∃ ι : curveRing (Leapfrog.phaseT (2 : ℚ)) →+* Leapfrog.Norm (2 : ℚ),
    Function.Injective ι ∧ ∀ z : Leapfrog.Norm (2 : ℚ),
      ∃ a d : curveRing (Leapfrog.phaseT (2 : ℚ)), d ≠ 0 ∧ ι d * z = ι a := by
  obtain ⟨-, ⟨ι, hi, -, hf, -⟩, -⟩ := leapfrogNormalization.2 ℚ 2
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨ι, hi, hf⟩

end Artform.Scores
