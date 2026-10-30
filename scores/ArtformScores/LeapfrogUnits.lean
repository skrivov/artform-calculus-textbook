import ArtformScores.LeapfrogCurve

/-!
# The group of the glued classes

`U` is the norm-one group of the fibre `E = F[r]/(r² - q)`, and `z ↦ z / z̄` identifies `E^×/F^×`
with it (Hilbert 90). The units of the normalization are the constants times powers of `s`,
`s - 1` and `s - q`, whose images are `-1`, `ρ` and `-ρ`.
-/

namespace Artform.Scores.Leapfrog

open Polynomial
open scoped QuadraticAlgebra

variable {F : Type*} [Field F] {q : F}

/-- The value of `theta`, as an element of the fibre. -/
noncomputable abbrev thetaV (z : (Fib q)ˣ) : Fib q := ((theta z : U q) : (Fib q)ˣ)

theorem thetaV_mul_star (z : (Fib q)ˣ) : thetaV z * star (z : Fib q) = z := by
  have h : (star z : (Fib q)ˣ) = star z := rfl
  have h2 := Units.inv_mul (star z)
  simp only [thetaV, theta, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul]
  rw [mul_assoc, ← Units.coe_star, h2, mul_one]

theorem isUnit_star (z : (Fib q)ˣ) : IsUnit (star (z : Fib q)) := by
  rw [← Units.coe_star]
  exact (star z).isUnit

/-- `theta z` is the only element `y` with `y z̄ = z`. -/
theorem theta_eq_of {z : (Fib q)ˣ} {y : U q} (h : ((y : (Fib q)ˣ) : Fib q) * star (z : Fib q) = z) :
    theta z = y := by
  have h1 : thetaV z = ((y : (Fib q)ˣ) : Fib q) :=
    (isUnit_star z).mul_left_inj.mp ((thetaV_mul_star z).trans h.symm)
  exact Subtype.ext (Units.ext h1)

theorem star_algebraMap (a : F) : star (algebraMap F (Fib q) a) = algebraMap F (Fib q) a := by
  ext <;> simp

theorem star_eq_self_iff (h2 : (2 : F) ≠ 0) {w : Fib q} : star w = w ↔ w.im = 0 := by
  constructor
  · intro h
    have h1 := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.im_star] at h1
    have h3 : 2 * w.im = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  · intro h
    ext <;> simp [h]

/-- Two units have the same image exactly when they differ by a nonzero constant. -/
theorem theta_eq_iff (h2 : (2 : F) ≠ 0) {z z' : (Fib q)ˣ} :
    theta z = theta z' ↔ ∃ a : F, a ≠ 0 ∧ (z' : Fib q) = algebraMap F (Fib q) a * z := by
  constructor
  · intro h
    have h1 := thetaV_mul_star z
    have h3 := thetaV_mul_star z'
    have h4 : thetaV z' = thetaV z := by simp only [thetaV, h]
    rw [h4] at h3
    -- `w = z' / z` is fixed by conjugation
    let w : Fib q := (z' : Fib q) * ((z⁻¹ : (Fib q)ˣ) : Fib q)
    have hzi : (z : Fib q) * ((z⁻¹ : (Fib q)ˣ) : Fib q) = 1 := Units.mul_inv z
    have hzw : (z' : Fib q) = w * z := by
      simp only [w]
      linear_combination (-(z' : Fib q)) * hzi
    have hstar : star w = w := by
      have hs : star (z' : Fib q) = star w * star (z : Fib q) := by
        rw [hzw, star_mul']
      rw [hs] at h3
      have h5 : (star w - w) * (z : Fib q) = 0 := by
        linear_combination (-star w) * h1 + h3 + hzw
      exact sub_eq_zero.mp ((z.isUnit.mul_left_eq_zero).mp h5)
    have him : w.im = 0 := (star_eq_self_iff h2).mp hstar
    have hw : w = algebraMap F (Fib q) w.re := by
      ext <;> simp [him]
    refine ⟨w.re, ?_, by rw [← hw]; exact hzw⟩
    intro h0
    rw [h0, map_zero] at hw
    rw [hw, zero_mul] at hzw
    exact z'.ne_zero hzw
  · rintro ⟨a, ha, h⟩
    refine (theta_eq_of ?_).symm
    have h1 := thetaV_mul_star z
    rw [h, star_mul', star_algebraMap]
    linear_combination algebraMap F (Fib q) a * h1

/-- The fibre's constants have the trivial image. -/
theorem theta_const {z : (Fib q)ˣ} (h : (z : Fib q) = algebraMap F (Fib q) (z : Fib q).re) :
    theta z = 1 := by
  refine theta_eq_of ?_
  rw [h, star_algebraMap]
  simp

/-- Hilbert 90: every element of `U` is `z / z̄`. -/
theorem theta_surjective (hq0 : q ≠ 0) (h2 : (2 : F) ≠ 0) :
    Function.Surjective (theta : (Fib q)ˣ →* U q) := by
  intro y
  have hy := mem_U.mp y.2
  set u : Fib q := ((y : (Fib q)ˣ) : Fib q) with hu
  have hstar : star u * u = 1 := by
    have := QuadraticAlgebra.algebraMap_norm_eq_mul_star u
    rw [hy, map_one] at this
    rw [mul_comm]
    exact this.symm
  by_cases hm : u = -1
  · -- `r / r̄ = -1`
    refine ⟨(isUnit_rE hq0).unit, theta_eq_of ?_⟩
    rw [← hu, hm, IsUnit.unit_spec]
    ext <;> simp [rE]
  · -- `(1 + u) / (1 + ū) = u`
    have hn : (1 + u).norm ≠ 0 := by
      intro h0
      have hre : u.re * u.re - q * u.im * u.im = 1 := by
        have := hy
        rw [QuadraticAlgebra.norm_def] at this
        simpa using this
      rw [QuadraticAlgebra.norm_def] at h0
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, zero_add, zero_mul, add_zero] at h0
      have h3 : 2 * (1 + u.re) = 0 := by linear_combination h0 - hre
      have h4 : u.re = -1 := by
        have := (mul_eq_zero.mp h3).resolve_left h2
        linear_combination this
      have h5 : q * (u.im * u.im) = 0 := by
        rw [h4] at hre
        linear_combination -hre
      have h6 : u.im = 0 := by
        have := (mul_eq_zero.mp h5).resolve_left hq0
        exact mul_self_eq_zero.mp this
      exact hm (by ext <;> simp [h4, h6])
    have hunit : IsUnit (1 + u) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (IsUnit.mk0 _ hn)
    refine ⟨hunit.unit, theta_eq_of ?_⟩
    rw [IsUnit.unit_spec, star_add, star_one, ← hu]
    linear_combination hstar

/-! ### The units of the normalization -/

variable (hq0 : q ≠ 0) (hq1 : q ≠ 1)

/-- The value on the fibre, on units. -/
noncomputable abbrev epsU : (Norm q)ˣ →* (Fib q)ˣ := Units.map (eps hq0 hq1 : Norm q →* Fib q)

/-- `s` goes to `-1`. -/
theorem theta_eps_s : thetaV (epsU hq0 hq1 (uS q)) = -1 := by
  have h := thetaV_mul_star (epsU hq0 hq1 (uS q))
  have hv : ((epsU hq0 hq1 (uS q) : (Fib q)ˣ) : Fib q) = rE := eps_s hq0 hq1
  rw [hv] at h
  have hs : star (rE : Fib q) = -rE := by ext <;> simp [rE]
  rw [hs] at h
  apply (isUnit_rE (q := q) hq0).mul_left_inj.mp
  linear_combination -h

/-- `s - 1` goes to `ρ`. -/
theorem theta_eps_s1 : thetaV (epsU hq0 hq1 (uS1 q)) * (1 + rE) = 1 - rE := by
  have h := thetaV_mul_star (epsU hq0 hq1 (uS1 q))
  have hv : ((epsU hq0 hq1 (uS1 q) : (Fib q)ˣ) : Fib q) = rE - 1 := by
    change eps hq0 hq1 (sN q - 1) = _
    rw [map_sub, map_one, eps_s]
  rw [hv] at h
  have hs : star ((rE : Fib q) - 1) = -(1 + rE) := by ext <;> simp [rE]
  rw [hs] at h
  linear_combination -h

/-- `s - q` goes to `-ρ`. -/
theorem theta_eps_sq : -thetaV (epsU hq0 hq1 (uSq q)) * (1 + rE) = 1 - rE := by
  have h := thetaV_mul_star (epsU hq0 hq1 (uSq q))
  have hv : ((epsU hq0 hq1 (uSq q) : (Fib q)ˣ) : Fib q) = rE - algebraMap F (Fib q) q := by
    change eps hq0 hq1 (sN q - qN q) = _
    rw [map_sub, eps_s, eps_qN]
  rw [hv] at h
  have hs : star ((rE : Fib q) - algebraMap F (Fib q) q) =
      -(rE * (1 + rE)) := by
    ext <;> simp [rE]
  rw [hs] at h
  apply (isUnit_rE (q := q) hq0).mul_right_inj.mp
  have hr := rE_mul_self (q := q)
  linear_combination h + hr

/-- A nonzero constant as a unit of the normalization. -/
noncomputable def constU (c : Fˣ) : (Norm q)ˣ :=
  Units.map (algebraMap F (Norm q) : F →* Norm q) c

theorem val_constU (c : Fˣ) :
    ((constU c : (Norm q)ˣ) : Norm q) = algebraMap F (Norm q) (c : F) := rfl

/-- The units whose image lies in `⟨-1, ρ⟩`. -/
noncomputable def goodUnits : Subgroup (Norm q)ˣ :=
  ((gluing q).comap theta).comap (epsU hq0 hq1)

theorem mem_goodUnits {v : (Norm q)ˣ} :
    v ∈ goodUnits hq0 hq1 ↔ theta (epsU hq0 hq1 v) ∈ gluing q := Iff.rfl

theorem constU_mem (c : Fˣ) : constU c ∈ goodUnits hq0 hq1 := by
  rw [mem_goodUnits]
  have h : theta (epsU hq0 hq1 (constU c)) = 1 := by
    apply theta_const
    have hv : ((epsU hq0 hq1 (constU c) : (Fib q)ˣ) : Fib q) = algebraMap F (Fib q) (c : F) :=
      eps_const hq0 hq1 (c : F)
    rw [hv]
    ext <;> simp
  rw [h]
  exact one_mem _

theorem uS_mem : uS q ∈ goodUnits hq0 hq1 := by
  rw [mem_goodUnits]
  exact Subgroup.subset_closure (Or.inl (theta_eps_s hq0 hq1))

theorem uS1_mem : uS1 q ∈ goodUnits hq0 hq1 := by
  rw [mem_goodUnits]
  exact Subgroup.subset_closure (Or.inr (theta_eps_s1 hq0 hq1))

theorem uSq_mem : uSq q ∈ goodUnits hq0 hq1 := by
  rw [mem_goodUnits]
  -- `s - q` goes to `(-1) ρ`.
  have hmem : theta (epsU hq0 hq1 (uS q)) * theta (epsU hq0 hq1 (uSq q)) ∈ gluing q := by
    refine Subgroup.subset_closure (Or.inr ?_)
    have h1 := theta_eps_s hq0 hq1
    have h2 := theta_eps_sq hq0 hq1
    simp only [thetaV] at h1 h2
    simp only [Subgroup.coe_mul, Units.val_mul, h1]
    linear_combination h2
  have hs : theta (epsU hq0 hq1 (uS q)) ∈ gluing q :=
    Subgroup.subset_closure (Or.inl (theta_eps_s hq0 hq1))
  exact (Subgroup.mul_mem_cancel_left _ hs).mp hmem

section UnitInduction

variable (K : Subgroup (Norm q)ˣ)

/-- The polynomials whose image is a unit in `K`. -/
def InGood (P : F[X]) : Prop :=
  ∃ w ∈ K, (w : Norm q) = algebraMap F[X] (Norm q) P

variable {K}

theorem inGood_C (hc : ∀ c : Fˣ, constU c ∈ K) {c : F} (hc0 : c ≠ 0) : InGood K (C c) :=
  ⟨constU (Units.mk0 c hc0), hc _, (map_C c).symm⟩

theorem inGood_mul {P Q : F[X]} (hP : InGood K P) (hQ : InGood K Q) : InGood K (P * Q) := by
  obtain ⟨w, hw, hw'⟩ := hP
  obtain ⟨w₁, hw₁, hw₁'⟩ := hQ
  exact ⟨w * w₁, mul_mem hw hw₁, by rw [Units.val_mul, hw', hw₁', map_mul]⟩

theorem inGood_X (h1 : uS q ∈ K) : InGood K (X : F[X]) := ⟨uS q, h1, rfl⟩

theorem inGood_X_sub_one (h2 : uS1 q ∈ K) : InGood K (X - C 1 : F[X]) :=
  ⟨uS1 q, h2, by rw [val_uS1, map_sub, map_C, map_one]; rfl⟩

theorem inGood_X_sub_q (h3 : uSq q ∈ K) : InGood K (X - C q : F[X]) :=
  ⟨uSq q, h3, by rw [val_uSq, map_sub, map_C]; rfl⟩

/-- An irreducible factor of `s (s - 1) (s - q)` is one of the three, up to a constant. -/
theorem inGood_irreducible (hc : ∀ c : Fˣ, constU c ∈ K) (h1 : uS q ∈ K) (h2 : uS1 q ∈ K)
    (h3 : uSq q ∈ K) {i : F[X]} (hi : Irreducible i) (hd : i ∣ poles q) : InGood K i := by
  have key : ∀ a : F, i ∣ (X - C a) → InGood K (X - C a) → InGood K i := by
    intro a hda hg
    obtain ⟨u, hu⟩ := hi.associated_of_dvd (irreducible_X_sub_C a) hda
    obtain ⟨c, hc', hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have e : i = (X - C a) * C (c⁻¹) := by
      have hc0 : c ≠ 0 := hc'.ne_zero
      rw [← hu, ← hcu, mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, mul_one]
    rw [e]
    exact inGood_mul hg (inGood_C hc (inv_ne_zero hc'.ne_zero))
  have hp := hi.prime
  rcases (hp.dvd_or_dvd hd) with h | h
  · rcases (hp.dvd_or_dvd h) with h | h
    · have h' : i ∣ (X - C 0 : F[X]) := by simpa using h
      refine key 0 h' ?_
      simpa using inGood_X h1
    · have h' : i ∣ (X - C 1 : F[X]) := by simpa using h
      exact key 1 h' (inGood_X_sub_one h2)
  · exact key q h (inGood_X_sub_q h3)

/-- Every factor of a power of `s (s - 1) (s - q)` has its image in `K`. -/
theorem inGood_of_dvd (hc : ∀ c : Fˣ, constU c ∈ K) (h1 : uS q ∈ K) (h2 : uS1 q ∈ K)
    (h3 : uSq q ∈ K) (k : ℕ) (a : F[X]) (hd : a ∣ poles q ^ k) : InGood K a := by
  induction a using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    exact absurd (zero_dvd_iff.mp hd) (pow_ne_zero _ poles_ne_zero)
  | unit u hu =>
    obtain ⟨c, hc', rfl⟩ := Polynomial.isUnit_iff.mp hu
    exact inGood_C hc hc'.ne_zero
  | mul a i _ hi ih =>
    have hi' : i ∣ poles q := hi.prime.dvd_of_dvd_pow ((dvd_mul_right i a).trans hd)
    exact inGood_mul (inGood_irreducible hc h1 h2 h3 hi hi') (ih ((dvd_mul_left a i).trans hd))

/-- The unit `s (s - 1) (s - q)`. -/
theorem val_poles :
    (uS q * uS1 q * uSq q : (Norm q)ˣ).val = algebraMap F[X] (Norm q) (poles q) := by
  simp only [Units.val_mul, val_uS, val_uS1, val_uSq, poles, map_mul, map_sub, map_one, map_C, sN]

/-- Every unit of the normalization is a constant times powers of `s`, `s - 1` and `s - q`. -/
theorem mem_of_generators (hc : ∀ c : Fˣ, constU c ∈ K) (h1 : uS q ∈ K) (h2 : uS1 q ∈ K)
    (h3 : uSq q ∈ K) (v : (Norm q)ˣ) : v ∈ K := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (poles q) (v : Norm q)
  obtain ⟨m, b, h'⟩ := IsLocalization.Away.surj (poles q) ((v⁻¹ : (Norm q)ˣ) : Norm q)
  have hab : a * b = poles q ^ (n + m) := by
    apply poly_injective (q := q)
    rw [map_mul, ← h, ← h', map_pow, pow_add]
    have hv := Units.mul_inv v
    linear_combination (algebraMap F[X] (Norm q) (poles q) ^ n *
      algebraMap F[X] (Norm q) (poles q) ^ m) * hv
  obtain ⟨w, hw, hw'⟩ := inGood_of_dvd hc h1 h2 h3 (n + m) a ⟨b, hab.symm⟩
  have hp : uS q * uS1 q * uSq q ∈ K := mul_mem (mul_mem h1 h2) h3
  have e : v = w * ((uS q * uS1 q * uSq q) ^ n)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, val_poles, h, hw']
  rw [e]
  exact mul_mem hw (inv_mem (pow_mem hp n))

end UnitInduction

/-- Every unit of the normalization is in `goodUnits`. -/
theorem goodUnits_eq_top (v : (Norm q)ˣ) : v ∈ goodUnits hq0 hq1 :=
  mem_of_generators (constU_mem hq0 hq1) (uS_mem hq0 hq1) (uS1_mem hq0 hq1) (uSq_mem hq0 hq1) v

/-- The image of a unit of the normalization lies in `⟨-1, ρ⟩`. -/
theorem theta_eps_mem (v : (Norm q)ˣ) : theta (epsU hq0 hq1 v) ∈ gluing q :=
  goodUnits_eq_top hq0 hq1 v

include hq1 in
/-- `ρ` is determined by `ρ (1 + r) = 1 - r`. -/
theorem isUnit_one_add_rE : IsUnit (1 + (rE : Fib q)) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_def]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, rE]
  refine IsUnit.mk0 _ ?_
  have : (1 + 0) * (1 + 0) + 0 * (1 + 0) * (0 + 1) - q * (0 + 1) * (0 + 1) = 1 - q := by ring
  rw [this]
  exact sub_ne_zero.mpr (Ne.symm hq1)

/-- Every element of `⟨-1, ρ⟩` comes from a unit of the normalization. -/
theorem exists_unit_of_mem {h : U q} (hh : h ∈ gluing q) :
    ∃ v : (Norm q)ˣ, theta (epsU hq0 hq1 v) = h := by
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · refine ⟨uS q, Subtype.ext (Units.ext ?_)⟩
      exact (theta_eps_s hq0 hq1).trans hy.symm
    · refine ⟨uS1 q, Subtype.ext (Units.ext ?_)⟩
      exact (isUnit_one_add_rE hq1).mul_left_inj.mp ((theta_eps_s1 hq0 hq1).trans hy.symm)
  | one => exact ⟨1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨w, rfl⟩ := hb
    exact ⟨v * w, by simp⟩
  | inv a _ ha =>
    obtain ⟨v, rfl⟩ := ha
    exact ⟨v⁻¹, by simp⟩

end Artform.Scores.Leapfrog
