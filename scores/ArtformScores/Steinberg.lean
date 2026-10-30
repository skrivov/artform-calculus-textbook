import ArtformScores.Euclid
import ArtformScores.Rules

/-!
# Commutation, the fewest steps and the index as a group

- **R2.** Steinberg's relations for the steps on `c` channels. The realizer reverses the order, so
  the commutator of two laws is the score that takes the inverses first.
- **T1, the fewest steps.** Two steps of one kind merge, and a kick and a move have `d = 1` or
  `a = 1`.
- **T2, the index.** By T1, `E₂` over `F[x, 1/x]` is the kernel of the determinant. The units of the
  Laurent ring over a field are monomials, by unique factorization in `F[X]`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open LaurentPolynomial

section Chan
variable {c : ℕ} {S : Type*} [CommRing S]

theorem single_zero {i j k l : Fin c} (f g : S) (h : j ≠ k) :
    Matrix.single i j f * Matrix.single k l g = 0 :=
  Matrix.single_mul_single_of_ne f i j k h g

theorem mul_of_ne {i j k l : Fin c} (f g : S) (hjk : j ≠ k) :
    Matrix.transvection i j f * Matrix.transvection k l g =
      1 + Matrix.single i j f + Matrix.single k l g := by
  simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, single_zero f g hjk]
  abel

theorem commute_of_ne {i j k l : Fin c} (f g : S) (hjk : j ≠ k) (hil : i ≠ l) :
    Matrix.transvection i j f * Matrix.transvection k l g =
      Matrix.transvection k l g * Matrix.transvection i j f := by
  rw [mul_of_ne f g hjk, mul_of_ne g f hil.symm]
  abel

theorem ring_commutator {R : Type*} [Ring R] {F G H : R} (h1 : F * F = 0) (h2 : G * G = 0)
    (h3 : F * G = H) (h4 : G * F = 0) (h5 : H * F = 0) (h6 : H * G = 0) :
    (1 + F) * (1 + G) * (1 - F) * (1 - G) = 1 + H := by
  calc (1 + F) * (1 + G) * (1 - F) * (1 - G)
      = (1 + F + G + F * G) * (1 - F) * (1 - G) := by noncomm_ring
    _ = (1 + F + G + H) * (1 - F) * (1 - G) := by rw [h3]
    _ = (1 + G + H - F * F - G * F - H * F) * (1 - G) := by noncomm_ring
    _ = (1 + G + H) * (1 - G) := by rw [h1, h4, h5]; simp
    _ = 1 + H - G * G - H * G := by noncomm_ring
    _ = 1 + H := by rw [h2, h6]; simp

/-- Steinberg's relation for the laws. -/
theorem commutator_law {i j k : Fin c} (f g : S) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Matrix.transvection i j f * Matrix.transvection j k g * Matrix.transvection i j (-f) *
      Matrix.transvection j k (-g) = Matrix.transvection i k (f * g) := by
  have h := ring_commutator (F := Matrix.single i j f) (G := Matrix.single j k g)
    (H := Matrix.single i k (f * g)) (single_zero f f hij.symm) (single_zero g g hjk.symm)
    (Matrix.single_mul_single_same f i j k g) (single_zero g f hik.symm)
    (single_zero (f * g) f hik.symm) (single_zero (f * g) g hjk.symm)
  simpa only [Matrix.transvection, Matrix.single_neg, sub_eq_add_neg] using h

theorem ring_commutator' {R : Type*} [Ring R] {F G H : R} (h1 : F * F = 0) (h2 : G * G = 0)
    (h3 : F * G = H) (h4 : G * F = 0) (h5 : H * F = 0) :
    (1 - G) * (1 - F) * (1 + G) * (1 + F) = 1 - H := by
  calc (1 - G) * (1 - F) * (1 + G) * (1 + F)
      = (1 - G - F + G * F) * (1 + G) * (1 + F) := by noncomm_ring
    _ = (1 - G - F) * (1 + G) * (1 + F) := by rw [h4]; simp
    _ = (1 - F - G * G - F * G) * (1 + F) := by noncomm_ring
    _ = (1 - F - H) * (1 + F) := by rw [h2, h3]; simp
    _ = 1 - H - F * F - H * F := by noncomm_ring
    _ = 1 - H := by rw [h1, h5]; simp

/-- In time order, the commutator of the two steps has the law `e_ik(-f g)`. -/
theorem time_commutator {i j k : Fin c} (f g : S) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    realizeC [⟨i, j, f⟩, ⟨j, k, g⟩, ⟨i, j, -f⟩, ⟨j, k, -g⟩] =
      (⟨i, k, -(f * g)⟩ : ChanStep c S).mat := by
  have h := ring_commutator' (F := Matrix.single i j f) (G := Matrix.single j k g)
    (H := Matrix.single i k (f * g)) (single_zero f f hij.symm) (single_zero g g hjk.symm)
    (Matrix.single_mul_single_same f i j k g) (single_zero g f hik.symm)
    (single_zero (f * g) f hik.symm)
  simpa only [realizeC, ChanStep.mat, one_mul, Matrix.transvection, Matrix.single_neg,
    sub_eq_add_neg] using h

/-- In time order, the commutator with both signs reversed has the law `e_ik(f g)`. -/
theorem time_commutator' {i j k : Fin c} (f g : S) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    realizeC [⟨j, k, -g⟩, ⟨i, j, -f⟩, ⟨j, k, g⟩, ⟨i, j, f⟩] =
      (⟨i, k, f * g⟩ : ChanStep c S).mat := by
  simp only [realizeC, ChanStep.mat, one_mul]
  exact commutator_law f g hij hjk hik

/-- **R2**. -/
theorem steinbergRules (i j k l : Fin c) (f g : S) :
    (i ≠ j → realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨i, j, g⟩] = realizeC [⟨i, j, f + g⟩]) ∧
    realizeC [(⟨i, j, 0⟩ : ChanStep c S)] = 1 ∧
    (j ≠ k → i ≠ l → realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨k, l, g⟩] =
      realizeC [⟨k, l, g⟩, ⟨i, j, f⟩]) ∧
    (i ≠ j → j ≠ k → i ≠ k →
      Matrix.transvection i j f * Matrix.transvection j k g * Matrix.transvection i j (-f) *
        Matrix.transvection j k (-g) = Matrix.transvection i k (f * g) ∧
      realizeC [(⟨j, k, -g⟩ : ChanStep c S), ⟨i, j, -f⟩, ⟨j, k, g⟩, ⟨i, j, f⟩] =
        (⟨i, k, f * g⟩ : ChanStep c S).mat ∧
      realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨j, k, g⟩, ⟨i, j, -f⟩, ⟨j, k, -g⟩] =
        (⟨i, k, -(f * g)⟩ : ChanStep c S).mat) := by
  refine ⟨fun hij => ?_, ?_, fun hjk hil => ?_, fun hij hjk hik => ⟨commutator_law f g hij hjk hik,
    time_commutator' f g hij hjk hik, time_commutator f g hij hjk hik⟩⟩
  · simp only [realizeC, ChanStep.mat, one_mul]
    rw [Matrix.transvection_mul_transvection_same _ _ hij, add_comm]
  · simp [realizeC, ChanStep.mat]
  · simp only [realizeC, ChanStep.mat, one_mul]
    exact (commute_of_ne f g hjk hil).symm

end Chan

section Fewest

variable {S : Type*} [CommRing S]

/-- A law is a step exactly when it is a shear. -/
theorem one_step_iff (T : SpecialLinearGroup (Fin 2) S) :
    (∃ s : Step S, s.sl = T) ↔ T.1 0 0 = 1 ∧ T.1 1 1 = 1 ∧ (T.1 0 1 = 0 ∨ T.1 1 0 = 0) := by
  constructor
  · rintro ⟨s, rfl⟩
    cases s <;> simp [Step.mat]
  · rintro ⟨ha, hd, hbc | hbc⟩
    · refine ⟨Step.kick (T.1 1 0), ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Step.mat, ha, hd, hbc]
    · refine ⟨Step.move (T.1 0 1), ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Step.mat, ha, hd, hbc]

/-- A law is a score of at most two steps exactly when `a = 1` or `d = 1`. -/
theorem two_steps_iff (T : SpecialLinearGroup (Fin 2) S) :
    (∃ w : Score S, w.length ≤ 2 ∧ realize w = T) ↔ T.1 0 0 = 1 ∨ T.1 1 1 = 1 := by
  have hdet : T.1 0 0 * T.1 1 1 - T.1 0 1 * T.1 1 0 = 1 := by
    have := T.2
    rwa [Matrix.det_fin_two] at this
  constructor
  · rintro ⟨w, hw, rfl⟩
    match w, hw with
    | [], _ => simp
    | [s], _ =>
      cases s <;> simp [realize, Step.mat]
    | [s, t], _ =>
      cases s <;> cases t <;>
        simp [realize, Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
          Fin.sum_univ_two]
  · rintro (ha | hd)
    · refine ⟨[Step.move (T.1 0 1), Step.kick (T.1 1 0)], by simp, ?_⟩
      apply Subtype.ext
      simp only [realize, one_mul, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
        Matrix.mul_fin_two]
      rw [ha] at hdet
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha]
      linear_combination -hdet
    · refine ⟨[Step.kick (T.1 1 0), Step.move (T.1 0 1)], by simp, ?_⟩
      apply Subtype.ext
      simp only [realize, one_mul, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
        Matrix.mul_fin_two]
      rw [hd] at hdet
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hd]
      linear_combination -hdet

end Fewest

section Index

variable {F : Type*} [Field F]

/-- The units of the Laurent ring over a field are the monomials `r xᵏ`. -/
theorem units_laurent (u : (LaurentPolynomial F)ˣ) :
    ∃ (r : Fˣ) (k : ℤ), (u : LaurentPolynomial F) = C (r : F) * T k := by
  obtain ⟨a, p, hp⟩ := (u : LaurentPolynomial F).exists_T_pow
  obtain ⟨b, q, hq⟩ := ((u⁻¹ : (LaurentPolynomial F)ˣ) : LaurentPolynomial F).exists_T_pow
  have hprod : Polynomial.toLaurent (p * q) = Polynomial.toLaurent (Polynomial.X ^ (a + b)) := by
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow]
    have : (u : LaurentPolynomial F) * ((u⁻¹ : (LaurentPolynomial F)ˣ) : LaurentPolynomial F) = 1 :=
      u.mul_inv
    calc (u : LaurentPolynomial F) * T a * (((u⁻¹ : (LaurentPolynomial F)ˣ) :
          LaurentPolynomial F) * T b)
        = ((u : LaurentPolynomial F) * ((u⁻¹ : (LaurentPolynomial F)ˣ) : LaurentPolynomial F)) *
          (T a * T b) := by ring
      _ = T (↑(a + b)) := by rw [this, one_mul, ← T_add]; push_cast; rfl
  have hpq : p * q = Polynomial.X ^ (a + b) := Polynomial.toLaurent_injective hprod
  have hdvd : p ∣ Polynomial.X ^ (a + b) := ⟨q, hpq.symm⟩
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X _).mp hdvd
  obtain ⟨v, hv⟩ := hi.symm
  obtain ⟨r, hr, hrv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  refine ⟨hr.unit, (i : ℤ) - a, ?_⟩
  have hp2 : Polynomial.toLaurent p = C r * T (i : ℤ) := by
    rw [← hv, ← hrv, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]
  rw [hp] at hp2
  have hcancel : (u : LaurentPolynomial F) = (u : LaurentPolynomial F) * T a * T (-(a : ℤ)) := by
    rw [mul_assoc, ← T_add]
    simp
  rw [hcancel, hp2, IsUnit.unit_spec, mul_assoc, ← T_add]
  rfl

/-- The chiral movers make the determinant onto. -/
theorem det_surjective {S : Type*} [CommRing S] :
    Function.Surjective (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) S →* Sˣ) := by
  intro u
  let g : Matrix.GeneralLinearGroup (Fin 2) S :=
    ⟨!![(u : S), 0; 0, 1], !![((u⁻¹ : Sˣ) : S), 0; 0, 1],
      by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  refine ⟨g, ?_⟩
  apply Units.ext
  simp [g, Matrix.det_fin_two_of]

end Index

/-- **R2** (commutation; Steinberg's relations). -/
@[ledger "R2"]
theorem steinbergRules' : Statement.steinbergRules := fun _ _ _ i j k l f g =>
  steinbergRules i j k l f g

/-- **T1** (the fewest steps). -/
@[ledger "T1"]
theorem fewestSteps : Statement.fewestSteps := by
  intro S _
  refine ⟨one_step_iff, two_steps_iff, fun k m hkm w hw => ?_⟩
  by_contra hlt
  have htwo : ∃ w : Score S, w.length ≤ 2 ∧
      realize w = realize [Step.kick k, Step.move m, Step.kick k] := ⟨w, by omega, hw⟩
  rw [two_steps_iff] at htwo
  have h1 : (realize [Step.kick k, Step.move m, Step.kick k]).1 0 0 = 1 + m * k := by
    simp [realize, Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : (realize [Step.kick k, Step.move m, Step.kick k]).1 1 1 = 1 + k * m := by
    simp [realize, Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h1, h2] at htwo
  rcases htwo with h | h
  · exact hkm (by linear_combination h)
  · exact hkm (by linear_combination h)

/-- **T2** (the index as a group). -/
theorem indexGroup : Statement.indexGroup := by
  intro F _
  refine ⟨?_, det_surjective, units_laurent, fun r k => ?_, ?_⟩
  · apply le_antisymm
    · rw [elementary, Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      apply Units.ext
      simp
    · intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hdet : g.1.det = 1 := congrArg Units.val hg
      obtain ⟨w, hw⟩ := everyLawIsAScore F ⟨g.1, hdet⟩
      have hg' : g = ((realize w : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) :
          Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial F)) := by
        rw [hw]
        apply Units.ext
        rfl
      rw [hg']
      clear hg' hw
      induction w with
      | nil =>
        rw [realize_nil, map_one]
        exact Subgroup.one_mem _
      | cons s w ih =>
        rw [realize_cons, map_mul]
        exact Subgroup.mul_mem _ ih (Subgroup.subset_closure ⟨s, rfl⟩)
  · exact (IsUnit.map (C : F →+* LaurentPolynomial F) r.isUnit).mul (isUnit_T k)
  · let u : (LaurentPolynomial F)ˣ := (isUnit_T 1).unit
    have hu : (u : LaurentPolynomial F) = T 1 := rfl
    have hinv : ((u⁻¹ : (LaurentPolynomial F)ˣ) : LaurentPolynomial F) = T (-1) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hu, ← T_add]
      simp
    refine ⟨Score.reverse (whitehead 1) ++ whitehead u, by simp [Score.reverse, whitehead], ?_⟩
    rw [realize_append, timeReversal]
    have := balanced_mat u
    rw [balanced, hu, hinv] at this
    exact this

/-! ## Non-vacuity

- Steinberg's relation over `F₇` on three channels, from `e_01(2)` and `e_12(3)`.
- The law `[[1 + x, 1], [x, 1]]` over `F₇[x, 1/x]` is two steps, and the tick `K(1) M(-3)` is too.
-/

example : Matrix.transvection (0 : Fin 3) 1 (2 : ZMod 7) * Matrix.transvection 1 2 3 *
    Matrix.transvection 0 1 (-2) * Matrix.transvection 1 2 (-3) = Matrix.transvection 0 2 6 := by
  have := ((steinbergRules' (ZMod 7) 3 0 1 2 0 2 3).2.2.2 (by decide) (by decide) (by decide)).1
  rwa [show (2 : ZMod 7) * 3 = 6 by decide] at this

end Artform.Scores
