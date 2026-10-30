import ArtformScores.Euclid

/-!
# Lifting: every law on the dials `Z/p^k` is a score

T1 of the algebra of scores for the dials `Z/p^k`, `p` prime, from the field
`F_p` (`Euclid.lean`).
- A law whose corner `a` is a unit is the product `K(c/a) diag(a, 1/a) M(b/a)`
  of a kick, a balanced mover and a move: the ledger's lifting step.
- Reduce a law over `Z/p^k` modulo `p`, write the reduction as a score over
  `F_p`, and lift the score's stencils back to `Z/p^k`. The law is that score's
  law times a law whose corner is `1` plus a multiple of `p`. A multiple of `p`
  is nilpotent, so the corner is a unit.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open LaurentPolynomial

section Maps

variable {S S' : Type*} [CommRing S] [CommRing S']

/-- A step read through a ring map: the same step with its stencil mapped. -/
def Step.map (φ : S →+* S') : Step S → Step S'
  | .kick f => .kick (φ f)
  | .move f => .move (φ f)

theorem Step.map_sl (φ : S →+* S') (s : Step S) :
    (s.map φ).sl = Matrix.SpecialLinearGroup.map φ s.sl := by
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;> simp [Step.map, Step.mat]

/-- A score read through a ring map realizes the mapped law. -/
theorem realize_map (φ : S →+* S') (w : Score S) :
    realize (w.map (Step.map φ)) = Matrix.SpecialLinearGroup.map φ (realize w) := by
  induction w with
  | nil => simp
  | cons s w ih => rw [List.map_cons, realize_cons, realize_cons, ih, map_mul, Step.map_sl]

/-- Every score over `S'` lifts along a ring map onto `S'`. -/
theorem exists_score_map {φ : S →+* S'} (hφ : Function.Surjective φ) (w' : Score S') :
    ∃ w : Score S, w.map (Step.map φ) = w' := by
  induction w' with
  | nil => exact ⟨[], rfl⟩
  | cons s w' ih =>
    obtain ⟨w, hw⟩ := ih
    cases s with
    | kick f =>
      obtain ⟨g, rfl⟩ := hφ f
      exact ⟨.kick g :: w, by rw [List.map_cons, hw]; rfl⟩
    | move f =>
      obtain ⟨g, rfl⟩ := hφ f
      exact ⟨.move g :: w, by rw [List.map_cons, hw]; rfl⟩

/-- The lifting step. A law `[[a, b], [c, d]]` whose corner `a` is a unit is the
product `K(c/a) diag(a, 1/a) M(b/a)` of a kick, a balanced mover and a move. -/
theorem isScore_of_isUnit (A : SpecialLinearGroup (Fin 2) S)
    (h : IsUnit ((A : Matrix (Fin 2) (Fin 2) S) 0 0)) : IsScore A := by
  obtain ⟨u, hu⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two, ← hu] at hdet
  have hinv : (u : S) * ↑u⁻¹ = 1 := u.mul_inv
  have hA : A = (Step.kick ((A : Matrix (Fin 2) (Fin 2) S) 1 0 * ↑u⁻¹)).sl * balanced u *
      (Step.move (↑u⁻¹ * (A : Matrix (Fin 2) (Fin 2) S) 0 1)).sl := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, balanced_mat, Step.coe_sl, Step.mat,
      Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp [← hu]
    linear_combination (↑u⁻¹ : S) * hdet - (A : Matrix (Fin 2) (Fin 2) S) 1 1 * hinv
  rw [hA]
  exact ((IsScore.step _).mul (isScore_balanced u)).mul (IsScore.step _)

/-- Lifting. If every law over `S'` is a score, and `φ : S → S'` is onto with a
kernel of nilpotents, then every law over `S` is a score. -/
theorem isScore_of_lift {φ : S →+* S'} (hφ : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 → IsNilpotent a)
    (h' : ∀ A' : SpecialLinearGroup (Fin 2) S', IsScore A') (A : SpecialLinearGroup (Fin 2) S) :
    IsScore A := by
  obtain ⟨w', hw'⟩ := h' (Matrix.SpecialLinearGroup.map φ A)
  obtain ⟨w, rfl⟩ := exists_score_map hφ w'
  rw [realize_map] at hw'
  set B := (realize w)⁻¹ * A with hBdef
  have hB : Matrix.SpecialLinearGroup.map φ B = 1 := by
    rw [hBdef, map_mul, map_inv, hw', inv_mul_cancel]
  have h00 : φ ((B : Matrix (Fin 2) (Fin 2) S) 0 0) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using
      congrArg (fun X : SpecialLinearGroup (Fin 2) S' => (X : Matrix (Fin 2) (Fin 2) S') 0 0) hB
  have hu : IsUnit ((B : Matrix (Fin 2) (Fin 2) S) 0 0) := by
    have hn := hker _ (show φ (_ - 1) = 0 by rw [map_sub, h00, map_one, sub_self])
    simpa using hn.isUnit_add_one
  have hA := IsScore.mul (⟨w, rfl⟩ : IsScore (realize w)) (isScore_of_isUnit B hu)
  rwa [hBdef, mul_inv_cancel_left] at hA

end Maps

section Dials

/-- Over a ring with `1 = 0`, every law is the empty score's. -/
theorem isScore_of_one_eq_zero {S : Type*} [CommRing S] (h : (1 : S) = 0)
    (A : SpecialLinearGroup (Fin 2) S) : IsScore A := by
  have hall : ∀ x : S, x = 0 := fun x => by rw [← mul_one x, h, mul_zero]
  refine ⟨[], ?_⟩
  ext i j
  rw [hall ((realize [] : SpecialLinearGroup (Fin 2) S) i j), hall ((A : Matrix _ _ S) i j)]

theorem laurent_one_eq_zero {n : ℕ} (hn : n = 1) : (1 : LaurentPolynomial (ZMod n)) = 0 := by
  have : Subsingleton (ZMod n) := ZMod.subsingleton_iff.mpr hn
  rw [← map_one C, ← map_zero C, Subsingleton.elim (1 : ZMod n) 0]

/-- Reduction of the stencils modulo `m`, for `m ∣ n`. -/
noncomputable def reduce {m n : ℕ} (h : m ∣ n) :
    LaurentPolynomial (ZMod n) →+* LaurentPolynomial (ZMod m) :=
  AddMonoidAlgebra.mapRingHom ℤ (ZMod.castHom h (ZMod m))

theorem reduce_surjective {m n : ℕ} (h : m ∣ n) : Function.Surjective (reduce h) :=
  AddMonoidAlgebra.map_surjective _ (ZMod.ringHom_surjective (ZMod.castHom h (ZMod m)))

theorem coeff_reduce {m n : ℕ} (h : m ∣ n) (x : LaurentPolynomial (ZMod n)) (i : ℤ) :
    (reduce h x).coeff i = ZMod.castHom h (ZMod m) (x.coeff i) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

theorem reduce_C {m n : ℕ} (h : m ∣ n) (c : ZMod n) :
    reduce h (C c) = C (ZMod.castHom h (ZMod m) c) :=
  congrArg (fun f : ZMod n →+* LaurentPolynomial (ZMod m) => f c)
    (Subsingleton.elim ((reduce h).comp C) (C.comp (ZMod.castHom h (ZMod m))))

/-- In `Z/p^k`, a number that is `0` modulo `p` is nilpotent. -/
theorem isNilpotent_of_castHom {p k : ℕ} (hp : p ≠ 0) (hk : k ≠ 0) (c : ZMod (p ^ k))
    (hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0) : IsNilpotent c := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hc
  obtain ⟨m, hm⟩ := hc
  refine ⟨k, ?_⟩
  rw [← ZMod.natCast_zmod_val c, hm, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self,
    zero_mul]

/-- A stencil over `Z/p^k` that is `0` modulo `p` is nilpotent. -/
theorem reduce_ker_isNilpotent {p k : ℕ} (hp : p ≠ 0) (hk : k ≠ 0)
    (x : LaurentPolynomial (ZMod (p ^ k))) (hx : reduce (dvd_pow_self p hk) x = 0) :
    IsNilpotent x := by
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine isNilpotent_sum fun i _ => ?_
  rw [single_eq_C_mul_T]
  refine Commute.isNilpotent_mul_right (Commute.all _ _) ((isNilpotent_of_castHom hp hk _ ?_).map C)
  simpa [coeff_reduce] using congrArg (fun y => y.coeff i) hx

end Dials

/-- **T1** (one dimension, every dial) for the dials `Z/p^k`, `p` prime. -/
@[ledger "T1"]
theorem everyLawIsAScorePrimePower : Statement.everyLawIsAScorePrimePower := by
  intro p k hp A
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact isScore_of_one_eq_zero (laurent_one_eq_zero (pow_zero p)) A
  · have : Fact p.Prime := ⟨hp⟩
    exact isScore_of_lift (reduce_surjective (dvd_pow_self p hk.ne'))
      (reduce_ker_isNilpotent hp.ne_zero hk.ne') (everyLawIsAScore (ZMod p)) A

/-! ## Non-vacuity

The statement needs a prime and a law of determinant 1. The running example's
prime `7`, squared: -/

/-- The law `[[7x, 1], [-1, 0]]` over `(Z/49)[x, 1/x]`, whose corner `7x` is
nilpotent and not a unit, is a score. -/
example : ∃ w : Score (LaurentPolynomial (ZMod (7 ^ 2))),
    (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod (7 ^ 2)))) =
      !![7 * T 1, 1; -1, 0] := by
  obtain ⟨w, hw⟩ := everyLawIsAScorePrimePower 7 2 (by norm_num)
    ⟨!![7 * T 1, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩
  exact ⟨w, by rw [hw]⟩

end Artform.Scores
