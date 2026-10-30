import ArtformScores.Rules

/-!
# Every law on a dial is a score

T1 of the algebra of scores over a field `F`: every law of determinant 1 on a
dial, `A ∈ SL(2, F[x, 1/x])`, is the law of a score. The proof is Euclid's
algorithm on the first column `(a, c)` of `A`.
- Every Laurent polynomial is `p(x) xᵏ` with `p` a polynomial, and dividing by
  `p(x) xᵏ` is dividing by `p` in `F[X]`.
- The move `M(-q)` with the quotient `q`, then the swap `w(1)`, turn the column
  into `(c, -r)`, where the remainder `r` has a smaller degree than `c`.
- When `c = 0`, the law is a balanced mover (R4) then a move.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open Polynomial LaurentPolynomial

section Ring

variable {S : Type*} [CommRing S]

/-- A law is a score when some score realizes it. -/
def IsScore (A : SpecialLinearGroup (Fin 2) S) : Prop := ∃ w : Score S, realize w = A

theorem IsScore.step (s : Step S) : IsScore s.sl := ⟨[s], realize_singleton s⟩

/-- One score after another realizes the product of their laws. -/
theorem IsScore.mul {A B : SpecialLinearGroup (Fin 2) S} (hA : IsScore A) (hB : IsScore B) :
    IsScore (A * B) := by
  obtain ⟨wA, rfl⟩ := hA
  obtain ⟨wB, rfl⟩ := hB
  exact ⟨wB ++ wA, realize_append wB wA⟩

/-- The inverse of a score's law is a score's law: each step's inverse is a step. -/
theorem IsScore.inv {A : SpecialLinearGroup (Fin 2) S} (hA : IsScore A) : IsScore A⁻¹ := by
  obtain ⟨w, rfl⟩ := hA
  induction w with
  | nil => exact ⟨[], by simp⟩
  | cons s w ih =>
    rw [realize_cons, mul_inv_rev, ← Step.sl_neg]
    exact (IsScore.step s.neg).mul ih

theorem IsScore.of_mul_left {E A : SpecialLinearGroup (Fin 2) S} (hE : IsScore E)
    (h : IsScore (E * A)) : IsScore A := by
  simpa using hE.inv.mul h

theorem isScore_balanced (u : Sˣ) : IsScore (balanced u) :=
  IsScore.mul ⟨_, rfl⟩ (IsScore.inv ⟨_, rfl⟩)

/-- The end of Euclid's algorithm. A law `[[a, b], [0, d]]` has `ad = 1`, so it is
the balanced mover `diag(a, d)` then the move `M(db)`. -/
theorem isScore_of_lower_eq_zero (A : SpecialLinearGroup (Fin 2) S)
    (h : (A : Matrix (Fin 2) (Fin 2) S) 1 0 = 0) : IsScore A := by
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  let u : Sˣ := ⟨_, _, hdet, by rw [mul_comm]; exact hdet⟩
  have hA : A = balanced u * (Step.move ((A : Matrix (Fin 2) (Fin 2) S) 1 1 *
      (A : Matrix (Fin 2) (Fin 2) S) 0 1)).sl := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, balanced_mat, Step.coe_sl, Step.mat,
      Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp [u, h]
    all_goals linear_combination -(A : Matrix (Fin 2) (Fin 2) S) 0 1 * hdet
  rw [hA]
  exact (isScore_balanced u).mul (IsScore.step _)

/-- Euclid's step. The move `M(-q)` then the swap `w(1)` turn the first column
`(a, c)` into `(c, -(a - qc))`. -/
theorem euclid_step_mat (A : SpecialLinearGroup (Fin 2) S) (q : S) :
    ((realize (whitehead 1) * (Step.move (-q)).sl * A : SpecialLinearGroup (Fin 2) S) :
      Matrix (Fin 2) (Fin 2) S) 1 0 =
      -((A : Matrix (Fin 2) (Fin 2) S) 0 0 - q * (A : Matrix (Fin 2) (Fin 2) S) 1 0) := by
  simp [Matrix.SpecialLinearGroup.coe_mul, whitehead_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Step.mat]
  ring

theorem isScore_of_euclid_step (A : SpecialLinearGroup (Fin 2) S) (q : S)
    (h : IsScore (realize (whitehead 1) * (Step.move (-q)).sl * A)) : IsScore A :=
  IsScore.of_mul_left (IsScore.mul ⟨_, rfl⟩ (IsScore.step _)) h

end Ring

section Field

variable {F : Type*} [Field F]

/-- Every Laurent polynomial is `p(x) xᵏ` for a polynomial `p` and an integer `k`. -/
theorem exists_poly_mul_T {R : Type*} [CommSemiring R] (f : LaurentPolynomial R) :
    ∃ (p : R[X]) (k : ℤ), f = toLaurent p * T k := by
  obtain ⟨n, p, hp⟩ := exists_T_pow f
  refine ⟨p, -n, ?_⟩
  rw [hp, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]

/-- Division on a dial. Dividing `a` by `p(x) xᵏ`, `p ≠ 0`, leaves a remainder
`r(x) xʲ` with `deg r < deg p`. -/
theorem exists_div (a : LaurentPolynomial F) {p : F[X]} (hp : p ≠ 0) (k : ℤ) :
    ∃ (q : LaurentPolynomial F) (r : F[X]) (j : ℤ), r.degree < p.degree ∧
      a - q * (toLaurent p * T k) = toLaurent r * T j := by
  obtain ⟨s, j, rfl⟩ := exists_poly_mul_T a
  refine ⟨toLaurent (s / p) * T (j - k), s % p, j, Polynomial.degree_mod_lt s hp, ?_⟩
  have hT : (T (j - k) : LaurentPolynomial F) * T k = T j := by rw [← T_add, sub_add_cancel]
  have hs : toLaurent s = toLaurent p * toLaurent (s / p) + toLaurent (s % p) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  linear_combination (T j : LaurentPolynomial F) * hs - toLaurent (s / p) * toLaurent p * hT

/-- Euclid's algorithm. A law whose lower-left entry is `p(x) xᵏ` is a score, by
strong induction on the degree of `p`. -/
theorem isScore_of_lower (n : ℕ) :
    ∀ (A : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) (p : F[X]) (k : ℤ),
      p.natDegree = n → (A : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 0 =
        toLaurent p * T k → IsScore A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A p k hn hc
  by_cases hp : p = 0
  · exact isScore_of_lower_eq_zero A (by rw [hc, hp, map_zero, zero_mul])
  obtain ⟨q, r, j, hr, hq⟩ :=
    exists_div ((A : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 0 0) hp k
  apply isScore_of_euclid_step A q
  have hc' : ((realize (whitehead 1) * (Step.move (-q)).sl * A :
      SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 0 = toLaurent (-r) * T j := by
    rw [euclid_step_mat, hc, hq, map_neg, neg_mul]
  by_cases hr0 : r = 0
  · exact isScore_of_lower_eq_zero _ (by rw [hc', hr0, neg_zero, map_zero, zero_mul])
  · refine ih _ ?_ _ (-r) j rfl hc'
    rw [natDegree_neg, ← hn]
    exact natDegree_lt_natDegree hr0 hr

end Field

/-- **T1** (one dimension, every dial). Over a field, every law of determinant 1 on
a dial is a score. -/
@[ledger "T1"]
theorem everyLawIsAScore : Statement.everyLawIsAScore := by
  intro F _ A
  obtain ⟨p, k, hc⟩ :=
    exists_poly_mul_T ((A : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 0)
  exact isScore_of_lower _ A p k rfl hc

/-! ## Non-vacuity

The statement has no hypotheses beyond a field and a law of determinant 1. Two
laws of the running example's ring `F₇[x, 1/x]`, whose shift is `x = T 1`: -/

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The balanced pair `diag(x, 1/x)` has determinant 1, so it is a score, unlike
the chiral mover `diag(x, 1)` of T2. -/
example : ∃ w : Score (LaurentPolynomial (ZMod 7)),
    (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 7))) =
      !![T 1, 0; 0, T (-1)] := by
  obtain ⟨w, hw⟩ := everyLawIsAScore (ZMod 7)
    ⟨!![T 1, 0; 0, T (-1)], by rw [Matrix.det_fin_two_of, ← T_add]; simp⟩
  exact ⟨w, by rw [hw]⟩

/-- The law `[[1 + x, -1], [x², 1 - x]]`, given by its entries and not as a score,
is a score: Euclid's algorithm runs on the column `(1 + x, x²)`. -/
example : ∃ w : Score (LaurentPolynomial (ZMod 7)),
    (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 7))) =
      !![1 + T 1, -1; T 1 ^ 2, 1 - T 1] := by
  obtain ⟨w, hw⟩ := everyLawIsAScore (ZMod 7)
    ⟨!![1 + T 1, -1; T 1 ^ 2, 1 - T 1], by rw [Matrix.det_fin_two_of]; ring⟩
  exact ⟨w, by rw [hw]⟩

end Artform.Scores
