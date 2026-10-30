import ArtformScores.Lifting

/-!
# The Chinese remainder theorem: every law on the dials `Z/n` is a score

T1 of the algebra of scores for every dial `Z/n`, `n ≥ 1`, from the dials
`Z/p^k` (`Lifting.lean`).
- For coprime `a` and `b`, `Z/ab` splits as `Z/a × Z/b`. Lift a score over
  `Z/a` to `Z/ab` and multiply its stencils by the idempotent that is `1`
  modulo `a` and `0` modulo `b`: the lifted score acts on the `Z/a` part only.
  Likewise for `Z/b`.
- The two lifted scores, one after the other, realize the law modulo `a` and
  modulo `b`, hence the law itself.
- Induction over the factorization of `n` finishes.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open LaurentPolynomial

section Scale

variable {S S' : Type*} [CommRing S] [CommRing S']

/-- A step with its stencil multiplied by `e`. -/
def Step.scale (e : S) : Step S → Step S
  | .kick f => .kick (e * f)
  | .move f => .move (e * f)

theorem Step.map_scale (φ : S →+* S') (e : S) (s : Step S) :
    (s.scale e).map φ = (s.map φ).scale (φ e) := by
  cases s <;> simp [Step.scale, Step.map]

theorem realize_scale_one (w : Score S) : realize (w.map (Step.scale 1)) = realize w := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp [Step.scale, ih]

theorem realize_scale_zero (w : Score S) : realize (w.map (Step.scale 0)) = 1 := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [List.map_cons, realize_cons, ih, one_mul]
    ext i j
    cases s <;> fin_cases i <;> fin_cases j <;> simp [Step.scale, Step.mat]

theorem map_realize_scale (φ : S →+* S') (e : S) (w : Score S) :
    Matrix.SpecialLinearGroup.map φ (realize (w.map (Step.scale e))) =
      realize ((w.map (Step.map φ)).map (Step.scale (φ e))) := by
  rw [← realize_map, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun s _ => Step.map_scale φ e s

/-- The product step. If `S` maps onto `S₁` and `S₂`, the two maps together are
one to one, and `S` has the two idempotents of the splitting, then every law over
`S` is a score when every law over `S₁` and over `S₂` is. -/
theorem isScore_of_prod {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] {φ₁ : S →+* S₁}
    {φ₂ : S →+* S₂} (h₁ : Function.Surjective φ₁) (h₂ : Function.Surjective φ₂)
    (hinj : ∀ a b, φ₁ a = φ₁ b → φ₂ a = φ₂ b → a = b) {e₁ e₂ : S}
    (he₁ : φ₁ e₁ = 1 ∧ φ₂ e₁ = 0) (he₂ : φ₁ e₂ = 0 ∧ φ₂ e₂ = 1)
    (T₁ : ∀ A : SpecialLinearGroup (Fin 2) S₁, IsScore A)
    (T₂ : ∀ A : SpecialLinearGroup (Fin 2) S₂, IsScore A) (A : SpecialLinearGroup (Fin 2) S) :
    IsScore A := by
  obtain ⟨v₁, hv₁⟩ := T₁ (Matrix.SpecialLinearGroup.map φ₁ A)
  obtain ⟨w₁, rfl⟩ := exists_score_map h₁ v₁
  obtain ⟨v₂, hv₂⟩ := T₂ (Matrix.SpecialLinearGroup.map φ₂ A)
  obtain ⟨w₂, rfl⟩ := exists_score_map h₂ v₂
  rw [realize_map] at hv₁ hv₂
  refine ⟨w₁.map (Step.scale e₁) ++ w₂.map (Step.scale e₂), ?_⟩
  have k₁ : Matrix.SpecialLinearGroup.map φ₁
      (realize (w₁.map (Step.scale e₁) ++ w₂.map (Step.scale e₂))) =
        Matrix.SpecialLinearGroup.map φ₁ A := by
    rw [realize_append, map_mul, map_realize_scale, map_realize_scale, he₁.1, he₂.1,
      realize_scale_zero, realize_scale_one, one_mul, realize_map, hv₁]
  have k₂ : Matrix.SpecialLinearGroup.map φ₂
      (realize (w₁.map (Step.scale e₁) ++ w₂.map (Step.scale e₂))) =
        Matrix.SpecialLinearGroup.map φ₂ A := by
    rw [realize_append, map_mul, map_realize_scale, map_realize_scale, he₁.2, he₂.2,
      realize_scale_zero, realize_scale_one, mul_one, realize_map, hv₂]
  ext i j
  apply hinj
  · simpa using congrArg (fun B : SpecialLinearGroup (Fin 2) S₁ =>
      (B : Matrix (Fin 2) (Fin 2) S₁) i j) k₁
  · simpa using congrArg (fun B : SpecialLinearGroup (Fin 2) S₂ =>
      (B : Matrix (Fin 2) (Fin 2) S₂) i j) k₂

end Scale

section Remainders

theorem castHom_eq_crt_fst {a b : ℕ} (hab : a.Coprime b) (z : ZMod (a * b)) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) z = (ZMod.chineseRemainder hab z).1 :=
  congrArg (fun f : ZMod (a * b) →+* ZMod a => f z)
    (Subsingleton.elim _ ((RingHom.fst (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder hab)))

theorem castHom_eq_crt_snd {a b : ℕ} (hab : a.Coprime b) (z : ZMod (a * b)) :
    ZMod.castHom (dvd_mul_left b a) (ZMod b) z = (ZMod.chineseRemainder hab z).2 :=
  congrArg (fun f : ZMod (a * b) →+* ZMod b => f z)
    (Subsingleton.elim _ ((RingHom.snd (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder hab)))

/-- The Chinese remainder theorem on the stencils: reduction modulo `a` and modulo
`b` together is one to one. -/
theorem reduce_crt_injective {a b : ℕ} (hab : a.Coprime b)
    (x y : LaurentPolynomial (ZMod (a * b)))
    (h₁ : reduce (dvd_mul_right a b) x = reduce (dvd_mul_right a b) y)
    (h₂ : reduce (dvd_mul_left b a) x = reduce (dvd_mul_left b a) y) : x = y := by
  ext i
  apply (ZMod.chineseRemainder hab).injective
  have e₁ := congrArg (fun z => z.coeff i) h₁
  have e₂ := congrArg (fun z => z.coeff i) h₂
  simp only [coeff_reduce, castHom_eq_crt_fst hab, castHom_eq_crt_snd hab] at e₁ e₂
  exact Prod.ext e₁ e₂

/-- The constant stencil with the remainders `u` modulo `a` and `v` modulo `b`. -/
theorem reduce_crt_C {a b : ℕ} (hab : a.Coprime b) (u : ZMod a) (v : ZMod b) :
    reduce (dvd_mul_right a b) (C ((ZMod.chineseRemainder hab).symm (u, v))) = C u ∧
      reduce (dvd_mul_left b a) (C ((ZMod.chineseRemainder hab).symm (u, v))) = C v := by
  rw [reduce_C, reduce_C, castHom_eq_crt_fst hab, castHom_eq_crt_snd hab,
    RingEquiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩

end Remainders

/-- **T1** (one dimension, every dial) for every dial `Z/n`, `n ≥ 1`. -/
@[ledger "T1"]
theorem everyLawIsAScoreModulus : Statement.everyLawIsAScoreModulus := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => exact fun _ => everyLawIsAScorePrimePower p k hp
  | zero => exact fun h => absurd rfl h
  | one => exact fun _ => isScore_of_one_eq_zero (laurent_one_eq_zero rfl)
  | coprime a b ha hb hab iha ihb =>
    intro _
    have e₁ := reduce_crt_C hab 1 0
    have e₂ := reduce_crt_C hab 0 1
    rw [map_one, map_zero] at e₁ e₂
    exact isScore_of_prod (reduce_surjective (dvd_mul_right a b))
      (reduce_surjective (dvd_mul_left b a)) (reduce_crt_injective hab) e₁ e₂
      (iha (by omega)) (ihb (by omega))

/-! ## Non-vacuity

The statement needs a modulus `n ≥ 1` and a law of determinant 1. The dial
`Z/14 = Z/2 × Z/7`, beside the running example's prime `7`: -/

/-- The law `[[7, 2x], [3/x, 1]]` over `(Z/14)[x, 1/x]`, whose entries `7` and `2`
are zero divisors, is a score. -/
example : ∃ w : Score (LaurentPolynomial (ZMod 14)),
    (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 14))) =
      !![7, 2 * T 1; 3 * T (-1), 1] := by
  obtain ⟨w, hw⟩ := everyLawIsAScoreModulus 14 (by norm_num)
    ⟨!![7, 2 * T 1; 3 * T (-1), 1], by
      rw [Matrix.det_fin_two_of, mul_mul_mul_comm, ← T_add, add_neg_cancel, T_zero]; norm_num⟩
  exact ⟨w, by rw [hw]⟩

end Artform.Scores
