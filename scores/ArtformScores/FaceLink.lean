import ArtformScores.Lifting

/-!
# The face form and the link form

The ledger's T11, finding 064, Theorem S3.10. The link form of a score is its face form conjugated
by `Λ = diag(1, D*)`, the change of variables `E = D* e`. At the zero mode every move of the face
form vanishes, and every step of the link form does, so the face form is a kick there and the link
form the identity. Passing to the link form forgets the gluing at the zero mode: the ideals agree
away from it, and the link ideal lies between `D*` times the face ideal and the face ideal.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open LaurentPolynomial

section FaceLink

variable {R : Type*} [CommRing R]

theorem stencilG_eq : stencilG R = diffD R * diffDs R := by
  have h : (T 1 : LaurentPolynomial R) * T (-1) = 1 := by rw [← T_add]; simp
  simp only [stencilG, diffD, diffDs]
  linear_combination -h

/-- The link form of a step is the face form conjugated by `Λ = diag(1, D*)`. -/
theorem step_intertwine (κ ℓ : R) (s : Step R) :
    (linkStep κ ℓ s).mat * lambdaMat R = lambdaMat R * (faceStep κ ℓ s).mat := by
  cases s with
  | kick w =>
    simp only [linkStep, faceStep, Step.mat, lambdaMat, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  | move w =>
    simp only [linkStep, faceStep, Step.mat, lambdaMat, Matrix.mul_fin_two, stencilG_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_assoc]

/-- The link form of a score is the face form conjugated by `Λ`. -/
theorem score_intertwine (κ ℓ : R) (w : List (Step R)) :
    (realize (w.map (linkStep κ ℓ))).1 * lambdaMat R =
      lambdaMat R * (realize (w.map (faceStep κ ℓ))).1 := by
  induction w with
  | nil => simp
  | cons s w ih =>
    simp only [List.map_cons, realize_cons, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl]
    rw [Matrix.mul_assoc, step_intertwine, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem atZero_C (r : R) : atZero R (C r) = r := LaurentPolynomial.eval₂_C _ _ r

theorem atZero_T (n : ℤ) : atZero R (T n) = 1 := by
  simp [atZero, LaurentPolynomial.eval₂_T]

theorem atZero_D : atZero R (diffD R) = 0 := by
  simp [diffD, atZero_T]

theorem atZero_Ds : atZero R (diffDs R) = 0 := by
  simp [diffDs, atZero_T]

theorem atZero_g : atZero R (stencilG R) = 0 := by
  rw [stencilG_eq, map_mul, atZero_D, zero_mul]

theorem kick_zero {S : Type*} [CommRing S] : (Step.kick (0 : S)).sl = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Step.mat]

theorem move_zero {S : Type*} [CommRing S] : (Step.move (0 : S)).sl = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Step.mat]

/-- At the zero mode the link form is the identity: unglued. -/
theorem link_at_zero (κ ℓ : R) (w : List (Step R)) :
    Matrix.SpecialLinearGroup.map (atZero R) (realize (w.map (linkStep κ ℓ))) = 1 := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [List.map_cons, realize_cons, map_mul, ih, one_mul, ← Step.map_sl]
    cases s <;> simp [linkStep, Step.map, atZero_D, atZero_Ds, kick_zero, move_zero]

/-- At the zero mode the face form is the kick of the total weight: glued when that is not zero. -/
theorem face_at_zero (κ ℓ : R) (w : List (Step R)) :
    (Matrix.SpecialLinearGroup.map (atZero R) (realize (w.map (faceStep κ ℓ)))).1 =
      !![1, 0; totalKick w * κ, 1] := by
  induction w with
  | nil =>
    simp only [List.map_nil, realize_nil, map_one, Matrix.SpecialLinearGroup.coe_one, totalKick,
      zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons s w ih =>
    rw [List.map_cons, realize_cons, map_mul, Matrix.SpecialLinearGroup.coe_mul, ih, ← Step.map_sl]
    cases s with
    | kick r =>
      simp only [faceStep, Step.map, Step.coe_sl, Step.mat, totalKick, atZero_C,
        Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      ring
    | move r =>
      simp only [faceStep, Step.map, Step.coe_sl, Step.mat, totalKick, map_mul, atZero_g, mul_zero,
        Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end FaceLink

/-- **T11** (face and link). -/
theorem faceAndLink : Statement.faceAndLink := by
  intro R _ _ κ ℓ w Tf Tl
  have hint : Tl.1 * lambdaMat R = lambdaMat R * Tf.1 := score_intertwine κ ℓ w
  have hTl : Tl.1 = !![Tl.1 0 0, Tl.1 0 1; Tl.1 1 0, Tl.1 1 1] := Matrix.eta_fin_two _
  have hTf : Tf.1 = !![Tf.1 0 0, Tf.1 0 1; Tf.1 1 0, Tf.1 1 1] := Matrix.eta_fin_two _
  have hentries := hint
  rw [hTl, hTf, lambdaMat, Matrix.mul_fin_two, Matrix.mul_fin_two] at hentries
  have e00 : Tl.1 0 0 = Tf.1 0 0 := by
    have := congrFun (congrFun hentries 0) 0
    simpa using this
  have e01 : Tf.1 0 1 = Tl.1 0 1 * diffDs R := by
    have := congrFun (congrFun hentries 0) 1
    simpa using this.symm
  have e10 : Tl.1 1 0 = diffDs R * Tf.1 1 0 := by
    have := congrFun (congrFun hentries 1) 0
    simpa using this
  have hDs : diffDs R ≠ 0 := by
    intro h
    have hT : (T (-1) : LaurentPolynomial R) = T 0 := by
      rw [T_zero]
      exact (sub_eq_zero.mp h).symm
    have h0 := congrArg (fun f : LaurentPolynomial R => f.coeff 0) hT
    simp only [LaurentPolynomial.T_apply] at h0
    simp at h0
  have e11 : Tl.1 1 1 = Tf.1 1 1 := by
    have := congrFun (congrFun hentries 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_zero, zero_add, add_zero, zero_mul] at this
    exact mul_right_cancel₀ hDs (this.trans (mul_comm _ _))
  refine ⟨hint, e00, e10, e01, e11, link_at_zero κ ℓ w, face_at_zero κ ℓ w, fun t => ⟨?_, ?_⟩⟩
  · simp only [lawIdeal, e00, e10]
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · simp only [lawIdeal, e00, e10]
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro x (rfl | rfl)
      · rw [← map_mul]
        exact Ideal.subset_span (by simp)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    · intro a x _ hx
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx

/-! ## Non-vacuity

The book's tick `K(1), M(-g)` over `F₇`: at the zero mode the face form is `K(1)` and the link form
is the identity.
-/

example : (Matrix.SpecialLinearGroup.map (atZero (ZMod 7))
    (realize ([.kick 1, .move 1].map (faceStep (1 : ZMod 7) 1)))).1 = !![1, 0; 1, 1] := by
  have := face_at_zero (1 : ZMod 7) 1 [.kick 1, .move 1]
  simpa [totalKick] using this

end Artform.Scores
