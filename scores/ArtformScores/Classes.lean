import ArtformScores.StepOrders

/-!
# The class of a law

T7 of the algebra of scores, after Latimer and MacDuffee (the ledger's finding 057, §1).
A law `T = [[a, b], [c, d]]` of phase `t` lives on the curve `λ + 1/λ = t`, whose ring is
`A_t = S[λ]/(λ² - tλ + 1)`.
- `u = (c, λ - a)` is a left eigenvector, `u T = λ u`, since `λ² = tλ - 1` and `ad - bc = 1`.
- Processing, `T′ = P T P⁻¹`, takes `u` to the eigenvector `w = u P⁻¹` of `T′`. The first
  column of `w (T′ - λ) = 0` reads `c′ w₁ = w₀ (λ - a′)`, so
  `c′ (c, λ - a) = w₀ (c′, λ - a′)`: the two ideals are in the same class.
- Both factors are non-zero-divisors when `t² - 4` is not a square: `c′ ≠ 0`, and `w₀`
  has the norm `c Q_T(q) ≠ 0`, with `Q_T` the law's quadratic form and `q` the first
  column of `P⁻¹`.
- A cyclic vector `v` makes `[v | T v]` invertible and conjugates `T` to the companion
  tick, whose ideal `(1, λ)` is the whole ring.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open Polynomial

section Proofs

variable {S : Type*} [CommRing S]

theorem eig_sq (t : S) : eig t * eig t = algebraMap S (curveRing t) t * eig t - 1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C t * X + 1 : S[X])
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_one] at h
  rw [AdjoinRoot.algebraMap_eq]
  unfold eig
  linear_combination h

/-- `u = (c, λ - a)` is a left eigenvector: `u T = λ u` on the curve of the phase. -/
theorem eigenRow_vecMul (t : S) (T : SpecialLinearGroup (Fin 2) S) (ht : phase T = t) :
    Matrix.vecMul (eigenRow t T)
        ((T : Matrix (Fin 2) (Fin 2) S).map (algebraMap S (curveRing t))) =
      eig t • eigenRow t T := by
  have hdet := Matrix.SpecialLinearGroup.det_coe T
  rw [Matrix.det_fin_two] at hdet
  have htr : (T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 = t := by
    rw [← ht, phase, Matrix.trace_fin_two]
  have hsq := eig_sq t
  have h1 := congrArg (algebraMap S (curveRing t)) hdet
  have h2 := congrArg (algebraMap S (curveRing t)) htr
  simp only [map_sub, map_mul, map_one, map_add] at h1 h2
  ext j
  fin_cases j
  · simp [eigenRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [eigenRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    simp only [AdjoinRoot.algebraMap_eq] at h1 h2 hsq ⊢
    linear_combination -hsq - h1 + eig t * h2

theorem curve_monic (t : S) : (X ^ 2 - C t * X + 1 : S[X]).Monic := by
  monicity!

section Domain

variable [IsDomain S]

/-- A nonzero element of `S` is a non-zero-divisor of the curve's ring, a free `S`-module. -/
theorem algebraMap_mem_nonZeroDivisors (t : S) {s : S} (hs : s ≠ 0) :
    algebraMap S (curveRing t) s ∈ nonZeroDivisors (curveRing t) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro y hy
    rw [← Algebra.smul_def] at hy
    exact ((AdjoinRoot.powerBasis' (curve_monic t)).basis.smul_eq_zero.mp hy).resolve_left hs
  · intro y hy
    rw [mul_comm, ← Algebra.smul_def] at hy
    exact ((AdjoinRoot.powerBasis' (curve_monic t)).basis.smul_eq_zero.mp hy).resolve_left hs

/-- An element whose norm `α ᾱ` is a nonzero element of `S` is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_norm (t : S) {α conj : curveRing t} {N : S} (hN : N ≠ 0)
    (h : α * conj = algebraMap S (curveRing t) N) : α ∈ nonZeroDivisors (curveRing t) := by
  have hN' := algebraMap_mem_nonZeroDivisors t hN
  rw [mem_nonZeroDivisors_iff] at hN' ⊢
  constructor
  · intro y hy
    exact hN'.1 y (by rw [← h, mul_comm α conj, mul_assoc, hy, mul_zero])
  · intro y hy
    exact hN'.2 y (by rw [← h, ← mul_assoc, hy, zero_mul])

/-- A law of phase `t`, with `t² - 4` not a square, has `c ≠ 0`. -/
theorem lower_ne_zero {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) : (T : Matrix (Fin 2) (Fin 2) S) 1 0 ≠ 0 := by
  intro hc
  have hdet := Matrix.SpecialLinearGroup.det_coe T
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have htr : (T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 = t := by
    rw [← ht, phase, Matrix.trace_fin_two]
  have := hnsq ((T : Matrix (Fin 2) (Fin 2) S) 0 0 - (T : Matrix (Fin 2) (Fin 2) S) 1 1) 1
    (by rw [← htr]; linear_combination (-4 : S) * hdet)
  exact one_ne_zero this

/-- The quadratic form `c v₀² + (d - a) v₀ v₁ - b v₁²` of a law of phase `t` has no zero
but `0`, when `t² - 4` is not a square. -/
theorem quadForm_ne_zero {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) {v₀ v₁ : S} (hv : v₀ ≠ 0 ∨ v₁ ≠ 0) :
    (T : Matrix (Fin 2) (Fin 2) S) 1 0 * v₀ * v₀ +
      ((T : Matrix (Fin 2) (Fin 2) S) 1 1 - (T : Matrix (Fin 2) (Fin 2) S) 0 0) * v₀ * v₁ -
      (T : Matrix (Fin 2) (Fin 2) S) 0 1 * v₁ * v₁ ≠ 0 := by
  intro hQ
  have hdet := Matrix.SpecialLinearGroup.det_coe T
  rw [Matrix.det_fin_two] at hdet
  have htr : (T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 = t := by
    rw [← ht, phase, Matrix.trace_fin_two]
  have hc := lower_ne_zero hnsq T ht
  have h1 : v₁ = 0 := hnsq
    (2 * (T : Matrix (Fin 2) (Fin 2) S) 1 0 * v₀ +
      ((T : Matrix (Fin 2) (Fin 2) S) 1 1 - (T : Matrix (Fin 2) (Fin 2) S) 0 0) * v₁) v₁
    (by linear_combination 4 * (T : Matrix (Fin 2) (Fin 2) S) 1 0 * hQ - 4 * v₁ * v₁ * hdet +
      ((T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 + t) * v₁ * v₁ * htr)
  subst h1
  have : (T : Matrix (Fin 2) (Fin 2) S) 1 0 * (v₀ * v₀) = 0 := by linear_combination hQ
  rcases mul_eq_zero.mp this with h | h
  · exact hc h
  · exact hv.elim (fun h0 => h0 (mul_self_eq_zero.mp h)) (fun h0 => h0 rfl)

theorem span_singleton_mul_span_pair {A : Type*} [CommRing A] (a b c : A) :
    Ideal.span {a} * Ideal.span {b, c} = Ideal.span {a * b, a * c} := by
  simp only [Ideal.span, Submodule.span_mul_span, Set.singleton_mul, Set.image_insert_eq,
    Set.image_singleton]

/-- T7's invariance: processing keeps the class of `(c, λ - a)`. -/
theorem sameClass_of_conj (t : S) (hnsq : NonSquareDisc t) (T T' : SpecialLinearGroup (Fin 2) S)
    (P : GL (Fin 2) S) (ht : phase T = t)
    (hT' : (T' : Matrix (Fin 2) (Fin 2) S) =
      (P : Matrix (Fin 2) (Fin 2) S) * T * ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)) :
    SameClass (lawIdeal t T') (lawIdeal t T) := by
  set ι := algebraMap S (curveRing t) with hι
  set Pm : Matrix (Fin 2) (Fin 2) S := (P : Matrix (Fin 2) (Fin 2) S) with hPm
  set Qm : Matrix (Fin 2) (Fin 2) S := ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) with hQm
  have hQP : Qm * Pm = 1 := by rw [hQm, hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ht' : phase T' = t := by
    rw [← ht, phase, phase, hT', Matrix.trace_mul_cycle, hQP, one_mul]
  have hQPA : Qm.map ι * Pm.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ι) (map_one ι)]
  set u := eigenRow t (T : Matrix (Fin 2) (Fin 2) S) with hu_def
  have hu := eigenRow_vecMul t T ht
  set w := Matrix.vecMul u (Qm.map ι) with hw_def
  have hw : Matrix.vecMul w ((T' : Matrix (Fin 2) (Fin 2) S).map ι) = eig t • w := by
    calc Matrix.vecMul w ((T' : Matrix (Fin 2) (Fin 2) S).map ι)
        = Matrix.vecMul u (Qm.map ι * (Pm.map ι * (T : Matrix (Fin 2) (Fin 2) S).map ι *
            Qm.map ι)) := by
          rw [hT', Matrix.map_mul, Matrix.map_mul, hw_def, Matrix.vecMul_vecMul]
      _ = Matrix.vecMul (Matrix.vecMul u ((T : Matrix (Fin 2) (Fin 2) S).map ι)) (Qm.map ι) := by
          rw [← mul_assoc, ← mul_assoc, hQPA, one_mul, ← Matrix.vecMul_vecMul]
      _ = eig t • w := by rw [hu, Matrix.smul_vecMul]
  have hcol : ι ((T' : Matrix (Fin 2) (Fin 2) S) 1 0) * w 1 =
      w 0 * (eig t - ι ((T' : Matrix (Fin 2) (Fin 2) S) 0 0)) := by
    have := congrFun hw 0
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] at this
    linear_combination this
  have huw : Matrix.vecMul w (Pm.map ι) = u := by
    rw [hw_def, Matrix.vecMul_vecMul, hQPA, Matrix.vecMul_one]
  have hspan : Ideal.span {w 0, w 1} = lawIdeal t T := by
    have hl : lawIdeal t T = Ideal.span {u 0, u 1} := by
      simp [lawIdeal, hu_def, eigenRow]
    rw [hl]
    apply le_antisymm
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩ <;>
      · simp only [hw_def, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩ <;>
      · rw [← huw]
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  refine ⟨w 0, ?_, ι ((T' : Matrix (Fin 2) (Fin 2) S) 1 0),
    algebraMap_mem_nonZeroDivisors t (lower_ne_zero hnsq T' ht'), ?_⟩
  · -- the norm of `w 0` is `c Q_T(q)`, `q` the first column of `P⁻¹`
    have hdet := Matrix.SpecialLinearGroup.det_coe T
    rw [Matrix.det_fin_two] at hdet
    have htr : (T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 = t := by
      rw [← ht, phase, Matrix.trace_fin_two]
    have hq : Qm 0 0 ≠ 0 ∨ Qm 1 0 ≠ 0 := by
      by_contra hq
      push Not at hq
      have hd := congrArg Matrix.det hQP
      rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two Qm, hq.1, hq.2] at hd
      simp at hd
    set a := (T : Matrix (Fin 2) (Fin 2) S) 0 0
    set b := (T : Matrix (Fin 2) (Fin 2) S) 0 1
    set c := (T : Matrix (Fin 2) (Fin 2) S) 1 0
    set d := (T : Matrix (Fin 2) (Fin 2) S) 1 1
    set q₀ := Qm 0 0
    set q₁ := Qm 1 0
    have hN : (c * q₀ - a * q₁) * (c * q₀ - a * q₁) + t * (c * q₀ - a * q₁) * q₁ + q₁ * q₁ =
        c * (c * q₀ * q₀ + (d - a) * q₀ * q₁ - b * q₁ * q₁) := by
      linear_combination (a * q₁ * q₁ - c * q₀ * q₁) * htr - q₁ * q₁ * hdet
    refine mem_nonZeroDivisors_of_norm t (α := w 0)
      (conj := ι (c * q₀ - a * q₁ + t * q₁) - ι q₁ * eig t)
      (mul_ne_zero (lower_ne_zero hnsq T ht) (quadForm_ne_zero hnsq T ht hq)) ?_
    rw [← hN]
    have hsq := eig_sq t
    simp only [hw_def, hu_def, eigenRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul]
    linear_combination (-(ι q₁ * ι q₁)) * hsq
  · rw [← hspan, lawIdeal, span_singleton_mul_span_pair, span_singleton_mul_span_pair,
      ← hcol, mul_comm (w 0)]

/-- T7's trivial class: a cyclic vector conjugates the law to the companion tick, and then
the class of `(c, λ - a)` is trivial. -/
theorem trivialClass_of_cyclic (t : S) (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (v : Fin 2 → S) (ht : phase T = t)
    (hv : IsUnit (cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) v).det) :
    (T : Matrix (Fin 2) (Fin 2) S) * cyclicMatrix T v = cyclicMatrix T v * companion t ∧
      SameClass (lawIdeal t T) ⊤ := by
  have hdet := Matrix.SpecialLinearGroup.det_coe T
  rw [Matrix.det_fin_two] at hdet
  have htr : (T : Matrix (Fin 2) (Fin 2) S) 0 0 + (T : Matrix (Fin 2) (Fin 2) S) 1 1 = t := by
    rw [← ht, phase, Matrix.trace_fin_two]
  have hmat :
      (T : Matrix (Fin 2) (Fin 2) S) * cyclicMatrix T v = cyclicMatrix T v * companion t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix, companion, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · linear_combination ((T : Matrix (Fin 2) (Fin 2) S) 0 0 * v 0 +
        (T : Matrix (Fin 2) (Fin 2) S) 0 1 * v 1) * htr - v 0 * hdet
    · linear_combination ((T : Matrix (Fin 2) (Fin 2) S) 1 0 * v 0 +
        (T : Matrix (Fin 2) (Fin 2) S) 1 1 * v 1) * htr - v 1 * hdet
  refine ⟨hmat, ?_⟩
  set P : GL (Fin 2) S := ((Matrix.isUnit_iff_isUnit_det _).mpr hv).unit with hP
  have hPm : (P : Matrix (Fin 2) (Fin 2) S) = cyclicMatrix T v := rfl
  let Cs : SpecialLinearGroup (Fin 2) S :=
    ⟨companion t, by simp [companion, Matrix.det_fin_two]⟩
  have hCt : phase Cs = t := by simp [phase, Cs, companion, Matrix.trace_fin_two]
  set Q : Matrix (Fin 2) (Fin 2) S := ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) with hQ
  have hconj : (T : Matrix (Fin 2) (Fin 2) S) = (P : Matrix (Fin 2) (Fin 2) S) * Cs * Q := by
    calc (T : Matrix (Fin 2) (Fin 2) S)
        = (T : Matrix (Fin 2) (Fin 2) S) * P * Q := by
          rw [hQ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = (P : Matrix (Fin 2) (Fin 2) S) * Cs * Q := by
          rw [hPm, hmat]
  have hcl := sameClass_of_conj t hnsq Cs T P hCt hconj
  have htop : lawIdeal t (Cs : Matrix (Fin 2) (Fin 2) S) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ?_) isUnit_one
    simp [Cs, companion]
  rwa [htop] at hcl

end Domain

end Proofs

/-- **T7** (Latimer–MacDuffee: the class of a law). -/
@[ledger "T7"]
theorem classInvariance : Statement.classInvariance := fun _ _ _ t hnsq T T' P ht hT' =>
  ⟨eigenRow_vecMul t T ht, sameClass_of_conj t hnsq T T' P ht hT'⟩

/-- **T7** (the trivial class). -/
@[ledger "T7"]
theorem trivialClass : Statement.trivialClass := fun _ _ _ t hnsq T v ht hv =>
  trivialClass_of_cyclic t hnsq T v ht hv

/-! ## Non-vacuity

Both statements on the book's tick at pull 2, `K(1)` then `M(-2)`, over the integers. Its
phase is `0`, a quarter turn of order 4 (T13), so its curve ring is `ℤ[λ]/(λ² + 1)`, the
Gaussian integers, and `t² - 4 = -4` is not a square. -/

/-- `t² - 4 = -4` is not a square over the integers. -/
theorem nonSquareDisc_zero : NonSquareDisc (0 : ℤ) := by
  intro y z h
  nlinarith [sq_nonneg y, sq_nonneg z]

/-- Processing the tick by the move `M(1)` keeps its class. -/
example : SameClass (lawIdeal (0 : ℤ) ((Step.move 1).sl * tick 2 * ((Step.move 1).sl)⁻¹ :
      SpecialLinearGroup (Fin 2) ℤ)) (lawIdeal 0 (tick 2)) :=
  (classInvariance ℤ 0 nonSquareDisc_zero (tick 2) _
    (Matrix.SpecialLinearGroup.toGL (Step.move (1 : ℤ)).sl)
    (by simp [phase, tick_mat, Matrix.trace_fin_two])
    rfl).2

/-- The vector `(1, 0)` is cyclic for the tick: `det[v | T v] = 1`. So the tick is
conjugate to the companion `[[0, -1], [1, 0]]`, and its class is trivial. -/
example : (tick 2 : Matrix (Fin 2) (Fin 2) ℤ) * cyclicMatrix (tick 2) ![1, 0] =
      cyclicMatrix (tick 2) ![1, 0] * companion 0 ∧ SameClass (lawIdeal (0 : ℤ) (tick 2)) ⊤ :=
  trivialClass ℤ 0 nonSquareDisc_zero (tick 2) ![1, 0]
    (by simp [phase, tick_mat, Matrix.trace_fin_two])
    (by simp [cyclicMatrix, tick_mat, Matrix.det_fin_two, Matrix.mulVec, dotProduct])

end Artform.Scores
