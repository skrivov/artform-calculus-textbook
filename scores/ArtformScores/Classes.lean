import ArtformScores.StepOrders
import ArtformScores.Euclid

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
- **One class, one law.** The ideal `(c, λ - a)` is the `S`-span of `c` and `λ - a`, since
  `u T = λ u`, and the two are independent over `S`. If `α (c′, λ - a′)` and `β (c, λ - a)`
  span one ideal, they differ by a matrix `P ∈ GL₂(S)`, and the eigenvector equation gives
  `T′ = P⁻¹ T P`. Through the companion tick, a law in the trivial class has a cyclic vector.
- **Every class is a law's,** over a principal ideal domain. A nonzero ideal `I` is free of
  rank 2 over `S` (`Submodule.basisOfPid`). The matrix `T` of `λ` on a basis of `I`
  satisfies `C_t R = R T`, where `R` holds the basis in `1, λ`. So `det T = 1`, and by the
  adjugate `tr T = t`. Then `(c, λ - a)` and `I` are in the same class.
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

theorem curve_natDegree [Nontrivial S] (t : S) : (X ^ 2 - C t * X + 1 : S[X]).natDegree = 2 := by
  compute_degree!

/-- Every element of the curve's ring is `p + q λ`. -/
theorem curve_decomp [Nontrivial S] (t : S) (a : curveRing t) :
    ∃ p q : S, a = algebraMap S (curveRing t) p + algebraMap S (curveRing t) q * eig t := by
  have hf := curve_monic t
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  have hdeg : (g %ₘ (X ^ 2 - C t * X + 1 : S[X])).natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt g hf (by
      intro h1
      have := curve_natDegree t
      rw [h1, natDegree_one] at this
      omega)
    rw [curve_natDegree] at h
    omega
  refine ⟨(g %ₘ (X ^ 2 - C t * X + 1 : S[X])).coeff 0,
    (g %ₘ (X ^ 2 - C t * X + 1 : S[X])).coeff 1, ?_⟩
  have h1 : AdjoinRoot.mk (X ^ 2 - C t * X + 1 : S[X]) g =
      AdjoinRoot.mk (X ^ 2 - C t * X + 1 : S[X]) (g %ₘ (X ^ 2 - C t * X + 1 : S[X])) := by
    conv_lhs => rw [← modByMonic_add_div g (X ^ 2 - C t * X + 1 : S[X])]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  conv_lhs => rw [h1, eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, eig, AdjoinRoot.algebraMap_eq]
  exact add_comm _ _

/-- `1` and `λ` are independent over `S`. -/
theorem curve_coeff_eq_zero [Nontrivial S] (t : S) {p q : S}
    (h : algebraMap S (curveRing t) p + algebraMap S (curveRing t) q * eig t = 0) :
    p = 0 ∧ q = 0 := by
  have hf := curve_monic t
  have hmk : algebraMap S (curveRing t) p + algebraMap S (curveRing t) q * eig t =
      AdjoinRoot.mk (X ^ 2 - C t * X + 1 : S[X]) (C q * X + C p) := by
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, eig, AdjoinRoot.algebraMap_eq]
    ring
  rw [hmk] at h
  have h2 := congrArg (AdjoinRoot.modByMonicHom hf) h
  have hlt : (C q * X + C p : S[X]).degree < (X ^ 2 - C t * X + 1 : S[X]).degree := by
    refine lt_of_le_of_lt degree_linear_le ?_
    rw [degree_eq_natDegree (curve_monic t).ne_zero, curve_natDegree]
    exact_mod_cast (show 1 < 2 by norm_num)
  rw [AdjoinRoot.modByMonicHom_mk, map_zero, (modByMonic_eq_self_iff hf).mpr hlt] at h2
  have e0 := congrArg (coeff · 0) h2
  have e1 := congrArg (coeff · 1) h2
  simp only [coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, zero_add,
    coeff_zero, coeff_mul_X, coeff_C_succ, add_zero] at e0 e1
  exact ⟨e0, e1⟩

/-- The norm `(p + qλ)(p + tq - qλ) = p² + tpq + q²`. -/
theorem curve_mul_conj (t p q : S) :
    (algebraMap S (curveRing t) p + algebraMap S (curveRing t) q * eig t) *
      (algebraMap S (curveRing t) (p + t * q) - algebraMap S (curveRing t) q * eig t) =
    algebraMap S (curveRing t) (p * p + t * p * q + q * q) := by
  have hsq := eig_sq t
  simp only [map_add, map_mul]
  linear_combination (-(algebraMap S (curveRing t) q * algebraMap S (curveRing t) q)) * hsq

theorem SameClass.refl {A : Type*} [CommRing A] (I : Ideal A) : SameClass I I :=
  ⟨1, one_mem _, 1, one_mem _, rfl⟩

theorem SameClass.symm {A : Type*} [CommRing A] {I J : Ideal A} (h : SameClass I J) :
    SameClass J I := by
  obtain ⟨α, hα, β, hβ, h⟩ := h
  exact ⟨β, hβ, α, hα, h.symm⟩

theorem SameClass.trans {A : Type*} [CommRing A] {I J K : Ideal A} (h₁ : SameClass I J)
    (h₂ : SameClass J K) : SameClass I K := by
  obtain ⟨α, hα, β, hβ, h₁⟩ := h₁
  obtain ⟨γ, hγ, δ, hδ, h₂⟩ := h₂
  refine ⟨γ * α, mul_mem hγ hα, β * δ, mul_mem hβ hδ, ?_⟩
  calc Ideal.span {γ * α} * I = Ideal.span {γ} * (Ideal.span {α} * I) := by
        rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    _ = Ideal.span {β} * (Ideal.span {γ} * J) := by rw [h₁, mul_left_comm]
    _ = Ideal.span {β * δ} * K := by
        rw [h₂, ← mul_assoc, Ideal.span_singleton_mul_span_singleton]

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

theorem curveNorm_ne_zero {t : S} (hnsq : NonSquareDisc t) {p q : S} (h : p ≠ 0 ∨ q ≠ 0) :
    p * p + t * p * q + q * q ≠ 0 := by
  intro hN
  have hq : q = 0 := hnsq (2 * p + t * q) q (by linear_combination 4 * hN)
  subst hq
  have : p * p = 0 := by linear_combination hN
  rcases h with h | h
  · exact h (mul_self_eq_zero.mp this)
  · exact h rfl

/-- When `t² - 4` is not a square, every nonzero element of the curve's ring is a
non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_ne_zero {t : S} (hnsq : NonSquareDisc t) {α : curveRing t}
    (hα : α ≠ 0) : α ∈ nonZeroDivisors (curveRing t) := by
  obtain ⟨p, q, rfl⟩ := curve_decomp t α
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    push Not at h
    apply hα
    rw [h.1, h.2, map_zero, zero_mul, add_zero]
  exact mem_nonZeroDivisors_of_norm t (curveNorm_ne_zero hnsq hpq) (curve_mul_conj t p q)

/-- The ideal `(c, λ - a)` of a law of phase `t` is nonzero. -/
theorem lawIdeal_ne_bot {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) : lawIdeal t T ≠ ⊥ := by
  intro h
  have hmem : algebraMap S (curveRing t) ((T : Matrix (Fin 2) (Fin 2) S) 1 0) ∈
      lawIdeal t T := Ideal.subset_span (by simp)
  rw [h, Ideal.mem_bot] at hmem
  exact lower_ne_zero hnsq T ht (curve_coeff_eq_zero t (p := (T : Matrix (Fin 2) (Fin 2) S) 1 0)
    (q := 0) (by rw [map_zero, zero_mul, add_zero]; exact hmem)).1

/-- For a left eigenvector `w` of `T`, the ideal `(w₀, w₁)` is the `S`-span of `w₀` and `w₁`. -/
theorem mem_span_eigen (t : S) (T : Matrix (Fin 2) (Fin 2) S) (w : Fin 2 → curveRing t)
    (hw : Matrix.vecMul w (T.map (algebraMap S (curveRing t))) = eig t • w) {x : curveRing t}
    (hx : x ∈ Ideal.span {w 0, w 1}) :
    ∃ s₀ s₁ : S, x = algebraMap S (curveRing t) s₀ * w 0 + algebraMap S (curveRing t) s₁ * w 1 := by
  obtain ⟨a₀, a₁, rfl⟩ := Ideal.mem_span_pair.mp hx
  obtain ⟨p₀, q₀, rfl⟩ := curve_decomp t a₀
  obtain ⟨p₁, q₁, rfl⟩ := curve_decomp t a₁
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul] at h0 h1
  refine ⟨p₀ + T 0 0 * q₀ + T 0 1 * q₁, p₁ + T 1 0 * q₀ + T 1 1 * q₁, ?_⟩
  simp only [map_add, map_mul]
  linear_combination (-algebraMap S (curveRing t) q₀) * h0 + (-algebraMap S (curveRing t) q₁) * h1

/-- `γ c` and `γ (λ - a)` are independent over `S`, for a non-zero-divisor `γ`. -/
theorem eigenRow_indep {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) {γ : curveRing t} (hγ : γ ∈ nonZeroDivisors (curveRing t)) {s₀ s₁ : S}
    (h : algebraMap S (curveRing t) s₀ * (γ * eigenRow t T 0) +
      algebraMap S (curveRing t) s₁ * (γ * eigenRow t T 1) = 0) : s₀ = 0 ∧ s₁ = 0 := by
  have h' : γ * (algebraMap S (curveRing t) (s₀ * (T : Matrix (Fin 2) (Fin 2) S) 1 0 -
      s₁ * (T : Matrix (Fin 2) (Fin 2) S) 0 0) + algebraMap S (curveRing t) s₁ * eig t) = 0 := by
    rw [← h]
    simp only [eigenRow, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_mul]
    ring
  rw [mem_nonZeroDivisors_iff] at hγ
  obtain ⟨h1, h2⟩ := curve_coeff_eq_zero t (hγ.2 _ (by rw [mul_comm]; exact h'))
  subst h2
  simp only [zero_mul, sub_zero] at h1
  exact ⟨(mul_eq_zero.mp h1).resolve_right (lower_ne_zero hnsq T ht), rfl⟩

/-- A matrix over `S` is read off from `γ u M`, `u = (c, λ - a)`. -/
theorem eq_of_vecMul_eigenRow {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) {γ : curveRing t} (hγ : γ ∈ nonZeroDivisors (curveRing t))
    {M N : Matrix (Fin 2) (Fin 2) S}
    (h : Matrix.vecMul (γ • eigenRow t T) (M.map (algebraMap S (curveRing t))) =
      Matrix.vecMul (γ • eigenRow t T) (N.map (algebraMap S (curveRing t)))) : M = N := by
  have key : ∀ j, M 0 j = N 0 j ∧ M 1 j = N 1 j := by
    intro j
    have hj := congrFun h j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] at hj
    obtain ⟨e0, e1⟩ := eigenRow_indep hnsq T ht hγ (s₀ := M 0 j - N 0 j) (s₁ := M 1 j - N 1 j)
      (by simp only [map_sub]; linear_combination hj)
    exact ⟨sub_eq_zero.mp e0, sub_eq_zero.mp e1⟩
  ext i j
  fin_cases i
  · exact (key j).1
  · exact (key j).2

/-- T7's injectivity: two laws of phase `t` in the same class are processing-equivalent. -/
theorem conj_of_sameClass {t : S} (hnsq : NonSquareDisc t) (T T' : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) (ht' : phase T' = t) (h : SameClass (lawIdeal t T') (lawIdeal t T)) :
    ∃ P : GL (Fin 2) S, (T' : Matrix (Fin 2) (Fin 2) S) =
      (P : Matrix (Fin 2) (Fin 2) S) * T * ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by
  obtain ⟨α, hα, β, hβ, hαβ⟩ := h
  set ι := algebraMap S (curveRing t) with hι
  set Tm := (T : Matrix (Fin 2) (Fin 2) S)
  set Tm' := (T' : Matrix (Fin 2) (Fin 2) S)
  set u := eigenRow t Tm with hu_def
  set u' := eigenRow t Tm' with hu'_def
  have hu := eigenRow_vecMul t T ht
  have hu' := eigenRow_vecMul t T' ht'
  set w := α • u' with hw_def
  set z := β • u with hz_def
  have hw : Matrix.vecMul w (Tm'.map ι) = eig t • w := by
    rw [hw_def, Matrix.smul_vecMul, hu', smul_comm]
  have hz : Matrix.vecMul z (Tm.map ι) = eig t • z := by
    rw [hz_def, Matrix.smul_vecMul, hu, smul_comm]
  have hspan : Ideal.span {w 0, w 1} = Ideal.span {z 0, z 1} := by
    have l1 : lawIdeal t Tm' = Ideal.span {u' 0, u' 1} := by simp [lawIdeal, hu'_def, eigenRow]
    have l2 : lawIdeal t Tm = Ideal.span {u 0, u 1} := by simp [lawIdeal, hu_def, eigenRow]
    rw [l1, l2, span_singleton_mul_span_pair, span_singleton_mul_span_pair] at hαβ
    simpa [hw_def, hz_def] using hαβ
  -- the coordinates of `w` in `z`, and of `z` in `w`
  have hwz : ∀ j, ∃ s₀ s₁ : S, w j = ι s₀ * z 0 + ι s₁ * z 1 := fun j =>
    mem_span_eigen t Tm z hz (by rw [← hspan]; fin_cases j <;> exact Ideal.subset_span (by simp))
  have hzw : ∀ j, ∃ s₀ s₁ : S, z j = ι s₀ * w 0 + ι s₁ * w 1 := fun j =>
    mem_span_eigen t Tm' w hw (by rw [hspan]; fin_cases j <;> exact Ideal.subset_span (by simp))
  choose a b hab using hwz
  choose c d hcd using hzw
  set P : Matrix (Fin 2) (Fin 2) S := !![a 0, a 1; b 0, b 1] with hP
  set Q : Matrix (Fin 2) (Fin 2) S := !![c 0, c 1; d 0, d 1] with hQ
  have hwP : w = Matrix.vecMul z (P.map ι) := by
    funext j
    rw [hab j]
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hP] <;> ring
  have hzQ : z = Matrix.vecMul w (Q.map ι) := by
    funext j
    rw [hcd j]
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hQ] <;> ring
  have hQP : Q * P = 1 := by
    apply eq_of_vecMul_eigenRow hnsq T' ht' hα
    rw [Matrix.map_mul, ← Matrix.vecMul_vecMul, ← hzQ, ← hwP, Matrix.map_one _ (map_zero ι)
      (map_one ι), Matrix.vecMul_one]
  have hPQ : P * Q = 1 := by
    apply eq_of_vecMul_eigenRow hnsq T ht hβ
    rw [Matrix.map_mul, ← Matrix.vecMul_vecMul, ← hwP, ← hzQ, Matrix.map_one _ (map_zero ι)
      (map_one ι), Matrix.vecMul_one]
  have hPT : P * Tm' = Tm * P := by
    apply eq_of_vecMul_eigenRow hnsq T ht hβ
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hwP,
      hw, ← hz_def, hz, Matrix.smul_vecMul, ← hwP]
  refine ⟨⟨Q, P, hQP, hPQ⟩, ?_⟩
  change Tm' = Q * Tm * P
  rw [mul_assoc, ← hPT, ← mul_assoc, hQP, one_mul]

/-- The converse of the trivial-class criterion: a law in the trivial class has a cyclic
vector. -/
theorem cyclic_of_trivialClass {t : S} (hnsq : NonSquareDisc t) (T : SpecialLinearGroup (Fin 2) S)
    (ht : phase T = t) (h : SameClass (lawIdeal t T) ⊤) :
    ∃ v : Fin 2 → S, IsUnit (cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) v).det := by
  let Cs : SpecialLinearGroup (Fin 2) S :=
    ⟨companion t, by simp [companion, Matrix.det_fin_two]⟩
  have hCt : phase Cs = t := by simp [phase, Cs, companion, Matrix.trace_fin_two]
  have htop : lawIdeal t (Cs : Matrix (Fin 2) (Fin 2) S) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ?_) isUnit_one
    simp [Cs, companion]
  rw [← htop] at h
  obtain ⟨P, hP⟩ := conj_of_sameClass hnsq Cs T hCt ht h
  set Pm := (P : Matrix (Fin 2) (Fin 2) S) with hPm
  have hTP : (T : Matrix (Fin 2) (Fin 2) S) * Pm = Pm * companion t := by
    rw [hP, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have e0 := congrFun (congrFun hTP 0) 0
  have e1 := congrFun (congrFun hTP 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, companion, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_zero, mul_one, zero_add] at e0 e1
  refine ⟨fun i => Pm i 0, ?_⟩
  have hcyc : cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) (fun i => Pm i 0) = Pm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0, e1]
  rw [hcyc]
  exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit

/-- T7's surjectivity: over a principal ideal domain, every nonzero ideal of the curve's ring
is in the class of the ideal of a law of phase `t`. -/
theorem exists_law_of_ideal [IsPrincipalIdealRing S] {t : S} (hnsq : NonSquareDisc t)
    (I : Ideal (curveRing t)) (hI : I ≠ ⊥) :
    ∃ T : SpecialLinearGroup (Fin 2) S, phase T = t ∧ SameClass (lawIdeal t T) I := by
  set ι := algebraMap S (curveRing t) with hι
  let pb := AdjoinRoot.powerBasis' (curve_monic t)
  have : Module.Finite S (curveRing t) := Module.Finite.of_basis pb.basis
  have : Module.Free S (curveRing t) := Module.Free.of_basis pb.basis
  have hdimA : Module.finrank S (curveRing t) = 2 := by
    rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin]
    exact curve_natDegree t
  obtain ⟨n, e⟩ := Submodule.basisOfPid pb.basis (I.restrictScalars S)
  have : Module.Finite S (I.restrictScalars S) := Module.Finite.of_basis e
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hxnzd := mem_nonZeroDivisors_of_ne_zero hnsq hx0
  let φ : curveRing t →ₗ[S] I.restrictScalars S :=
    { toFun := fun a => ⟨a * x, I.mul_mem_left a hxI⟩
      map_add' := fun a b => by ext; simp [add_mul]
      map_smul' := fun s a => by ext; simp [Algebra.smul_def, mul_assoc] }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : (a - b) * x = 0 := by
      have := congrArg Subtype.val hab
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [sub_mul, this, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hxnzd).2 _ h1)
  have hn : n = 2 := by
    have h1 := Submodule.finrank_le (I.restrictScalars S)
    have h2 := LinearMap.finrank_le_finrank_of_injective hφ
    rw [Module.finrank_eq_card_basis e, Fintype.card_fin] at h1 h2
    omega
  let e2 := e.reindex (finCongr hn)
  set E : Fin 2 → curveRing t := fun j => (e2 j : curveRing t) with hE
  have hEI : ∀ j, E j ∈ I := fun j => (e2 j).2
  -- the matrix of `λ` on the basis `E`
  let y : Fin 2 → I.restrictScalars S := fun j => ⟨eig t * E j, I.mul_mem_left _ (hEI j)⟩
  set Tm : Matrix (Fin 2) (Fin 2) S := Matrix.of fun i j => e2.repr (y j) i with hTm
  have hlamE : ∀ j, eig t * E j = ι (Tm 0 j) * E 0 + ι (Tm 1 j) * E 1 := by
    intro j
    have := congrArg Subtype.val (e2.sum_repr (y j))
    rw [Submodule.coe_sum, Fin.sum_univ_two] at this
    simp only [Submodule.coe_smul, Algebra.smul_def] at this
    exact this.symm
  -- the coordinates of the basis in `1, λ`
  choose pc qc hpq using curve_decomp t
  set Rm : Matrix (Fin 2) (Fin 2) S := !![pc (E 0), pc (E 1); qc (E 0), qc (E 1)] with hRm
  have hsq := eig_sq t
  have hcol : ∀ j, -qc (E j) = Tm 0 j * pc (E 0) + Tm 1 j * pc (E 1) ∧
      pc (E j) + t * qc (E j) = Tm 0 j * qc (E 0) + Tm 1 j * qc (E 1) := by
    intro j
    have hj := curve_coeff_eq_zero t
      (p := -qc (E j) - (Tm 0 j * pc (E 0) + Tm 1 j * pc (E 1)))
      (q := pc (E j) + t * qc (E j) - (Tm 0 j * qc (E 0) + Tm 1 j * qc (E 1))) (by
        have h0 := hpq (E 0)
        have h1 := hpq (E 1)
        have hjj := hpq (E j)
        simp only [map_sub, map_add, map_mul, map_neg]
        linear_combination hlamE j + (-eig t) * hjj + ι (Tm 0 j) * h0 + ι (Tm 1 j) * h1 +
          (-ι (qc (E j))) * hsq)
    exact ⟨by linear_combination hj.1, by linear_combination hj.2⟩
  have hCR : companion t * Rm = Rm * Tm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [companion, Matrix.mul_apply, Fin.sum_univ_two, hRm]
    · linear_combination (hcol 0).1
    · linear_combination (hcol 1).1
    · linear_combination (hcol 0).2
    · linear_combination (hcol 1).2
  have hdetR : Rm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hRv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have r0 := congrFun hRv 0
    have r1 := congrFun hRv 1
    simp only [Matrix.mulVec, dotProduct, hRm, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one,
      Pi.zero_apply] at r0 r1
    have hsum : ∑ i, v i • e2 i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Fin.sum_univ_two]
      simp only [Submodule.coe_smul, Algebra.smul_def, Submodule.coe_zero]
      have h0 := hpq (E 0)
      have h1 := hpq (E 1)
      change ι (v 0) * E 0 + ι (v 1) * E 1 = 0
      rw [h0, h1]
      have r0' := congrArg ι r0
      have r1' := congrArg ι r1
      simp only [map_add, map_mul, map_zero] at r0' r1'
      linear_combination r0' + eig t * r1'
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp e2.linearIndependent v hsum i)
  have hdetC : (companion t).det = 1 := by simp [companion, Matrix.det_fin_two]
  have hdetT : Tm.det = 1 := by
    have := congrArg Matrix.det hCR
    rw [Matrix.det_mul, Matrix.det_mul, hdetC, one_mul] at this
    have h2 : Rm.det * (Tm.det - 1) = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hdetR)
  have htrT : Tm.trace = t := by
    have h1 : Rm.det • Tm = Rm.adjugate * companion t * Rm := by
      rw [mul_assoc, hCR, ← mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
    have h2 := congrArg Matrix.trace h1
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle, Matrix.mul_adjugate, Matrix.smul_mul, one_mul,
      Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at h2
    have h3 : (companion t).trace = t := by simp [companion, Matrix.trace_fin_two]
    rw [h3] at h2
    exact (mul_left_cancel₀ hdetR h2)
  let T : SpecialLinearGroup (Fin 2) S := ⟨Tm, hdetT⟩
  have hT : phase T = t := htrT
  refine ⟨T, hT, E 0, mem_nonZeroDivisors_of_ne_zero hnsq ?_, ι (Tm 1 0),
    algebraMap_mem_nonZeroDivisors t (lower_ne_zero hnsq T hT), ?_⟩
  · intro h0
    exact e2.ne_zero 0 (Subtype.ext h0)
  · have hspan : Ideal.span {E 0, E 1} = I := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hEI 0, hEI 1⟩
      · intro z hz
        have := congrArg Subtype.val (e2.sum_repr ⟨z, hz⟩)
        rw [Submodule.coe_sum, Fin.sum_univ_two] at this
        simp only [Submodule.coe_smul, Algebra.smul_def] at this
        rw [← this]
        exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩
    have hl : lawIdeal t (T : Matrix (Fin 2) (Fin 2) S) =
        Ideal.span {ι (Tm 1 0), eig t - ι (Tm 0 0)} :=
      rfl
    have h0 := hlamE 0
    rw [hl, span_singleton_mul_span_pair, ← hspan, span_singleton_mul_span_pair]
    congr 2
    · exact mul_comm _ _
    · simp only [Set.singleton_eq_singleton_iff]
      linear_combination h0

end Domain

end Proofs

/-- **T7** (Latimer–MacDuffee: the class of a law). -/
@[ledger "T7"]
theorem classInvariance : Statement.classInvariance := fun _ _ _ t hnsq T T' P ht hT' =>
  ⟨eigenRow_vecMul t T ht, sameClass_of_conj t hnsq T T' P ht hT'⟩

/-- **T7** (the trivial class). -/
@[ledger "T7"]
theorem trivialClass : Statement.trivialClass := fun _ _ _ t hnsq T ht =>
  ⟨fun v hv => (trivialClass_of_cyclic t hnsq T v ht hv).1,
    ⟨cyclic_of_trivialClass hnsq T ht, fun ⟨v, hv⟩ => (trivialClass_of_cyclic t hnsq T v ht hv).2⟩⟩

/-- **T7** (Latimer–MacDuffee: one class, one law up to processing). -/
@[ledger "T7"]
theorem classesOneToOne : Statement.classesOneToOne := fun _ _ _ t hnsq T T' ht ht' =>
  ⟨lawIdeal_ne_bot hnsq T ht, conj_of_sameClass hnsq T T' ht ht',
    fun ⟨P, hP⟩ => sameClass_of_conj t hnsq T T' P ht hP⟩

/-- **T7** (Latimer–MacDuffee: every class is a law's). -/
@[ledger "T7"]
theorem classesOnto : Statement.classesOnto := fun _ _ _ _ _ hnsq I hI =>
  exists_law_of_ideal hnsq I hI

/-! ## Non-vacuity

The statements on the book's tick at pull 2, `K(1)` then `M(-2)`, over the integers. Its
phase is `0`, a quarter turn of order 4 (T13), so its curve ring is `ℤ[λ]/(λ² + 1)`, the
Gaussian integers, and `t² - 4 = -4` is not a square. The integers are a principal ideal
domain, and so is the ledger's `F[x, 1/x]` (`Euclid.lean`). -/

/-- `t² - 4 = -4` is not a square over the integers. -/
theorem nonSquareDisc_zero : NonSquareDisc (0 : ℤ) := by
  intro y z h
  nlinarith [sq_nonneg y, sq_nonneg z]

theorem phase_tick_two : phase (tick 2) = 0 := by
  simp [phase, tick_mat, Matrix.trace_fin_two]

/-- Processing the tick by the move `M(1)` keeps its class. -/
example : SameClass (lawIdeal (0 : ℤ) ((Step.move 1).sl * tick 2 * ((Step.move 1).sl)⁻¹ :
      SpecialLinearGroup (Fin 2) ℤ)) (lawIdeal 0 (tick 2)) :=
  (classInvariance ℤ 0 nonSquareDisc_zero (tick 2) _
    (Matrix.SpecialLinearGroup.toGL (Step.move (1 : ℤ)).sl) phase_tick_two rfl).2

/-- The vector `(1, 0)` is cyclic for the tick: `det[v | T v] = 1`. So the tick is
conjugate to the companion `[[0, -1], [1, 0]]`, and its class is trivial. -/
example : (tick 2 : Matrix (Fin 2) (Fin 2) ℤ) * cyclicMatrix (tick 2) ![1, 0] =
      cyclicMatrix (tick 2) ![1, 0] * companion 0 ∧ SameClass (lawIdeal (0 : ℤ) (tick 2)) ⊤ := by
  have hv : IsUnit (cyclicMatrix (tick 2 : Matrix (Fin 2) (Fin 2) ℤ) ![1, 0]).det := by
    simp [cyclicMatrix, tick_mat, Matrix.det_fin_two, Matrix.mulVec, dotProduct]
  obtain ⟨h1, h2⟩ := trivialClass ℤ 0 nonSquareDisc_zero (tick 2) phase_tick_two
  exact ⟨h1 _ hv, h2.mpr ⟨_, hv⟩⟩

/-- The companion `C₀ = [[0, -1], [1, 0]]` and the tick are both in the trivial class, so
processing turns the tick into `C₀`. -/
example : ∃ P : GL (Fin 2) ℤ, (companion 0 : Matrix (Fin 2) (Fin 2) ℤ) =
    (P : Matrix (Fin 2) (Fin 2) ℤ) * tick 2 *
      ((P⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  let C₀ : SpecialLinearGroup (Fin 2) ℤ := ⟨companion 0, by simp [companion, Matrix.det_fin_two]⟩
  have hC : phase C₀ = 0 := by simp [phase, C₀, companion, Matrix.trace_fin_two]
  have h1 := (trivialClass ℤ 0 nonSquareDisc_zero (tick 2) phase_tick_two).2.mpr
    ⟨![1, 0], by simp [cyclicMatrix, tick_mat, Matrix.det_fin_two, Matrix.mulVec, dotProduct]⟩
  have htop : lawIdeal (0 : ℤ) (C₀ : Matrix (Fin 2) (Fin 2) ℤ) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ?_) isUnit_one
    simp [C₀, companion]
  have h2 : SameClass (lawIdeal (0 : ℤ) (C₀ : Matrix (Fin 2) (Fin 2) ℤ)) ⊤ :=
    htop ▸ SameClass.refl _
  exact ((classesOneToOne ℤ 0 nonSquareDisc_zero (tick 2) C₀ phase_tick_two hC).2.mp
    (h2.trans h1.symm))

/-- The processed tick `M(1) T M(1)⁻¹` is in the trivial class too, by invariance, so it has
a cyclic vector, by the converse. -/
example : ∃ v : Fin 2 → ℤ, IsUnit (cyclicMatrix (((Step.move 1).sl * tick 2 *
      ((Step.move 1).sl)⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) v).det := by
  have hT' : phase ((Step.move 1).sl * tick 2 * ((Step.move 1).sl)⁻¹ :
      SpecialLinearGroup (Fin 2) ℤ) = 0 := by
    rw [← phase_tick_two, phase, phase, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      one_mul]
  have h1 := (classInvariance ℤ 0 nonSquareDisc_zero (tick 2)
    ((Step.move 1).sl * tick 2 * ((Step.move 1).sl)⁻¹ : SpecialLinearGroup (Fin 2) ℤ)
    (Matrix.SpecialLinearGroup.toGL (Step.move (1 : ℤ)).sl) phase_tick_two rfl).2
  have h2 := (trivialClass ℤ 0 nonSquareDisc_zero (tick 2) phase_tick_two).2.mpr
    ⟨![1, 0], by simp [cyclicMatrix, tick_mat, Matrix.det_fin_two, Matrix.mulVec, dotProduct]⟩
  exact (trivialClass ℤ 0 nonSquareDisc_zero _ hT').2.mp (h1.trans h2)

/-- Every nonzero ideal of the Gaussian integers is the class of a law of phase `0`; here
`(1 + λ)`, the prime `1 + i`. -/
example : ∃ T : SpecialLinearGroup (Fin 2) ℤ, phase T = 0 ∧
    SameClass (lawIdeal (0 : ℤ) T) (Ideal.span {1 + eig (0 : ℤ)}) := by
  refine classesOnto ℤ 0 nonSquareDisc_zero _ ?_
  intro h
  have hmem : 1 + eig (0 : ℤ) ∈ (⊥ : Ideal (curveRing (0 : ℤ))) := h ▸ Ideal.subset_span rfl
  rw [Ideal.mem_bot] at hmem
  exact one_ne_zero (curve_coeff_eq_zero (0 : ℤ) (p := 1) (q := 1) (by simpa using hmem)).1

/-- The ledger's stencil ring `F[x, 1/x]` meets the hypotheses of `classesOnto`. -/
example (F : Type) [Field F] :
    IsDomain (LaurentPolynomial F) ∧ IsPrincipalIdealRing (LaurentPolynomial F) :=
  ⟨inferInstance, inferInstance⟩

end Artform.Scores
