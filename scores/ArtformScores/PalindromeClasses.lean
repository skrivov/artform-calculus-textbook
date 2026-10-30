import ArtformScores.Classes

/-!
# Palindromes and time reversal

The ledger's T12 says that palindromes lie exactly in the classes that time reversal fixes, and meet
each of them. The second half holds only with a condition, which this file proves. A law `T` is
processing-equivalent to a palindrome exactly when some invertible `P` has `P T P⁻¹ = T⁻¹` with
`-det P` a square.
- **Palindrome to reversal.** `P = Q⁻¹ diag(1, -1) Q`, of determinant `-1`.
- **Reversal to palindrome.** `P` anticommutes with `N = T - t/2`, so it is traceless, and
  `P² = -det P = w²`. Its eigenlines for `w` and `-w` are free and split the plane, over a principal
  ideal domain with `2` invertible, and `N` swaps them. In their basis `N` has no diagonal.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

section Palindrome

variable {S : Type*} [CommRing S] [IsDomain S]

local notation "M2" => Matrix (Fin 2) (Fin 2) S
local notation "GL2" => Matrix.GeneralLinearGroup (Fin 2) S
local notation "SL2" => SpecialLinearGroup (Fin 2) S

/-- A coprime pair on a nonzero vector, over a principal ideal domain. -/
theorem exists_primitive [IsPrincipalIdealRing S] {y₀ y₁ : S} (hy : y₀ ≠ 0 ∨ y₁ ≠ 0) :
    ∃ d v₀ v₁ : S, d ≠ 0 ∧ y₀ = d * v₀ ∧ y₁ = d * v₁ ∧ IsCoprime v₀ v₁ := by
  obtain ⟨d, hd⟩ := IsPrincipalIdealRing.principal (Ideal.span {y₀, y₁})
  have h0 : y₀ ∈ Ideal.span {y₀, y₁} := Ideal.subset_span (by simp)
  have h1 : y₁ ∈ Ideal.span {y₀, y₁} := Ideal.subset_span (by simp)
  have hdm : d ∈ Ideal.span {y₀, y₁} := by
    rw [hd]
    exact Submodule.mem_span_singleton_self d
  rw [hd, Submodule.mem_span_singleton] at h0 h1
  obtain ⟨v₀, hv₀⟩ := h0
  obtain ⟨v₁, hv₁⟩ := h1
  rw [Ideal.mem_span_pair] at hdm
  obtain ⟨a, b, hab⟩ := hdm
  simp only [smul_eq_mul] at hv₀ hv₁
  have hd0 : d ≠ 0 := by
    rintro rfl
    rcases hy with h | h
    · exact h (by simpa using hv₀.symm)
    · exact h (by simpa using hv₁.symm)
  refine ⟨d, v₀, v₁, hd0, by rw [← hv₀, mul_comm], by rw [← hv₁, mul_comm], a, b, ?_⟩
  apply mul_left_cancel₀ hd0
  rw [mul_one]
  rw [← hv₀, ← hv₁] at hab
  linear_combination hab

/-- An eigenvector of `P` with the eigenvalue `w`, primitive, from a nonzero column of `P + w`. -/
theorem exists_eigen [IsPrincipalIdealRing S] {p q r s w : S} (h1 : p * p + q * r = w * w)
    (h2 : r * p + s * r = 0) (h3 : p * q + q * s = 0) (h4 : r * q + s * s = w * w)
    (hne : p + w ≠ 0 ∨ r ≠ 0 ∨ q ≠ 0 ∨ s + w ≠ 0) :
    ∃ v₀ v₁ : S, IsCoprime v₀ v₁ ∧ p * v₀ + q * v₁ = w * v₀ ∧ r * v₀ + s * v₁ = w * v₁ := by
  have key : ∀ y₀ y₁ : S, (y₀ ≠ 0 ∨ y₁ ≠ 0) → p * y₀ + q * y₁ = w * y₀ →
      r * y₀ + s * y₁ = w * y₁ →
      ∃ v₀ v₁ : S, IsCoprime v₀ v₁ ∧ p * v₀ + q * v₁ = w * v₀ ∧ r * v₀ + s * v₁ = w * v₁ := by
    intro y₀ y₁ hy e1 e2
    obtain ⟨d, v₀, v₁, hd, rfl, rfl, hc⟩ := exists_primitive hy
    refine ⟨v₀, v₁, hc, ?_, ?_⟩
    · apply mul_left_cancel₀ hd
      linear_combination e1
    · apply mul_left_cancel₀ hd
      linear_combination e2
  by_cases hcol : p + w ≠ 0 ∨ r ≠ 0
  · refine key (p + w) r hcol ?_ ?_
    · linear_combination h1
    · linear_combination h2
  · refine key q (s + w) ?_ ?_ ?_
    · rcases hne with h | h | h | h
      · exact absurd (Or.inl h) hcol
      · exact absurd (Or.inr h) hcol
      · exact Or.inl h
      · exact Or.inr h
    · linear_combination h3
    · linear_combination h4

/-- An eigenvector line is one line: two vectors with the same eigenvalue of a traceless `P`, one
of them primitive, are proportional. -/
theorem eigen_multiple {p q r w u₀ u₁ v₀ v₁ : S} (h2 : (2 : S) ≠ 0) (hw : w ≠ 0)
    (hu0 : p * u₀ + q * u₁ = w * u₀) (hu1 : r * u₀ + -p * u₁ = w * u₁)
    (hv0 : p * v₀ + q * v₁ = w * v₀) (hv1 : r * v₀ + -p * v₁ = w * v₁) (hc : IsCoprime v₀ v₁) :
    ∃ μ : S, u₀ = μ * v₀ ∧ u₁ = μ * v₁ := by
  have hdet : u₀ * v₁ - u₁ * v₀ = 0 := by
    have : (2 * w) * (u₀ * v₁ - u₁ * v₀) = 0 := by
      linear_combination (-v₁) * hu0 + v₀ * hu1 - u₀ * hv1 + u₁ * hv0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hw)
  obtain ⟨α, β, hab⟩ := hc
  refine ⟨α * u₀ + β * u₁, ?_, ?_⟩
  · linear_combination (-u₀) * hab + β * hdet
  · linear_combination (-u₁) * hab - α * hdet

/-- **The criterion for palindromes.** Over a principal ideal domain in which `2` is invertible, a
law is processing-equivalent to a palindrome exactly when some `P` reverses it, with `-det P` a
square. The hard direction. -/
theorem palindrome_of_reversal [IsPrincipalIdealRing S] [Invertible (2 : S)] (T : SL2) (P : GL2)
    (hP : P.1 * T.1 = ((T⁻¹ : SL2) : M2) * P.1) {w : S} (hw : -(P.1.det) = w * w) :
    ∃ Q : GL2, (Q.1 * T.1 * (Q⁻¹ : GL2).1) 0 0 = (Q.1 * T.1 * (Q⁻¹ : GL2).1) 1 1 := by
  have h2 : (2 : S) ≠ 0 := Invertible.ne_zero 2
  -- the entries
  set a := T.1 0 0 with ha
  set b := T.1 0 1 with hb
  set c := T.1 1 0 with hc
  set d := T.1 1 1 with hd
  have hT : T.1 = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdetT : a * d - b * c = 1 := by
    have := T.2
    rw [hT, Matrix.det_fin_two_of] at this
    exact this
  set p := P.1 0 0 with hp
  set q := P.1 0 1 with hq
  set r := P.1 1 0 with hr
  set s := P.1 1 1 with hs
  have hPm : P.1 = !![p, q; r, s] := Matrix.eta_fin_two _
  have hTinv : ((T⁻¹ : SL2) : M2) = !![d, -b; -c, a] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hT, Matrix.adjugate_fin_two_of]
  rw [hPm, hT, hTinv, Matrix.mul_fin_two, Matrix.mul_fin_two] at hP
  have e00 : p * a + q * c = d * p + -b * r := congrFun (congrFun hP 0) 0
  have e01 : p * b + q * d = d * q + -b * s := congrFun (congrFun hP 0) 1
  have e10 : r * a + s * c = -c * p + a * r := congrFun (congrFun hP 1) 0
  have e11 : r * b + s * d = -c * q + a * s := congrFun (congrFun hP 1) 1
  by_cases htriv : b = 0 ∧ c = 0 ∧ a = d
  · refine ⟨1, ?_⟩
    obtain ⟨-, -, h⟩ := htriv
    simpa using h
  have htr : p + s = 0 := by
    by_contra hne
    apply htriv
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp (show (p + s) * b = 0 by linear_combination e01)).resolve_left hne
    · exact (mul_eq_zero.mp (show (p + s) * c = 0 by linear_combination e10)).resolve_left hne
    · have : (p + s) * (a - d) = 0 := by linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  have hs' : s = -p := by linear_combination htr
  have hdetP : P.1.det = p * s - q * r := by
    rw [hPm, Matrix.det_fin_two_of]
  have hsq : p * p + q * r = w * w := by
    rw [← hw, hdetP, hs']
    ring
  -- `w` is a unit
  have hunitdet : IsUnit (P.1.det) := by
    have := P.isUnit.map (Matrix.detMonoidHom : M2 →* S)
    exact this
  obtain ⟨u, hu⟩ := hunitdet
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (u : S) = 0 := by
      rw [hu]
      linear_combination -hw
    exact u.ne_zero this
  -- the two eigenvectors
  have hwne : ¬ (p + w = 0 ∧ s + w = 0) := by
    rintro ⟨h3, h4⟩
    have : 2 * w = 0 := by linear_combination h3 + h4 - htr
    exact (mul_ne_zero h2 hw0) this
  have hwne' : ¬ (p - w = 0 ∧ s - w = 0) := by
    rintro ⟨h3, h4⟩
    have : 2 * w = 0 := by linear_combination htr - h3 - h4
    exact (mul_ne_zero h2 hw0) this
  obtain ⟨v₀, v₁, hc₁, hv0, hv1⟩ := exists_eigen (p := p) (q := q) (r := r) (s := -p) (w := w) hsq
    (by ring) (by ring) (by linear_combination hsq)
    (by
      by_contra hall
      push Not at hall
      exact hwne ⟨hall.1, by rw [hs']; linear_combination hall.2.2.2⟩)
  obtain ⟨v₀', v₁', hc₂, hv0', hv1'⟩ := exists_eigen (p := -p) (q := -q) (r := -r) (s := p) (w := w)
    (by linear_combination hsq) (by ring) (by ring) (by linear_combination hsq)
    (by
      by_contra hall
      push Not at hall
      exact hwne' ⟨by linear_combination -hall.1, by rw [hs']; linear_combination -hall.2.2.2⟩)
  have hv0'' : p * v₀' + q * v₁' = -w * v₀' := by linear_combination -hv0'
  have hv1'' : r * v₀' + -p * v₁' = -w * v₁' := by linear_combination -hv1'
  have hv1 : r * v₀ + -p * v₁ = w * v₁ := hv1
  -- the inverse of `w`
  obtain ⟨w', hw'⟩ : ∃ w' : S, w * w' = 1 := by
    refine ⟨w * ((u⁻¹ : Sˣ) : S) * (-1), ?_⟩
    have h5 : (u : S) * ((u⁻¹ : Sˣ) : S) = 1 := u.mul_inv
    rw [hu] at h5
    linear_combination ((u⁻¹ : Sˣ) : S) * hw + h5
  set ι : S := ⅟2 with hι
  have hι2 : 2 * ι = 1 := mul_invOf_self 2
  have hmw : -w ≠ 0 := neg_ne_zero.mpr hw0
  -- every vector splits along the two eigenvectors
  have hsplit : ∀ x y : S, ∃ α β : S, x = α * v₀ + β * v₀' ∧ y = α * v₁ + β * v₁' := by
    intro x y
    have hE1 : p * (ι * (x + w' * (p * x + q * y))) + q * (ι * (y + w' * (r * x + -p * y))) =
        w * (ι * (x + w' * (p * x + q * y))) := by
      linear_combination (ι * w' * x) * hsq + (ι * (w * x - (p * x + q * y))) * hw'
    have hE2 : r * (ι * (x + w' * (p * x + q * y))) + -p * (ι * (y + w' * (r * x + -p * y))) =
        w * (ι * (y + w' * (r * x + -p * y))) := by
      linear_combination (ι * w' * y) * hsq + (ι * (w * y - (r * x + -p * y))) * hw'
    have hE3 : p * (ι * (x - w' * (p * x + q * y))) + q * (ι * (y - w' * (r * x + -p * y))) =
        -w * (ι * (x - w' * (p * x + q * y))) := by
      linear_combination (-ι * w' * x) * hsq + (-ι * ((p * x + q * y) + w * x)) * hw'
    have hE4 : r * (ι * (x - w' * (p * x + q * y))) + -p * (ι * (y - w' * (r * x + -p * y))) =
        -w * (ι * (y - w' * (r * x + -p * y))) := by
      linear_combination (-ι * w' * y) * hsq + (-ι * ((r * x + -p * y) + w * y)) * hw'
    obtain ⟨μ, hμ0, hμ1⟩ := eigen_multiple h2 hw0 hE1 hE2 hv0 hv1 hc₁
    obtain ⟨ν, hν0, hν1⟩ := eigen_multiple h2 hmw hE3 hE4 hv0'' hv1'' hc₂
    refine ⟨μ, ν, ?_, ?_⟩
    · rw [← hμ0, ← hν0]
      linear_combination (-x) * hι2
    · rw [← hμ1, ← hν1]
      linear_combination (-y) * hι2
  obtain ⟨x00, x10, h00, h10⟩ := hsplit 1 0
  obtain ⟨x01, x11, h01, h11⟩ := hsplit 0 1
  -- the change of basis
  let R : M2 := !![v₀, v₀'; v₁, v₁']
  let X : M2 := !![x00, x01; x10, x11]
  have hRX : R * X = 1 := by
    simp only [R, X, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination -h00
    · linear_combination -h01
    · linear_combination -h10
    · linear_combination -h11
  have hXR : X * R = 1 := mul_eq_one_comm.mp hRX
  let Q : GL2 := ⟨X, R, hXR, hRX⟩
  refine ⟨Q, ?_⟩
  change (X * T.1 * R) 0 0 = (X * T.1 * R) 1 1
  have hXR00 : x00 * v₀ + x01 * v₁ = 1 := by
    have := congrFun (congrFun hXR 0) 0
    simpa [X, R, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hXR01 : x00 * v₀' + x01 * v₁' = 0 := by
    have := congrFun (congrFun hXR 0) 1
    simpa [X, R, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hXR10 : x10 * v₀ + x11 * v₁ = 0 := by
    have := congrFun (congrFun hXR 1) 0
    simpa [X, R, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hXR11 : x10 * v₀' + x11 * v₁' = 1 := by
    have := congrFun (congrFun hXR 1) 1
    simpa [X, R, Matrix.mul_apply, Fin.sum_univ_two] using this
  -- `2 N` swaps the two eigenlines
  have hE5 : p * (a - d) + q * c + b * r = 0 := by linear_combination e00
  have hG1 : p * ((a - d) * v₀ + 2 * b * v₁) + q * (2 * c * v₀ - (a - d) * v₁) =
      -w * ((a - d) * v₀ + 2 * b * v₁) := by
    linear_combination 2 * v₀ * hE5 - (a - d) * hv0 - 2 * b * hv1
  have hG2 : r * ((a - d) * v₀ + 2 * b * v₁) + -p * (2 * c * v₀ - (a - d) * v₁) =
      -w * (2 * c * v₀ - (a - d) * v₁) := by
    linear_combination 2 * v₁ * hE5 - 2 * c * hv0 + (a - d) * hv1
  have hG3 : p * ((a - d) * v₀' + 2 * b * v₁') + q * (2 * c * v₀' - (a - d) * v₁') =
      w * ((a - d) * v₀' + 2 * b * v₁') := by
    linear_combination 2 * v₀' * hE5 - (a - d) * hv0'' - 2 * b * hv1''
  have hG4 : r * ((a - d) * v₀' + 2 * b * v₁') + -p * (2 * c * v₀' - (a - d) * v₁') =
      w * (2 * c * v₀' - (a - d) * v₁') := by
    linear_combination 2 * v₁' * hE5 - 2 * c * hv0'' + (a - d) * hv1''
  obtain ⟨μ, hμ0, hμ1⟩ := eigen_multiple h2 hmw hG1 hG2 hv0'' hv1'' hc₂
  obtain ⟨ν, hν0, hν1⟩ := eigen_multiple h2 hw0 hG3 hG4 hv0 hv1 hc₁
  have h1 : 2 * (X * T.1 * R) 0 0 = a + d := by
    simp only [X, R, hT, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    linear_combination (a + d) * hXR00 + x00 * hμ0 + x01 * hμ1 + μ * hXR01
  have h3 : 2 * (X * T.1 * R) 1 1 = a + d := by
    simp only [X, R, hT, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination (a + d) * hXR11 + x10 * hν0 + x11 * hν1 + ν * hXR10
  exact mul_left_cancel₀ h2 (h1.trans h3.symm)

omit [IsDomain S] in
/-- A palindrome's class is fixed by time reversal: the `P` of a law processed to a palindrome. -/
theorem reversal_of_palindrome (T : SL2) (Q : GL2)
    (h : (Q.1 * T.1 * (Q⁻¹ : GL2).1) 0 0 = (Q.1 * T.1 * (Q⁻¹ : GL2).1) 1 1) :
    ∃ P : GL2, P.1 * T.1 = ((T⁻¹ : SL2) : M2) * P.1 ∧ -(P.1.det) = 1 * 1 := by
  have hQQ : Q.1 * (Q⁻¹ : GL2).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : (Q⁻¹ : GL2).1 * Q.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdetQ : Q.1.det * (Q⁻¹ : GL2).1.det = 1 := by
    rw [← Matrix.det_mul, hQQ, Matrix.det_one]
  -- the processed law
  let T₁ : SL2 := ⟨Q.1 * T.1 * (Q⁻¹ : GL2).1, by
    rw [Matrix.det_mul, Matrix.det_mul, T.2, mul_one, hdetQ]⟩
  have hinv : ((T₁⁻¹ : SL2) : M2) = Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1 := by
    have h1 : (T₁ : M2) * (Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1) = 1 := by
      change Q.1 * T.1 * (Q⁻¹ : GL2).1 * (Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1) = 1
      have h2 : T.1 * ((T⁻¹ : SL2) : M2) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      calc Q.1 * T.1 * (Q⁻¹ : GL2).1 * (Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1)
          = Q.1 * T.1 * ((Q⁻¹ : GL2).1 * Q.1) * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1 := by
            simp only [Matrix.mul_assoc]
        _ = Q.1 * (T.1 * ((T⁻¹ : SL2) : M2)) * (Q⁻¹ : GL2).1 := by
            rw [hQQ', Matrix.mul_one, Matrix.mul_assoc Q.1]
        _ = 1 := by rw [h2, Matrix.mul_one, hQQ]
    have h3 : ((T₁⁻¹ : SL2) : M2) * (T₁ : M2) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((T₁⁻¹ : SL2) : M2)
        = ((T₁⁻¹ : SL2) : M2) * ((T₁ : M2) * (Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1)) := by
          rw [h1, Matrix.mul_one]
      _ = Q.1 * ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1 := by
          rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have hpal : (!![1, 0; 0, -1] : M2) * (T₁ : M2) * !![1, 0; 0, -1] = ((T₁⁻¹ : SL2) : M2) := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
        show (T₁ : M2) 0 0 = (T₁ : M2) 1 1 from h]
  -- `P = Q⁻¹ P₀ Q`
  let P₀ : M2 := !![1, 0; 0, -1]
  have hP₀ : P₀ * P₀ = 1 := by
    simp only [P₀, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hP₀T : P₀ * (T₁ : M2) = ((T₁⁻¹ : SL2) : M2) * P₀ := by
    rw [← hpal]
    calc P₀ * (T₁ : M2) = P₀ * (T₁ : M2) * (P₀ * P₀) := by rw [hP₀, Matrix.mul_one]
      _ = P₀ * (T₁ : M2) * P₀ * P₀ := by simp only [Matrix.mul_assoc]
  let Pm : M2 := (Q⁻¹ : GL2).1 * P₀ * Q.1
  let Pm' : M2 := (Q⁻¹ : GL2).1 * P₀ * Q.1
  have hPP : Pm * Pm' = 1 := by
    change (Q⁻¹ : GL2).1 * P₀ * Q.1 * ((Q⁻¹ : GL2).1 * P₀ * Q.1) = 1
    calc (Q⁻¹ : GL2).1 * P₀ * Q.1 * ((Q⁻¹ : GL2).1 * P₀ * Q.1)
        = (Q⁻¹ : GL2).1 * P₀ * (Q.1 * (Q⁻¹ : GL2).1) * P₀ * Q.1 := by simp only [Matrix.mul_assoc]
      _ = (Q⁻¹ : GL2).1 * (P₀ * P₀) * Q.1 := by
          rw [hQQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP₀, Matrix.mul_one, hQQ']
  let P : GL2 := ⟨Pm, Pm', hPP, hPP⟩
  refine ⟨P, ?_, ?_⟩
  · change (Q⁻¹ : GL2).1 * P₀ * Q.1 * T.1 = ((T⁻¹ : SL2) : M2) * ((Q⁻¹ : GL2).1 * P₀ * Q.1)
    have e1 : Q.1 * T.1 = (T₁ : M2) * Q.1 := by
      change Q.1 * T.1 = Q.1 * T.1 * (Q⁻¹ : GL2).1 * Q.1
      rw [Matrix.mul_assoc _ _ Q.1, hQQ', Matrix.mul_one]
    have e2 : (Q⁻¹ : GL2).1 * ((T₁⁻¹ : SL2) : M2) = ((T⁻¹ : SL2) : M2) * (Q⁻¹ : GL2).1 := by
      rw [hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    calc (Q⁻¹ : GL2).1 * P₀ * Q.1 * T.1 = (Q⁻¹ : GL2).1 * P₀ * (Q.1 * T.1) := by
          rw [Matrix.mul_assoc _ Q.1]
      _ = (Q⁻¹ : GL2).1 * (P₀ * (T₁ : M2)) * Q.1 := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = (Q⁻¹ : GL2).1 * ((T₁⁻¹ : SL2) : M2) * P₀ * Q.1 := by
          rw [hP₀T]
          simp only [Matrix.mul_assoc]
      _ = ((T⁻¹ : SL2) : M2) * ((Q⁻¹ : GL2).1 * P₀ * Q.1) := by
          rw [e2]
          simp only [Matrix.mul_assoc]
  · change -(((Q⁻¹ : GL2).1 * P₀ * Q.1).det) = 1 * 1
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, mul_comm (Q⁻¹ : GL2).1.det, hdetQ, one_mul]
    simp [P₀, Matrix.det_fin_two_of]

end Palindrome

/-- **T12** (the criterion for palindromes). -/
@[ledger "T12"]
theorem palindromeCriterion : Statement.palindromeCriterion := by
  intro S _ _ _ _ T
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨P, h1, h2⟩ := reversal_of_palindrome T Q hQ
    exact ⟨P, h1, 1, h2⟩
  · rintro ⟨P, h1, w, hw⟩
    exact palindrome_of_reversal T P h1 hw

/-! ## Non-vacuity

A palindrome, the quarter turn `[[0, -1], [1, 0]]` over `ℚ`: its class is fixed by time reversal,
by a `P` whose `-det P` is a square.
-/

example : ∃ P : Matrix.GeneralLinearGroup (Fin 2) ℚ,
    P.1 * (⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩ : SpecialLinearGroup (Fin 2) ℚ).1 =
      (((⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩ : SpecialLinearGroup (Fin 2) ℚ)⁻¹ :
        SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * P.1 ∧ IsSquare (-(P.1.det)) :=
  (palindromeCriterion ℚ _).mp ⟨1, by simp⟩

end Artform.Scores
