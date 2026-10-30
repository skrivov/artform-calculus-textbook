import ArtformScores.ReviewRepair.Statements

/-! # Face and link ideals on a normal extension -/

namespace Artform.Scores
open Matrix (SpecialLinearGroup)
open LaurentPolynomial

/-- Every face score is a constant kick modulo the face stencil. All three
other entries retain their identity values modulo that stencil. -/
theorem face_score_shape {F : Type} [Field F] (κ ℓ : F) (w : Score F) :
    ∃ a b c d : LaurentPolynomial F,
      (realize (w.map (faceStep κ ℓ))).1 =
        !![1 + stencilG F * a, stencilG F * b;
          C (totalKick w * κ) + stencilG F * c, 1 + stencilG F * d] := by
  induction w with
  | nil => exact ⟨0, 0, 0, 0, by simp [totalKick, Matrix.one_fin_two]⟩
  | cons s w ih =>
    obtain ⟨a, b, c, d, h⟩ := ih
    cases s with
    | kick r =>
      refine ⟨a + b * C (r * κ), b, c + d * C (r * κ), d, ?_⟩
      simp only [List.map_cons, realize_cons, Matrix.SpecialLinearGroup.coe_mul,
        h, Step.coe_sl, faceStep, Step.mat, totalKick, map_add, add_mul, Matrix.mul_fin_two]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    | move r =>
      let m : LaurentPolynomial F := C (-(r * ℓ))
      refine ⟨a, b + m + stencilG F * a * m, c,
        d + C (totalKick w * κ) * m + stencilG F * c * m, ?_⟩
      simp only [List.map_cons, realize_cons, Matrix.SpecialLinearGroup.coe_mul,
        h, Step.coe_sl, faceStep, Step.mat, totalKick, Matrix.mul_fin_two]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [m] <;> ring

/-- The face stencil has a double zero at the zero mode. -/
theorem stencilG_double_zero {F : Type} [Field F] :
    stencilG F = -(T 1 : LaurentPolynomial F) * (diffDs F) ^ 2 := by
  have h : (T 1 : LaurentPolynomial F) * T (-1) = 1 := by rw [← T_add]; simp
  simp only [stencilG, diffDs]
  linear_combination (T (-1) - 2 : LaurentPolynomial F) * h

/-- Dividing the eigenvector entry by `D` is legitimate in every normal
extension: its square is divisible by `D²`. This is the missing normalization
step, rather than an assumption about the eigenvector. -/
theorem normalized_ideal_comparison {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (a b c d D lam : B)
    (hdet : a * d - b * c = 1) (hroot : lam * lam - (a + d) * lam + 1 = 0)
    (ha : D ^ 2 ∣ a - 1) (hb : D ^ 2 ∣ b) (hd : D ^ 2 ∣ d - 1)
    (hcD : IsCoprime c D) :
    Ideal.span {D * c, lam - a} = Ideal.span {D} * Ideal.span {c, lam - a} := by
  obtain ⟨α, hα⟩ := ha
  obtain ⟨β, hβ⟩ := hb
  obtain ⟨δ, hδ⟩ := hd
  have hh : D ^ 2 ∣ (lam - a) ^ 2 := by
    refine ⟨(δ - α) * (lam - a) + β * c, ?_⟩
    linear_combination hroot + hdet + (lam - a) * hδ - (lam - a) * hα + c * hβ
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hh
  rw [hz]
  have heq : Ideal.span ({c, z} : Set B) = Ideal.span {c, D * z} := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro y hy
      rcases Set.mem_insert_iff.mp hy with hy | hy
      · subst y; exact Ideal.subset_span (by simp)
      · have hy := Set.mem_singleton_iff.mp hy
        subst y
        obtain ⟨u, v, huv⟩ := hcD
        have he : z = (u * z) * c + v * (D * z) := by linear_combination -z * huv
        have hm : (u * z) * c + v * (D * z) ∈ Ideal.span ({c, D * z} : Set B) :=
          Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        rw [← he] at hm
        exact hm
    · apply Ideal.span_le.mpr
      rintro y (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  rw [← span_singleton_mul_span_pair, heq]

/-- **T11** (the principal-divisor comparison after normalization). -/
@[ledger "T11"]
theorem faceAndLinkNormalization : Statement.faceAndLinkNormalization := by
  refine ⟨faceAndLink, ?_⟩
  intro F _ κ ℓ w hkick Tf Tl B _ _ _ ι _hι lam hroot
  obtain ⟨a, b, c, d, hshape⟩ := face_score_shape κ ℓ w
  have hentry := faceAndLink F κ ℓ w
  have hc : ι (Tl.1 1 0) = ι (diffDs F) * ι (Tf.1 1 0) := by
    rw [hentry.2.2.1, map_mul]
  have ha : ι (Tl.1 0 0) = ι (Tf.1 0 0) := congrArg ι hentry.2.1
  rw [hc, ha]
  apply normalized_ideal_comparison (ι (Tf.1 0 0)) (ι (Tf.1 0 1))
    (ι (Tf.1 1 0)) (ι (Tf.1 1 1)) (ι (diffDs F)) lam
  · have hdet := Tf.2
    rw [Matrix.det_fin_two] at hdet
    simpa only [map_sub, map_mul, map_one] using congrArg ι hdet
  · simpa only [phase, Matrix.trace_fin_two, map_add] using hroot
  · refine ⟨ι (-(T 1) * a), ?_⟩
    rw [show Tf.1 = _ from hshape]
    simp [stencilG_double_zero, map_mul, map_pow]
    ring
  · refine ⟨ι (-(T 1) * b), ?_⟩
    rw [show Tf.1 = _ from hshape]
    simp [stencilG_double_zero, map_mul, map_pow]
    ring
  · refine ⟨ι (-(T 1) * d), ?_⟩
    rw [show Tf.1 = _ from hshape]
    simp [stencilG_double_zero, map_mul, map_pow]
    ring
  · let u : LaurentPolynomial F := C ((totalKick w * κ)⁻¹)
    have hu : u * C (totalKick w * κ) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hkick, map_one]
    refine ⟨ι u, ι (-u * (-(T 1)) * diffDs F * c), ?_⟩
    have hcshape : Tf.1 1 0 = C (totalKick w * κ) + stencilG F * c :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F) => M 1 0) hshape
    rw [hcshape]
    simp only [map_add, map_mul, stencilG_double_zero, map_pow, map_neg]
    have hu' := congrArg ι hu
    simp only [map_mul, map_one] at hu'
    linear_combination hu'

/-! ## Non-vacuity -/

/-- The book's nonzero kick satisfies the corrected gluedness hypothesis. -/
example : totalKick ([.kick 1, .move 1] : Score ℚ) * 1 ≠ 0 := by
  norm_num [totalKick]

/-- The comparison is realized on the book's unit kick, in a concrete normal
extension of the rational stencil ring. -/
example :
    let w : Score ℚ := [.kick 1]
    let ι := Leapfrog.psi (by norm_num : (2 : ℚ) ≠ 0)
    let Tf := realize (w.map (faceStep 1 1))
    let Tl := realize (w.map (linkStep 1 1))
    Ideal.span {ι (Tl.1 1 0), 1 - ι (Tl.1 0 0)} =
      Ideal.span {ι (diffDs ℚ)} * Ideal.span {ι (Tf.1 1 0), 1 - ι (Tf.1 0 0)} := by
  apply faceAndLinkNormalization.2 ℚ 1 1 [.kick 1] (by norm_num [totalKick])
    (Leapfrog.Norm (2 : ℚ)) (Leapfrog.psi (by norm_num))
    (Leapfrog.psi_injective (by norm_num)) 1
  simp only [List.map_cons, List.map_nil, realize_singleton]
  norm_num [phase, faceStep, Step.coe_sl, Step.mat, Matrix.trace_fin_two]
  rw [map_ofNat]
  ring

end Artform.Scores
