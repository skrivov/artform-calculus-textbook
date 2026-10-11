import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import ArtformTextbook.Ch11.Statements

/-!
# Averaging counts (Proposition 11.5)

The proof of Proposition 11.5. Mathlib proves the three facts with `χ(g⁻¹)` in
place of the book's `conj χ(g)`: the average is the projector onto the
invariants (`Representation.isProj_averageMap`), and the dimension counts
(`Representation.card_inv_mul_sum_char_eq_finrank`,
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`,
`Representation.char_orthonormal`). The book imports the orthogonality from
Serre; here it comes from Mathlib, and the one step added is
`χ(g⁻¹) = conj χ(g)` for a complex representation of a finite group.
-/

namespace Artform

open scoped ComplexConjugate Matrix

open scoped ComplexOrder in
/-- For a complex representation of a finite group, the character at `g⁻¹` is
the complex conjugate of the character at `g`. In a basis, the matrices `M g`
keep the positive definite form `P = Σ_h (M h)ᴴ (M h)`, that is
`(M g)ᴴ P (M g) = P`; so `(M g)ᴴ = P M(g⁻¹) P⁻¹`, and taking traces gives
`conj χ(g) = χ(g⁻¹)`. -/
theorem character_inv_eq_conj {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  classical
  have := Fintype.ofFinite G
  let b := Module.finBasis ℂ V
  let M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ
  have hχ (h : G) : ρ.character h = (M h).trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ h)
  set P := ∑ h, (M h)ᴴ * M h with hPdef
  -- `P` is invariant: `h ↦ h * g` permutes the terms of the sum.
  have hP : (M g)ᴴ * P * M g = P := by
    rw [hPdef, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    simp [Matrix.conjTranspose_mul, mul_assoc]
  -- `P` is positive definite, as a sum of `Aᴴ A` with `A` invertible, hence invertible.
  have hPu : IsUnit P := by
    refine (Matrix.posDef_sum Finset.univ_nonempty fun h _ => ?_).isUnit
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Group.isUnit h).map M))
  have h1 : (M g)ᴴ * P = P * M g⁻¹ := by
    calc (M g)ᴴ * P = (M g)ᴴ * P * (M g * M g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = P * M g⁻¹ := by rw [← mul_assoc, hP]
  have h2 : (M g)ᴴ = P * M g⁻¹ * P⁻¹ := by
    rw [← h1, mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).mp hPu),
      mul_one]
  rw [hχ, hχ, starRingEnd_apply, ← Matrix.trace_conjTranspose, h2, Matrix.trace_conj hPu]

/-- **Proposition 11.5** (averaging counts). For a representation `W` of `G`,
the average `(1/|G|) Σ_U W(U)` is the projector onto the vectors fixed by `G`,
so the number of independent fixed vectors is `(1/|G|) Σ_U χ_W(U)`. For two
irreducible characters, `(1/|G|) Σ_U χ_ρ(U) conj(χ_σ(U))` is `1` when `ρ = σ`
and `0` otherwise; hence the number of times `ρ` occurs in `W` is
`(1/|G|) Σ_U χ_W(U) conj(χ_ρ(U))`. -/
@[book "prop:mt-average"]
theorem mtAverage : Statement.mtAverage := by
  intro G _ _
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let _ : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hG
  have hcard : (Fintype.card G : ℂ) = Nat.card G := by rw [Nat.card_eq_fintype_card]
  refine ⟨fun V _ _ _ W => ?_, fun V V' _ _ _ _ _ _ ρ σ _ _ => ?_,
    fun V V' _ _ _ _ _ _ W ρ _ => ?_⟩
  · -- The average is Mathlib's `averageMap`, a projection onto the invariants.
    let _ : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (hcard ▸ hG)
    intro avg
    have havg : avg = W.averageMap := by
      simp [avg, Representation.averageMap, GroupAlgebra.average, map_sum, invOf_eq_inv]
    have hproj := W.isProj_averageMap
    rw [havg]
    refine ⟨hproj.isIdempotentElem.eq, ?_, ?_⟩
    · exact LinearMap.IsProj.submodule_unique
        ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hproj.isIdempotentElem) hproj
    · rw [hcard, W.card_inv_mul_sum_char_eq_finrank]
  · -- Orthonormality, with `conj χ_σ(g) = χ_σ(g⁻¹)`; an equivalence can be inverted.
    simp_rw [← character_inv_eq_conj, hcard, Representation.char_orthonormal ρ σ]
    classical
    exact if_congr ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩ rfl rfl
  · -- The dimension of the intertwining maps, with `conj χ_ρ(g) = χ_ρ(g⁻¹)`.
    simp_rw [← character_inv_eq_conj, hcard,
      Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ W]

/-! ## Non-vacuity -/

/-- The hypotheses of parts 2 and 3 can be met: the trivial one-dimensional
representation of the group of order two is irreducible. -/
example : (Representation.trivial ℂ (Multiplicative (ZMod 2)) ℂ).IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Artform
