import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ArtformTextbook.Ch03.Statements.Metric

/-!
# Reflections create perpendicularity (Theorem 3.25 and Proposition 3.26)

Averaging an inner product over a finite group gives an invariant one; for an invariant inner
product the mirror and the normal line of a reflection are perpendicular. The proofs are the
book's: the summands are positive, multiplication by `h` permutes the summation index, and
`⟨u, v⟩ = ⟨s u, s v⟩ = -⟨u, v⟩`.
-/

namespace Artform

theorem averagedForm_apply {G V : Type*} [Monoid G] [Fintype G] [AddCommGroup V] [Module ℝ V]
    (ρ : Representation ℝ G V) (B₀ : LinearMap.BilinForm ℝ V) (u v : V) :
    averagedForm ρ B₀ u v = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, B₀ (ρ g u) (ρ g v) := by
  simp [averagedForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply]

/-- **Theorem 3.25** (averaged invariant metric). The averaged form is a positive-definite inner
product and is `G`-invariant. -/
@[book "nolabel:03-pattern-geometry:averaged-invariant-metric"]
theorem averagedInvariantMetric : Statement.averagedInvariantMetric := by
  intro G _ _ V _ _ ρ B₀ ⟨hsymm, hpos⟩
  refine ⟨⟨⟨fun u v => ?_⟩, fun v hv => ?_⟩, fun h u v => ?_⟩
  · -- Symmetry, term by term.
    rw [averagedForm_apply, averagedForm_apply]
    congr 1
    exact Finset.sum_congr rfl fun g _ => hsymm.eq _ _
  · -- If `v ≠ 0` then every `g v ≠ 0`, so every summand is positive.
    rw [averagedForm_apply]
    have hcard : (0 : ℝ) < (Fintype.card G : ℝ)⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    refine mul_pos hcard (Finset.sum_pos (fun g _ => hpos _ fun h0 => hv ?_) Finset.univ_nonempty)
    have h1 := congrArg (ρ g⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h1
  · -- Multiplication by `h` permutes the summation index.
    rw [averagedForm_apply, averagedForm_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => by
      simp [map_mul, Module.End.mul_apply]

/-- **Proposition 3.26** (perpendicularity from symmetry). For a `G`-invariant inner product, the
`+1` and `-1` eigenspaces of a reflection are perpendicular. -/
@[book "nolabel:03-pattern-geometry:perpendicularity-from-symmetry"]
theorem perpendicularityFromSymmetry : Statement.perpendicularityFromSymmetry := by
  intro G _ V _ _ ρ B _ hinv s _ u hu v hv
  rw [Module.End.mem_eigenspace_iff, one_smul] at hu
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hv
  have h := hinv s u v
  rw [hu, hv, map_neg] at h
  linarith

/-! ## Non-vacuity -/

/-- The mirror `s` in the vertical midline of the square, `(x, y) ↦ (-x, y)`, on the plane in
which Section 3.5 realizes the canvas of squares. -/
private noncomputable def midlineMirror : Module.End ℝ (Fin 2 → ℝ) where
  toFun p := ![-p 0, p 1]
  map_add' p q := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp

private theorem midlineMirror_mul_self : midlineMirror * midlineMirror = 1 := by
  ext p i
  fin_cases i <;> simp [midlineMirror]

/-- The two elements of the group of order two, written multiplicatively. -/
private theorem mul_zmod_two_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  exact h (Multiplicative.toAdd g)

/-- The group `{1, s}` of the identity and the midline mirror, a subgroup of the square's group
`D₄`, acting on the plane. -/
private noncomputable def mirrorRep : Representation ℝ (Multiplicative (ZMod 2)) (Fin 2 → ℝ) where
  toFun g := if g = 1 then 1 else midlineMirror
  map_one' := by simp
  map_mul' g h := by
    have h2 := mul_zmod_two_cases
    have hs : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hss : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases h2 g with rfl | rfl <;> rcases h2 h with rfl | rfl
    · simp
    · simp [hs]
    · simp [hs]
    · simp [hs, hss, midlineMirror_mul_self]

private theorem mirrorRep_s : mirrorRep (Multiplicative.ofAdd 1) = midlineMirror := by
  have hs : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [mirrorRep, hs]

/-- The dot product `⟨u, v⟩ = u₀ v₀ + u₁ v₁` of the plane. -/
private noncomputable def dotForm : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ (fun u v => u 0 * v 0 + u 1 * v 1)
    (fun u u' v => by simp; ring) (fun c u v => by simp; ring)
    (fun u v v' => by simp; ring) (fun c u v => by simp; ring)

private theorem dotForm_apply (u v : Fin 2 → ℝ) : dotForm u v = u 0 * v 0 + u 1 * v 1 := rfl

private theorem dotForm_isInnerProduct : IsInnerProduct dotForm := by
  refine ⟨⟨fun u v => by rw [dotForm_apply, dotForm_apply]; ring⟩, fun v hv => ?_⟩
  rw [dotForm_apply]
  by_contra hle
  apply hv
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Theorem 3.25: the group `{1, s}` acts linearly on the plane, and the dot product is a
positive-definite inner product to average. -/
example : IsInnerProduct dotForm ∧ mirrorRep (Multiplicative.ofAdd 1) = midlineMirror :=
  ⟨dotForm_isInnerProduct, mirrorRep_s⟩

/-- Proposition 3.26: the dot product is invariant under `{1, s}`, and the midline mirror is a
reflection, its `-1` eigenspace being the line of `(1, 0)`. -/
example : (∀ (h : Multiplicative (ZMod 2)) (u v : Fin 2 → ℝ),
      dotForm (mirrorRep h u) (mirrorRep h v) = dotForm u v) ∧
    IsReflection mirrorRep (Multiplicative.ofAdd 1) := by
  refine ⟨fun h u v => ?_, by decide, ?_⟩
  · rcases mul_zmod_two_cases h with rfl | rfl
    · simp
    · rw [mirrorRep_s, dotForm_apply, dotForm_apply]
      simp [midlineMirror]
  · rw [mirrorRep_s]
    have he : Module.End.eigenspace midlineMirror (-1) = ℝ ∙ ![1, 0] := by
      ext v
      rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
      constructor
      · intro hv
        have hv1 : v 1 = -v 1 := by simpa [midlineMirror] using congrFun hv 1
        refine ⟨v 0, ?_⟩
        ext i
        fin_cases i
        · simp
        · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            smul_eq_mul, mul_zero]
          linarith
      · rintro ⟨a, rfl⟩
        ext i
        fin_cases i <;> simp [midlineMirror]
    rw [he, finrank_span_singleton]
    intro h0
    simpa using congrFun h0 0

end Artform
