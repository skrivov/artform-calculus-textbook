import ArtformStages.Maxwell

/-!
# Coulomb's problem on a board

On a board whose corners are joined, with a weight `λ > 0` on every line, every charge that sums to
`0` is the divergence of a still field, the gradient of a potential fixed up to a constant
(finding 444 of the research ledger on a layered universe):

* `Board.gauge_mulVec` (CL1): `G φ` at a line is `φ` at its head less `φ` at its tail;
* `Board.gauge_const` (CL2): on a board whose corners are joined, `G φ = 0` makes `φ` constant;
* `Board.coulomb` (CL3): a charge is `M φ` for the Laplacian `M = Gᵀ diag (1 / λ) G` exactly when
  it sums to `0`;
* `Board.coulomb_unique` (CL4): the potential is unique up to a constant;
* `Board.coulomb_field` (CL5): a charge is the divergence of a still field exactly when it sums to
  `0`.

The proof of CL3 counts dimensions: the kernel of `M` is the constants, so its range has one
dimension less than the corners, and it lies in the charges that sum to `0`, which have as many.
-/

open Matrix Module

namespace Artform.Stages

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- The corners of a board are *joined* when any two are linked by a chain of corners, each joined
to the next by a line. -/
def CornersJoined : Prop :=
  ∀ a b : v, Relation.ReflTransGen
    (fun x y => ∃ ℓ, (B.tail ℓ = x ∧ B.head ℓ = y) ∨ (B.tail ℓ = y ∧ B.head ℓ = x)) a b

/-- The Laplacian of a board on its corners, with the weight `1 / λ` on each line. -/
noncomputable def laplacian [Fintype e] [DecidableEq e] [DecidableEq v] (l : e → ℝ) :
    Matrix v v ℝ :=
  B.gaugeᵀ * diagonal (fun ℓ => 1 / l ℓ) * B.gauge

/-- CL1. `G φ` at a line is `φ` at its head less `φ` at its tail. -/
theorem gauge_mulVec [Fintype v] [DecidableEq v] (φ : v → ℝ) (ℓ : e) :
    (B.gauge *ᵥ φ) ℓ = φ (B.head ℓ) - φ (B.tail ℓ) := by
  simp [mulVec, dotProduct, gauge, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- CL2. On a board whose corners are joined, `G φ = 0` makes `φ` the same at every corner. -/
theorem gauge_const [Fintype v] [DecidableEq v] (hJ : B.CornersJoined) (φ : v → ℝ)
    (h : B.gauge *ᵥ φ = 0) (a b : v) : φ a = φ b := by
  have hab := hJ a b
  induction hab with
  | refl => rfl
  | tail _ hxy ih =>
    obtain ⟨ℓ, hℓ | hℓ⟩ := hxy
    · have h0 := congrFun h ℓ
      rw [B.gauge_mulVec, Pi.zero_apply, hℓ.1, hℓ.2, sub_eq_zero] at h0
      exact ih.trans h0.symm
    · have h0 := congrFun h ℓ
      rw [B.gauge_mulVec, Pi.zero_apply, hℓ.1, hℓ.2, sub_eq_zero] at h0
      exact ih.trans h0

/-- The Laplacian's values sum to `0` over the corners. -/
theorem laplacian_sum [Fintype e] [DecidableEq e] [Fintype v] [DecidableEq v] (l : e → ℝ)
    (φ : v → ℝ) : ∑ w, (B.laplacian l *ᵥ φ) w = 0 := by
  have h := B.divergence_sum (diagonal (fun ℓ => 1 / l ℓ) *ᵥ (B.gauge *ᵥ φ))
  simp only [divergence, Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero] at h
  simpa [laplacian, mulVec_mulVec, Matrix.mul_assoc] using h

/-- The Laplacian has no value on a field that it sends to `0` but the constants. -/
theorem laplacian_gauge [Fintype e] [DecidableEq e] [Fintype v] [DecidableEq v] (l : e → ℝ)
    (hl : ∀ ℓ, 0 < l ℓ) (φ : v → ℝ) (h : B.laplacian l *ᵥ φ = 0) : B.gauge *ᵥ φ = 0 :=
  still_field_zero B.gauge (fun ℓ => 1 / l ℓ) (fun ℓ => one_div_pos.mpr (hl ℓ)) φ h

/-- **CL3.** On a board whose corners are joined, with every `λ > 0`, a charge `ρ` is `M φ` for
some potential `φ` if and only if it sums to `0` over the corners. -/
theorem coulomb [Fintype e] [DecidableEq e] [Fintype v] [DecidableEq v] [Nonempty v]
    (hJ : B.CornersJoined) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (ρ : v → ℝ) :
    (∃ φ : v → ℝ, B.laplacian l *ᵥ φ = ρ) ↔ ∑ w, ρ w = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact B.laplacian_sum l φ
  · intro hρ
    let s : (v → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => ∑ w, x w
        map_add' := fun x y => by simp [Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [Finset.mul_sum] }
    let T := (B.laplacian l).mulVecLin
    have hle : LinearMap.range T ≤ LinearMap.ker s := by
      rintro _ ⟨φ, rfl⟩
      exact B.laplacian_sum l φ
    have hker : LinearMap.ker T = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
      ext φ
      rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
      constructor
      · intro h
        have hG := B.laplacian_gauge l hl φ h
        obtain ⟨w₀⟩ := ‹Nonempty v›
        exact ⟨φ w₀, funext fun w => by simp [B.gauge_const hJ φ hG w₀ w]⟩
      · rintro ⟨c, rfl⟩
        have h1 : B.gauge *ᵥ (fun _ => (1 : ℝ)) = 0 := by
          funext ℓ
          simp [B.gauge_mulVec]
        change B.laplacian l *ᵥ (c • fun _ => (1 : ℝ)) = 0
        rw [mulVec_smul, laplacian, ← mulVec_mulVec, h1, mulVec_zero, smul_zero]
    have h1 : finrank ℝ (LinearMap.ker T) = 1 := by
      rw [hker]
      refine finrank_span_singleton fun h0 => ?_
      have := congrFun h0 (Classical.arbitrary v)
      simp at this
    have hT := LinearMap.finrank_range_add_finrank_ker T
    rw [h1, Module.finrank_fintype_fun_eq_card] at hT
    have hs : Function.Surjective s := fun c =>
      ⟨Pi.single (Classical.arbitrary v) c, by simp [s]⟩
    have hS := LinearMap.finrank_range_add_finrank_ker s
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card] at hS
    have heq : LinearMap.range T = LinearMap.ker s :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hmem : ρ ∈ LinearMap.ker s := hρ
    rw [← heq] at hmem
    obtain ⟨φ, hφ⟩ := hmem
    exact ⟨φ, hφ⟩

/-- **CL4.** There the potential is unique up to a constant. -/
theorem coulomb_unique [Fintype e] [DecidableEq e] [Fintype v] [DecidableEq v]
    (hJ : B.CornersJoined) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (φ ψ : v → ℝ)
    (h : B.laplacian l *ᵥ φ = B.laplacian l *ᵥ ψ) (a b : v) : φ a - ψ a = φ b - ψ b := by
  have h0 : B.laplacian l *ᵥ (φ - ψ) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.mpr h
  have := B.gauge_const hJ (φ - ψ) (B.laplacian_gauge l hl _ h0) a b
  simpa using this

/-- **CL5.** There a charge is the divergence of a still field, one whose electric field `L E`
has no curl, if and only if it sums to `0`; the field can be taken as `- diag (1 / λ) G φ`. -/
theorem coulomb_field [Fintype e] [DecidableEq e] [Fintype v] [DecidableEq v] [Nonempty v]
    (hJ : B.CornersJoined) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (ρ : v → ℝ) :
    (∃ E : e → ℝ, divergence B.gauge E = ρ ∧ (B.incidence * diagonal l) *ᵥ E = 0) ↔
      ∑ w, ρ w = 0 := by
  constructor
  · rintro ⟨E, hE, -⟩
    rw [← hE]
    exact B.divergence_sum E
  · intro hρ
    obtain ⟨φ, hφ⟩ := (B.coulomb hJ l hl ρ).mpr hρ
    have hLD : diagonal l * diagonal (fun ℓ => 1 / l ℓ) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext ℓ
      field_simp [(hl ℓ).ne']
    refine ⟨-(diagonal (fun ℓ => 1 / l ℓ) *ᵥ (B.gauge *ᵥ φ)), ?_, ?_⟩
    · rw [← hφ]
      simp [divergence, laplacian, mulVec_neg, mulVec_mulVec, Matrix.mul_assoc]
    · have hC : ∀ x : e → ℝ,
          (B.incidence * diagonal l) *ᵥ (diagonal (fun ℓ => 1 / l ℓ) *ᵥ x) = B.incidence *ᵥ x := by
        intro x
        rw [mulVec_mulVec, Matrix.mul_assoc, hLD, Matrix.mul_one]
      rw [mulVec_neg, hC, mulVec_mulVec, B.incidence_mul_gauge, zero_mulVec, neg_zero]

end Board

end Artform.Stages
