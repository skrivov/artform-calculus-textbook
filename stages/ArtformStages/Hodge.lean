import ArtformStages.Pair

/-!
# The three parts of a field

Wherever `C G = 0`, every field on the lines is uniquely a gradient `G φ`, a transverse field
`Cᵀ ψ` and a harmonic field `h`, with no divergence and no curl, the three orthogonal (finding 451
of the research ledger on a layered universe):

* `mul_transpose_solve` (HD1): `A Aᵀ y = A x` has a solution, for every real `A`;
* `hodge_exists` (HD2), `hodge_orthogonal` (HD3), `hodge_unique` (HD4): the decomposition;
* `hodge_charge`, `hodge_curl` (HD5): the gradient part carries the divergence, the transverse
  part the curl;
* `pair_parts` (HD6): the kick of Pair moves only the transverse part of `E`.
-/

open Matrix

namespace Artform.Stages

/-- HD1. For every real matrix `A` and every `x`, some `y` has `A Aᵀ y = A x`. -/
theorem mul_transpose_solve {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (x : n → ℝ) : ∃ y : m → ℝ, (A * Aᵀ) *ᵥ y = A *ᵥ x := by
  have hle : LinearMap.range (A * Aᵀ).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Aᵀ *ᵥ y, by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_mulVec]⟩
  have heq : LinearMap.range (A * Aᵀ).mulVecLin = LinearMap.range A.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (Matrix.rank_self_mul_transpose A)
  have hx : A *ᵥ x ∈ LinearMap.range (A * Aᵀ).mulVecLin := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable {f e v : Type*} [Fintype f] [Fintype e] [Fintype v]

/-- A field read against a gradient: `(A φ) ⬝ w = (Aᵀ w) ⬝ φ`. -/
theorem dotProduct_mulVec_left {a b : Type*} [Fintype a] [Fintype b] (A : Matrix a b ℝ)
    (φ : b → ℝ) (w : a → ℝ) : (A *ᵥ φ) ⬝ᵥ w = (Aᵀ *ᵥ w) ⬝ᵥ φ := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose]

/-- HD2. Wherever `C G = 0`, every field on the lines is `G φ + Cᵀ ψ + h` with `h` harmonic. -/
theorem hodge_exists (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0) (E : e → ℝ) :
    ∃ (φ : v → ℝ) (ψ : f → ℝ) (h : e → ℝ),
      E = G *ᵥ φ + Cᵀ *ᵥ ψ + h ∧ Gᵀ *ᵥ h = 0 ∧ C *ᵥ h = 0 := by
  obtain ⟨φ, hφ⟩ := mul_transpose_solve Gᵀ E
  obtain ⟨ψ, hψ⟩ := mul_transpose_solve C E
  rw [transpose_transpose] at hφ
  have hGC : Gᵀ * Cᵀ = 0 := by rw [← transpose_mul, hCG, transpose_zero]
  refine ⟨φ, ψ, E - G *ᵥ φ - Cᵀ *ᵥ ψ, by abel, ?_, ?_⟩
  · rw [mulVec_sub, mulVec_sub, mulVec_mulVec, hφ, mulVec_mulVec, hGC, zero_mulVec, sub_self,
      sub_zero]
  · rw [mulVec_sub, mulVec_sub, mulVec_mulVec, hCG, zero_mulVec, sub_zero, mulVec_mulVec, hψ,
      sub_self]

/-- HD3. The three parts are orthogonal. -/
theorem hodge_orthogonal (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0) (φ : v → ℝ)
    (ψ : f → ℝ) (h : e → ℝ) (h1 : Gᵀ *ᵥ h = 0) (h2 : C *ᵥ h = 0) :
    (G *ᵥ φ) ⬝ᵥ (Cᵀ *ᵥ ψ) = 0 ∧ (G *ᵥ φ) ⬝ᵥ h = 0 ∧ (Cᵀ *ᵥ ψ) ⬝ᵥ h = 0 := by
  have hGC : Gᵀ * Cᵀ = 0 := by rw [← transpose_mul, hCG, transpose_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [dotProduct_mulVec_left, mulVec_mulVec, hGC, zero_mulVec, zero_dotProduct]
  · rw [dotProduct_mulVec_left, h1, zero_dotProduct]
  · rw [dotProduct_mulVec_left, transpose_transpose, h2, zero_dotProduct]

/-- HD4. Each part is unique. -/
theorem hodge_unique (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0) (φ φ' : v → ℝ)
    (ψ ψ' : f → ℝ) (h h' : e → ℝ) (hh : Gᵀ *ᵥ h = 0 ∧ C *ᵥ h = 0)
    (hh' : Gᵀ *ᵥ h' = 0 ∧ C *ᵥ h' = 0)
    (heq : G *ᵥ φ + Cᵀ *ᵥ ψ + h = G *ᵥ φ' + Cᵀ *ᵥ ψ' + h') :
    G *ᵥ φ = G *ᵥ φ' ∧ Cᵀ *ᵥ ψ = Cᵀ *ᵥ ψ' ∧ h = h' := by
  have hc1 : Gᵀ *ᵥ (h - h') = 0 := by rw [mulVec_sub, hh.1, hh'.1, sub_zero]
  have hc2 : C *ᵥ (h - h') = 0 := by rw [mulVec_sub, hh.2, hh'.2, sub_zero]
  obtain ⟨o1, o2, o3⟩ := hodge_orthogonal C G hCG (φ - φ') (ψ - ψ') (h - h') hc1 hc2
  have hsum : G *ᵥ (φ - φ') + Cᵀ *ᵥ (ψ - ψ') + (h - h') = 0 := by
    rw [mulVec_sub, mulVec_sub]
    rw [← sub_eq_zero] at heq
    rw [← heq]
    abel
  set a := G *ᵥ (φ - φ')
  set b := Cᵀ *ᵥ (ψ - ψ')
  set c := h - h'
  have ha : a = -(b + c) := eq_neg_of_add_eq_zero_left (by rw [← hsum]; abel)
  have haa : a ⬝ᵥ a = 0 := by
    calc a ⬝ᵥ a = a ⬝ᵥ (-(b + c)) := by rw [← ha]
      _ = 0 := by rw [dotProduct_neg, dotProduct_add, o1, o2, add_zero, neg_zero]
  have ha0 : a = 0 := dotProduct_self_eq_zero.mp haa
  have hb : b = -(a + c) := eq_neg_of_add_eq_zero_left (by rw [← hsum]; abel)
  have hbb : b ⬝ᵥ b = 0 := by
    calc b ⬝ᵥ b = b ⬝ᵥ (-(a + c)) := by rw [← hb]
      _ = 0 := by
        rw [dotProduct_neg, dotProduct_add, dotProduct_comm b a, o1, o3, add_zero, neg_zero]
  have hb0 : b = 0 := dotProduct_self_eq_zero.mp hbb
  have hc0 : c = 0 := by
    have := hsum
    rw [ha0, hb0, zero_add, zero_add] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · have : G *ᵥ (φ - φ') = 0 := ha0
    rw [mulVec_sub, sub_eq_zero] at this
    exact this
  · have : Cᵀ *ᵥ (ψ - ψ') = 0 := hb0
    rw [mulVec_sub, sub_eq_zero] at this
    exact this
  · exact sub_eq_zero.mp hc0

/-- HD5. The gradient part carries all the divergence. -/
theorem hodge_charge (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0) (φ : v → ℝ)
    (ψ : f → ℝ) (h : e → ℝ) (h1 : Gᵀ *ᵥ h = 0) :
    Gᵀ *ᵥ (G *ᵥ φ + Cᵀ *ᵥ ψ + h) = (Gᵀ * G) *ᵥ φ := by
  have hGC : Gᵀ * Cᵀ = 0 := by rw [← transpose_mul, hCG, transpose_zero]
  rw [mulVec_add, mulVec_add, h1, mulVec_mulVec, mulVec_mulVec, hGC, zero_mulVec, add_zero,
    add_zero]

/-- HD5. The transverse part carries all the curl. -/
theorem hodge_curl (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0) (φ : v → ℝ)
    (ψ : f → ℝ) (h : e → ℝ) (h2 : C *ᵥ h = 0) :
    C *ᵥ (G *ᵥ φ + Cᵀ *ᵥ ψ + h) = (C * Cᵀ) *ᵥ ψ := by
  rw [mulVec_add, mulVec_add, h2, mulVec_mulVec, mulVec_mulVec, hCG, zero_mulVec, zero_add,
    add_zero]

/-- HD6. The kick of Pair moves only the transverse part of `E`. -/
theorem pair_parts (C : Matrix f e ℝ) (G : Matrix e v ℝ) (K : Matrix f f ℝ) (L : Matrix e e ℝ)
    (A : e → ℝ) (φ' : v → ℝ) (ψ' : f → ℝ) (h' : e → ℝ) :
    (pair (Cᵀ * K * C) L (A, G *ᵥ φ' + Cᵀ *ᵥ ψ' + h')).2 =
      G *ᵥ φ' + Cᵀ *ᵥ (ψ' + K *ᵥ (C *ᵥ A)) + h' := by
  simp only [pair]
  rw [mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec]
  abel

end Artform.Stages
