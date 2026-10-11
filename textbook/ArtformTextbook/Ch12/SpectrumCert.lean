import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import ArtformTextbook.Ch12.FockCalc

/-!
# Counting eigenvalues with certificates

The spectra of Chapter 12 are multiplicities: the dimension of the space of states on which an
operator takes a given value. They are certified as the book's verifier certifies them, from a
basis of eigenvectors:

* an operator `T` on a space `V` that a basis `Φ` of a subspace `W` carries to a matrix `K`,
  `T (Φ a) = Φ (K a)`, has on `W` the eigenspaces of `K` (`finrank_inf_eigenspace`);
* a matrix `K` with a basis of eigenvectors, the columns of `C` with `K C = C diag(ν)` and
  `D C = diag(d)` for some `D` and nonzero `d`, has the eigenvalue `μ` with the multiplicity
  `#{k | ν_k = μ}` (`finrank_eigenspace_of_diagonalizes`);
* the matrices `K`, `C` and `D` are sparse integer data, given column by column, and the two
  identities are checked by the kernel with the tries of `FockCalc` (`colMat_mulVec`).
-/

namespace Artform.SpecCert

open FockCalc Module

open scoped Matrix

/-! ### Linear algebra -/

theorem finrank_eigenspace_diagonal {n : ℕ} (ν : Fin n → ℂ) (μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' (Matrix.diagonal ν)) μ) =
      (Finset.univ.filter fun k => ν k = μ).card := by
  classical
  let S := {k : Fin n // ν k ≠ μ}
  let r : (Fin n → ℂ) →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun k => LinearMap.proj (k : Fin n)
  have hker : End.eigenspace (Matrix.toLin' (Matrix.diagonal ν)) μ = LinearMap.ker r := by
    ext a
    rw [End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro h
      funext k
      have hk := congrFun h k
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hk
      have : (ν k - μ) * a k = 0 := by rw [sub_mul, hk, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr k.2)
    · intro h
      funext k
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hk : ν k = μ
      · rw [hk]
      · have := congrFun h ⟨k, hk⟩
        simp only [r, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] at this
        rw [this, mul_zero, mul_zero]
  have hsurj : Function.Surjective r := by
    intro b
    refine ⟨fun k => if h : ν k ≠ μ then b ⟨k, h⟩ else 0, ?_⟩
    funext ⟨k, hk⟩
    simp [r, hk]
  have hrank := LinearMap.finrank_range_add_finrank_ker r
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrank
  rw [hker]
  have hS : Fintype.card S = (Finset.univ.filter fun k => ¬ ν k = μ).card :=
    Fintype.card_subtype _
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun k : Fin n => ν k = μ)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- A matrix with a basis of eigenvectors: the columns of `C`, with `K C = C diag(ν)`, and
`D C = diag(d)` with `d` nonzero, so that the columns are independent. The eigenvalue `μ` then
has the multiplicity `#{k | ν_k = μ}`. -/
theorem finrank_eigenspace_of_diagonalizes {n : ℕ} (K C D : Matrix (Fin n) (Fin n) ℂ)
    (ν dg : Fin n → ℂ) (hKC : K * C = C * Matrix.diagonal ν)
    (hDC : D * C = Matrix.diagonal dg) (hdg : ∀ k, dg k ≠ 0) (μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' K) μ) =
      (Finset.univ.filter fun k => ν k = μ).card := by
  have hinj : Function.Injective (Matrix.toLin' C) := by
    intro a b hab
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hab
    have h := congrArg (fun x => D *ᵥ x) hab
    simp only [Matrix.mulVec_mulVec, hDC] at h
    funext k
    have hk := congrFun h k
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hk
    exact mul_left_cancel₀ (hdg k) hk
  have hsurj : Function.Surjective (Matrix.toLin' C) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hmap : (End.eigenspace (Matrix.toLin' (Matrix.diagonal ν)) μ).map (Matrix.toLin' C) =
      End.eigenspace (Matrix.toLin' K) μ := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [End.mem_eigenspace_iff] at ha ⊢
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at *
      rw [Matrix.mulVec_mulVec, hKC, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul]
    · intro hx
      obtain ⟨a, rfl⟩ := hsurj x
      refine ⟨a, ?_, rfl⟩
      rw [End.mem_eigenspace_iff] at hx ⊢
      apply hinj
      rw [map_smul]
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hx ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hKC, ← Matrix.mulVec_mulVec, hx]
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm,
    finrank_eigenspace_diagonal]

/-- An operator `T` that a basis `Φ` of a subspace `W` carries to the matrix `K` has on `W` the
eigenspaces of `K`. -/
theorem finrank_inf_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (W : Submodule ℂ V) (T : End ℂ V) (Φ : (Fin n → ℂ) →ₗ[ℂ] V) (hΦ : Function.Injective Φ)
    (hW : LinearMap.range Φ = W) (K : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ a, T (Φ a) = Φ (K *ᵥ a)) (μ : ℂ) :
    finrank ℂ ↥(W ⊓ End.eigenspace T μ) = finrank ℂ (End.eigenspace (Matrix.toLin' K) μ) := by
  have hmap : (End.eigenspace (Matrix.toLin' K) μ).map Φ = W ⊓ End.eigenspace T μ := by
    ext x
    rw [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply] at ha
      refine ⟨hW ▸ LinearMap.mem_range_self Φ a, ?_⟩
      rw [End.mem_eigenspace_iff, hT, ha, map_smul]
    · rintro ⟨hxW, hxT⟩
      rw [← hW] at hxW
      obtain ⟨a, rfl⟩ := hxW
      refine ⟨a, ?_, rfl⟩
      rw [End.mem_eigenspace_iff, hT, ← map_smul] at hxT
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hΦ hxT
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hΦ _).symm]

/-! ### Sparse integer vectors and matrices -/

/-- Every index of a sparse vector is below `n`. -/
def keysLt (n : ℕ) (v : Vec) : Bool := v.all fun p => decide (p.1 < n)

/-- A sparse vector read as a vector of `ℂⁿ`, its entries summed index by index. -/
noncomputable def vecFun (d n : ℕ) (v : Vec) : Fin n → ℂ := fun i => (Vec.sumAt d i v : ℂ)

/-- A sparse matrix given by its columns, read as a matrix. -/
noncomputable def colMat (d n : ℕ) (cols : List Vec) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (Vec.sumAt d i (cols.getD j []) : ℂ)

/-- The combination `Σ_j c_j col_j` of the columns, for a sparse vector `c`. -/
def apply (cols : List Vec) (c : Vec) : Vec := Vec.combo (c.map fun p => (p.2, cols.getD p.1 []))

theorem sumAt_cons (d i : ℕ) (p : ℕ × ℤ) (v : Vec) :
    Vec.sumAt d i (p :: v) = (if p.1 % 2 ^ d = i % 2 ^ d then p.2 else 0) + Vec.sumAt d i v := by
  simp only [Vec.sumAt, List.filter_cons]
  split_ifs with h1 h2 h2 <;> simp_all

theorem sumAt_append (d i : ℕ) (v v' : Vec) :
    Vec.sumAt d i (v ++ v') = Vec.sumAt d i v + Vec.sumAt d i v' := by
  simp [Vec.sumAt, List.filter_append]

theorem sumAt_smul (d i : ℕ) (a : ℤ) (v : Vec) :
    Vec.sumAt d i (Vec.smul a v) = a * Vec.sumAt d i v := by
  induction v with
  | nil => simp [Vec.smul, Vec.sumAt]
  | cons p v ih =>
    rw [Vec.smul, List.map_cons, ← Vec.smul, sumAt_cons, ih, sumAt_cons]
    split_ifs <;> ring

theorem sumAt_combo (d i : ℕ) (l : List (ℤ × Vec)) :
    Vec.sumAt d i (Vec.combo l) = (l.map fun t => t.1 * Vec.sumAt d i t.2).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [Vec.combo, List.flatMap_cons, ← Vec.combo, sumAt_append, sumAt_smul, ih, List.map_cons,
      List.sum_cons]

/-- A sum over the entries of a sparse vector with indices below `n ≤ 2^d` is a sum over the
indices. -/
theorem sum_entries {d n : ℕ} (hn : n ≤ 2 ^ d) (v : Vec) (hv : keysLt n v = true)
    (f : ℕ → ℂ) :
    (v.map fun p => (p.2 : ℂ) * f p.1).sum = ∑ j : Fin n, (Vec.sumAt d j v : ℂ) * f j := by
  induction v with
  | nil => simp [Vec.sumAt]
  | cons p v ih =>
    simp only [keysLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [List.map_cons, List.sum_cons, ih hv.2]
    simp only [sumAt_cons, Int.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (⟨p.1, hv.1⟩ : Fin n)]
    · simp
    · intro j _ hj
      rw [ite_eq_right]
      · simp
      · intro h
        apply hj
        apply Fin.ext
        rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hv.1 hn),
          Nat.mod_eq_of_lt (lt_of_lt_of_le j.2 hn)] at h
        exact h.symm
    · simp

theorem cast_sum_map {α : Type*} (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℂ) = (l.map fun a => (f a : ℂ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem colMat_mulVec {d n : ℕ} (hn : n ≤ 2 ^ d) (cols : List Vec) (c : Vec)
    (hc : keysLt n c = true) :
    colMat d n cols *ᵥ vecFun d n c = vecFun d n (apply cols c) := by
  funext i
  have h1 := sum_entries hn c hc (fun j => (Vec.sumAt d i (cols.getD j []) : ℂ))
  have h2 : vecFun d n (apply cols c) i =
      (c.map fun p => (p.2 : ℂ) * (Vec.sumAt d i (cols.getD p.1 []) : ℂ)).sum := by
    simp only [vecFun, apply, sumAt_combo, List.map_map, cast_sum_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp
  rw [h2, h1]
  simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply, vecFun]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecFun_smul (d n : ℕ) (a : ℤ) (v : Vec) :
    vecFun d n (Vec.smul a v) = (a : ℂ) • vecFun d n v := by
  funext i
  simp [vecFun, sumAt_smul]

theorem vecFun_eq_of_trie_eq {d n : ℕ} {v v' : Vec} (h : Vec.trie d v = Vec.trie d v') :
    vecFun d n v = vecFun d n v' := by
  funext i
  simp only [vecFun]
  rw [← Vec.get_trie, ← Vec.get_trie, h]

theorem vecFun_single {d n : ℕ} (hn : n ≤ 2 ^ d) (k : Fin n) (z : ℤ) :
    vecFun d n [((k : ℕ), z)] = Pi.single k (z : ℂ) := by
  funext i
  simp only [vecFun, Vec.sumAt, List.filter_cons, List.filter_nil]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le k.2 hn), Nat.mod_eq_of_lt (lt_of_lt_of_le i.2 hn)]
  by_cases h : (k : ℕ) = i
  · have : k = i := Fin.ext h
    subst this
    simp
  · have : i ≠ k := fun h' => h (congrArg Fin.val h'.symm)
    simp [h, this]

/-! ### The certificate of a spectrum -/

/-- The eigenvector certificate: `(ν_k, c_k)` with `K c_k = ν_k c_k` for each `k`, every index
below `n`, and `n` of them. -/
def eigOK (d n : ℕ) (cols : List Vec) (eigs : List (ℤ × Vec)) : Bool :=
  eigs.length == n &&
    eigs.all fun e => keysLt n e.2 && Vec.trie d (apply cols e.2) == Vec.trie d (Vec.smul e.1 e.2)

/-- The independence certificate: `D c_k = d_k e_k`, `d_k ≠ 0`, with `D` given by columns. -/
def invOK (d n : ℕ) (dcols : List Vec) (eigs : List (ℤ × Vec)) (dg : List ℤ) : Bool :=
  dg.length == n &&
    (List.range n).all fun k =>
      dg.getD k 0 != 0 &&
        Vec.trie d (apply dcols (eigs.getD k (0, [])).2) == Vec.trie d [(k, dg.getD k 0)]

theorem eigOK_spec {d n : ℕ} {cols : List Vec} {eigs : List (ℤ × Vec)}
    (h : eigOK d n cols eigs = true) :
    eigs.length = n ∧ ∀ e ∈ eigs, keysLt n e.2 = true ∧
      Vec.trie d (apply cols e.2) = Vec.trie d (Vec.smul e.1 e.2) := by
  simp only [eigOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun e he => by simpa using h.2 e he⟩

/-- The multiplicities of a certified spectrum: the eigenvalue `μ` of `K` has the multiplicity
`#{k | ν_k = μ}`. -/
theorem finrank_eigenspace_colMat {d n : ℕ} (hn : n ≤ 2 ^ d) (cols dcols : List Vec)
    (eigs : List (ℤ × Vec)) (dg : List ℤ) (h1 : eigOK d n cols eigs = true)
    (h2 : invOK d n dcols eigs dg = true) (μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' (colMat d n cols)) μ) =
      (Finset.univ.filter fun k : Fin n => ((eigs.getD k (0, [])).1 : ℂ) = μ).card := by
  obtain ⟨hlen, heig⟩ := eigOK_spec h1
  simp only [invOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq] at h2
  obtain ⟨hdlen, hinv⟩ := h2
  have hmem : ∀ k : Fin n, eigs.getD k (0, []) ∈ eigs := by
    intro k
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  let C : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => vecFun d n (eigs.getD k (0, [])).2 i
  let ν : Fin n → ℂ := fun k => ((eigs.getD k (0, [])).1 : ℂ)
  let dgf : Fin n → ℂ := fun k => (dg.getD k 0 : ℂ)
  have hcol : ∀ (X : Matrix (Fin n) (Fin n) ℂ) k, (X * C).col k =
      X *ᵥ vecFun d n (eigs.getD k (0, [])).2 := by
    intro X k
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, C]
  have hKC : colMat d n cols * C = C * Matrix.diagonal ν := by
    ext i k
    have h := congrFun (hcol (colMat d n cols) k) i
    simp only [Matrix.col_apply] at h
    rw [h, colMat_mulVec hn _ _ (heig _ (hmem k)).1,
      vecFun_eq_of_trie_eq (heig _ (hmem k)).2, vecFun_smul, Matrix.mul_diagonal]
    simp [C, ν, mul_comm]
  have hDC : colMat d n dcols * C = Matrix.diagonal dgf := by
    ext i k
    have h := congrFun (hcol (colMat d n dcols) k) i
    simp only [Matrix.col_apply] at h
    rw [h, colMat_mulVec hn _ _ (heig _ (hmem k)).1, vecFun_eq_of_trie_eq (hinv k k.2).2,
      vecFun_single hn k]
    by_cases hik : i = k
    · subst hik
      simp [dgf]
    · simp [hik]
  have hdg : ∀ k, dgf k ≠ 0 := by
    intro k
    simp only [dgf, ne_eq, Int.cast_eq_zero]
    exact (hinv k k.2).1
  exact finrank_eigenspace_of_diagonalizes _ C _ ν dgf hKC hDC hdg μ

end Artform.SpecCert
