import ArtformTextbook.Ch12.SpectrumCert

/-!
# Common eigenvectors

Several commuting matrices with one basis of common eigenvectors, the columns of `C`
(`K_r C = C diag(ν_r)`, `D C = diag(d)` with `d` nonzero): a vector is an eigenvector of `K_r`
for `μ` exactly when it is a combination of the columns `k` with `ν_r k = μ`
(`SpecCert.mem_eigenspace_iff_of_diag`). Hence the dimension of a joint eigenspace of two of them
is the number of columns with both values (`SpecCert.finrank_inf_eigenspace_of_diag`), and an
eigenspace of one lies in an eigenspace of another when the values match column by column.
-/

namespace Artform.SpecCert

open FockCalc Module

open scoped Matrix

variable {n : ℕ}

/-- The vectors of an eigenspace are the combinations of the columns with that eigenvalue. -/
theorem mem_eigenspace_iff_of_diag (K C D : Matrix (Fin n) (Fin n) ℂ) (ν dg : Fin n → ℂ)
    (hKC : K * C = C * Matrix.diagonal ν) (hDC : D * C = Matrix.diagonal dg)
    (hdg : ∀ k, dg k ≠ 0) (μ : ℂ) (x : Fin n → ℂ) :
    x ∈ End.eigenspace (Matrix.toLin' K) μ ↔
      ∃ a : Fin n → ℂ, x = C *ᵥ a ∧ ∀ k, ν k ≠ μ → a k = 0 := by
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
  rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := hsurj x
    rw [Matrix.toLin'_apply] at hx ⊢
    refine ⟨a, rfl, fun k hk => ?_⟩
    rw [Matrix.mulVec_mulVec, hKC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul] at hx
    have h2 : Matrix.diagonal ν *ᵥ a = μ • a := hinj (by simpa only [Matrix.toLin'_apply] using hx)
    have h := congrFun h2 k
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
    have : (ν k - μ) * a k = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hk)
  · rintro ⟨a, rfl, ha⟩
    rw [Matrix.mulVec_mulVec, hKC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hk : ν k = μ
    · rw [hk]
    · rw [ha k hk, mul_zero, mul_zero]

/-- An eigenspace of `K₂` lies in an eigenspace of `K₁` when every column with the value `μ₂` for
`K₂` has the value `μ₁` for `K₁`. -/
theorem eigenspace_le_of_diag (K₁ K₂ C D : Matrix (Fin n) (Fin n) ℂ) (ν₁ ν₂ dg : Fin n → ℂ)
    (h₁ : K₁ * C = C * Matrix.diagonal ν₁) (h₂ : K₂ * C = C * Matrix.diagonal ν₂)
    (hDC : D * C = Matrix.diagonal dg) (hdg : ∀ k, dg k ≠ 0) (μ₁ μ₂ : ℂ)
    (h : ∀ k, ν₂ k = μ₂ → ν₁ k = μ₁) :
    End.eigenspace (Matrix.toLin' K₂) μ₂ ≤ End.eigenspace (Matrix.toLin' K₁) μ₁ := by
  intro x hx
  obtain ⟨a, rfl, ha⟩ := (mem_eigenspace_iff_of_diag K₂ C D ν₂ dg h₂ hDC hdg μ₂ x).mp hx
  refine (mem_eigenspace_iff_of_diag K₁ C D ν₁ dg h₁ hDC hdg μ₁ _).mpr ⟨a, rfl, fun k hk => ?_⟩
  by_contra hne
  exact hk (h k (by_contra fun h' => hne (ha k h')))

/-- The joint eigenspace of two matrices with common eigenvectors has the dimension of the number
of columns with both values. -/
theorem finrank_inf_eigenspace_of_diag (K₁ K₂ C D : Matrix (Fin n) (Fin n) ℂ)
    (ν₁ ν₂ dg : Fin n → ℂ) (h₁ : K₁ * C = C * Matrix.diagonal ν₁)
    (h₂ : K₂ * C = C * Matrix.diagonal ν₂) (hDC : D * C = Matrix.diagonal dg)
    (hdg : ∀ k, dg k ≠ 0) (μ₁ μ₂ : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' K₁) μ₁ ⊓ End.eigenspace (Matrix.toLin' K₂) μ₂) =
      (Finset.univ.filter fun k => ν₁ k = μ₁ ∧ ν₂ k = μ₂).card := by
  classical
  have hinj : Function.Injective (Matrix.toLin' C) := by
    intro a b hab
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hab
    have h := congrArg (fun x => D *ᵥ x) hab
    simp only [Matrix.mulVec_mulVec, hDC] at h
    funext k
    have hk := congrFun h k
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hk
    exact mul_left_cancel₀ (hdg k) hk
  let ν : Fin n → ℂ := fun k => if ν₁ k = μ₁ ∧ ν₂ k = μ₂ then 1 else 0
  have hmap : (End.eigenspace (Matrix.toLin' (Matrix.diagonal ν)) 1).map (Matrix.toLin' C) =
      End.eigenspace (Matrix.toLin' K₁) μ₁ ⊓ End.eigenspace (Matrix.toLin' K₂) μ₂ := by
    ext x
    rw [Submodule.mem_map, Submodule.mem_inf,
      mem_eigenspace_iff_of_diag K₁ C D ν₁ dg h₁ hDC hdg,
      mem_eigenspace_iff_of_diag K₂ C D ν₂ dg h₂ hDC hdg]
    have hd : ∀ a : Fin n → ℂ, a ∈ End.eigenspace (Matrix.toLin' (Matrix.diagonal ν)) 1 ↔
        ∀ k, ¬ (ν₁ k = μ₁ ∧ ν₂ k = μ₂) → a k = 0 := by
      intro a
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul]
      constructor
      · intro h k hk
        have := congrFun h k
        rw [Matrix.mulVec_diagonal] at this
        simp only [ν, hk, ite_false, zero_mul] at this
        exact this.symm
      · intro h
        funext k
        rw [Matrix.mulVec_diagonal]
        by_cases hk : ν₁ k = μ₁ ∧ ν₂ k = μ₂
        · simp [ν, hk]
        · simp [ν, hk, h k hk]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hd] at ha
      exact ⟨⟨a, rfl, fun k hk => ha k fun h => hk h.1⟩,
        ⟨a, rfl, fun k hk => ha k fun h => hk h.2⟩⟩
    · rintro ⟨⟨a, rfl, ha⟩, ⟨b, hab, hb⟩⟩
      have hba : a = b := hinj (by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hab)
      subst hba
      refine ⟨a, (hd a).mpr fun k hk => ?_, rfl⟩
      by_cases h1 : ν₁ k = μ₁
      · exact hb k fun h2 => hk ⟨h1, h2⟩
      · exact ha k h1
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm,
    finrank_eigenspace_diagonal]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ν]
  split_ifs with h <;> simp [h]

/-- The joint eigenspace of two operators on `W` read in a basis of `W`. -/
theorem finrank_inf_inf_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (T₁ T₂ : End ℂ V) (Φ : (Fin n → ℂ) →ₗ[ℂ] V) (hΦ : Function.Injective Φ)
    (hW : LinearMap.range Φ = W) (K₁ K₂ : Matrix (Fin n) (Fin n) ℂ)
    (hT₁ : ∀ a, T₁ (Φ a) = Φ (K₁ *ᵥ a)) (hT₂ : ∀ a, T₂ (Φ a) = Φ (K₂ *ᵥ a)) (μ₁ μ₂ : ℂ) :
    finrank ℂ ↥(W ⊓ End.eigenspace T₁ μ₁ ⊓ End.eigenspace T₂ μ₂) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' K₁) μ₁ ⊓ End.eigenspace (Matrix.toLin' K₂) μ₂) := by
  have hmap :
      (End.eigenspace (Matrix.toLin' K₁) μ₁ ⊓ End.eigenspace (Matrix.toLin' K₂) μ₂).map Φ =
      W ⊓ End.eigenspace T₁ μ₁ ⊓ End.eigenspace T₂ μ₂ := by
    ext x
    rw [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_inf]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨ha₁, ha₂⟩ := Submodule.mem_inf.mp ha
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply] at ha₁ ha₂
      refine ⟨⟨hW ▸ LinearMap.mem_range_self Φ a, ?_⟩, ?_⟩
      · rw [End.mem_eigenspace_iff, hT₁, ha₁, map_smul]
      · rw [End.mem_eigenspace_iff, hT₂, ha₂, map_smul]
    · rintro ⟨⟨hxW, hx₁⟩, hx₂⟩
      rw [← hW] at hxW
      obtain ⟨a, rfl⟩ := hxW
      refine ⟨a, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
      · rw [End.mem_eigenspace_iff, hT₁, ← map_smul] at hx₁
        rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hΦ hx₁
      · rw [End.mem_eigenspace_iff, hT₂, ← map_smul] at hx₂
        rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hΦ hx₂
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hΦ _).symm]

/-! ### The matrices of a certificate -/

/-- The vectors of a certificate as the columns of a matrix. -/
noncomputable def Cmat (d n : ℕ) (vs : List Vec) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => vecFun d n (vs.getD k []) i

theorem getD_map_snd (eigs : List (ℤ × Vec)) (k : ℕ) :
    (eigs.map Prod.snd).getD k [] = (eigs.getD k (0, [])).2 := by
  by_cases hk : k < eigs.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
      List.getElem_map]
  · push Not at hk
    rw [List.getD_eq_default _ _ (by simpa using hk), List.getD_eq_default _ _ hk]

theorem Cmat_col {d n : ℕ} (vs : List Vec) (X : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    (X * Cmat d n vs).col k = X *ᵥ vecFun d n (vs.getD k []) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Cmat]

/-- An eigenvector certificate: `K C = C diag(ν)`. -/
theorem colMat_mul_Cmat {d n : ℕ} (hn : n ≤ 2 ^ d) (cols : List Vec) (eigs : List (ℤ × Vec))
    (h : eigOK d n cols eigs = true) :
    colMat d n cols * Cmat d n (eigs.map Prod.snd) =
      Cmat d n (eigs.map Prod.snd) *
        Matrix.diagonal fun k : Fin n => ((eigs.getD k (0, [])).1 : ℂ) := by
  obtain ⟨hlen, heig⟩ := eigOK_spec h
  have hmem : ∀ k : Fin n, eigs.getD k (0, []) ∈ eigs := by
    intro k
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  ext i k
  have h1 := congrFun (Cmat_col (d := d) (eigs.map Prod.snd) (colMat d n cols) k) i
  simp only [Matrix.col_apply] at h1
  rw [h1, getD_map_snd, colMat_mulVec hn _ _ (heig _ (hmem k)).1,
    vecFun_eq_of_trie_eq (heig _ (hmem k)).2, vecFun_smul, Matrix.mul_diagonal, Cmat,
    Matrix.of_apply, getD_map_snd, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- An independence certificate: `D C = diag(d)` with `d` nonzero. -/
theorem D_mul_Cmat {d n : ℕ} (hn : n ≤ 2 ^ d) (cols dcols : List Vec) (eigs : List (ℤ × Vec))
    (dg : List ℤ) (h1 : eigOK d n cols eigs = true) (h2 : invOK d n dcols eigs dg = true) :
    colMat d n dcols * Cmat d n (eigs.map Prod.snd) =
      Matrix.diagonal (fun k : Fin n => (dg.getD k 0 : ℂ)) ∧
        ∀ k : Fin n, (dg.getD k 0 : ℂ) ≠ 0 := by
  obtain ⟨hlen, heig⟩ := eigOK_spec h1
  simp only [invOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq] at h2
  obtain ⟨_, hinv⟩ := h2
  have hmem : ∀ k : Fin n, eigs.getD k (0, []) ∈ eigs := by
    intro k
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  refine ⟨?_, fun k => by exact_mod_cast (hinv k k.2).1⟩
  ext i k
  have h := congrFun (Cmat_col (d := d) (eigs.map Prod.snd) (colMat d n dcols) k) i
  simp only [Matrix.col_apply] at h
  rw [h, getD_map_snd, colMat_mulVec hn _ _ (heig _ (hmem k)).1,
    vecFun_eq_of_trie_eq (hinv k k.2).2, vecFun_single hn k]
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

end Artform.SpecCert
