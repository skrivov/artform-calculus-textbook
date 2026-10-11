import ArtformTextbook.Ch12.VertexStates
import ArtformTextbook.Ch11.Tick

/-!
# Colour rotations of the eight states

In any order `ord` of the six modes of a vertex, `Γ(g) = Γ(g ⊗ 1)` transforms each creation,
`Γ(g) a†_{cs} = (Σ_{c'} g_{c'c} a†_{c's}) Γ(g)` (Proposition 11.12), and for a unitary `g` each
annihilation, `Γ(g) a_{cs} = (Σ_{c'} conj(g_{c'c}) a_{c's}) Γ(g)`. Hence:

* `Γ(g) |0⟩ = |0⟩` and `Γ(g) |full⟩ = det(g)² |full⟩` (the minor on all six modes);
* `Γ(g) ε_{s₁s₂s₃} = det(g) ε_{s₁s₂s₃}` (`Moments.t3_leviCivita`), and `a†_{1s} a†_{2s} a†_{3s} |0⟩`
  is `ε_{sss}/6`, the creations anticommuting;
* `Γ(g) D = Σ_{c'c''} (g gᵀ)_{c'c''} a†_{c'↑} a†_{c''↓} |0⟩`, and
  `Γ(g) H = det(g)² Σ_{c'c''} conj((g gᵀ)_{c'c''}) a_{c'↑} a_{c''↓} |full⟩` for unitary `g`.

So a rotation of `SU(3)` with real entries (`g gᵀ = g g† = 1`) fixes the eight states, every
matrix of `SU(3)` fixes the six of them built from `ε` alone, and `ω 1 ∈ SU(3)` multiplies the
pair by `ω²` and the paired holes by `ω`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Spin

namespace Vertex

variable (ord : LinearOrder (Fin 3 × Fin 2))

/-! ### Products of anticommuting factors -/

/-- Three factors of an anticommuting family: `X_a X_b X_c = ε_{abc} X_1 X_2 X_3`. -/
theorem anticomm_three {N : Type*} [Fintype N] (X : Fin 3 → Matrix N N ℂ)
    (h : ∀ i j, X i * X j = -(X j * X i)) (a b c : Fin 3) :
    X a * X b * X c = leviCivita a b c • (X 0 * X 1 * X 2) := by
  have hsq : ∀ i, X i * X i = 0 := by
    intro i
    have h2 : (2 : ℂ) • (X i * X i) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h i i]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have r : ∀ i j (Y : Matrix N N ℂ), X i * (X j * Y) = -(X j * (X i * Y)) := by
    intro i j Y
    rw [← mul_assoc, h i j, neg_mul, mul_assoc]
  have s : ∀ i (Y : Matrix N N ℂ), X i * (X i * Y) = 0 := by
    intro i Y
    rw [← mul_assoc, hsq, zero_mul]
  rw [Moments.leviCivita_eq]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Moments.lcTab, mul_assoc, hsq, s, h 1 0, h 2 0, h 2 1, r 1 0]

/-! ### Transformed creations and annihilations -/

theorem gamma_mul_creation (g : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 3 × Fin 2) :
    Fock.vertexGamma ord g * Fock.creation ord m =
      (∑ c', g c' m.1 • Fock.creation ord (c', m.2)) * Fock.vertexGamma ord g := by
  rw [Fock.vertexGamma, Fock.secondQuant_mul_creation, Fock.transformedCreation_kron]

theorem gamma_mul_annihilation {g : Matrix (Fin 3) (Fin 3) ℂ}
    (hg : g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (m : Fin 3 × Fin 2) :
    Fock.vertexGamma ord g * Fock.annihilation ord m =
      (∑ c', conj (g c' m.1) • Fock.annihilation ord (c', m.2)) * Fock.vertexGamma ord g := by
  set W : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
    Matrix.kroneckerMap (· * ·) g (1 : Matrix (Fin 2) (Fin 2) ℂ) with hWdef
  have hW : W ∈ Matrix.unitaryGroup (Fin 3 × Fin 2) ℂ := Fock.kron_one_mem_unitaryGroup hg
  have hconj := Fock.secondQuant_conj_annihilation ord hW m
  have hunit := Fock.secondQuant_mem_unitaryGroup ord hW
  have hinv : (Fock.secondQuant ord W)⁻¹ * Fock.secondQuant ord W = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (Fock.isUnit_of_mem_unitaryGroup hunit))
  have hsum : ∑ l, conj (W l m) • Fock.annihilation ord l =
      ∑ c', conj (g c' m.1) • Fock.annihilation ord (c', m.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_eq_single m.2]
    · simp [hWdef, Matrix.kroneckerMap_apply]
    · intro s _ hs
      simp [hWdef, Matrix.kroneckerMap_apply, Matrix.one_apply_ne hs]
    · simp
  rw [Fock.vertexGamma, ← hWdef, ← hsum, ← hconj, Matrix.mul_assoc _ _ (Fock.secondQuant ord W),
    hinv, Matrix.mul_one]

theorem gamma_ket_empty (g : Matrix (Fin 3) (Fin 3) ℂ) :
    Fock.vertexGamma ord g *ᵥ Fock.ket ∅ = Fock.ket ∅ :=
  Fock.secondQuant_mulVec_vacuum ord _

/-- `Γ(g)|full⟩ = det(g)² |full⟩`. -/
theorem gamma_full (g : Matrix (Fin 3) (Fin 3) ℂ) :
    Fock.vertexGamma ord g *ᵥ full = g.det ^ 2 • full := by
  funext n'
  rw [full, Fock.mulVec_ket]
  simp only [Pi.smul_apply, Fock.ket, Pi.single_apply, smul_eq_mul]
  split_ifs with hn
  · subst hn
    rw [mul_one, Fock.vertexGamma, Fock.secondQuant_diag_eq_det,
      ← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)).symm,
      Matrix.submatrix_submatrix]
    have : ((Subtype.val : ↥(Finset.univ : Finset (Fin 3 × Fin 2)) → Fin 3 × Fin 2) ∘
        (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)).symm) = id := by
      funext x
      rfl
    rw [this, Matrix.submatrix_id_id, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one,
      Fintype.card_fin]
  · rw [mul_zero]
    by_contra hne
    have hc := Fock.secondQuant_card_eq ord _ hne
    rw [Finset.card_univ] at hc
    exact hn (Finset.eq_univ_of_card _ hc)

/-! ### The pair, the quartet and the holes -/

theorem gamma_mul_ket_empty (g X : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ)
    (hg : g *ᵥ Fock.ket ∅ = Fock.ket ∅) : (X * g) *ᵥ Fock.ket ∅ = X *ᵥ Fock.ket ∅ := by
  rw [← Matrix.mulVec_mulVec, hg]

/-- `Γ(g) D = Σ_{c'c''} (g gᵀ)_{c'c''} a†_{c'↑} a†_{c''↓} |0⟩`. -/
theorem gamma_pair (g : Matrix (Fin 3) (Fin 3) ℂ) :
    Fock.vertexGamma ord g *ᵥ pair ord =
      ∑ c' : Fin 3, ∑ c'' : Fin 3, (g * gᵀ) c' c'' •
        ((Fock.creation ord (c', up) * Fock.creation ord (c'', down)) *ᵥ Fock.ket ∅) := by
  have key : ∀ c : Fin 3, Fock.vertexGamma ord g * (Fock.creation ord (c, up) *
      Fock.creation ord (c, down)) =
      (∑ c', g c' c • Fock.creation ord (c', up)) *
        (∑ c'', g c'' c • Fock.creation ord (c'', down)) * Fock.vertexGamma ord g := by
    intro c
    rw [← mul_assoc, gamma_mul_creation, mul_assoc, gamma_mul_creation, ← mul_assoc]
  simp only [pair, Matrix.mulVec_sum, Matrix.mulVec_mulVec, key,
    gamma_mul_ket_empty _ _ (gamma_ket_empty ord g), Finset.sum_mul_sum, smul_mul_smul_comm,
    Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  rw [← Finset.sum_smul]
  congr 1

/-- A matrix with `g gᵀ = 1` fixes the pair. -/
theorem gamma_pair_of_orth {g : Matrix (Fin 3) (Fin 3) ℂ} (hg : g * gᵀ = 1) :
    Fock.vertexGamma ord g *ᵥ pair ord = pair ord := by
  rw [gamma_pair, hg, pair]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_eq_single c']
  · simp
  · intro c'' _ hc
    simp [Matrix.one_apply_ne (Ne.symm hc)]
  · simp

theorem sum_three {β : Type*} [AddCommMonoid β] (f : Fin 3 → Fin 3 → Fin 3 → β) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ p : Fin 3 × Fin 3 × Fin 3, f p.1 p.2.1 p.2.2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]

/-- `Γ(g)` on `a†_{a s₁} a†_{b s₂} a†_{c s₃} |0⟩`. -/
theorem gamma_three (g : Matrix (Fin 3) (Fin 3) ℂ) (s₁ s₂ s₃ : Fin 2) (a b c : Fin 3) :
    Fock.vertexGamma ord g *ᵥ ((Fock.creation ord (a, s₁) * Fock.creation ord (b, s₂) *
      Fock.creation ord (c, s₃)) *ᵥ Fock.ket ∅) =
      ∑ a' : Fin 3, ∑ b' : Fin 3, ∑ c' : Fin 3, (g a' a * g b' b * g c' c) •
        ((Fock.creation ord (a', s₁) * Fock.creation ord (b', s₂) *
          Fock.creation ord (c', s₃)) *ᵥ Fock.ket ∅) := by
  have key : Fock.vertexGamma ord g * (Fock.creation ord (a, s₁) *
      Fock.creation ord (b, s₂) * Fock.creation ord (c, s₃)) =
      (∑ a', g a' a • Fock.creation ord (a', s₁)) * (∑ b', g b' b • Fock.creation ord (b', s₂)) *
        (∑ c', g c' c • Fock.creation ord (c', s₃)) * Fock.vertexGamma ord g := by
    rw [← mul_assoc, ← mul_assoc, gamma_mul_creation, mul_assoc _ (Fock.vertexGamma ord g),
      gamma_mul_creation, ← mul_assoc, mul_assoc _ (Fock.vertexGamma ord g),
      gamma_mul_creation, ← mul_assoc]
  rw [Matrix.mulVec_mulVec, key, gamma_mul_ket_empty _ _ (gamma_ket_empty ord g),
    Finset.sum_mul_sum, Finset.sum_mul]
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, Matrix.sum_mulVec, Matrix.smul_mulVec]

/-- `Γ(g) ε_{s₁s₂s₃} = det(g) ε_{s₁s₂s₃}`. -/
theorem gamma_epsState (g : Matrix (Fin 3) (Fin 3) ℂ) (s₁ s₂ s₃ : Fin 2) :
    Fock.vertexGamma ord g *ᵥ epsState ord s₁ s₂ s₃ = g.det • epsState ord s₁ s₂ s₃ := by
  set Y : Fin 3 → Fin 3 → Fin 3 → (Finset (Fin 3 × Fin 2) → ℂ) := fun a b c =>
    (Fock.creation ord (a, s₁) * Fock.creation ord (b, s₂) * Fock.creation ord (c, s₃)) *ᵥ
      Fock.ket ∅ with hY
  have ht' : ∀ a' b' c', ∑ a, ∑ b, ∑ c, leviCivita a b c * (g a' a * g b' b * g c' c) =
      g.det * leviCivita a' b' c' := by
    intro a' b' c'
    have := congrFun (congrFun (congrFun (Moments.t3_leviCivita g) a') b') c'
    simp only [Moments.t3, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  have lhs : Fock.vertexGamma ord g *ᵥ epsState ord s₁ s₂ s₃ =
      ∑ p : Fin 3 × Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3 × Fin 3,
        (leviCivita p.1 p.2.1 p.2.2 * (g q.1 p.1 * g q.2.1 p.2.1 * g q.2.2 p.2.2)) •
          Y q.1 q.2.1 q.2.2 := by
    rw [epsState]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [sum_three]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [gamma_three, sum_three, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul]
  have rhs : g.det • epsState ord s₁ s₂ s₃ =
      ∑ q : Fin 3 × Fin 3 × Fin 3, ∑ p : Fin 3 × Fin 3 × Fin 3,
        (leviCivita p.1 p.2.1 p.2.2 * (g q.1 p.1 * g q.2.1 p.2.1 * g q.2.2 p.2.2)) •
          Y q.1 q.2.1 q.2.2 := by
    rw [epsState, sum_three (fun a b c => leviCivita a b c • Y a b c), Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul, smul_smul,
      ← sum_three (fun a b c => leviCivita a b c * (g q.1 a * g q.2.1 b * g q.2.2 c)), ht']
  rw [lhs, rhs, Finset.sum_comm]

/-- `Γ(g) a†_{1s} a†_{2s} a†_{3s} |0⟩ = det(g) a†_{1s} a†_{2s} a†_{3s} |0⟩`. -/
theorem gamma_three_same (g : Matrix (Fin 3) (Fin 3) ℂ) (s : Fin 2) :
    Fock.vertexGamma ord g *ᵥ ((Fock.creation ord (0, s) * Fock.creation ord (1, s) *
      Fock.creation ord (2, s)) *ᵥ Fock.ket ∅) =
      g.det • ((Fock.creation ord (0, s) * Fock.creation ord (1, s) *
        Fock.creation ord (2, s)) *ᵥ Fock.ket ∅) := by
  have hX : ∀ i j : Fin 3, Fock.creation ord (i, s) * Fock.creation ord (j, s) =
      -(Fock.creation ord (j, s) * Fock.creation ord (i, s)) :=
    fun i j => Fock.creation_mul_creation ord _ _
  have hdet : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, g a 0 * g b 1 * g c 2 * leviCivita a b c =
      g.det := by
    have := congrFun (congrFun (congrFun (Moments.t3_leviCivita gᵀ) 0) 1) 2
    simp only [Moments.t3, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply,
      Matrix.det_transpose, Moments.leviCivita_012, mul_one] at this
    rw [← this]
  set Y0 := (Fock.creation ord (0, s) * Fock.creation ord (1, s) *
    Fock.creation ord (2, s)) *ᵥ Fock.ket ∅ with hY0
  have h3 : ∀ a b c : Fin 3, (Fock.creation ord (a, s) * Fock.creation ord (b, s) *
      Fock.creation ord (c, s)) *ᵥ Fock.ket ∅ = leviCivita a b c • Y0 := by
    intro a b c
    rw [anticomm_three (fun c => Fock.creation ord (c, s)) hX a b c, Matrix.smul_mulVec]
  rw [gamma_three]
  calc _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        (g a 0 * g b 1 * g c 2 * leviCivita a b c) • Y0 := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [h3, smul_smul]
    _ = g.det • Y0 := by simp only [← Finset.sum_smul, hdet]

/-- Each member of the quartet is multiplied by `det(g)`. -/
theorem gamma_quartet (g : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 4) :
    Fock.vertexGamma ord g *ᵥ quartet ord m = g.det • quartet ord m := by
  fin_cases m
  · exact gamma_three_same ord g up
  · simp only [quartet, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.mulVec_smul, gamma_epsState, smul_comm g.det]
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val, Matrix.mulVec_smul, gamma_epsState,
      smul_comm g.det]
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val]
    exact gamma_three_same ord g down

/-- `Γ(g) H = det(g)² Σ_{c'c''} conj((g gᵀ)_{c'c''}) a_{c'↑} a_{c''↓} |full⟩` for a unitary `g`. -/
theorem gamma_holes {g : Matrix (Fin 3) (Fin 3) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    Fock.vertexGamma ord g *ᵥ holes ord =
      g.det ^ 2 • ∑ c' : Fin 3, ∑ c'' : Fin 3, conj ((g * gᵀ) c' c'') •
        ((Fock.annihilation ord (c', up) * Fock.annihilation ord (c'', down)) *ᵥ full) := by
  have key : ∀ c : Fin 3, Fock.vertexGamma ord g * (Fock.annihilation ord (c, up) *
      Fock.annihilation ord (c, down)) =
      (∑ c', conj (g c' c) • Fock.annihilation ord (c', up)) *
        (∑ c'', conj (g c'' c) • Fock.annihilation ord (c'', down)) * Fock.vertexGamma ord g := by
    intro c
    rw [← mul_assoc, gamma_mul_annihilation ord hg, mul_assoc, gamma_mul_annihilation ord hg,
      ← mul_assoc]
  have hfull : ∀ X : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ,
      (X * Fock.vertexGamma ord g) *ᵥ full = g.det ^ 2 • (X *ᵥ full) := by
    intro X
    rw [← Matrix.mulVec_mulVec, gamma_full, Matrix.mulVec_smul]
  simp only [holes, Matrix.mulVec_sum, Matrix.mulVec_mulVec, key, hfull, ← Finset.smul_sum]
  congr 1
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp [Matrix.mul_apply, Matrix.transpose_apply, map_sum]

/-! ### The states fixed by a colour rotation -/

theorem det_eq_one {g : Matrix (Fin 3) (Fin 3) ℂ} (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    g.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hg).2

theorem mem_unitary {g : Matrix (Fin 3) (Fin 3) ℂ}
    (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) : g ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hg).1

/-- Every matrix of `SU(3)` fixes the six states built from `ε` alone. -/
theorem gamma_six {g : Matrix (Fin 3) (Fin 3) ℂ} (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (i : Fin 6) : Fock.vertexGamma ord g *ᵥ six ord i = six ord i := by
  fin_cases i <;> simp [six, empty, gamma_ket_empty, gamma_quartet, gamma_full, det_eq_one hg]

/-- A matrix of `SU(3)` with `g gᵀ = 1` (a rotation) fixes all eight states. -/
theorem gamma_eight {g : Matrix (Fin 3) (Fin 3) ℂ} (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hr : g * gᵀ = 1) (i : Fin 8) : Fock.vertexGamma ord g *ᵥ eight ord i = eight ord i := by
  have hholes : Fock.vertexGamma ord g *ᵥ holes ord = holes ord := by
    rw [gamma_holes ord (mem_unitary hg), hr, det_eq_one hg, one_pow, one_smul, holes]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_eq_single c']
    · simp
    · intro c'' _ hc
      simp [Matrix.one_apply_ne (Ne.symm hc)]
    · simp
  fin_cases i <;>
    simp [eight, empty, gamma_ket_empty, gamma_quartet, gamma_full, det_eq_one hg,
      gamma_pair_of_orth ord hr, hholes]

end Vertex

end Artform
