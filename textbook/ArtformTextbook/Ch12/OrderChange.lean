import ArtformTextbook.Ch11.Occupation
import ArtformTextbook.Ch11.Colourless
import ArtformTextbook.Ch12.Defs.Models

/-!
# A change of the order of the modes

Proposition 11.11 (`Fock.orderSigma`): in a new order of the modes the creations and the
annihilations are conjugated by the diagonal matrix `Σ` of signs. Here the second quantization
`Γ(W)` is conjugated in the same way (`Fock.secondQuant_change`), hence the gauge action of an
edge, and the zero-flux values in the new order are the old ones moved by `Σ`
(`Edge.zeroFluxValues_change`). The tally, the spin operators and the parity are conjugated
likewise, and the multiplicities of the values of an operator on the sector do not depend on
the order (`Edge.sectorMult_change`).
-/

namespace Artform

open scoped Matrix

namespace Fock

variable {M : Type*} [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
theorem orderSign_empty (ord₁ ord₂ : LinearOrder M) : orderSign ord₁ ord₂ ∅ = 1 := by
  simp [orderSign]

theorem orderSigma_mulVec_ket (ord₁ ord₂ : LinearOrder M) (n : Finset M) :
    orderSigma ord₁ ord₂ *ᵥ ket n = orderSign ord₁ ord₂ n • ket n := by
  funext n'
  rw [orderSigma, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ket, Pi.single_apply]
  split_ifs with h
  · rw [h]
  · simp

theorem orderSigma_inv_mulVec_ket_empty (ord₁ ord₂ : LinearOrder M) :
    (orderSigma ord₁ ord₂)⁻¹ *ᵥ ket ∅ = ket ∅ := by
  rw [orderSigma_inv, orderSigma_mulVec_ket, orderSign_empty, one_smul]

theorem orderSigma_mul_inv (ord₁ ord₂ : LinearOrder M) :
    orderSigma ord₁ ord₂ * (orderSigma ord₁ ord₂)⁻¹ = 1 := by
  rw [orderSigma_inv, orderSigma_mul_self]

theorem orderSigma_inv_mul (ord₁ ord₂ : LinearOrder M) :
    (orderSigma ord₁ ord₂)⁻¹ * orderSigma ord₁ ord₂ = 1 := by
  rw [orderSigma_inv, orderSigma_mul_self]

theorem orderSigma_conj_mul (ord₁ ord₂ : LinearOrder M) (A B : Matrix (Finset M) (Finset M) ℂ) :
    orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹ *
        (orderSigma ord₁ ord₂ * B * (orderSigma ord₁ ord₂)⁻¹) =
      orderSigma ord₁ ord₂ * (A * B) * (orderSigma ord₁ ord₂)⁻¹ := by
  calc orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹ *
        (orderSigma ord₁ ord₂ * B * (orderSigma ord₁ ord₂)⁻¹)
      = orderSigma ord₁ ord₂ * A * ((orderSigma ord₁ ord₂)⁻¹ * orderSigma ord₁ ord₂) * B *
          (orderSigma ord₁ ord₂)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [orderSigma_inv_mul, Matrix.mul_one, Matrix.mul_assoc (orderSigma ord₁ ord₂)]

theorem orderSigma_conj_add (ord₁ ord₂ : LinearOrder M) (A B : Matrix (Finset M) (Finset M) ℂ) :
    orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹ +
        orderSigma ord₁ ord₂ * B * (orderSigma ord₁ ord₂)⁻¹ =
      orderSigma ord₁ ord₂ * (A + B) * (orderSigma ord₁ ord₂)⁻¹ := by
  rw [Matrix.mul_add, Matrix.add_mul]

theorem orderSigma_conj_smul (ord₁ ord₂ : LinearOrder M) (c : ℂ)
    (A : Matrix (Finset M) (Finset M) ℂ) :
    c • (orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹) =
      orderSigma ord₁ ord₂ * (c • A) * (orderSigma ord₁ ord₂)⁻¹ := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem orderSigma_conj_sum {ι : Type*} (s : Finset ι) (ord₁ ord₂ : LinearOrder M)
    (A : ι → Matrix (Finset M) (Finset M) ℂ) :
    ∑ i ∈ s, orderSigma ord₁ ord₂ * A i * (orderSigma ord₁ ord₂)⁻¹ =
      orderSigma ord₁ ord₂ * (∑ i ∈ s, A i) * (orderSigma ord₁ ord₂)⁻¹ := by
  rw [Finset.mul_sum, Finset.sum_mul]

theorem orderSigma_conj_one (ord₁ ord₂ : LinearOrder M) :
    orderSigma ord₁ ord₂ * 1 * (orderSigma ord₁ ord₂)⁻¹ = 1 := by
  rw [Matrix.mul_one, orderSigma_mul_inv]

omit [Fintype M] in
theorem orderSigma_conjTranspose (ord₁ ord₂ : LinearOrder M) :
    (orderSigma ord₁ ord₂)ᴴ = orderSigma ord₁ ord₂ := by
  rw [orderSigma, Matrix.diagonal_conjTranspose]
  congr 1
  funext n
  rcases orderSign_eq_one_or ord₁ ord₂ n with h | h <;> simp [h]

theorem orderSigma_conj_conjTranspose (ord₁ ord₂ : LinearOrder M)
    (A : Matrix (Finset M) (Finset M) ℂ) :
    (orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹)ᴴ =
      orderSigma ord₁ ord₂ * Aᴴ * (orderSigma ord₁ ord₂)⁻¹ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, orderSigma_inv,
    orderSigma_conjTranspose, Matrix.mul_assoc]

/-- A diagonal matrix commutes with the signs. -/
theorem orderSigma_conj_diagonal (ord₁ ord₂ : LinearOrder M) (d : Finset M → ℂ) :
    orderSigma ord₁ ord₂ * Matrix.diagonal d * (orderSigma ord₁ ord₂)⁻¹ = Matrix.diagonal d := by
  rw [orderSigma_inv, orderSigma, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext n
  rcases orderSign_eq_one_or ord₁ ord₂ n with h | h <;> simp [h]

theorem crProd_change (ord₁ ord₂ : LinearOrder M) (L : List M) :
    crProd ord₂ L = orderSigma ord₁ ord₂ * crProd ord₁ L * (orderSigma ord₁ ord₂)⁻¹ := by
  induction L with
  | nil =>
    simp only [crProd, List.map_nil, List.prod_nil]
    exact (orderSigma_conj_one ord₁ ord₂).symm
  | cons a L ih =>
    have e : ∀ o, crProd o (a :: L) = creation o a * crProd o L := fun o => by
      simp only [crProd, List.map_cons, List.prod_cons]
    rw [e, e, ih, creation_change ord₁ ord₂ a, orderSigma_conj_mul]

theorem transformedCreation_change (ord₁ ord₂ : LinearOrder M) (W : Matrix M M ℂ) (m : M) :
    transformedCreation ord₂ W m =
      orderSigma ord₁ ord₂ * transformedCreation ord₁ W m * (orderSigma ord₁ ord₂)⁻¹ := by
  simp only [transformedCreation, creation_change ord₁ ord₂, orderSigma_conj_smul,
    orderSigma_conj_sum]

theorem trProd_change (ord₁ ord₂ : LinearOrder M) (W : Matrix M M ℂ) (L : List M) :
    trProd ord₂ W L = orderSigma ord₁ ord₂ * trProd ord₁ W L * (orderSigma ord₁ ord₂)⁻¹ := by
  induction L with
  | nil =>
    simp only [trProd, List.map_nil, List.prod_nil]
    exact (orderSigma_conj_one ord₁ ord₂).symm
  | cons a L ih =>
    have e : ∀ o, trProd o W (a :: L) = transformedCreation o W a * trProd o W L := fun o => by
      simp only [trProd, List.map_cons, List.prod_cons]
    rw [e, e, ih, transformedCreation_change ord₁ ord₂ W a, orderSigma_conj_mul]

/-- In a new order of the modes the second quantization is conjugated by the signs:
`Γ₂(W) = Σ Γ₁(W) Σ⁻¹`. -/
theorem secondQuant_change (ord₁ ord₂ : LinearOrder M) (W : Matrix M M ℂ) :
    secondQuant ord₂ W =
      orderSigma ord₁ ord₂ * secondQuant ord₁ W * (orderSigma ord₁ ord₂)⁻¹ := by
  apply ext_ket
  intro n
  have h1 : crProd ord₁ (letI := ord₂; n.sort) *ᵥ ket ∅ = (orderSigma ord₁ ord₂)⁻¹ *ᵥ ket n := by
    have h := crProd_sort_mulVec_vacuum ord₂ n
    rw [crProd_change ord₁ ord₂, ← Matrix.mulVec_mulVec, orderSigma_inv_mulVec_ket_empty,
      ← Matrix.mulVec_mulVec] at h
    rw [← h, Matrix.mulVec_mulVec, orderSigma_inv_mul, Matrix.one_mulVec]
  rw [secondQuant_mulVec_ket, trProd_change ord₁ ord₂, ← Matrix.mulVec_mulVec,
    orderSigma_inv_mulVec_ket_empty, ← Matrix.mulVec_mulVec, ← secondQuant_mulVec_crProd, h1,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Fock

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] {G : Type*}
  [Group G]

theorem pairHom_change (ρ : G →* Matrix C C ℂ) (ord₁ ord₂ : LinearOrder (Mode C S))
    (h : G × G) :
    pairHom ρ ord₂ h =
      Fock.orderSigma ord₁ ord₂ * pairHom ρ ord₁ h * (Fock.orderSigma ord₁ ord₂)⁻¹ :=
  Fock.secondQuant_change ord₁ ord₂ _

/-- The zero-flux values are the tables fixed by every gauge pair. -/
theorem mem_zeroFluxValues (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (v : Finset (Mode C S) → ℂ) :
    v ∈ zeroFluxValues ρ ord ↔ ∀ h, pairHom ρ ord h *ᵥ v = v := by
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ((mem_zeroFlux_iff ρ ord ψ).mp hψ).2
  · intro hv
    exact ⟨fun _ => v, (mem_zeroFlux_iff ρ ord _).mpr ⟨fun _ => rfl, hv⟩, rfl⟩

/-- The signs as a linear equivalence of the coefficient tables (`Σ² = 1`). -/
noncomputable def sigEquiv (ord₁ ord₂ : LinearOrder (Mode C S)) :
    (Finset (Mode C S) → ℂ) ≃ₗ[ℂ] (Finset (Mode C S) → ℂ) :=
  LinearEquiv.ofInvolutive (Matrix.toLin' (Fock.orderSigma ord₁ ord₂)) fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Fock.orderSigma_mul_self, Matrix.one_mulVec]

theorem sigEquiv_apply (ord₁ ord₂ : LinearOrder (Mode C S)) (v : Finset (Mode C S) → ℂ) :
    sigEquiv ord₁ ord₂ v = Fock.orderSigma ord₁ ord₂ *ᵥ v := rfl

theorem sigEquiv_symm_apply (ord₁ ord₂ : LinearOrder (Mode C S)) (v : Finset (Mode C S) → ℂ) :
    (sigEquiv ord₁ ord₂).symm v = (Fock.orderSigma ord₁ ord₂)⁻¹ *ᵥ v := by
  rw [Fock.orderSigma_inv]
  rfl

/-- An operator conjugated by the signs, as a linear map. -/
theorem toLin'_conj (ord₁ ord₂ : LinearOrder (Mode C S))
    (X : Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ) :
    Matrix.toLin' (Fock.orderSigma ord₁ ord₂ * X * (Fock.orderSigma ord₁ ord₂)⁻¹) =
      (sigEquiv ord₁ ord₂).conj (Matrix.toLin' X) := by
  apply LinearMap.ext
  intro v
  rw [LinearEquiv.conj_apply_apply, sigEquiv_symm_apply, sigEquiv_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The zero-flux values in a new order are the old ones moved by the signs. -/
theorem zeroFluxValues_change (ρ : G →* Matrix C C ℂ) (ord₁ ord₂ : LinearOrder (Mode C S)) :
    zeroFluxValues ρ ord₂ = (zeroFluxValues ρ ord₁).map (sigEquiv ord₁ ord₂).toLinearMap := by
  ext v
  rw [Submodule.mem_map_equiv, mem_zeroFluxValues, mem_zeroFluxValues, sigEquiv_symm_apply]
  refine forall_congr' fun h => ?_
  rw [pairHom_change ρ ord₁ ord₂, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro hv
    calc pairHom ρ ord₁ h *ᵥ ((Fock.orderSigma ord₁ ord₂)⁻¹ *ᵥ v)
        = (Fock.orderSigma ord₁ ord₂)⁻¹ *ᵥ (Fock.orderSigma ord₁ ord₂ *ᵥ
            (pairHom ρ ord₁ h *ᵥ ((Fock.orderSigma ord₁ ord₂)⁻¹ *ᵥ v))) := by
          rw [Matrix.mulVec_mulVec (M := (Fock.orderSigma ord₁ ord₂)⁻¹), Fock.orderSigma_inv_mul,
            Matrix.one_mulVec]
      _ = _ := by rw [hv]
  · intro hv
    rw [hv, Matrix.mulVec_mulVec, Fock.orderSigma_mul_inv, Matrix.one_mulVec]

/-- An eigenspace moved by a linear equivalence is the eigenspace of the conjugated operator. -/
theorem map_eigenspace_conj {V : Type*} [AddCommGroup V] [Module ℂ V] (E : V ≃ₗ[ℂ] V)
    (T : Module.End ℂ V) (μ : ℂ) :
    (Module.End.eigenspace T μ).map E.toLinearMap = Module.End.eigenspace (E.conj T) μ := by
  ext v
  rw [Submodule.mem_map_equiv, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
    LinearEquiv.conj_apply_apply]
  constructor
  · intro h
    rw [h, map_smul, LinearEquiv.apply_symm_apply]
  · intro h
    rw [← map_smul, ← h, LinearEquiv.symm_apply_apply]

theorem map_inf_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (E : V ≃ₗ[ℂ] V)
    (A B : Submodule ℂ V) : (A ⊓ B).map E.toLinearMap = A.map E.toLinearMap ⊓ B.map E.toLinearMap :=
  Submodule.map_inf _ E.injective

/-- The multiplicities of the values of an operator on the zero-flux sector do not depend on the
order of the modes. -/
theorem sectorMult_change (ρ : G →* Matrix C C ℂ) (ord₁ ord₂ : LinearOrder (Mode C S))
    (X : Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ) (μ : ℂ) :
    sectorMult ρ ord₂ (Fock.orderSigma ord₁ ord₂ * X * (Fock.orderSigma ord₁ ord₂)⁻¹) μ =
      sectorMult ρ ord₁ X μ := by
  rw [sectorMult, sectorMult, zeroFluxValues_change ρ ord₁ ord₂, toLin'_conj,
    ← map_eigenspace_conj, ← map_inf_equiv, LinearEquiv.finrank_map_eq]

/-! ### The operators of one edge in a new order -/

theorem hopA_change (ord₁ ord₂ : LinearOrder (Mode (Fin 3) S)) (c c' : Fin 3) :
    hopA ord₂ c c' =
      Fock.orderSigma ord₁ ord₂ * hopA ord₁ c c' * (Fock.orderSigma ord₁ ord₂)⁻¹ := by
  simp only [hopA, Fock.creation_change ord₁ ord₂, Fock.annihilation_change ord₁ ord₂,
    Fock.orderSigma_conj_mul, Fock.orderSigma_conj_sum]

theorem tally_change (ord₁ ord₂ : LinearOrder (Mode (Fin 3) S)) (m : ℕ) :
    tally ord₂ m =
      Fock.orderSigma ord₁ ord₂ * tally ord₁ m * (Fock.orderSigma ord₁ ord₂)⁻¹ := by
  simp only [tally, hopA_change ord₁ ord₂, Fock.orderSigma_conj_conjTranspose,
    Fock.orderSigma_conj_mul, Fock.orderSigma_conj_add, Fock.orderSigma_conj_sum,
    Fock.orderSigma_conj_smul]

theorem spinPlus_change (ord₁ ord₂ : LinearOrder (Mode (Fin 3) (Fin 2))) :
    spinPlus ord₂ =
      Fock.orderSigma ord₁ ord₂ * spinPlus ord₁ * (Fock.orderSigma ord₁ ord₂)⁻¹ := by
  simp only [spinPlus, Fock.creation_change ord₁ ord₂, Fock.annihilation_change ord₁ ord₂,
    Fock.orderSigma_conj_mul, Fock.orderSigma_conj_add, Fock.orderSigma_conj_sum]

theorem spinZ_change (ord₁ ord₂ : LinearOrder (Mode (Fin 3) (Fin 2))) :
    spinZ = Fock.orderSigma ord₁ ord₂ * spinZ * (Fock.orderSigma ord₁ ord₂)⁻¹ :=
  (Fock.orderSigma_conj_diagonal ord₁ ord₂ _).symm

theorem spinSq_change (ord₁ ord₂ : LinearOrder (Mode (Fin 3) (Fin 2))) :
    spinSq ord₂ =
      Fock.orderSigma ord₁ ord₂ * spinSq ord₁ * (Fock.orderSigma ord₁ ord₂)⁻¹ := by
  have hz : Fock.orderSigma ord₁ ord₂ * (spinZ * spinZ) * (Fock.orderSigma ord₁ ord₂)⁻¹ =
      spinZ * spinZ := by
    rw [spinZ, Matrix.diagonal_mul_diagonal, Fock.orderSigma_conj_diagonal]
  rw [spinSq, spinSq, spinPlus_change ord₁ ord₂, Fock.orderSigma_conj_conjTranspose,
    Fock.orderSigma_conj_mul, Fock.orderSigma_conj_mul, Fock.orderSigma_conj_add,
    Fock.orderSigma_conj_smul]
  conv_lhs => rw [← hz]
  rw [Fock.orderSigma_conj_add]

end Edge

end Artform
