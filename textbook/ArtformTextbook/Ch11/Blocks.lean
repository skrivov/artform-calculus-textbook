import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import ArtformTextbook.Ch11.Tables

/-!
# Blocks and one-edge operators (Theorems 11.4 and 11.6)

The book imports Theorem 11.4 from Serre (the decomposition of the group algebra into matrix
algebras); here it is proved from Schur's lemma, which Mathlib provides.

* **Orthogonality.** For irreducible `ρ`, `σ` the average `Σ_U σ(U) X ρ(U⁻¹)` of a linear map
  `X` is an intertwining map, so it vanishes when `ρ ≇ σ` and is the scalar `|G| Tr X / d` when
  `ρ = σ` (`schurAvg_eq_zero`, `schurAvg_self`). Hence
  `Σ_U Tr(A ρ(U⁻¹)) σ(U)` is `0`, respectively `(|G|/d) A` (`coeffSum_eq_zero`,
  `coeffSum_self`). A finite group keeps a positive definite form, so the complex conjugate of
  the table `U ↦ Tr(A ρ(U))` is a table `U ↦ Tr(A' ρ(U⁻¹))` (`exists_conj_trace`); blocks of
  non-isomorphic irreducible representations are therefore orthogonal, and orthogonal blocks are
  independent. The second relation makes `A ↦ (U ↦ Tr(A ρ(U)))` injective, so `B_ρ` has
  dimension `d²` (`finrank_block`).
* **Span.** If the blocks of a complete family did not span, the tables orthogonal to all of them
  would form a nonzero subspace that every right write keeps. A nonzero such subspace of least
  dimension carries an irreducible representation by right writes, every table in it lies in its
  block (`x(U) = Tr(A R_U)` with `A y = y(1) x`), and that block is the block of a member of the
  family: a nonzero table orthogonal to itself, which is impossible (`iSup_block_eq_top`).
* **Existence.** A family of pairwise non-isomorphic irreducible representations has at most
  `|G|` members, since its blocks are independent and nonzero; a largest one is complete
  (`exists_complete_family`).
* **One-edge operators.** Commuting with the right writes makes `B(V, U)` a function of `V U⁻¹`,
  commuting with the left writes makes it a class function (`commute_iff_convolution`). On a
  block, convolution by a class function `f` multiplies by `Tr(Σ_W f(W) ρ(W⁻¹)) / d`, by Schur's
  lemma (`convolution_mulVec_block`), and the orthogonality of characters gives the scalar `r(ρ)`
  for `f = (1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ` (`hat_charComb`).
-/

namespace Artform

open scoped ComplexConjugate Matrix

section Basic

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem blockMap_apply (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    blockMap ρ A = blockTable ρ A := by
  funext U
  simp [blockMap, blockTable]

theorem mem_block {ρ : Representation ℂ G V} {ψ : G → ℂ} :
    ψ ∈ block ρ ↔ ∃ A, blockTable ρ A = ψ := by
  simp [block, blockMap_apply]

theorem blockTable_mem_block (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    blockTable ρ A ∈ block ρ := mem_block.mpr ⟨A, rfl⟩

/-- Definition 11.3: a left write acts on the block by `A ↦ A ρ(h)⁻¹`. -/
theorem leftWrite_blockTable (ρ : Representation ℂ G V) (A : Module.End ℂ V) (h : G) :
    leftWrite h (blockTable ρ A) = blockTable ρ (A * ρ h⁻¹) := by
  funext U
  simp [blockTable, map_mul, mul_assoc]

/-- Definition 11.3: a right write acts on the block by `A ↦ ρ(h) A`. -/
theorem rightWrite_blockTable (ρ : Representation ℂ G V) (A : Module.End ℂ V) (h : G) :
    rightWrite h (blockTable ρ A) = blockTable ρ (ρ h * A) := by
  funext U
  simp only [blockTable, rightWrite_apply, map_mul]
  rw [← mul_assoc, LinearMap.trace_mul_comm ℂ (A * ρ U), ← mul_assoc]

/-- The table of the block with `A = 1` is the character `χ_ρ`. -/
theorem blockTable_one (ρ : Representation ℂ G V) : blockTable ρ 1 = ρ.character := by
  funext U
  simp [blockTable, Representation.character]

/-- Isomorphic representations have the same block. -/
theorem blockTable_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (B : Module.End ℂ W) :
    blockTable σ B = blockTable ρ (e.toLinearEquiv.symm.conj B) := by
  funext U
  simp only [blockTable]
  rw [← e.conj_apply_self U, ← LinearMap.trace_conj' _ e.toLinearEquiv.symm]
  congr 1
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearEquiv.conj_comp]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply, Representation.Equiv.coe_invFun]

theorem block_eq_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : block σ = block ρ := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨B, rfl⟩ := mem_block.mp hψ
    rw [blockTable_equiv e]
    exact blockTable_mem_block _ _
  · intro ψ hψ
    obtain ⟨A, rfl⟩ := mem_block.mp hψ
    rw [blockTable_equiv e.symm]
    exact blockTable_mem_block _ _

end Basic

/-! The rest of the argument lives in the namespace `Artform.Blocks`. -/

namespace Blocks

section Schur

variable {G : Type*} [Group G] [Fintype G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The average `Σ_U σ(U) ∘ X ∘ ρ(U⁻¹)` of a linear map `X : V → W`. -/
noncomputable def schurAvg (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (X : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  ∑ U, σ U ∘ₗ X ∘ₗ ρ U⁻¹

theorem schurAvg_comp (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (X : V →ₗ[ℂ] W) (h : G) : schurAvg ρ σ X ∘ₗ ρ h = σ h ∘ₗ schurAvg ρ σ X := by
  ext v
  simp only [schurAvg, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun U => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
  rw [← Module.End.mul_apply (ρ U⁻¹), ← map_mul, ← Module.End.mul_apply (σ h), ← map_mul,
    mul_inv_cancel_left]

/-- The average as an intertwining map. -/
noncomputable def schurAvgHom (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (X : V →ₗ[ℂ] W) : ρ.IntertwiningMap σ :=
  ⟨schurAvg ρ σ X, schurAvg_comp ρ σ X⟩

omit [Fintype G] in
theorem nontrivial_of_isIrreducible (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  simp [Subsingleton.elim v 0]

omit [Fintype G] in
theorem finrank_pos_of_isIrreducible [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] : 0 < Module.finrank ℂ V := by
  have := nontrivial_of_isIrreducible ρ
  exact Module.finrank_pos

/-- Schur's lemma for two irreducible representations that are not isomorphic: the average
vanishes. -/
theorem schurAvg_eq_zero [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ¬ Nonempty (ρ.Equiv σ)) (X : V →ₗ[ℂ] W) : schurAvg ρ σ X = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero (schurAvgHom ρ σ X) with hb | h0
  · exact absurd ⟨Representation.IntertwiningMap.ofBijective _ hb⟩ h
  · exact congrArg Representation.IntertwiningMap.toLinearMap h0

theorem trace_schurAvg_self (ρ : Representation ℂ G V) (X : Module.End ℂ V) :
    LinearMap.trace ℂ V (schurAvg ρ ρ X) = Fintype.card G * LinearMap.trace ℂ V X := by
  simp only [schurAvg, map_sum]
  rw [Finset.sum_congr rfl fun U _ => ?_, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm,
    mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- Schur's lemma for one irreducible representation over `ℂ`: the average is the scalar
`|G| Tr(X) / d`. -/
theorem schurAvg_self [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (X : Module.End ℂ V) :
    schurAvg ρ ρ X =
      ((Fintype.card G : ℂ) * LinearMap.trace ℂ V X / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (schurAvgHom ρ ρ X)
  have hX : schurAvg ρ ρ X = c • LinearMap.id := by
    have := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Representation.IntertwiningMap.algebraMap_apply] at this
    exact this.symm
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  have htr := trace_schurAvg_self ρ X
  rw [hX, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hX, ← htr, mul_div_cancel_right₀ _ hd]

end Schur

section Orthogonality

variable {G : Type*} [Group G] [Fintype G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- `A ↦ Σ_U Tr(A ρ(U⁻¹)) σ(U)`. -/
noncomputable def coeffSum (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.End ℂ V →ₗ[ℂ] Module.End ℂ W :=
  ∑ U, (LinearMap.toSpanSingleton ℂ (Module.End ℂ W) (σ U)) ∘ₗ
    (LinearMap.trace ℂ V ∘ₗ LinearMap.mulRight ℂ (ρ U⁻¹))

theorem coeffSum_apply (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : Module.End ℂ V) :
    coeffSum ρ σ A = ∑ U, LinearMap.trace ℂ V (A * ρ U⁻¹) • σ U := by
  simp [coeffSum, LinearMap.sum_apply]

theorem sum_trace_mul_trace (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : Module.End ℂ V) (B : Module.End ℂ W) :
    ∑ U, LinearMap.trace ℂ V (A * ρ U⁻¹) * LinearMap.trace ℂ W (B * σ U) =
      LinearMap.trace ℂ W (B * coeffSum ρ σ A) := by
  rw [coeffSum_apply, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul]

omit [Fintype G] in
/-- Every endomorphism is a sum of maps of rank one, `A = Σ_k b_k^* (·) A(b_k)`. -/
theorem eq_sum_smulRight {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V)
    (A : Module.End ℂ V) : A = ∑ k, (b.coord k).smulRight (A (b k)) := by
  refine b.ext fun j => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem coeffSum_smulRight_apply [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (f : Module.Dual ℂ V) (v : V) (w : W) :
    coeffSum ρ σ (f.smulRight v) w = schurAvg ρ σ (f.smulRight w) v := by
  rw [coeffSum_apply, schurAvg, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  have : f.smulRight v * ρ U⁻¹ = (f ∘ₗ ρ U⁻¹).smulRight v := by
    ext x
    simp
  simp [this]

/-- The first orthogonality relation: for irreducible representations that are not isomorphic,
`Σ_U Tr(A ρ(U⁻¹)) σ(U) = 0`. -/
theorem coeffSum_eq_zero [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ¬ Nonempty (ρ.Equiv σ)) (A : Module.End ℂ V) : coeffSum ρ σ A = 0 := by
  rw [eq_sum_smulRight (Module.finBasis ℂ V) A, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  ext w
  rw [coeffSum_smulRight_apply, schurAvg_eq_zero ρ σ h]
  rfl

/-- The second orthogonality relation: for an irreducible representation of dimension `d`,
`Σ_U Tr(A ρ(U⁻¹)) ρ(U) = (|G| / d) A`. -/
theorem coeffSum_self [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (A : Module.End ℂ V) :
    coeffSum ρ ρ A = ((Fintype.card G : ℂ) / Module.finrank ℂ V) • A := by
  conv_lhs => rw [eq_sum_smulRight (Module.finBasis ℂ V) A]
  conv_rhs => rw [eq_sum_smulRight (Module.finBasis ℂ V) A]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext w
  rw [coeffSum_smulRight_apply, schurAvg_self, LinearMap.trace_smulRight]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply, smul_smul]
  congr 1
  ring

theorem sum_trace_eq_zero [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ¬ Nonempty (ρ.Equiv σ)) (A : Module.End ℂ V) (B : Module.End ℂ W) :
    ∑ U, LinearMap.trace ℂ V (A * ρ U⁻¹) * LinearMap.trace ℂ W (B * σ U) = 0 := by
  rw [sum_trace_mul_trace, coeffSum_eq_zero ρ σ h, mul_zero, map_zero]

theorem sum_trace_self [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (A B : Module.End ℂ V) :
    ∑ U, LinearMap.trace ℂ V (A * ρ U⁻¹) * LinearMap.trace ℂ V (B * ρ U) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V * LinearMap.trace ℂ V (B * A) := by
  rw [sum_trace_mul_trace, coeffSum_self, mul_smul_comm, map_smul, smul_eq_mul]

end Orthogonality

section Conj

variable {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

open scoped ComplexOrder in
/-- A representation of a finite group keeps a positive definite form: in a basis the matrices
`M g` satisfy `(M g)ᴴ P (M g) = P` for `P = Σ_h (M h)ᴴ (M h)`, so `(M g)ᴴ = P M(g⁻¹) P⁻¹`.
Hence the complex conjugate of the table `U ↦ Tr(A ρ(U))` is a table `U ↦ Tr(A' ρ(U⁻¹))`, with
`A' = 1` when `A = 1`. -/
theorem exists_conj_trace (ρ : Representation ℂ G V) :
    ∃ Φ : Module.End ℂ V → Module.End ℂ V, Φ 1 = 1 ∧
      ∀ A U, conj (LinearMap.trace ℂ V (A * ρ U)) = LinearMap.trace ℂ V (Φ A * ρ U⁻¹) := by
  classical
  have := Fintype.ofFinite G
  let b := Module.finBasis ℂ V
  let E := LinearMap.toMatrixAlgEquiv b
  let M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    E.toMonoidHom.comp ρ
  have htr : ∀ X : Module.End ℂ V, LinearMap.trace ℂ V X = (E X).trace := fun X =>
    LinearMap.trace_eq_matrix_trace ℂ b X
  set P := ∑ h, (M h)ᴴ * M h with hPdef
  have hP : ∀ g, (M g)ᴴ * P * M g = P := by
    intro g
    rw [hPdef, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    simp [Matrix.conjTranspose_mul, mul_assoc]
  have hPu : IsUnit P := by
    refine (Matrix.posDef_sum Finset.univ_nonempty fun h _ => ?_).isUnit
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Group.isUnit h).map M))
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h2 : ∀ g, (M g)ᴴ = P * M g⁻¹ * P⁻¹ := by
    intro g
    have h1 : (M g)ᴴ * P = P * M g⁻¹ := by
      calc (M g)ᴴ * P = (M g)ᴴ * P * (M g * M g⁻¹) := by
            rw [← map_mul, mul_inv_cancel, map_one, mul_one]
        _ = P * M g⁻¹ := by rw [← mul_assoc, hP]
    rw [← h1, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
  refine ⟨fun A => E.symm (P⁻¹ * (E A)ᴴ * P), ?_, fun A U => ?_⟩
  · simp [Matrix.nonsing_inv_mul _ hdet]
  · rw [htr, htr, map_mul, map_mul, AlgEquiv.apply_symm_apply, starRingEnd_apply,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
    have hM : ∀ g, E (ρ g) = M g := fun g => rfl
    rw [hM, hM, h2]
    calc (P * M U⁻¹ * P⁻¹ * (E A)ᴴ).trace = (P * (M U⁻¹ * P⁻¹ * (E A)ᴴ)).trace := by
          simp only [mul_assoc]
      _ = (M U⁻¹ * P⁻¹ * (E A)ᴴ * P).trace := by
          rw [Matrix.trace_mul_comm]
      _ = (M U⁻¹ * (P⁻¹ * (E A)ᴴ * P)).trace := by simp only [mul_assoc]
      _ = (P⁻¹ * (E A)ᴴ * P * M U⁻¹).trace := Matrix.trace_mul_comm _ _

/-- `χ(U⁻¹) = conj χ(U)`. -/
theorem character_inv' (ρ : Representation ℂ G V) (U : G) :
    ρ.character U⁻¹ = conj (ρ.character U) := by
  obtain ⟨Φ, h1, hΦ⟩ := exists_conj_trace ρ
  have := hΦ 1 U
  rw [h1, one_mul, one_mul] at this
  exact this.symm

end Conj

section BlockFacts

variable {G : Type*} [Group G] [Fintype G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- Blocks of irreducible representations that are not isomorphic are orthogonal. -/
theorem coeffPairing_block_eq_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (h : ¬ Nonempty (ρ.Equiv σ)) {φ ψ : G → ℂ}
    (hφ : φ ∈ block ρ) (hψ : ψ ∈ block σ) : coeffPairing φ ψ = 0 := by
  obtain ⟨A, rfl⟩ := mem_block.mp hφ
  obtain ⟨B, rfl⟩ := mem_block.mp hψ
  obtain ⟨Φ, -, hΦ⟩ := exists_conj_trace ρ
  simp only [coeffPairing, blockTable, hΦ]
  exact sum_trace_eq_zero ρ σ h (Φ A) B

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem trace_mul_smulRight (B : Module.End ℂ V) (f : Module.Dual ℂ V) (v : V) :
    LinearMap.trace ℂ V (B * f.smulRight v) = f (B v) := by
  have : B * f.smulRight v = f.smulRight (B v) := by
    ext x
    simp
  rw [this, LinearMap.trace_smulRight]

omit [Fintype G] [FiniteDimensional ℂ W] in
/-- For an irreducible representation, `A ↦ (U ↦ Tr(A ρ(U)))` is injective. -/
theorem blockMap_injective [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Function.Injective (blockMap ρ) := by
  have := Fintype.ofFinite G
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro B hB
  have h0 : ∀ U, LinearMap.trace ℂ V (B * ρ U) = 0 := fun U => by
    simpa [blockMap_apply, blockTable] using congrFun hB U
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hAB : ∀ A, LinearMap.trace ℂ V (B * A) = 0 := by
    intro A
    have := sum_trace_self ρ A B
    simp only [h0, mul_zero, Finset.sum_const_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (div_ne_zero hG hd)
  ext v
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (B v)).mp fun f => ?_
  rw [← trace_mul_smulRight, hAB]

omit [Fintype G] [FiniteDimensional ℂ W] in
/-- Definition 11.3: the block of an irreducible representation of dimension `d` has dimension
`d²`. -/
theorem finrank_block [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ (block ρ) = Module.finrank ℂ V ^ 2 := by
  rw [block, LinearMap.finrank_range_of_inj (blockMap_injective ρ), Module.finrank_linearMap,
    sq]

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem character_ne_zero (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ρ.character ≠ 0 := by
  intro h
  have := congrFun h 1
  rw [Representation.char_one, Pi.zero_apply] at this
  exact (finrank_pos_of_isIrreducible ρ).ne' (by exact_mod_cast this)

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem block_ne_bot (ρ : Representation ℂ G V) [ρ.IsIrreducible] : block ρ ≠ ⊥ := by
  intro h
  have : ρ.character ∈ block ρ := by
    rw [← blockTable_one]
    exact blockTable_mem_block ρ 1
  rw [h, Submodule.mem_bot] at this
  exact character_ne_zero ρ this

end BlockFacts

section Pairing

variable {B : Type*} [Fintype B]

theorem coeffPairing_add_right (φ ψ ψ' : B → ℂ) :
    coeffPairing φ (ψ + ψ') = coeffPairing φ ψ + coeffPairing φ ψ' := by
  simp [coeffPairing, mul_add, Finset.sum_add_distrib]

theorem coeffPairing_smul_right (φ ψ : B → ℂ) (c : ℂ) :
    coeffPairing φ (c • ψ) = c * coeffPairing φ ψ := by
  simp [coeffPairing, Finset.mul_sum, mul_left_comm]

theorem coeffPairing_self_eq_zero {φ : B → ℂ} : coeffPairing φ φ = 0 ↔ φ = 0 := by
  open scoped ComplexOrder in
  exact dotProduct_star_self_eq_zero

theorem coeffPairing_add_left (φ φ' ψ : B → ℂ) :
    coeffPairing (φ + φ') ψ = coeffPairing φ ψ + coeffPairing φ' ψ := by
  simp [coeffPairing, add_mul, Finset.sum_add_distrib]

theorem coeffPairing_smul_left (φ ψ : B → ℂ) (c : ℂ) :
    coeffPairing (c • φ) ψ = conj c * coeffPairing φ ψ := by
  simp [coeffPairing, Finset.mul_sum, mul_assoc]

theorem coeffPairing_zero_left (ψ : B → ℂ) : coeffPairing 0 ψ = 0 := by
  simp [coeffPairing]

theorem coeffPairing_zero_right (φ : B → ℂ) : coeffPairing φ 0 = 0 := by
  simp [coeffPairing]

theorem coeffPairing_eq_dotProduct (φ ψ : B → ℂ) : coeffPairing φ ψ = star φ ⬝ᵥ ψ := rfl

/-- The tables orthogonal to every table of `S`. -/
def orth (S : Submodule ℂ (B → ℂ)) : Submodule ℂ (B → ℂ) where
  carrier := {ψ | ∀ φ ∈ S, coeffPairing φ ψ = 0}
  add_mem' {ψ ψ'} hψ hψ' φ hφ := by rw [coeffPairing_add_right, hψ φ hφ, hψ' φ hφ, add_zero]
  zero_mem' φ _ := by simp [coeffPairing]
  smul_mem' c ψ hψ φ hφ := by rw [coeffPairing_smul_right, hψ φ hφ, mul_zero]

theorem mem_orth {S : Submodule ℂ (B → ℂ)} {ψ : B → ℂ} :
    ψ ∈ orth S ↔ ∀ φ ∈ S, coeffPairing φ ψ = 0 := Iff.rfl

/-- A family of pairwise orthogonal subspaces is independent. -/
theorem iSupIndep_of_orthogonal {ι : Type*} (t : ι → Submodule ℂ (B → ℂ))
    (h : ∀ i j, i ≠ j → ∀ φ ∈ t i, ∀ ψ ∈ t j, coeffPairing φ ψ = 0) : iSupIndep t := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), t j) ≤ orth (Submodule.span ℂ {x}) := by
    refine iSup₂_le fun j hj ψ hψ φ hφ => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hφ
    have : coeffPairing (c • x) ψ = conj c * coeffPairing x ψ := by
      simp [coeffPairing, Finset.mul_sum, mul_assoc]
    rw [this, h i j (Ne.symm hj) x hx ψ hψ, mul_zero]
  exact coeffPairing_self_eq_zero.mp (hle hx' x (Submodule.mem_span_singleton_self x))

/-- A proper subspace has a nonzero table orthogonal to it. -/
theorem exists_mem_orth_ne_zero {S : Submodule ℂ (B → ℂ)} (hS : S ≠ ⊤) :
    ∃ ψ ∈ orth S, ψ ≠ 0 := by
  let e := WithLp.linearEquiv 2 ℂ (B → ℂ)
  let S' : Submodule ℂ (EuclideanSpace ℂ B) := S.comap e.toLinearMap
  have hS' : S' ≠ ⊤ := by
    intro h
    apply hS
    rw [eq_top_iff]
    intro φ _
    have : e.symm φ ∈ S' := h ▸ Submodule.mem_top
    simpa [S'] using this
  have hne : S'ᗮ ≠ ⊥ := fun h => hS' (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨e x, fun φ hφ => ?_, fun h => hx0 (e.injective (by simpa using h))⟩
  have h1 : e.symm φ ∈ S' := by simpa [S'] using hφ
  have := Submodule.inner_right_of_mem_orthogonal h1 hx
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  rw [coeffPairing, ← this]
  simp [dotProduct, e, mul_comm]

/-- If independent subspaces span, the dimension is the sum of their dimensions. -/
theorem finrank_eq_sum_of_iSupIndep {ι : Type*} [Fintype ι]
    (t : ι → Submodule ℂ (B → ℂ)) (hind : iSupIndep t) (htop : ⨆ i, t i = ⊤) :
    Fintype.card B = ∑ i, Module.finrank ℂ (t i) := by
  classical
  have hint : DirectSum.IsInternal t :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top t).mpr ⟨hind, htop⟩
  rw [← Module.finrank_fintype_fun_eq_card ℂ,
    ← LinearEquiv.finrank_eq (LinearEquiv.ofBijective (DirectSum.coeLinearMap t) hint),
    Module.finrank_directSum]

end Pairing

section Transport

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Irreducibility passes along an isomorphism of representations. -/
theorem isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := (e : V ≃ W).bijective
  exact IsSimpleModule.congr (LinearEquiv.ofBijective f hf).symm

/-- Every finite-dimensional representation is isomorphic to one on `Fin d → ℂ`. -/
theorem exists_fin_equiv [FiniteDimensional ℂ W] (σ : Representation ℂ G W) :
    ∃ σ' : Representation ℂ G (Fin (Module.finrank ℂ W) → ℂ), Nonempty (σ.Equiv σ') := by
  let e := (Module.finBasis ℂ W).equivFun
  let σ' : Representation ℂ G (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun g => e.conj (σ g)
      map_one' := by
        ext v
        simp [LinearEquiv.conj_apply]
      map_mul' := fun g h => by
        ext v
        simp [LinearEquiv.conj_apply] }
  refine ⟨σ', ⟨Representation.Equiv.mk e fun g => ?_⟩⟩
  ext v
  simp [σ', LinearEquiv.conj_apply]

end Transport

section Span

variable {G : Type*} [Group G]

/-- A subspace of tables that every right write carries into itself. -/
def RightInvariant (X : Submodule ℂ (G → ℂ)) : Prop :=
  ∀ (h : G), ∀ ψ ∈ X, rightWrite h ψ ∈ X

/-- The right writes, restricted to a right-invariant subspace of tables. -/
noncomputable def rightRep (X : Submodule ℂ (G → ℂ)) (hX : RightInvariant X) :
    Representation ℂ G X where
  toFun h :=
    { toFun := fun ψ => ⟨rightWrite h ψ, hX h ψ ψ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext ψ U
    change (ψ : G → ℂ) (U * 1) = (ψ : G → ℂ) U
    rw [mul_one]
  map_mul' h k := by
    ext ψ U
    change (ψ : G → ℂ) (U * (h * k)) = (ψ : G → ℂ) (U * h * k)
    rw [mul_assoc]

theorem rightRep_apply (X : Submodule ℂ (G → ℂ)) (hX : RightInvariant X) (h : G) (ψ : X) :
    ((rightRep X hX h ψ : X) : G → ℂ) = rightWrite h ψ := rfl

theorem rightInvariant_block {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : RightInvariant (block ρ) := by
  intro h ψ hψ
  obtain ⟨A, rfl⟩ := mem_block.mp hψ
  rw [rightWrite_blockTable]
  exact blockTable_mem_block _ _

theorem rightInvariant_iSup {ι : Type*} (t : ι → Submodule ℂ (G → ℂ))
    (ht : ∀ i, RightInvariant (t i)) : RightInvariant (⨆ i, t i) := by
  intro h ψ hψ
  refine Submodule.iSup_induction t (motive := fun φ => rightWrite h φ ∈ ⨆ i, t i) hψ
    (fun i φ hφ => Submodule.mem_iSup_of_mem i (ht i h φ hφ)) ?_ ?_
  · exact (Submodule.zero_mem _ : (0 : G → ℂ) ∈ ⨆ i, t i)
  · intro φ φ' h1 h2
    exact Submodule.add_mem _ h1 h2

variable [Fintype G]

theorem coeffPairing_rightWrite (φ ψ : G → ℂ) (h : G) :
    coeffPairing φ (rightWrite h ψ) = coeffPairing (rightWrite h⁻¹ φ) ψ := by
  simp only [coeffPairing, rightWrite_apply]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun U => by simp

theorem rightInvariant_orth {S : Submodule ℂ (G → ℂ)} (hS : RightInvariant S) :
    RightInvariant (orth S) := by
  intro h ψ hψ φ hφ
  rw [coeffPairing_rightWrite]
  exact hψ _ (hS h⁻¹ φ hφ)

omit [Fintype G] in
/-- Every table of a right-invariant subspace `X` lies in the block of the right writes on `X`:
`x(U) = Tr(A R_U)` with `A y = y(1) x`. -/
theorem mem_block_rightRep [Finite G] (X : Submodule ℂ (G → ℂ)) (hX : RightInvariant X)
    {x : G → ℂ} (hx : x ∈ X) : x ∈ block (rightRep X hX) := by
  let ev : X →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp X.subtype
  refine mem_block.mpr ⟨ev.smulRight ⟨x, hx⟩, ?_⟩
  funext U
  have : ev.smulRight ⟨x, hx⟩ * rightRep X hX U = (ev ∘ₗ rightRep X hX U).smulRight ⟨x, hx⟩ := by
    ext y
    simp
  simp [blockTable, this, ev, rightRep_apply]

omit [Fintype G] in
/-- The blocks of a complete family of irreducible representations span the tables. -/
theorem iSup_block_eq_top [Finite G] {ι : Type*} {d : ι → ℕ}
    (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hcomplete : ∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
      ∃ i, Nonempty (σ.Equiv (ρ i))) :
    ⨆ i, block (ρ i) = ⊤ := by
  classical
  have := Fintype.ofFinite G
  set S := ⨆ i, block (ρ i) with hSdef
  by_contra hS
  have hSinv : RightInvariant S := rightInvariant_iSup _ fun i => rightInvariant_block (ρ i)
  have hWinv := rightInvariant_orth hSinv
  obtain ⟨ψ, hψW, hψ0⟩ := exists_mem_orth_ne_zero hS
  let P : ℕ → Prop := fun n => ∃ X : Submodule ℂ (G → ℂ),
    X ≤ orth S ∧ X ≠ ⊥ ∧ RightInvariant X ∧ Module.finrank ℂ X = n
  have hP : ∃ n, P n := ⟨_, orth S, le_rfl,
    fun h => hψ0 (by rw [h] at hψW; exact (Submodule.mem_bot ℂ).mp hψW), hWinv, rfl⟩
  obtain ⟨X, hXW, hX0, hXinv, hXn⟩ := Nat.find_spec hP
  let σ := rightRep X hXinv
  have hirr : σ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun Y => ?_ }
    · obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
      have h1 : (⟨x, hxX⟩ : X) ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      exact hx0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).mp h1))
    · let Y' : Submodule ℂ (G → ℂ) := Y.toSubmodule.map X.subtype
      have hY'X : Y' ≤ X := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      by_cases hY' : Y' = ⊥
      · left
        apply Subrepresentation.toSubmodule_injective
        change Y.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro y hy
        have : (y : G → ℂ) ∈ Y' := ⟨y, hy, rfl⟩
        rw [hY', Submodule.mem_bot] at this
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext this)
      · right
        have hY'inv : RightInvariant Y' := by
          rintro h _ ⟨y, hy, rfl⟩
          exact ⟨rightRep X hXinv h y, Y.apply_mem_toSubmodule h hy, rfl⟩
        have hle : Module.finrank ℂ X ≤ Module.finrank ℂ Y' := by
          rw [hXn]
          exact Nat.find_min' hP ⟨Y', le_trans hY'X hXW, hY', hY'inv, rfl⟩
        have heq : Y' = X := Submodule.eq_of_le_of_finrank_le hY'X hle
        apply Subrepresentation.toSubmodule_injective
        change Y.toSubmodule = ⊤
        rw [eq_top_iff]
        intro y _
        have : (y : G → ℂ) ∈ Y' := by
          rw [heq]
          exact y.2
        obtain ⟨y', hy', hyy⟩ := this
        have hy'y : y' = y := Subtype.ext hyy
        exact hy'y ▸ hy'
  obtain ⟨σ', ⟨e⟩⟩ := exists_fin_equiv σ
  have hirr' : σ'.IsIrreducible := isIrreducible_of_equiv e
  obtain ⟨i, ⟨e'⟩⟩ := hcomplete _ σ' hirr'
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  have hxσ : x ∈ block σ := mem_block_rightRep X hXinv hxX
  rw [← block_eq_of_equiv e, ← block_eq_of_equiv e'] at hxσ
  have hxS : x ∈ S := (le_iSup (fun i => block (ρ i)) i) hxσ
  exact hx0 (coeffPairing_self_eq_zero.mp (hXW hxX x hxS))

end Span

section Family

variable {G : Type*} [Group G] [Fintype G]

/-- Blocks of a family of pairwise non-isomorphic irreducible representations are pairwise
orthogonal. -/
theorem block_orthogonal {ι : Type*} {d : ι → ℕ} (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hirr : ∀ i, (ρ i).IsIrreducible) (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    ∀ i j, i ≠ j → ∀ φ ∈ block (ρ i), ∀ ψ ∈ block (ρ j), coeffPairing φ ψ = 0 := by
  intro i j hij φ hφ ψ hψ
  have := hirr i
  have := hirr j
  exact coeffPairing_block_eq_zero (ρ i) (ρ j) (fun ⟨e⟩ => hij (hdist i j ⟨e⟩)) hφ hψ

/-- A family of pairwise non-isomorphic irreducible representations has at most `|G|`
members. -/
theorem card_le_of_pairwise {n : ℕ} {d : Fin n → ℕ}
    (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hirr : ∀ i, (ρ i).IsIrreducible) (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    n ≤ Fintype.card G := by
  classical
  have hind : iSupIndep (fun i => block (ρ i)) :=
    iSupIndep_of_orthogonal _ (block_orthogonal ρ hirr hdist)
  have hne : ∀ i, block (ρ i) ≠ ⊥ := fun i => by
    have := hirr i
    exact block_ne_bot (ρ i)
  have h := hind.subtype_ne_bot_le_finrank
  rw [Module.finrank_fintype_fun_eq_card,
    Fintype.card_congr (Equiv.subtypeUnivEquiv hne), Fintype.card_fin] at h
  exact h

omit [Fintype G] in
/-- The distinct irreducible representations exist, finitely many. -/
theorem exists_complete_family [Finite G] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) ∧
      ∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
        ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  have := Fintype.ofFinite G
  let P : ℕ → Prop := fun n => ∃ (d : Fin n → ℕ) (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
  have hP0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i⟩
  have hN : P (Nat.findGreatest P (Fintype.card G)) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨d, ρ, hirr, hdist⟩ := hN
  refine ⟨_, d, ρ, hirr, hdist, fun d' σ hσ => ?_⟩
  by_contra hno
  simp only [not_exists, not_nonempty_iff] at hno
  let d₁ : Fin (Nat.findGreatest P (Fintype.card G) + 1) → ℕ := Fin.cons d' d
  let ρ₁ : ∀ i, Representation ℂ G (Fin (d₁ i) → ℂ) := Fin.cons σ ρ
  have hirr₁ : ∀ i, (ρ₁ i).IsIrreducible := fun i =>
    Fin.cases (motive := fun i => (ρ₁ i).IsIrreducible) hσ (fun j => hirr j) i
  have hdist₁ : ∀ i j, Nonempty ((ρ₁ i).Equiv (ρ₁ j)) → i = j := by
    intro i j
    refine Fin.cases (motive := fun i => Nonempty ((ρ₁ i).Equiv (ρ₁ j)) → i = j) ?_ ?_ i
    · refine Fin.cases (motive := fun j => Nonempty ((ρ₁ 0).Equiv (ρ₁ j)) → 0 = j) ?_ ?_ j
      · exact fun _ => rfl
      · intro j ⟨e⟩
        exact (hno j).elim e
    · intro i
      refine Fin.cases (motive := fun j => Nonempty ((ρ₁ i.succ).Equiv (ρ₁ j)) → i.succ = j)
        ?_ ?_ j
      · intro ⟨e⟩
        exact (hno i).elim e.symm
      · intro j hij
        rw [hdist i j hij]
  have hle := card_le_of_pairwise ρ₁ hirr₁ hdist₁
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle ⟨d₁, ρ₁, hirr₁, hdist₁⟩

end Family

end Blocks

open Blocks in
/-- **Theorem 11.4** (blocks fill the table space). The blocks of the distinct irreducible
representations are independent, orthogonal for the pairing of `qr:hilbert`, and together span
the complex-valued tables: `Σ_ρ d_ρ² = |G|`. Every left and right write carries each block into
itself. -/
@[book "thm:mt-blocks"]
theorem mtBlocks : Statement.mtBlocks := by
  intro G _ _
  refine ⟨exists_complete_family, fun ι _ d ρ hirr hdist hcomplete => ?_⟩
  classical
  have horth := block_orthogonal ρ hirr hdist
  have hind := iSupIndep_of_orthogonal _ horth
  have htop := iSup_block_eq_top ρ hcomplete
  refine ⟨hind, horth, htop, ?_, fun i h ψ hψ => ?_⟩
  · rw [finrank_eq_sum_of_iSupIndep _ hind htop]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hirr i
    rw [finrank_block, Module.finrank_fin_fun]
  · obtain ⟨A, rfl⟩ := mem_block.mp hψ
    rw [leftWrite_blockTable, rightWrite_blockTable]
    exact ⟨blockTable_mem_block _ _, blockTable_mem_block _ _⟩

namespace Blocks

section Convolution

variable {G : Type*} [Group G] [Fintype G]

theorem convolution_mulVec_apply (f ψ : G → ℂ) (V : G) :
    (convolution f *ᵥ ψ) V = ∑ U, f (V * U⁻¹) * ψ U := by
  simp [convolution, Matrix.mulVec, dotProduct]

theorem sum_conv_eq_sum_leftWrite (f ψ : G → ℂ) (V : G) :
    ∑ U, f (V * U⁻¹) * ψ U = ∑ h, f h * leftWrite h ψ V := by
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft V)) _ _ fun U => ?_
  simp [mul_assoc]

omit [Fintype G] in
theorem rightWrite_single [DecidableEq G] (h W : G) :
    rightWrite h (Pi.single W (1 : ℂ)) = Pi.single (W * h⁻¹) 1 := by
  funext U
  simp only [rightWrite_apply, Pi.single_apply, eq_mul_inv_iff_mul_eq]

omit [Fintype G] in
theorem leftWrite_single [DecidableEq G] (h W : G) :
    leftWrite h (Pi.single W (1 : ℂ)) = Pi.single (h * W) 1 := by
  funext U
  simp only [leftWrite_apply, Pi.single_apply, inv_mul_eq_iff_eq_mul]

theorem commute_iff_convolution (B : Matrix G G ℂ) :
    ((∀ (h : G) (ψ : G → ℂ), B *ᵥ leftWrite h ψ = leftWrite h (B *ᵥ ψ)) ∧
      (∀ (h : G) (ψ : G → ℂ), B *ᵥ rightWrite h ψ = rightWrite h (B *ᵥ ψ))) ↔
    ∃ f : G → ℂ, IsClassFunction f ∧ B = convolution f := by
  classical
  constructor
  · rintro ⟨hL, hR⟩
    have hR' : ∀ h V W, B V (W * h⁻¹) = B (V * h) W := by
      intro h V W
      have := congrFun (hR h (Pi.single W 1)) V
      simpa [rightWrite_single, Matrix.mulVec_single_one] using this
    have hL' : ∀ h V W, B V (h * W) = B (h⁻¹ * V) W := by
      intro h V W
      have := congrFun (hL h (Pi.single W 1)) V
      simpa [leftWrite_single, Matrix.mulVec_single_one] using this
    have hB : ∀ X U, B X U = B (X * U⁻¹) 1 := by
      intro X U
      have := hR' U (X * U⁻¹) U
      rw [mul_inv_cancel, inv_mul_cancel_right] at this
      exact this.symm
    refine ⟨fun X => B X 1, fun h U => ?_, ?_⟩
    · have := hL' h (h * U) 1
      rw [mul_one, inv_mul_cancel_left, hB] at this
      simpa using this
    · ext X U
      simp [convolution, hB X U]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun h ψ => ?_, fun h ψ => ?_⟩
    · funext V
      simp only [convolution_mulVec_apply, leftWrite_apply]
      refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun U => ?_
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
      congr 1
      rw [← hf h⁻¹ (V * U⁻¹), inv_inv]
      congr 1
      group
    · funext V
      simp only [convolution_mulVec_apply, rightWrite_apply]
      refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun U => ?_
      simp only [Equiv.coe_mulRight, mul_inv_rev]
      congr 2
      group

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Convolution by a class function acts on the block of an irreducible representation as the
scalar `(1/d) Σ_U f(U) conj χ(U)`. -/
theorem convolution_mulVec_block (ρ : Representation ℂ G V) [ρ.IsIrreducible] {f : G → ℂ}
    (hf : IsClassFunction f) {ψ : G → ℂ} (hψ : ψ ∈ block ρ) :
    convolution f *ᵥ ψ =
      ((Module.finrank ℂ V : ℂ)⁻¹ * ∑ U, f U * conj (ρ.character U)) • ψ := by
  obtain ⟨A, rfl⟩ := mem_block.mp hψ
  let T : Module.End ℂ V := ∑ W, f W • ρ W⁻¹
  have hT : ∀ h, T ∘ₗ ρ h = ρ h ∘ₗ T := by
    intro h
    ext v
    simp only [T, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul]
    refine Fintype.sum_equiv ((MulAut.conj h⁻¹).toEquiv) _ _ fun W => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    have hfW := hf h⁻¹ W
    rw [inv_inv] at hfW
    rw [hfW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (ρ h), ← map_mul]
    congr 3
    group
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 ⟨T, hT⟩
  have hTc : T = c • LinearMap.id := by
    have := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Representation.IntertwiningMap.algebraMap_apply] at this
    exact this.symm
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  have htr : LinearMap.trace ℂ V T = ∑ U, f U * conj (ρ.character U) := by
    simp only [T, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [← character_inv']
    rfl
  have hc' : c = (Module.finrank ℂ V : ℂ)⁻¹ * ∑ U, f U * conj (ρ.character U) := by
    rw [← htr, hTc, map_smul, LinearMap.trace_id, smul_eq_mul]
    field_simp
  funext X
  rw [convolution_mulVec_apply, ← hc', Pi.smul_apply, smul_eq_mul]
  have : ∑ U, f (X * U⁻¹) * blockTable ρ A U = LinearMap.trace ℂ V (A * T * ρ X) := by
    simp only [T, Finset.mul_sum, Finset.sum_mul, map_sum, blockTable]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft X)) _ _ fun U => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, mul_inv_rev, inv_inv,
      mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 2
    rw [mul_assoc, ← map_mul]
    group
  rw [this, hTc, ← Module.End.one_eq_id, mul_smul_comm, mul_one, smul_mul_assoc, map_smul,
    smul_eq_mul]
  rfl

end Convolution


section Unitary

variable {B : Type*} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
theorem coeffPairing_mulVec (C : Matrix B B ℂ) (φ ψ : B → ℂ) :
    coeffPairing (C *ᵥ φ) (C *ᵥ ψ) = coeffPairing φ ((star C * C) *ᵥ ψ) := by
  rw [coeffPairing_eq_dotProduct, coeffPairing_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose]

theorem coeffPairing_single_left (V : B) (ψ : B → ℂ) :
    coeffPairing (Pi.single V 1) ψ = ψ V := by
  rw [coeffPairing, Finset.sum_eq_single V]
  · simp
  · intro U _ hU
    simp [hU]
  · simp

/-- A matrix is unitary exactly when it keeps the pairing. -/
theorem mem_unitaryGroup_iff_pairing (C : Matrix B B ℂ) :
    C ∈ Matrix.unitaryGroup B ℂ ↔
      ∀ φ ψ, coeffPairing (C *ᵥ φ) (C *ᵥ ψ) = coeffPairing φ ψ := by
  rw [Matrix.mem_unitaryGroup_iff']
  constructor
  · intro h φ ψ
    rw [coeffPairing_mulVec, h, Matrix.one_mulVec]
  · intro h
    ext V W
    have := h (Pi.single V 1) (Pi.single W 1)
    rw [coeffPairing_mulVec, coeffPairing_single_left, coeffPairing_single_left,
      Matrix.mulVec_single_one] at this
    rw [Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using this

/-- An operator that is a scalar on each subspace of an orthogonal family spanning the tables
is unitary exactly when each scalar has size one. -/
theorem mem_unitaryGroup_iff_of_blocks {ι : Type*} (t : ι → Submodule ℂ (B → ℂ))
    (horth : ∀ i j, i ≠ j → ∀ φ ∈ t i, ∀ ψ ∈ t j, coeffPairing φ ψ = 0)
    (htop : ⨆ i, t i = ⊤) (hne : ∀ i, t i ≠ ⊥) (C : Matrix B B ℂ) (r : ι → ℂ)
    (hC : ∀ i, ∀ ψ ∈ t i, C *ᵥ ψ = r i • ψ) :
    C ∈ Matrix.unitaryGroup B ℂ ↔ ∀ i, ‖r i‖ = 1 := by
  rw [mem_unitaryGroup_iff_pairing]
  have hnorm : ∀ i, conj (r i) * r i = 1 ↔ ‖r i‖ = 1 := by
    intro i
    rw [Complex.conj_mul']
    constructor
    · intro h
      have h' : ‖r i‖ ^ 2 = 1 := by exact_mod_cast h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h'
    · intro h
      rw [h]
      simp
  constructor
  · intro h i
    rw [← hnorm]
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
    have := h ψ ψ
    rw [hC i ψ hψ, coeffPairing_smul_left, coeffPairing_smul_right, ← mul_assoc] at this
    have hpp : coeffPairing ψ ψ ≠ 0 := fun h0 => hψ0 (coeffPairing_self_eq_zero.mp h0)
    exact mul_right_cancel₀ hpp (this.trans (one_mul _).symm)
  · intro h
    have hall : ∀ φ ψ, φ ∈ ⨆ i, t i → ψ ∈ ⨆ i, t i →
        coeffPairing (C *ᵥ φ) (C *ᵥ ψ) = coeffPairing φ ψ := by
      intro φ ψ hφ hψ
      refine Submodule.iSup_induction t
        (motive := fun φ => coeffPairing (C *ᵥ φ) (C *ᵥ ψ) = coeffPairing φ ψ) hφ ?_ ?_ ?_
      · intro i φ hφi
        refine Submodule.iSup_induction t
          (motive := fun ψ => coeffPairing (C *ᵥ φ) (C *ᵥ ψ) = coeffPairing φ ψ) hψ ?_ ?_ ?_
        · intro j ψ hψj
          rw [hC i φ hφi, hC j ψ hψj, coeffPairing_smul_left, coeffPairing_smul_right]
          by_cases hij : i = j
          · subst hij
            rw [← mul_assoc, (hnorm i).mpr (h i), one_mul]
          · rw [horth i j hij φ hφi ψ hψj, mul_zero, mul_zero]
        · rw [Matrix.mulVec_zero, coeffPairing_zero_right, coeffPairing_zero_right]
        · intro ψ ψ' h1 h2
          rw [Matrix.mulVec_add, coeffPairing_add_right, coeffPairing_add_right, h1, h2]
      · rw [Matrix.mulVec_zero, coeffPairing_zero_left, coeffPairing_zero_left]
      · intro φ φ' h1 h2
        rw [Matrix.mulVec_add, coeffPairing_add_left, coeffPairing_add_left, h1, h2]
    intro φ ψ
    exact hall φ ψ (htop ▸ Submodule.mem_top) (htop ▸ Submodule.mem_top)

end Unitary

section Characters

variable {G : Type*} [Group G] [Fintype G]

/-- Orthogonality of the characters of a family of distinct irreducible representations. -/
theorem sum_char_mul_conj_char {ι : Type*} {d : ι → ℕ}
    (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (hirr : ∀ i, (ρ i).IsIrreducible)
    (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) (i j : ι) [Decidable (i = j)] :
    ∑ U, (ρ i).character U * conj ((ρ j).character U) =
      if i = j then (Fintype.card G : ℂ) else 0 := by
  have := hirr i
  have := hirr j
  have hconj : ∀ U, conj ((ρ j).character U) = LinearMap.trace ℂ _ (1 * (ρ j) U⁻¹) := by
    intro U
    rw [one_mul, ← character_inv']
    rfl
  simp_rw [hconj, mul_comm ((ρ i).character _)]
  have hchar : ∀ U, (ρ i).character U = LinearMap.trace ℂ _ (1 * (ρ i) U) := by
    intro U
    rw [one_mul]
    rfl
  simp_rw [hchar]
  split_ifs with hij
  · subst hij
    rw [sum_trace_self, one_mul, LinearMap.trace_one, Module.finrank_fin_fun]
    have hd : (d i : ℂ) ≠ 0 := by
      have := finrank_pos_of_isIrreducible (ρ i)
      rw [Module.finrank_fin_fun] at this
      exact_mod_cast this.ne'
    field_simp
  · exact sum_trace_eq_zero (ρ j) (ρ i) (fun ⟨e⟩ => hij (hdist i j ⟨e.symm⟩)) 1 1

omit [Fintype G] in
theorem isClassFunction_character {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : IsClassFunction ρ.character := fun h U =>
  Representation.char_conj ρ U h

end Characters


section Expansion

variable {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- The class function `(1/|G|) Σ_i r_i d_i χ_i`. -/
noncomputable def charComb (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) :
    G → ℂ :=
  fun U => (Fintype.card G : ℂ)⁻¹ * ∑ i, r i * d i * (ρ i).character U

theorem isClassFunction_charComb (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) :
    IsClassFunction (charComb ρ r) := by
  intro h U
  simp [charComb, Representation.char_conj]

theorem hat_charComb (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hirr : ∀ i, (ρ i).IsIrreducible) (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
    (r : ι → ℂ) (j : ι) :
    (d j : ℂ)⁻¹ * ∑ U, charComb ρ r U * conj ((ρ j).character U) = r j := by
  classical
  have h1 : ∀ U, charComb ρ r U * conj ((ρ j).character U) =
      ∑ i, (Fintype.card G : ℂ)⁻¹ * (r i * d i) *
        ((ρ i).character U * conj ((ρ j).character U)) := by
    intro U
    simp only [charComb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl fun U _ => h1 U, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_char_mul_conj_char ρ hirr hdist]
  have := hirr j
  have hd : (d j : ℂ) ≠ 0 := by
    have := finrank_pos_of_isIrreducible (ρ j)
    rw [Module.finrank_fin_fun] at this
    exact_mod_cast this.ne'
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp

theorem convolution_charComb (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hirr : ∀ i, (ρ i).IsIrreducible) (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
    (r : ι → ℂ) (j : ι) {ψ : G → ℂ} (hψ : ψ ∈ block (ρ j)) :
    convolution (charComb ρ r) *ᵥ ψ = r j • ψ := by
  have := hirr j
  rw [convolution_mulVec_block (ρ j) (isClassFunction_charComb ρ r) hψ, Module.finrank_fin_fun,
    hat_charComb ρ hirr hdist]

theorem convolution_mulVec_single_one [DecidableEq G] (f : G → ℂ) :
    convolution f *ᵥ Pi.single 1 1 = f := by
  rw [Matrix.mulVec_single_one]
  funext V
  simp [convolution]

/-- Every class function is `(1/|G|) Σ_i r_i d_i χ_i` for some `r`. -/
theorem exists_eq_charComb (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (hirr : ∀ i, (ρ i).IsIrreducible) (hdist : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
    (hcomplete : ∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
      ∃ i, Nonempty (σ.Equiv (ρ i)))
    {f : G → ℂ} (hf : IsClassFunction f) : ∃ r : ι → ℂ, f = charComb ρ r := by
  classical
  let r : ι → ℂ := fun i => (d i : ℂ)⁻¹ * ∑ U, f U * conj ((ρ i).character U)
  refine ⟨r, ?_⟩
  have hblock : ∀ i, ∀ ψ ∈ block (ρ i),
      convolution f *ᵥ ψ = convolution (charComb ρ r) *ᵥ ψ := by
    intro i ψ hψ
    have := hirr i
    rw [convolution_charComb ρ hirr hdist r i hψ, convolution_mulVec_block (ρ i) hf hψ,
      Module.finrank_fin_fun]
  have hall : ∀ ψ ∈ ⨆ i, block (ρ i),
      convolution f *ᵥ ψ = convolution (charComb ρ r) *ᵥ ψ := by
    intro ψ hψ
    refine Submodule.iSup_induction _
      (motive := fun ψ => convolution f *ᵥ ψ = convolution (charComb ρ r) *ᵥ ψ) hψ hblock ?_ ?_
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
    · intro ψ ψ' h1 h2
      rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2]
  have := hall (Pi.single 1 1) (iSup_block_eq_top ρ hcomplete ▸ Submodule.mem_top)
  rwa [convolution_mulVec_single_one, convolution_mulVec_single_one] at this

end Expansion

end Blocks

open Blocks in
/-- **Theorem 11.6** (one-edge operators). A matrix on the table space commutes with all left
and right writes if and only if it is convolution by a class function `f`,
`(f * ψ)(V) = Σ_{U ∈ G} f(V U⁻¹) ψ(U) = Σ_{h ∈ G} f(h) (L_h ψ)(V)`. Convolution by `f` acts on
the block `B_ρ` as the scalar `f̂(ρ) = (1/d_ρ) Σ_U f(U) conj(χ_ρ(U))`. Writing
`f = (1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ`, the scalar on `B_ρ` is `r(ρ)`, so the operator is unitary
exactly when every `r(ρ)` is a unit phase. -/
@[book "thm:mt-convolution"]
theorem mtConvolution : Statement.mtConvolution := by
  intro G _ _ _
  refine ⟨commute_iff_convolution, fun f ψ V =>
    ⟨convolution_mulVec_apply f ψ V, sum_conv_eq_sum_leftWrite f ψ V⟩, ?_, ?_⟩
  · intro d ρ hρ f hf ψ hψ
    have := hρ
    rw [convolution_mulVec_block ρ hf hψ, Module.finrank_fin_fun]
  · intro ι _ d ρ hirr hdist hcomplete
    refine ⟨fun f hf => exists_eq_charComb ρ hirr hdist hcomplete hf, fun r => ?_⟩
    have hscalar : ∀ i, ∀ ψ ∈ block (ρ i), convolution (charComb ρ r) *ᵥ ψ = r i • ψ :=
      fun i _ hψ => convolution_charComb ρ hirr hdist r i hψ
    refine ⟨hscalar, ?_⟩
    exact mem_unitaryGroup_iff_of_blocks (fun i => block (ρ i)) (block_orthogonal ρ hirr hdist)
      (iSup_block_eq_top ρ hcomplete) (fun i => by have := hirr i; exact block_ne_bot (ρ i))
      _ r hscalar

/-! ## Non-vacuity -/

section NonVacuity

open Blocks

/-- Theorem 11.4 on the book's link over `S₃`: a choice of its distinct irreducible
representations exists, so the hypotheses can be met, and their blocks fill the six cells,
`Σ d² = 6`. -/
example : ∃ (n : ℕ) (d : Fin n → ℕ)
    (ρ : ∀ i, Representation ℂ (Equiv.Perm (Fin 3)) (Fin (d i) → ℂ)),
    (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) ∧
    (∀ (d' : ℕ) (σ : Representation ℂ (Equiv.Perm (Fin 3)) (Fin d' → ℂ)), σ.IsIrreducible →
      ∃ i, Nonempty (σ.Equiv (ρ i))) ∧ ∑ i, d i ^ 2 = 6 := by
  obtain ⟨n, d, ρ, h1, h2, h3⟩ := (mtBlocks (Equiv.Perm (Fin 3))).1
  refine ⟨n, d, ρ, h1, h2, h3, ?_⟩
  rw [((mtBlocks (Equiv.Perm (Fin 3))).2 (Fin n) d ρ h1 h2 h3).2.2.2.1, Fintype.card_perm,
    Fintype.card_fin]
  rfl

/-- Theorem 11.6 on the link over `S₃`: the hypotheses of its last two parts can be met. Some
irreducible representation exists, its character is a class function, and the response `1` on
every block gives a unitary convolution. -/
example : (∃ (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Fin 3)) (Fin d → ℂ)),
      ρ.IsIrreducible ∧ IsClassFunction ρ.character) ∧
    ∃ (n : ℕ) (d : Fin n → ℕ)
      (ρ : ∀ i, Representation ℂ (Equiv.Perm (Fin 3)) (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) ∧
      (∀ (d' : ℕ) (σ : Representation ℂ (Equiv.Perm (Fin 3)) (Fin d' → ℂ)),
        σ.IsIrreducible → ∃ i, Nonempty (σ.Equiv (ρ i))) ∧
      convolution (fun U => (Fintype.card (Equiv.Perm (Fin 3)) : ℂ)⁻¹ *
        ∑ i, 1 * d i * (ρ i).character U) ∈ Matrix.unitaryGroup (Equiv.Perm (Fin 3)) ℂ := by
  obtain ⟨n, d, ρ, h1, h2, h3⟩ := (mtBlocks (Equiv.Perm (Fin 3))).1
  have hn : n ≠ 0 := by
    rintro rfl
    have := ((mtBlocks (Equiv.Perm (Fin 3))).2 (Fin 0) d ρ h1 h2 h3).2.2.2.1
    rw [Fintype.card_perm, Fintype.card_fin] at this
    simp [Nat.factorial] at this
  refine ⟨⟨d ⟨0, Nat.pos_of_ne_zero hn⟩, ρ _, h1 _, isClassFunction_character _⟩,
    n, d, ρ, h1, h2, h3, ?_⟩
  exact ((((mtConvolution (Equiv.Perm (Fin 3))).2.2.2 (Fin n) d ρ h1 h2 h3).2
    (fun _ => 1)).2).mpr fun _ => by simp

end NonVacuity

end Artform
