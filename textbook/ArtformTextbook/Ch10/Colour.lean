import Mathlib.RingTheory.RootsOfUnity.Complex
import ArtformTextbook.Ch10.Statements.Colour
import ArtformTextbook.Exact.ZOmegaPhi

/-!
# Colour and triality (Propositions 10.1 and 10.2)

`(g ⊗ g ⊗ g) ε = det(g) ε` is the book's computation: expanding each factor `g e_{σ(i)}`
gives the sum over all index triples `f` of `(Σ_σ sgn σ Π_i g_{f(i) σ(i)}) e_f`; the bracket is
the determinant of the rows `f(1), f(2), f(3)` of `g`, which vanishes unless `f` is a
permutation `τ`, and is then `sgn(τ) det g`.

The centre of `SU(3)` is found as in the book: a central matrix commutes with the diagonal
matrix `diag(1, ω, ω²)`, whose entries are distinct, so it is diagonal; it commutes with the
cyclic permutation of the coordinates, so its diagonal entries agree.
-/

namespace Artform

open scoped TensorProduct

namespace Colour

/-! ## The state `ε` -/

theorem toLin'_e (g : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) :
    Matrix.toLin' g (e a) = ∑ b, g b a • e b := by
  ext c
  simp [e, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

theorem tensorCube_tprod (g : Matrix (Fin 3) (Fin 3) ℂ) (s : Fin 3 → Fin 3) :
    tensorCube g (⨂ₜ[ℂ] i, e (s i)) =
      ∑ f : Fin 3 → Fin 3, (∏ i, g (f i) (s i)) • ⨂ₜ[ℂ] i, e (f i) := by
  rw [tensorCube, PiTensorProduct.map_tprod]
  simp_rw [toLin'_e]
  rw [MultilinearMap.map_sum]
  simp_rw [MultilinearMap.map_smul_univ]

/-- The bracket of the book's proof: `Σ_σ sgn σ Π_i g_{f(i) σ(i)}` is the determinant of the
matrix whose rows are the rows `f(1), f(2), f(3)` of `g`. -/
theorem sum_sign_prod (g : Matrix (Fin 3) (Fin 3) ℂ) (f : Fin 3 → Fin 3) :
    ∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g (f i) (σ i) =
      (g.submatrix f id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp

theorem tensorCube_epsilon (g : Matrix (Fin 3) (Fin 3) ℂ) :
    tensorCube g epsilon = g.det • epsilon := by
  classical
  rw [epsilon, map_sum]
  simp_rw [map_smul, tensorCube_tprod, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_sign_prod]
  -- Only the injective `f`, which are the permutations, contribute.
  let φ : Equiv.Perm (Fin 3) ↪ (Fin 3 → Fin 3) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map φ))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [φ, Function.Embedding.coeFn_mk]
    rw [Matrix.det_permute, mul_comm]
  · intro f _ hf
    have hinj : ¬ Function.Injective f := by
      intro hi
      apply hf
      rw [Finset.mem_map]
      exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hi), Finset.mem_univ _, rfl⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa [Function.Injective] using hinj
    rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]), zero_smul]

/-- The coefficient of `e₁ ⊗ e₂ ⊗ e₃`, a linear functional on `V ⊗ V ⊗ V`. -/
noncomputable def coeff123 : ⨂[ℂ]^3 (Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compLinearMap
    fun i => LinearMap.proj i)

theorem coeff123_epsilon : coeff123 epsilon = 1 := by
  rw [epsilon, map_sum, Fintype.sum_eq_single 1]
  · simp [coeff123, e]
  · intro σ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hσ (Equiv.ext h)
    rw [map_smul, coeff123, PiTensorProduct.lift.tprod]
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.proj_apply, e]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi.symm]),
      smul_zero]

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  intro h
  have := coeff123_epsilon
  rw [h, map_zero] at this
  exact zero_ne_one this

/-! ## Contraction with `ε` -/

theorem contraction_eq_det (w : Fin 3 → Fin 3 → ℂ) :
    contraction w = (Matrix.of fun a i => w i a).det := by
  rw [Matrix.det_apply]
  simp [contraction, Units.smul_def, zsmul_eq_mul]

theorem contraction_smul (g : Matrix (Fin 3) (Fin 3) ℂ) (w : Fin 3 → Fin 3 → ℂ) :
    contraction (fun k => Matrix.toLin' g (w k)) = g.det * contraction w := by
  rw [contraction_eq_det, contraction_eq_det, ← Matrix.det_mul]
  rfl

theorem contraction_e : contraction (fun k => e k) = 1 := by
  rw [contraction_eq_det]
  have : (Matrix.of fun a i => e i a) = 1 := by
    ext a i
    simp [e, Matrix.one_apply, Pi.single_apply]
  rw [this, Matrix.det_one]

/-! ## `ω` -/

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem omega_pow_three : omega ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_zero : omega ≠ 0 := omega_isPrimitiveRoot.ne_zero (by norm_num)

theorem star_omega : star omega = omega⁻¹ := by
  have h : ‖omega‖ = 1 := omega_isPrimitiveRoot.norm'_eq_one (by norm_num)
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

theorem star_mul_self_of_pow_three {c : ℂ} (hc : c ^ 3 = 1) : star c * c = 1 := by
  have h : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc (by norm_num)
  rw [RCLike.star_def, Complex.conj_mul', h]
  simp

/-! ## The centre of `SU(3)` -/

theorem scalar_mem {c : ℂ} (hc : c ^ 3 = 1) :
    c • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, by simp [hc]⟩
  rw [star_smul, star_one, smul_mul_smul_comm, mul_one, star_mul_self_of_pow_three hc, one_smul]

/-- The diagonal matrix `diag(1, ω, ω²)`. -/
noncomputable def diag1ww : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, omega, omega ^ 2]

/-- The cyclic permutation of the coordinates, `e₁ ↦ e₂ ↦ e₃ ↦ e₁`. -/
def cyc : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem diag1ww_mem : diag1ww ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  have h1 : (starRingEnd ℂ) omega * omega = 1 := star_mul_self_of_pow_three omega_pow_three
  refine ⟨?_, ?_⟩
  · rw [diag1ww, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [h1, star_pow, ← mul_pow]
  · rw [diag1ww, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [← pow_succ', omega_pow_three]

theorem cyc_mem : cyc ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose]
  · simp [cyc, Matrix.det_fin_three]

/-- Chapter 10's `ω` is the `ω` of the exact arithmetic, `e^{2πi/3}`, by
definition. -/
theorem omega_eq_exact : omega = Exact.omega := rfl

theorem omega_ne_one : omega ≠ 1 :=
  omega_isPrimitiveRoot.ne_one (by norm_num)

theorem omega_sq_ne_one : omega ^ 2 ≠ 1 :=
  omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

theorem omega_ne_omega_sq : omega ≠ omega ^ 2 := by
  intro h
  apply omega_ne_one
  have : omega * 1 = omega * omega := by rw [mul_one, ← sq]; exact h
  exact (mul_left_cancel₀ omega_ne_zero this).symm

/-- A matrix commuting with `diag(1, ω, ω²)` and with the cyclic permutation is scalar. -/
theorem eq_smul_one_of_commute {M : Matrix (Fin 3) (Fin 3) ℂ} (hD : diag1ww * M = M * diag1ww)
    (hP : cyc * M = M * cyc) : M = M 0 0 • 1 := by
  have hd : ∀ i j, (![1, omega, omega ^ 2] i - ![1, omega, omega ^ 2] j) * M i j = 0 := by
    intro i j
    have := congrFun (congrFun hD i) j
    rw [diag1ww, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    rw [sub_mul, this, mul_comm, sub_self]
  have hc : ∀ i j, (cyc * M) i j = (M * cyc) i j := fun i j => by rw [hP]
  have hdist : ∀ i j : Fin 3, i ≠ j → ![1, omega, omega ^ 2] i ≠ ![1, omega, omega ^ 2] j := by
    have h01 : (1 : ℂ) ≠ omega := omega_ne_one.symm
    have h02 : (1 : ℂ) ≠ omega ^ 2 := omega_sq_ne_one.symm
    have h12 : omega ≠ omega ^ 2 := omega_ne_omega_sq
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [h01, h02, h12, h01.symm, h02.symm, h12.symm] at hij ⊢
  have off : ∀ i j, i ≠ j → M i j = 0 := fun i j hij =>
    (mul_eq_zero.mp (hd i j)).resolve_left (sub_ne_zero.mpr (hdist i j hij))
  have h00 : M 0 0 = M 1 1 := by
    simpa [cyc, Matrix.mul_apply, Fin.sum_univ_three] using hc 1 0
  have h11 : M 1 1 = M 2 2 := by
    simpa [cyc, Matrix.mul_apply, Fin.sum_univ_three] using hc 2 1
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [h00, h11]
  · rw [off i j hij]
    simp [hij]

theorem mem_center_iff (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (∃ g ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin 3) ℂ),
        (g : Matrix (Fin 3) (Fin 3) ℂ) = M) ↔
      M = 1 ∨ M = omega • 1 ∨ M = omega ^ 2 • 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_center_iff] at hg
    have hD := congrArg Subtype.val (hg ⟨diag1ww, diag1ww_mem⟩)
    have hP := congrArg Subtype.val (hg ⟨cyc, cyc_mem⟩)
    simp only [Submonoid.coe_mul] at hD hP
    have hM := eq_smul_one_of_commute hD hP
    have hdet : (g : Matrix (Fin 3) (Fin 3) ℂ).det = 1 :=
      (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
    rw [hM, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    obtain ⟨i, hi, hi'⟩ := omega_isPrimitiveRoot.eq_pow_of_pow_eq_one hdet
    rw [hM, ← hi']
    interval_cases i <;> simp
  · intro h
    have hc : ∃ c : ℂ, c ^ 3 = 1 ∧ M = c • 1 := by
      rcases h with h | h | h
      · exact ⟨1, by simp, by simp [h]⟩
      · exact ⟨omega, omega_pow_three, h⟩
      · exact ⟨omega ^ 2, by rw [← pow_mul, mul_comm, pow_mul, omega_pow_three, one_pow], h⟩
    obtain ⟨c, hc3, rfl⟩ := hc
    refine ⟨⟨c • 1, scalar_mem hc3⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

/-! ## `ωI` on quarks and antiquarks -/

theorem piTensor_map_smul_id (n : ℕ) (c : ℂ) :
    (PiTensorProduct.map fun _ : Fin n => c • (LinearMap.id : (Fin 3 → ℂ) →ₗ[ℂ] _)) =
      c ^ n • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp [PiTensorProduct.map_tprod, MultilinearMap.map_smul_univ]

theorem act_smul_one (q qbar : ℕ) (c : ℂ) :
    act q qbar (c • 1) = (c ^ q * star c ^ qbar) • LinearMap.id := by
  have h1 : Matrix.toLin' (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = c • LinearMap.id := by
    rw [map_smul, Matrix.toLin'_one]
  have h2 : (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)).map (starRingEnd ℂ) = star c • 1 := by
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  rw [act, h2, h1, map_smul, Matrix.toLin'_one, piTensor_map_smul_id, piTensor_map_smul_id,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, TensorProduct.map_id, smul_smul]

theorem act_omega (q qbar : ℕ) (x : QuarkStates q qbar) :
    act q qbar (omega • 1) x = omega ^ ((q : ℤ) - qbar) • x := by
  rw [act_smul_one, LinearMap.smul_apply, LinearMap.id_apply, star_omega,
    zpow_sub₀ omega_ne_zero, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

end Colour

/-- **Proposition 10.1** (the colourless three-quark state). Let `g ∈ GL(3, ℂ)` act on
`V ⊗ V ⊗ V` by `g ⊗ g ⊗ g`. Then `(g ⊗ g ⊗ g) ε = det(g) ε`. Hence `ε` is fixed by `g` if and
only if `det g = 1`, and contraction with `ε` is an intertwiner in the sense of
Definition 5.31 for a group `G ≤ GL(3, ℂ)` exactly when `G ≤ SL(3, ℂ)`. -/
@[book "prop:mp-epsilon"]
theorem mpEpsilon : Statement.mpEpsilon := by
  refine ⟨fun g => Colour.tensorCube_epsilon g, fun g => ?_, fun G => ?_⟩
  · rw [Colour.tensorCube_epsilon]
    constructor
    · intro h
      have h' : ((g : Matrix (Fin 3) (Fin 3) ℂ).det - 1) • Colour.epsilon = 0 := by
        rw [sub_smul, h, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right Colour.epsilon_ne_zero)
    · intro h
      rw [h, one_smul]
  · have hrange : ∀ g : GL (Fin 3) ℂ, g ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) ℂ →* GL (Fin 3) ℂ).range ↔
          (g : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := by
      intro g
      constructor
      · rintro ⟨A, rfl⟩
        exact A.2
      · intro h
        exact ⟨⟨g, h⟩, Units.ext rfl⟩
    constructor
    · intro hι g hg
      rw [hrange]
      have := hι ⟨g, hg⟩ fun k => Colour.e k
      simp only [Colour.triplet, MonoidHom.coe_mk, OneHom.coe_mk] at this
      rw [Colour.contraction_smul, Colour.contraction_e, mul_one] at this
      exact this
    · intro hG g w
      simp only [Colour.triplet, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Colour.contraction_smul, (hrange _).mp (hG g.2), one_mul]

/-- **Proposition 10.2** (triality). The centre of `SU(3)` is `{I, ωI, ω²I}` with
`ω = e^{2πi/3}`. On a state of `q` quarks and `q̄` antiquarks the element `ωI` acts as
multiplication by `ω^{q - q̄}`. A colourless state therefore has `q - q̄ ≡ 0 (mod 3)`. -/
@[book "prop:mp-triality"]
theorem mpTriality : Statement.mpTriality := by
  refine ⟨Colour.mem_center_iff, Colour.act_omega, fun q qbar x hx hfix => ?_⟩
  have h := hfix _ (Colour.scalar_mem Colour.omega_pow_three)
  rw [Colour.act_omega] at h
  have h' : (Colour.omega ^ ((q : ℤ) - qbar) - 1) • x = 0 := by
    rw [sub_smul, h, one_smul, sub_self]
  have h1 : Colour.omega ^ ((q : ℤ) - qbar) = 1 :=
    sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hx)
  rw [Int.modEq_zero_iff_dvd]
  exact_mod_cast (Colour.omega_isPrimitiveRoot.zpow_eq_one_iff_dvd _).mp h1

/-! ## Non-vacuity -/

section NonVacuity

open Colour

/-- The scalar matrix `ωI` as an element of `GL(3, ℂ)`. -/
noncomputable def Colour.omegaGL : GL (Fin 3) ℂ :=
  ⟨omega • 1, omega⁻¹ • 1, by simp [smul_smul, omega_ne_zero],
    by simp [smul_smul, omega_ne_zero]⟩

/-- Proposition 10.1 on the book's example `ωI`, of determinant one: it fixes `ε`, and
contraction with `ε` is an intertwiner for the group it generates, the centre of `SU(3)`. -/
example : tensorCube (omegaGL : Matrix (Fin 3) (Fin 3) ℂ) epsilon = epsilon ∧
    IsIntertwiner (fun _ : Fin 3 => triplet (Subgroup.zpowers omegaGL)) contraction := by
  have hdet : (omegaGL : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := by
    simp [omegaGL, omega_pow_three]
  refine ⟨(mpEpsilon.2.1 omegaGL).mpr hdet, (mpEpsilon.2.2 _).mpr ?_⟩
  rw [Subgroup.zpowers_le]
  exact ⟨⟨omega • 1, by simp [omega_pow_three]⟩, Units.ext rfl⟩

/-- The empty tensor, the unit of `V̄^{⊗0} = ℂ`. -/
noncomputable def Colour.emptyTensor : ⨂[ℂ]^0 (Fin 3 → ℂ) := ⨂ₜ[ℂ] i, Fin.elim0 i

/-- Proposition 10.2 on the baryon: `ε` is a nonzero state of three quarks and no antiquark
fixed by every element of `SU(3)`, so the hypotheses of the last part can be met. -/
example : (epsilon ⊗ₜ[ℂ] emptyTensor : QuarkStates 3 0) ≠ 0 ∧
    ∀ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
      act 3 0 g (epsilon ⊗ₜ[ℂ] emptyTensor) = epsilon ⊗ₜ[ℂ] emptyTensor := by
  constructor
  · intro h
    have := congrArg (TensorProduct.lid ℂ ℂ ∘ TensorProduct.map coeff123
      (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap) h
    simp [emptyTensor, coeff123_epsilon, PiTensorProduct.isEmptyEquiv_apply_tprod] at this
  · intro g hg
    have hdet : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hg).2
    have h0 : (PiTensorProduct.map fun _ : Fin 0 =>
        Matrix.toLin' (g.map (starRingEnd ℂ))) emptyTensor = emptyTensor := by
      rw [emptyTensor, PiTensorProduct.map_tprod]
      congr 1
      ext i
      exact Fin.elim0 i
    rw [act, TensorProduct.map_tmul, h0]
    congr 1
    rw [← tensorCube, tensorCube_epsilon, hdet, one_smul]

end NonVacuity

end Artform
