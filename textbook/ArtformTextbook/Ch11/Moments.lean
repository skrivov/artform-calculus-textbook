import ArtformTextbook.Ch11.Tick

/-!
# Link moments (Proposition 11.19)

Each moment is an average over the group of a product of matrix entries, and each is read off
an invariant:
* the average of the triplet's matrices has invariant columns, and an irreducible triplet has no
  nonzero invariant vector, since its span would be a subrepresentation of dimension one
  (`Moments.eq_zero_of_invariant`);
* `Σ_U U E U⁻¹` commutes with the triplet, for any matrix `E`, so it is a scalar by Schur's lemma
  (`Blocks.schurAvg_self`); with `E` a matrix unit and `U⁻¹ = U†` this is the moment
  `Σ_U U_{ij} conj(U_{kl}) = |G| δ_{ik} δ_{jl} / 3`;
* `Σ_U U E Uᵀ` is an invariant of `3 ⊗ 3`, zero when there is none;
* `T_{ikm} = Σ_U U_{ij} U_{kl} U_{mn}`, for fixed `j, l, n`, is an invariant of `3^{⊗3}`, so a
  multiple `c_{jln} ε_{ikm}` of the invariant `ε` when it is the only one; replacing `U` by
  `U⁻¹ = U†` shows that the coefficients are `conj(c_{012}) ε_{jln}`, and contracting with `ε`,
  which every `U` of determinant one fixes, gives `6 conj(c_{012}) = 1`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

namespace Moments

/-- The action of `A ⊗ A ⊗ A` on a tensor of `3^{⊗3}`, given by its components. -/
def t3 (A : Matrix (Fin 3) (Fin 3) ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun i k m => ∑ j, ∑ l, ∑ n, A i j * A k l * A m n * T j l n

theorem t3_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    t3 A (t3 B T) = t3 (A * B) T := by
  funext i k m
  simp only [t3, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- `T ↦ (A ⊗ A ⊗ A) T` is linear. -/
def t3Lin (A : Matrix (Fin 3) (Fin 3) ℂ) :
    (Fin 3 → Fin 3 → Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → Fin 3 → Fin 3 → ℂ) where
  toFun := t3 A
  map_add' T T' := by
    funext i k m
    simp [t3, mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    funext i k m
    simp only [t3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun n _ => ?_
    ring

theorem t3_sum {G : Type*} [Fintype G] (A : Matrix (Fin 3) (Fin 3) ℂ)
    (T : G → Fin 3 → Fin 3 → Fin 3 → ℂ) : t3 A (∑ U, T U) = ∑ U, t3 A (T U) :=
  map_sum (t3Lin A) T Finset.univ

theorem t3_smul (A : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    t3 A (c • T) = c • t3 A T :=
  (t3Lin A).map_smul c T

/-- The Levi-Civita symbol with integer values. -/
def lcZ (i k m : Fin 3) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 3), if σ 0 = i ∧ σ 1 = k ∧ σ 2 = m then (Equiv.Perm.sign σ : ℤ) else 0

/-- The table of the Levi-Civita symbol. -/
def lcTab : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

theorem lcZ_eq_lcTab : ∀ i k m, lcZ i k m = lcTab i k m := by decide +kernel

theorem leviCivita_eq (i k m : Fin 3) : leviCivita i k m = (lcTab i k m : ℂ) := by
  rw [← lcZ_eq_lcTab, leviCivita, lcZ]
  push_cast
  rfl

/-- `A ⊗ A ⊗ A` multiplies `ε` by `det A`. -/
theorem t3_leviCivita (A : Matrix (Fin 3) (Fin 3) ℂ) :
    t3 A (fun i k m => leviCivita i k m) = A.det • fun i k m => leviCivita i k m := by
  funext i k m
  simp only [t3, leviCivita_eq, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases k <;> fin_cases m <;>
    simp [Fin.sum_univ_three, lcTab, Matrix.det_fin_three] <;> ring

theorem sum_leviCivita_sq :
    ∑ j, ∑ l, ∑ n, leviCivita j l n * leviCivita j l n = 6 := by
  simp only [leviCivita_eq, Fin.sum_univ_three, lcTab]
  norm_num

theorem leviCivita_012 : leviCivita 0 1 2 = 1 := by
  rw [leviCivita_eq]
  simp [lcTab]

theorem leviCivita_real (i k m : Fin 3) : conj (leviCivita i k m) = leviCivita i k m := by
  rw [leviCivita_eq, map_intCast]

theorem mul_single_mul_apply (A B : Matrix (Fin 3) (Fin 3) ℂ) (i j l k : Fin 3) :
    (A * Matrix.single j l (1 : ℂ) * B) i k = A i j * B l k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
  · simp

theorem trace_single_one (j l : Fin 3) :
    (Matrix.single j l (1 : ℂ)).trace = if j = l then 1 else 0 := by
  by_cases h : j = l
  · subst h
    rw [Matrix.trace_single_eq_same, ite_eq_left rfl]
  · rw [Matrix.trace_single_eq_of_ne j l 1 h, ite_eq_right h]

variable {G : Type*} [Group G]

theorem tripletRep_apply (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (g : G) (v : Fin 3 → ℂ) :
    Edge.tripletRep ρ g v = ρ g *ᵥ v := rfl

/-- An irreducible triplet has no nonzero invariant vector. -/
theorem eq_zero_of_invariant {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hirr : (Edge.tripletRep ρ).IsIrreducible) {v : Fin 3 → ℂ} (hv : ∀ g, ρ g *ᵥ v = v) :
    v = 0 := by
  by_contra hv0
  let W : Subrepresentation (Edge.tripletRep ρ) :=
    ⟨Submodule.span ℂ {v}, fun g w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, tripletRep_apply, hv]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)⟩
  have := hirr
  rcases eq_bot_or_eq_top W with h | h
  · have hmem : v ∈ W.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact hv0 ((Submodule.mem_bot ℂ).mp hmem)
  · have h' : Submodule.span ℂ {v} = ⊤ := congrArg Subrepresentation.toSubmodule h
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [h', finrank_top, Module.finrank_fin_fun] at h1
    norm_num at h1

variable [Fintype G]

/-- Schur's lemma for the triplet, entry by entry:
`Σ_U U_{ij} (U⁻¹)_{lk} = |G| δ_{ik} δ_{jl} / 3`. -/
theorem sum_mul_inv_apply {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hirr : (Edge.tripletRep ρ).IsIrreducible) (i j k l : Fin 3) :
    ∑ U, ρ U i j * ρ U⁻¹ l k =
      (Fintype.card G : ℂ) * (if i = k ∧ j = l then 1 else 0) / 3 := by
  have := hirr
  have h := Blocks.schurAvg_self (Edge.tripletRep ρ) (Matrix.toLin' (Matrix.single j l 1))
  have hmat : ∑ U, ρ U * Matrix.single j l 1 * ρ U⁻¹ =
      ((Fintype.card G : ℂ) * (if j = l then 1 else 0) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    apply_fun LinearMap.toMatrix' at h
    rw [Blocks.schurAvg, map_sum, Matrix.trace_toLin'_eq, trace_single_one,
      Module.finrank_fin_fun, Nat.cast_ofNat, map_smul, LinearMap.toMatrix'_id] at h
    rw [← h]
    refine Finset.sum_congr rfl fun U _ => ?_
    have hT : ∀ g, LinearMap.toMatrix' (Edge.tripletRep ρ g) = ρ g := fun g =>
      LinearMap.toMatrix'_toLin' (ρ g)
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, hT, LinearMap.toMatrix'_toLin',
      mul_assoc]
  have := congrFun (congrFun hmat i) k
  rw [Matrix.sum_apply] at this
  simp only [mul_single_mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  rw [this]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

end Moments

open Moments in
/-- **Proposition 11.19** (link moments). For an irreducible triplet of a finite subgroup of
`SU(3)`, using a real orthonormal basis when the triplet is real,
`(1/|G|) Σ_U U = 0`, `(1/|G|) Σ_U U_{ij} conj(U_{kl}) = δ_{ik} δ_{jl} / 3`,
`(1/|G|) Σ_U U_{ij} U_{kl}` is `δ_{ik} δ_{jl} / 3` if the triplet is real and `0` if `3 ⊗ 3`
has no invariant, and when `3^{⊗3}` has exactly one invariant,
`(1/|G|) Σ_U U_{ij} U_{kl} U_{mn} = ε_{ikm} ε_{jln} / 6`. -/
@[book "prop:mt-moments"]
theorem mtMoments : Statement.mtMoments := by
  intro G _ _ ρ hρ hirr
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ := fun g =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (hρ g)).1
  have hinv : ∀ U k l, ρ U⁻¹ l k = conj (ρ U k l) := by
    intro U k l
    rw [← Edge.star_eq_inv hunit, Matrix.star_apply, Complex.star_def]
  -- the second moment
  have h2 : ∀ i j k l, (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * conj (ρ U k l) =
      (if i = k ∧ j = l then 1 else 0) / 3 := by
    intro i j k l
    simp only [← hinv]
    rw [sum_mul_inv_apply hirr]
    field_simp
  refine ⟨?_, h2, fun hreal i j k l => ?_, fun hnone i j k l => ?_, fun hone => ?_⟩
  · -- the first moment
    ext i j
    have hcol : (fun i => ((Fintype.card G : ℂ)⁻¹ • ∑ U, ρ U) i j) = 0 := by
      refine eq_zero_of_invariant hirr fun g => ?_
      funext i
      have hA : ρ g * ((Fintype.card G : ℂ)⁻¹ • ∑ U, ρ U) =
          (Fintype.card G : ℂ)⁻¹ • ∑ U, ρ U := by
        rw [Matrix.mul_smul, Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun U => (map_mul ρ g U).symm
      have := congrFun (congrFun hA i) j
      rw [Matrix.mul_apply] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    exact congrFun hcol i
  · -- a real triplet
    have := h2 i j k l
    simp only [hreal] at this
    exact this
  · -- no invariant of `3 ⊗ 3`
    set Y : Matrix (Fin 3) (Fin 3) ℂ := ∑ U, ρ U * Matrix.single j l 1 * (ρ U)ᵀ with hY
    have hYinv : ∀ g, ρ g * Y * (ρ g)ᵀ = Y := by
      intro g
      rw [hY, Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun U => ?_
      simp only [Equiv.coe_mulLeft, map_mul, Matrix.transpose_mul, mul_assoc]
    have hY0 := hnone Y hYinv
    have := congrFun (congrFun hY0 i) k
    rw [hY, Matrix.sum_apply] at this
    simp only [mul_single_mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    rw [this, mul_zero]
  · -- exactly one invariant of `3^{⊗3}`
    intro i j k l m n
    set ε : Fin 3 → Fin 3 → Fin 3 → ℂ := fun i k m => leviCivita i k m with hε
    have hεinv : ∀ U, t3 (ρ U) ε = ε := by
      intro U
      rw [hε, t3_leviCivita, (Matrix.mem_specialUnitaryGroup_iff.mp (hρ U)).2, one_smul]
    have hεmem : ε ∈ Edge.tripleInvariants ρ := hεinv
    have hε0 : ε ≠ 0 := by
      intro h
      have := congrFun (congrFun (congrFun h 0) 1) 2
      rw [hε] at this
      simp only [leviCivita_012, Pi.zero_apply] at this
      exact one_ne_zero this
    -- every invariant is a multiple of `ε`
    have hmult : ∀ T ∈ Edge.tripleInvariants ρ, ∃ c : ℂ, T = c • ε := by
      intro T hT
      have hne : (⟨ε, hεmem⟩ : Edge.tripleInvariants ρ) ≠ 0 := fun h => hε0 (congrArg Subtype.val h)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hone ⟨T, hT⟩
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
    -- the moment tensor
    set P : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ := fun i k m j l n =>
      (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * ρ U k l * ρ U m n with hP
    have hcolumn : ∀ j l n, (fun i k m => P i k m j l n) ∈ Edge.tripleInvariants ρ := by
      intro j l n g
      have hdelta : (fun i k m => P i k m j l n) = (Fintype.card G : ℂ)⁻¹ •
          ∑ U, t3 (ρ U) (fun a b c => if a = j ∧ b = l ∧ c = n then 1 else 0) := by
        funext i k m
        simp only [hP, t3, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        congr 1
        refine Finset.sum_congr rfl fun U _ => ?_
        simp [Finset.sum_ite_eq', ite_and]
      change t3 (ρ g) _ = _
      rw [hdelta, t3_smul, t3_sum]
      congr 1
      simp only [t3_mul, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun U => rfl
    choose c hc using fun j l n => hmult _ (hcolumn j l n)
    have hPc : ∀ i k m j l n, P i k m j l n = c j l n * leviCivita i k m := by
      intro i k m j l n
      have := congrFun (congrFun (congrFun (hc j l n) i) k) m
      simpa [hε, smul_eq_mul] using this
    -- replacing `U` by `U⁻¹ = U†`
    have hconj : ∀ i k m j l n, P i k m j l n = conj (P j l n i k m) := by
      intro i k m j l n
      simp only [hP, map_mul, map_inv₀, map_natCast, map_sum]
      congr 1
      refine Fintype.sum_equiv (Equiv.inv G) _ _ fun U => ?_
      simp only [Equiv.inv_apply, hinv, Complex.conj_conj]
    have hcform : ∀ j l n, c j l n = conj (c 0 1 2) * leviCivita j l n := by
      intro j l n
      have h1 := hconj 0 1 2 j l n
      rw [hPc, hPc, leviCivita_012, mul_one, map_mul, leviCivita_real] at h1
      exact h1
    set a : ℂ := conj (c 0 1 2) with ha_def
    have hPa : ∀ i k m j l n, P i k m j l n = a * leviCivita j l n * leviCivita i k m := by
      intro i k m j l n
      rw [hPc, hcform]
    -- contracting with `ε`
    have hsum4 : ∀ f : G → Fin 3 → Fin 3 → Fin 3 → ℂ,
        ∑ j, ∑ l, ∑ n, ∑ U, f U j l n = ∑ U, ∑ j, ∑ l, ∑ n, f U j l n := by
      intro f
      simp only [Fin.sum_univ_three, Finset.sum_add_distrib]
    have hcontract : ∑ j, ∑ l, ∑ n, P 0 1 2 j l n * leviCivita j l n = 1 := by
      have hsum : ∑ j, ∑ l, ∑ n, P 0 1 2 j l n * leviCivita j l n =
          (Fintype.card G : ℂ)⁻¹ * ∑ U, t3 (ρ U) ε 0 1 2 := by
        simp only [hP, t3, hε, Finset.sum_mul, Finset.mul_sum]
        rw [← hsum4]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun U _ => ?_
        ring
      rw [hsum]
      simp only [hεinv]
      simp only [hε, leviCivita_012, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      field_simp
    have ha : a * 6 = 1 := by
      have h := hcontract
      simp only [hPa, leviCivita_012, mul_one] at h
      have hs : ∑ j, ∑ l, ∑ n, a * leviCivita j l n * leviCivita j l n =
          a * ∑ j, ∑ l, ∑ n, leviCivita j l n * leviCivita j l n := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun n _ => ?_
        ring
      rw [hs, sum_leviCivita_sq] at h
      exact h
    have hP' := hPa i k m j l n
    simp only [hP] at hP'
    rw [hP']
    have : a = 1 / 6 := by
      field_simp
      linear_combination ha
    rw [this]
    ring

/-! ## Non-vacuity -/

section NonVacuity

/-- Proposition 11.19 on the book's running example, the cube group: its triplet takes values in
`SU(3)` and is irreducible, and it is real, so the real-triplet moment applies:
`(1/24) Σ_U U_{ij} U_{kl} = δ_{ik} δ_{jl} / 3`. -/
example : letI := CubeGroup.fintype
    ∀ i j k l, (Fintype.card cubeGroup : ℂ)⁻¹ * ∑ U, cubeTriplet U i j * cubeTriplet U k l =
      (if i = k ∧ j = l then 1 else 0) / 3 := by
  let := CubeGroup.fintype
  refine (mtMoments cubeGroup cubeTriplet cubeTriplet_mem CubeGroup.isIrreducible_tripletRep).2.2.1
    fun U i j => ?_
  obtain ⟨p, rfl⟩ := CubeGroup.exists_toGroup U
  simp only [cubeTriplet, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    Submonoid.coe_subtype, CubeGroup.toGroup_val, signedPermMatrix, Matrix.of_apply]
  split_ifs <;> simp

end NonVacuity

end Artform
