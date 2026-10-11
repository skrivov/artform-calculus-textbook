import ArtformTextbook.Ch12.ModelsGroups
import ArtformTextbook.Ch12.VertexCensus
import ArtformTextbook.Ch12.OrderChange
import ArtformTextbook.Ch13.Defs.Transfer

/-!
# The third moments of the four colour groups, and `P V³ P`

* `3 ⊗ 3 ⊗ 3` has exactly one invariant for the cube group, the icosahedral group, `C₃ × A₅` and
  Valentiner's group (`TransferMoments.finrank_tripleInvariants_cube` and its companions): the
  number of invariants is the average of `χ³` (Proposition 11.5), `1` for the first two, and the
  other two contain the icosahedral group. Hence the cubic moment of Proposition 11.19,
  `⟨U_{ij} U_{kl} U_{mn}⟩ = ε_{ikm} ε_{jln}/6`.
* For a triplet containing `ω 1`, the moments with one or two conjugated entries vanish.
* So `Σ_U V_U³ = |G| L`, `L` the words of Theorem 13.8 for a real or a complex triplet
  (`TransferMoments.sum_hopAt_cube`), and for every orthogonal projector `P` onto the zero-flux
  sector, `P V³ P` is `L` there (`TransferMoments.transferVal_eq`), the argument of Theorem 11.20
  one order further.
-/

namespace Artform

open scoped Matrix ComplexConjugate Kronecker

open Module Edge ThereAndBack ColourGroups Exact

namespace TransferMoments

/-! ### Six sums -/

theorem sum_reorder {M : Type*} [AddCommMonoid M]
    (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ c₃, ∑ c₃', ∑ c₂, ∑ c₂', ∑ c₁, ∑ c₁', f c₁ c₂ c₃ c₁' c₂' c₃' =
      ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃', f c₁ c₂ c₃ c₁' c₂' c₃' := by
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃']
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₁, 2, c₃]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₁]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₁, 2, c₂, 2, c₃, 2, c₃']
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₁, 2, c₂, 2, c₃]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₁, 2, c₂, 2, c₃, 2, c₁']
    rw [Finset.sum_comm]

/-- Renaming `c₁ ↔ c₃` and `c'₁ ↔ c'₃` in a sixfold sum. -/
theorem sum_swap13 {M : Type*} [AddCommMonoid M]
    (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃', f c₃ c₂ c₁ c₃' c₂' c₁' =
      ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃', f c₁ c₂ c₃ c₁' c₂' c₃' := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, b, 2, c]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, b, 2, c, 2, d]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, b, 2, c]
    rw [Finset.sum_comm]

theorem leviCivita_rev (a b c : Fin 3) : leviCivita c b a = -leviCivita a b c := by
  rw [Moments.leviCivita_eq, Moments.leviCivita_eq]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [Moments.lcTab]

theorem leviCivita_rev_mul (a b c a' b' c' : Fin 3) :
    leviCivita c b a * leviCivita c' b' a' = leviCivita a b c * leviCivita a' b' c' := by
  rw [leviCivita_rev a b c, leviCivita_rev a' b' c']
  ring

/-! ### The invariants of `3 ⊗ 3 ⊗ 3` -/

variable {G : Type} [Group G]

/-- `U ↦ U ⊗ U ⊗ U` on the tensors with three upper indices. -/
noncomputable def tripleHom (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    G →* Matrix ((Fin 3 × Fin 3) × Fin 3) ((Fin 3 × Fin 3) × Fin 3) ℂ where
  toFun g := (ρ g ⊗ₖ ρ g) ⊗ₖ ρ g
  map_one' := by rw [map_one, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  map_mul' a b := by rw [map_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

/-- Tensors with three indices as functions on the triples of indices. -/
def curryEquiv : (Fin 3 → Fin 3 → Fin 3 → ℂ) ≃ₗ[ℂ] ((Fin 3 × Fin 3) × Fin 3 → ℂ) where
  toFun T p := T p.1.1 p.1.2 p.2
  invFun f i k m := f ((i, k), m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem tripleHom_mulVec (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (g : G)
    (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    tripleHom ρ g *ᵥ curryEquiv T = curryEquiv (Moments.t3 (ρ g) T) := by
  funext ⟨⟨i, k⟩, m⟩
  simp only [tripleHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, curryEquiv, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Moments.t3]

theorem map_tripleInvariants (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    (tripleInvariants ρ).map curryEquiv.toLinearMap = Fock.fixedSub (tripleHom ρ) := by
  ext f
  rw [Submodule.mem_map_equiv, Fock.mem_fixedSub]
  change (∀ U, Moments.t3 (ρ U) (curryEquiv.symm f) = curryEquiv.symm f) ↔ _
  refine forall_congr' fun U => ?_
  conv_rhs => rw [← curryEquiv.apply_symm_apply f, tripleHom_mulVec]
  exact ⟨fun h => by rw [h], fun h => curryEquiv.injective (by rw [h, curryEquiv.apply_symm_apply])⟩

/-- The number of invariants of `3 ⊗ 3 ⊗ 3` is the average of `χ³` (Proposition 11.5). -/
theorem finrank_tripleInvariants [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    (finrank ℂ ↥(tripleInvariants ρ) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 3 := by
  rw [← LinearEquiv.finrank_map_eq curryEquiv, map_tripleInvariants, Fock.finrank_fixedSub]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [tripleHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.trace_kronecker]
  ring

/-- `ε` is an invariant of `3 ⊗ 3 ⊗ 3` for a triplet in `SU(3)`. -/
theorem epsilon_mem (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    (fun i k m => leviCivita i k m) ∈ tripleInvariants ρ := fun U => by
  change Moments.t3 (ρ U) _ = _
  rw [Moments.t3_leviCivita, (Matrix.mem_specialUnitaryGroup_iff.mp (hρ U)).2, one_smul]

theorem epsilon_ne_zero : (fun i k m => leviCivita i k m : Fin 3 → Fin 3 → Fin 3 → ℂ) ≠ 0 := by
  intro h
  have := congrFun (congrFun (congrFun h 0) 1) 2
  simp only [Moments.leviCivita_012, Pi.zero_apply] at this
  exact one_ne_zero this

theorem one_le_finrank_tripleInvariants (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    1 ≤ finrank ℂ ↥(tripleInvariants ρ) := by
  rw [← finrank_span_singleton (K := ℂ) epsilon_ne_zero]
  exact Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr (epsilon_mem ρ hρ))

theorem cube_sum_trace_cube : ∑ k : Fin 24, M3Z.trace (cubeE k) ^ 3 = ⟨24, 0, 0, 0⟩ := by
  decide +kernel

theorem ico_sum_trace_cube : ∑ k : Fin 60, trA5 k ^ 3 = ⟨480, 0, 0, 0⟩ := by decide +kernel

theorem finrank_tripleInvariants_cube : finrank ℂ ↥(tripleInvariants cubeTriplet) = 1 := by
  apply Nat.cast_injective (R := ℂ)
  rw [finrank_tripleInvariants, Vertex.sum_cubeGroup]
  simp only [Vertex.cube_trace, ← ZOP.toComplex_pow, ← ColourGroups.toComplex_sum,
    cube_sum_trace_cube]
  have hcard : Fintype.card cubeGroup = 24 := by
    rw [← Nat.card_eq_fintype_card, card_cubeGroup]
  rw [hcard]
  simp [ZOP.toComplex]

theorem finrank_tripleInvariants_ico : finrank ℂ ↥(tripleInvariants icoTriplet) = 1 := by
  apply Nat.cast_injective (R := ℂ)
  rw [finrank_tripleInvariants, Vertex.sum_icoGroup]
  simp only [Vertex.ico_trace, div_pow, ← ZOP.toComplex_pow, ← Finset.sum_div]
  rw [Vertex.toComplex_sum_fin (fun k => trA5 k ^ 3), ico_sum_trace_cube]
  have hcard : Fintype.card icoGroup = 60 := by
    rw [← Nat.card_eq_fintype_card, card_icoGroup]
  rw [hcard]
  simp [ZOP.toComplex]
  norm_num

theorem tripleInvariants_c3a5_le :
    tripleInvariants c3a5Triplet ≤ tripleInvariants icoTriplet := fun T hT g => by
  have := hT (1, g)
  rwa [Vertex.c3a5Triplet_ico] at this

theorem tripleInvariants_valentiner_le :
    tripleInvariants valentinerTriplet ≤ tripleInvariants c3a5Triplet := fun T hT x => by
  have := hT (Vertex.c3a5ToValentiner x)
  rwa [Vertex.valentinerTriplet_c3a5] at this

theorem finrank_tripleInvariants_c3a5 : finrank ℂ ↥(tripleInvariants c3a5Triplet) = 1 :=
  le_antisymm (finrank_tripleInvariants_ico ▸ Submodule.finrank_mono tripleInvariants_c3a5_le)
    (one_le_finrank_tripleInvariants _ Vertex.c3a5Triplet_mem)

theorem finrank_tripleInvariants_valentiner :
    finrank ℂ ↥(tripleInvariants valentinerTriplet) = 1 :=
  le_antisymm
    (finrank_tripleInvariants_c3a5 ▸ Submodule.finrank_mono tripleInvariants_valentiner_le)
    (one_le_finrank_tripleInvariants _ Vertex.valentinerTriplet_mem)

/-- The triplet of Refinement II is irreducible: it contains that of Refinement I. -/
theorem valentiner_irreducible : (tripletRep valentinerTriplet).IsIrreducible :=
  ModelsGroups.isIrreducible_of_turns valentinerTriplet
    (fun i => by
      obtain ⟨g, hg⟩ := ModelsGroups.ico_halfTurns i
      exact ⟨Vertex.c3a5ToValentiner (1, g), by
        rw [Vertex.valentinerTriplet_c3a5, Vertex.c3a5Triplet_ico, hg]⟩)
    ⟨Vertex.c3a5ToValentiner (1, icoElt 40), fun w => by
      rw [Vertex.valentinerTriplet_c3a5, Vertex.c3a5Triplet_ico, ModelsGroups.icoTriplet_icoElt,
        ModelsGroups.rotC_40_mulVec]⟩

/-- The cubic moment of Proposition 11.19, `Σ_U U_{ij} U_{kl} U_{mn} = |G| ε_{ikm} ε_{jln}/6`. -/
theorem third_moment [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (hirr : (tripletRep ρ).IsIrreducible)
    (h1 : finrank ℂ ↥(tripleInvariants ρ) = 1) (i j k l m n : Fin 3) :
    ∑ U, ρ U i j * ρ U k l * ρ U m n =
      (Fintype.card G : ℂ) * (leviCivita i k m * leviCivita j l n / 6) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← (mtMoments G ρ hρ hirr).2.2.2.2 h1 i j k l m n, mul_inv_cancel_left₀ hcard]

/-! ### Moments with conjugated entries -/

/-- A sum over a group that `ω 1` multiplies by a factor `c ≠ 1` vanishes. -/
theorem sum_eq_zero_of_centre [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) {h₀ : G}
    (hh₀ : ρ h₀ = Exact.omega • 1) (f : Matrix (Fin 3) (Fin 3) ℂ → ℂ) {c : ℂ} (hc : c ≠ 1)
    (hf : ∀ M, f (Exact.omega • M) = c * f M) : ∑ U, f (ρ U) = 0 := by
  have h : ∑ U, f (ρ U) = c * ∑ U, f (ρ U) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft h₀) _ _ fun U => ?_).symm
    simp only [Equiv.coe_mulLeft, map_mul, hh₀, Matrix.smul_mul, Matrix.one_mul, hf]
  have h2 : (1 - c) * ∑ U, f (ρ U) = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

theorem conj_omega : conj Exact.omega = Exact.omega ^ 2 := by
  have h := Exact.omega_mul_conj
  have h3 := Exact.omega_pow_three
  have hne := Exact.omega_ne_zero
  calc conj Exact.omega = Exact.omega ^ 3 * conj Exact.omega := by rw [h3, one_mul]
    _ = Exact.omega ^ 2 * (Exact.omega * conj Exact.omega) := by ring
    _ = Exact.omega ^ 2 := by rw [h, mul_one]

/-! ### `Σ_U V_U³` -/

variable {S : Type} [Fintype S] [DecidableEq S]

/-- An entry of `U`, or its conjugate. -/
def entry (b : Bool) (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) : ℂ :=
  if b then M i j else conj (M i j)

/-- `A_{cc'}` or `A_{cc'}†`. -/
noncomputable def hopX (ord : LinearOrder (Mode (Fin 3) S)) (b : Bool) (c c' : Fin 3) :
    Matrix (Finset (Mode (Fin 3) S)) (Finset (Mode (Fin 3) S)) ℂ :=
  if b then hopA ord c c' else (hopA ord c c')ᴴ

/-- `V_U = Σ_{c, c'} Σ_b U^b_{cc'} X^b_{cc'}`, with `U^true = U`, `U^false = conj U`,
`X^true = A`, `X^false = A†`. -/
theorem hopAt_eq_bool (ord : LinearOrder (Mode (Fin 3) S)) (U : Matrix (Fin 3) (Fin 3) ℂ) :
    hopAt ord U = ∑ c, ∑ c', ∑ b : Bool, entry b U c c' • hopX ord b c c' := by
  rw [hopAt_eq_pairs, ← Finset.sum_add_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  rw [Fintype.sum_bool]
  simp [entry, hopX]

theorem sum_mul_sum_mul_sum {R : Type*} [NonUnitalNonAssocSemiring R] {ι κ μ : Type*}
    (s : Finset ι) (t : Finset κ) (u : Finset μ) (f : ι → R) (g : κ → R) (h : μ → R) :
    (∑ i ∈ s, f i) * (∑ j ∈ t, g j) * (∑ k ∈ u, h k) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i * g j * h k := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

theorem hopAt_cube (ord : LinearOrder (Mode (Fin 3) S)) (U : Matrix (Fin 3) (Fin 3) ℂ) :
    hopAt ord U * hopAt ord U * hopAt ord U =
      ∑ c₃, ∑ c₃', ∑ c₂, ∑ c₂', ∑ c₁, ∑ c₁', ∑ b₃ : Bool, ∑ b₂ : Bool, ∑ b₁ : Bool,
        (entry b₃ U c₃ c₃' * entry b₂ U c₂ c₂' * entry b₁ U c₁ c₁') •
          (hopX ord b₃ c₃ c₃' * hopX ord b₂ c₂ c₂' * hopX ord b₁ c₁ c₁') := by
  set Y : Fin 3 × Fin 3 → Matrix (Finset (Mode (Fin 3) S)) (Finset (Mode (Fin 3) S)) ℂ :=
    fun p => ∑ b : Bool, entry b U p.1 p.2 • hopX ord b p.1 p.2 with hY
  have hH : hopAt ord U = ∑ p, Y p := by
    rw [hopAt_eq_bool, Fintype.sum_prod_type]
  rw [hH, sum_mul_sum_mul_sum]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c₃ _ => Finset.sum_congr rfl fun c₃' _ =>
    Finset.sum_congr rfl fun c₂ _ => Finset.sum_congr rfl fun c₂' _ =>
      Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₁' _ => ?_
  rw [hY, sum_mul_sum_mul_sum]
  simp only [smul_mul_smul_comm]

/-- The moments of a monomial in the entries and their conjugates. -/
theorem sum_entry_mono [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (real : Bool)
    (hm : ∀ i j k l m n : Fin 3, ∑ U, ρ U i j * ρ U k l * ρ U m n =
      (Fintype.card G : ℂ) * (leviCivita i k m * leviCivita j l n / 6))
    (hreal : real = true → ∀ U i j, conj (ρ U i j) = ρ U i j)
    (hcentre : real = false → ∃ h₀, ρ h₀ = Exact.omega • 1)
    (b₃ b₂ b₁ : Bool) (c₃ c₃' c₂ c₂' c₁ c₁' : Fin 3) :
    ∑ U, entry b₃ (ρ U) c₃ c₃' * entry b₂ (ρ U) c₂ c₂' * entry b₁ (ρ U) c₁ c₁' =
      if real || (b₃ == b₂ && b₂ == b₁) then
        (Fintype.card G : ℂ) * (leviCivita c₃ c₂ c₁ * leviCivita c₃' c₂' c₁' / 6) else 0 := by
  cases real with
  | true =>
    have he : ∀ b U i j, entry b (ρ U) i j = ρ U i j := fun b U i j => by
      cases b
      · exact hreal rfl U i j
      · rfl
    simp only [he, Bool.true_or, ite_true]
    exact hm _ _ _ _ _ _
  | false =>
    obtain ⟨h₀, hh₀⟩ := hcentre rfl
    have hT : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ) i j,
        entry true (Exact.omega • M) i j = Exact.omega * entry true M i j := by
      intro M i j
      simp [entry]
    have hF : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ) i j,
        entry false (Exact.omega • M) i j = Exact.omega ^ 2 * entry false M i j := by
      intro M i j
      simp [entry, conj_omega]
    have h4 : Exact.omega ^ 4 = Exact.omega := by
      linear_combination Exact.omega * Exact.omega_pow_three
    have h5 : Exact.omega ^ 5 = Exact.omega ^ 2 := by
      linear_combination Exact.omega ^ 2 * Exact.omega_pow_three
    have hmix : ∀ c : ℂ, c ≠ 1 → (∀ M : Matrix (Fin 3) (Fin 3) ℂ,
        entry b₃ (Exact.omega • M) c₃ c₃' * entry b₂ (Exact.omega • M) c₂ c₂' *
          entry b₁ (Exact.omega • M) c₁ c₁' =
        c * (entry b₃ M c₃ c₃' * entry b₂ M c₂ c₂' * entry b₁ M c₁ c₁')) →
        ∑ U, entry b₃ (ρ U) c₃ c₃' * entry b₂ (ρ U) c₂ c₂' * entry b₁ (ρ U) c₁ c₁' = 0 :=
      fun c hc hf => sum_eq_zero_of_centre ρ hh₀
        (fun M => entry b₃ M c₃ c₃' * entry b₂ M c₂ c₂' * entry b₁ M c₁ c₁') hc hf
    have hne1 : Exact.omega ≠ 1 := Vertex.omega_ne_one
    have hne2 : Exact.omega ^ 2 ≠ 1 := Vertex.omega_sq_ne_one
    cases b₃ <;> cases b₂ <;> cases b₁
    · rw [ite_eq_left (by decide)]
      have h := congrArg conj (hm c₃ c₃' c₂ c₂' c₁ c₁')
      simp only [map_sum, map_mul, map_natCast, map_div₀, map_ofNat,
        Moments.leviCivita_real] at h
      simpa [entry] using h
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne2 fun M => by
        rw [hF, hF, hT]
        linear_combination (entry false M c₃ c₃' * entry false M c₂ c₂' *
          entry true M c₁ c₁') * h5
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne2 fun M => by
        rw [hF, hT, hF]
        linear_combination (entry false M c₃ c₃' * entry true M c₂ c₂' *
          entry false M c₁ c₁') * h5
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne1 fun M => by
        rw [hF, hT, hT]
        linear_combination (entry false M c₃ c₃' * entry true M c₂ c₂' *
          entry true M c₁ c₁') * h4
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne2 fun M => by
        rw [hT, hF, hF]
        linear_combination (entry true M c₃ c₃' * entry false M c₂ c₂' *
          entry false M c₁ c₁') * h5
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne1 fun M => by
        rw [hT, hF, hT]
        linear_combination (entry true M c₃ c₃' * entry false M c₂ c₂' *
          entry true M c₁ c₁') * h4
    · rw [ite_eq_right (by decide)]
      exact hmix _ hne1 fun M => by
        rw [hT, hT, hF]
        linear_combination (entry true M c₃ c₃' * entry true M c₂ c₂' *
          entry false M c₁ c₁') * h4
    · rw [ite_eq_left (by decide)]
      simpa [entry] using hm c₃ c₃' c₂ c₂' c₁ c₁'

/-- `Σ_U V_U³ = |G| L`, with `L` the words of Theorem 13.8: for a real triplet each of the eight
words in `A` and `A†` carries the cubic moment; for a complex one only `A A A` and `A† A† A†`
survive. -/
theorem sum_hopAt_cube [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S)) (real : Bool)
    (hm : ∀ i j k l m n : Fin 3, ∑ U, ρ U i j * ρ U k l * ρ U m n =
      (Fintype.card G : ℂ) * (leviCivita i k m * leviCivita j l n / 6))
    (hreal : real = true → ∀ U i j, conj (ρ U i j) = ρ U i j)
    (hcentre : real = false → ∃ h₀, ρ h₀ = Exact.omega • 1) :
    ∑ U, hopAt ord (ρ U) * hopAt ord (ρ U) * hopAt ord (ρ U) =
      (Fintype.card G : ℂ) • transferOf (hopA ord) real := by
  simp only [hopAt_cube]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃']
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂, 2, c₂']
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂, 2, c₂', 2, c₁]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂, 2, c₂', 2, c₁, 2, c₁']
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂, 2, c₂', 2, c₁, 2, c₁', 2, b₃]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, c₃, 2, c₃', 2, c₂, 2, c₂', 2, c₁, 2, c₁', 2, b₃, 2, b₂]
    rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_entry_mono ρ real hm hreal hcentre]
  have hrev : ∀ c₁ c₂ c₃ c₁' c₂' c₃' : Fin 3,
      (Fintype.card G : ℂ) * (leviCivita c₃ c₂ c₁ * leviCivita c₃' c₂' c₁' / 6) =
        (Fintype.card G : ℂ) * (1 / 6) * (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') := by
    intro c₁ c₂ c₃ c₁' c₂' c₃'
    rw [leviCivita_rev_mul]
    ring
  cases real with
  | true =>
    have hB : ∀ c c', ∑ b : Bool, hopX ord b c c' = hopA ord c c' + (hopA ord c c')ᴴ := by
      intro c c'
      rw [Fintype.sum_bool]
      simp [hopX]
    simp only [Bool.true_or, ite_true, ← Finset.smul_sum]
    simp only [← sum_mul_sum_mul_sum, hB, hrev, transferOf, ite_true, Finset.smul_sum,
      smul_smul]
    conv_rhs => rw [← sum_reorder]
    simp only [mul_assoc]
  | false =>
    have hW : ∀ (m : ℂ) (c₃ c₃' c₂ c₂' c₁ c₁' : Fin 3),
        ∑ b₃ : Bool, ∑ b₂ : Bool, ∑ b₁ : Bool,
          (if (false || (b₃ == b₂ && b₂ == b₁)) = true then m else 0) •
            (hopX ord b₃ c₃ c₃' * hopX ord b₂ c₂ c₂' * hopX ord b₁ c₁ c₁') =
          m • (hopA ord c₃ c₃' * hopA ord c₂ c₂' * hopA ord c₁ c₁' +
            (hopA ord c₃ c₃')ᴴ * (hopA ord c₂ c₂')ᴴ * (hopA ord c₁ c₁')ᴴ) := by
      intro m c₃ c₃' c₂ c₂' c₁ c₁'
      simp [hopX, smul_add]
    simp only [hW, hrev]
    have hstar : ∀ i k m : Fin 3, star (leviCivita i k m) = leviCivita i k m :=
      Moments.leviCivita_real
    have hS : (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
        (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
          (hopA ord c₃ c₃' * hopA ord c₂ c₂' * hopA ord c₁ c₁'))ᴴ =
        ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
          (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
            ((hopA ord c₃ c₃')ᴴ * (hopA ord c₂ c₂')ᴴ * (hopA ord c₁ c₁')ᴴ) := by
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_mul', hstar,
        Matrix.conjTranspose_mul]
      rw [← sum_swap13]
      simp only [leviCivita_rev_mul, Matrix.mul_assoc]
    rw [transferOf, ite_eq_right (by decide), Matrix.conjTranspose_smul, hS,
      show star (1 / 6 : ℂ) = 1 / 6 by simp, ← smul_add, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← smul_add]
    conv_rhs => rw [← sum_reorder]
    simp only [Finset.smul_sum, smul_smul, mul_assoc]

/-! ### `P V³ P` on the zero-flux sector -/

/-- The gauge pairs commute with `Σ_U V_U³`. -/
theorem pairHom_mul_sum_cube [Fintype G] {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Mode (Fin 3) S))
    (h : G × G) :
    pairHom ρ ord h * ∑ U, hopAt ord (ρ U) * hopAt ord (ρ U) * hopAt ord (ρ U) =
      (∑ U, hopAt ord (ρ U) * hopAt ord (ρ U) * hopAt ord (ρ U)) * pairHom ρ ord h := by
  obtain ⟨hx, hy⟩ := h
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv ((Equiv.mulLeft hy).trans (Equiv.mulRight hx⁻¹)) _ _ fun U => ?_
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight]
  have hD := pairHom_mul_hopAt hρ ord hx hy U
  set D := pairHom ρ ord (hx, hy)
  set V := hopAt ord (ρ U)
  set V' := hopAt ord (ρ (hy * U * hx⁻¹))
  calc D * (V * V * V) = D * V * V * V := by simp only [Matrix.mul_assoc]
    _ = V' * D * V * V := by rw [hD]
    _ = V' * (D * V) * V := by simp only [Matrix.mul_assoc]
    _ = V' * (V' * D) * V := by rw [hD]
    _ = V' * V' * (D * V) := by simp only [Matrix.mul_assoc]
    _ = V' * V' * (V' * D) := by rw [hD]
    _ = V' * V' * V' * D := by simp only [Matrix.mul_assoc]

/-- For every orthogonal projector `P` onto the zero-flux sector, `L = P V³ P` acts on the
zero-flux values as the words of Theorem 13.8. -/
theorem transferVal_eq [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S)) (real : Bool)
    (hm : ∀ i j k l m n : Fin 3, ∑ U, ρ U i j * ρ U k l * ρ U m n =
      (Fintype.card G : ℂ) * (leviCivita i k m * leviCivita j l n / 6))
    (hreal : real = true → ∀ U i j, conj (ρ U i j) = ρ U i j)
    (hcentre : real = false → ∃ h₀, ρ h₀ = Exact.omega • 1)
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ))
    (hP : IsZeroFluxProj ρ ord P) (v : Finset (Mode (Fin 3) S) → ℂ)
    (hv : v ∈ zeroFluxValues ρ ord) :
    transferVal ρ ord P v = transferOf (hopA ord) real *ᵥ v := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  have hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ := fun g =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (hρ g)).1
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum := sum_hopAt_cube ρ ord real hm hreal hcentre
  set L := transferOf (hopA ord) real with hLdef
  have hL : ∀ h : G × G, pairHom ρ ord h * L = L * pairHom ρ ord h := by
    intro h
    have := pairHom_mul_sum_cube hunit ord h
    rw [hsum, Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ hcard this
  have hvψ : (fun _ : G => v) ∈ zeroFlux ρ ord := by
    rw [mem_zeroFlux_iff]
    exact ⟨fun _ => rfl, (Edge.mem_zeroFluxValues ρ ord v).mp hv⟩
  have hLmem : (fun _ : G => L *ᵥ v) ∈ zeroFlux ρ ord := by
    rw [mem_zeroFlux_iff]
    refine ⟨fun _ => rfl, fun h => ?_⟩
    rw [Matrix.mulVec_mulVec, hL, ← Matrix.mulVec_mulVec,
      (Edge.mem_zeroFluxValues ρ ord v).mp hv h]
  have hV3 : hop ρ ord (hop ρ ord (hop ρ ord (fun _ : G => v))) =
      fun U => (hopAt ord (ρ U) * hopAt ord (ρ U) * hopAt ord (ρ U)) *ᵥ v := by
    funext U
    simp only [hop, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hproj : P (hop ρ ord (hop ρ ord (hop ρ ord (fun _ : G => v)))) =
      fun _ : G => L *ᵥ v := by
    refine proj_eq_of_orth hP1 hP2 hP3 hLmem fun ξ hξ => ?_
    rw [const_of_mem_zeroFlux hξ, hV3, statePairing_const_atEach, hsum]
    have e : (fun _ : G => L *ᵥ v) = fun U => (fun _ : G => L) U *ᵥ v := rfl
    rw [e, statePairing_const_atEach, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
  change P (hop ρ ord (hop ρ ord (hop ρ ord (P fun _ => v)))) 1 = _
  rw [hP2 _ hvψ, hproj]

/-! ### The four finite models -/

theorem transferVal_cube (ord : LinearOrder (Mode (Fin 3) (Fin 2)))
    (P : (cubeGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
      (cubeGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ))
    (hP : IsZeroFluxProj cubeTriplet ord P) (v : Finset (Mode (Fin 3) (Fin 2)) → ℂ)
    (hv : v ∈ zeroFluxValues cubeTriplet ord) :
    transferVal cubeTriplet ord P v = transferWords ord true *ᵥ v :=
  transferVal_eq cubeTriplet cubeTriplet_mem ord true
    (third_moment cubeTriplet cubeTriplet_mem CubeGroup.isIrreducible_tripletRep
      finrank_tripleInvariants_cube) (fun _ => cubeTriplet_real) (fun h => absurd h (by decide))
    P hP v hv

theorem transferVal_ico (ord : LinearOrder (Mode (Fin 3) (Fin 2)))
    (P : (icoGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
      (icoGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ))
    (hP : IsZeroFluxProj icoTriplet ord P) (v : Finset (Mode (Fin 3) (Fin 2)) → ℂ)
    (hv : v ∈ zeroFluxValues icoTriplet ord) :
    transferVal icoTriplet ord P v = transferWords ord true *ᵥ v :=
  transferVal_eq icoTriplet Vertex.icoTriplet_mem ord true
    (third_moment icoTriplet Vertex.icoTriplet_mem ModelsGroups.ico_irreducible
      finrank_tripleInvariants_ico) (fun _ => ModelsGroups.ico_real)
    (fun h => absurd h (by decide)) P hP v hv

theorem transferVal_c3a5 (ord : LinearOrder (Mode (Fin 3) (Fin 2)))
    (P : (C3A5 → Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
      (C3A5 → Finset (Mode (Fin 3) (Fin 2)) → ℂ))
    (hP : IsZeroFluxProj c3a5Triplet ord P) (v : Finset (Mode (Fin 3) (Fin 2)) → ℂ)
    (hv : v ∈ zeroFluxValues c3a5Triplet ord) :
    transferVal c3a5Triplet ord P v = transferWords ord false *ᵥ v :=
  transferVal_eq c3a5Triplet Vertex.c3a5Triplet_mem ord false
    (third_moment c3a5Triplet Vertex.c3a5Triplet_mem ModelsGroups.c3a5_irreducible
      finrank_tripleInvariants_c3a5) (fun h => absurd h (by decide))
    (fun _ => ⟨(Multiplicative.ofAdd 1, 1), Vertex.c3a5Triplet_omega⟩) P hP v hv

theorem transferVal_valentiner (ord : LinearOrder (Mode (Fin 3) (Fin 2)))
    (P : (valentiner → Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
      (valentiner → Finset (Mode (Fin 3) (Fin 2)) → ℂ))
    (hP : IsZeroFluxProj valentinerTriplet ord P) (v : Finset (Mode (Fin 3) (Fin 2)) → ℂ)
    (hv : v ∈ zeroFluxValues valentinerTriplet ord) :
    transferVal valentinerTriplet ord P v = transferWords ord false *ᵥ v :=
  transferVal_eq valentinerTriplet Vertex.valentinerTriplet_mem ord false
    (third_moment valentinerTriplet Vertex.valentinerTriplet_mem valentiner_irreducible
      finrank_tripleInvariants_valentiner) (fun h => absurd h (by decide))
    (fun _ => ⟨Vertex.c3a5ToValentiner (Multiplicative.ofAdd 1, 1), by
      rw [Vertex.valentinerTriplet_c3a5, Vertex.c3a5Triplet_omega]; rfl⟩) P hP v hv

end TransferMoments

end Artform
