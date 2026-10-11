import ArtformTextbook.Ch12.VertexBasis
import ArtformTextbook.Ch12.GroupsValentiner

/-!
# The colourless states of one vertex, for the five colour groups

* **The dimension.** For a finite group with a triplet in `SU(3)`, the invariant tables of one
  vertex with two slots number `⟨(2 + χ + χ̄)²⟩`, since `det(1 + g) = 2 + χ + χ̄` on `SU(3)`
  (Theorem 11.15 at `z = 1`): `8` for the cube group and the icosahedral group, whose characters
  are real with `⟨χ⟩ = 0` and `⟨χ²⟩ = 1`.
* **The cube and the icosahedron.** The eight states are invariants of both (a rotation fixes
  them) and independent, so they span the invariants.
* **The centre.** `ω 1` multiplies the eight states by `1, ω², 1, 1, 1, 1, ω, 1`; so the vectors of
  the span of the eight that `ω 1` fixes are those of the span of the six. `SU(3)` contains the
  cube group and `ω 1`; `C₃ × A₅` contains the icosahedral group and `ω 1`; Valentiner's group
  contains `C₃ × A₅`; each fixes the six. So their invariants are the span of the six.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Polynomial Spin ColourGroups Exact

namespace Vertex

/-! ### The dimension of the invariants -/

/-- `det(1 + g) = 2 + χ(g) + conj χ(g)` on `SU(3)`. -/
theorem det_one_add_of_mem {g : Matrix (Fin 3) (Fin 3) ℂ}
    (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    (1 + g).det = 2 + g.trace + conj g.trace := by
  have h := congrArg (Polynomial.eval 1) (Edge.det_one_add_X_smul_of_mem_specialUnitaryGroup hg)
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det] at h
  have e : (Polynomial.evalRingHom 1).mapMatrix (1 + (X : ℂ[X]) • g.map C) = 1 + g := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [e] at h
  rw [h]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, one_pow,
    mul_one]
  ring

variable {G : Type*} [Group G] [Fintype G]

/-- The dimension of the invariants of one vertex with two slots, from the averages. -/
theorem finrank_of_sums (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Fin 3 × Fin 2))
    (s1 s2 s11 : ℂ) (h1 : ∑ g, (ρ g).trace = s1) (h1' : ∑ g, conj (ρ g).trace = conj s1)
    (h2 : ∑ g, (ρ g).trace ^ 2 = s2) (h2' : ∑ g, conj (ρ g).trace ^ 2 = conj s2)
    (h11 : ∑ g, (ρ g).trace * conj (ρ g).trace = s11) :
    (Module.finrank ℂ ↥(Edge.vertexInvariants ρ ord) : ℂ) = (Fintype.card G : ℂ)⁻¹ *
      (4 * Fintype.card G + 4 * s1 + 4 * conj s1 + s2 + conj s2 + 2 * s11) := by
  rw [Edge.finrank_vertexInvariants, Fintype.card_fin]
  congr 1
  simp only [det_one_add_of_mem (hρ _)]
  have e : ∀ g : G, (2 + (ρ g).trace + conj (ρ g).trace) ^ 2 =
      4 + 4 * (ρ g).trace + 4 * conj (ρ g).trace + (ρ g).trace ^ 2 + conj (ρ g).trace ^ 2 +
        2 * ((ρ g).trace * conj (ρ g).trace) := fun g => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h1', h2, h2', h11,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- `n` independent vectors of a subspace of dimension `n` span it. -/
theorem span_eq_of_finrank {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Fin n → V)
    (hb : LinearIndependent ℂ b) (W : Submodule ℂ V) (hmem : ∀ i, b i ∈ W)
    [FiniteDimensional ℂ W] (hW : Module.finrank ℂ W = n) :
    Submodule.span ℂ (Set.range b) = W := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hb, Fintype.card_fin, hW]

theorem finiteDimensional_vertexInvariants {G : Type*} [Group G]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (ord : LinearOrder (Fin 3 × Fin 2)) :
    FiniteDimensional ℂ ↥(Edge.vertexInvariants ρ ord) := inferInstance

/-! ### The cube group -/

theorem cube_mul_transpose (g : cubeGroup) : cubeTriplet g * (cubeTriplet g)ᵀ = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (cubeTriplet_unitary g)
  have : (cubeTriplet g)ᵀ = star (cubeTriplet g) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.star_apply]
    exact (cubeTriplet_real g j i).symm
  rw [this, hu]

theorem cube_finrank (ord : LinearOrder (Fin 3 × Fin 2)) :
    Module.finrank ℂ ↥(Edge.vertexInvariants cubeTriplet ord) = 8 := by
  have hcard : Fintype.card cubeGroup = 24 := by
    rw [← Nat.card_eq_fintype_card, card_cubeGroup]
  have h := finrank_of_sums cubeTriplet cubeTriplet_mem ord 0 24 24 cube_sums.1
    (by simp only [cube_conj_trace, map_zero]; exact cube_sums.1) cube_sums.2
    (by simp only [cube_conj_trace]; rw [cube_sums.2, map_ofNat])
    (by simp only [cube_conj_trace, ← sq]; exact cube_sums.2)
  rw [hcard] at h
  apply Nat.cast_injective (R := ℂ)
  rw [h]
  simp only [map_ofNat, map_zero]
  norm_num

/-- The colourless states of one vertex of Model I are spanned by the eight states. -/
theorem cube_span (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (eight ord)) = Edge.vertexInvariants cubeTriplet ord :=
  span_eq_of_finrank _ (eight_linearIndependent ord) _
    (fun i g => gamma_eight ord (cubeTriplet_mem g) (cube_mul_transpose g) i) (cube_finrank ord)

/-! ### The icosahedral group -/

theorem sum_icoGroup (f : icoGroup → ℂ) : ∑ g, f g = ∑ k : Fin 60, f (icoElt k) :=
  (Fintype.sum_equiv icoEquiv _ _ fun _ => rfl).symm

theorem ico_trace (k : Fin 60) :
    (icoTriplet (icoElt k)).trace = ZOP.toComplex (trA5 k) / 2 :=
  char_icoElt k

theorem ico_sum_trace : ∑ k : Fin 60, trA5 k = 0 := by decide +kernel

theorem ico_sum_trace_sq : ∑ k : Fin 60, trA5 k ^ 2 = ⟨240, 0, 0, 0⟩ := by decide +kernel

theorem ico_conj_trace (g : icoGroup) : conj (icoTriplet g).trace = (icoTriplet g).trace := by
  obtain ⟨k, rfl⟩ := icoElt_surjective g
  exact conj_char_icoElt k

theorem toComplex_sum_fin {n : ℕ} (f : Fin n → ZOP) :
    ∑ k, ZOP.toComplex (f k) = ZOP.toComplex (∑ k, f k) := by
  rw [← ZOP.toComplexHom_apply, map_sum]
  rfl

theorem ico_sums : ∑ g, (icoTriplet g).trace = 0 ∧ ∑ g, (icoTriplet g).trace ^ 2 = 60 := by
  rw [sum_icoGroup, sum_icoGroup]
  simp only [ico_trace, div_pow, ← ZOP.toComplex_pow, ← Finset.sum_div]
  rw [toComplex_sum_fin (fun k => trA5 k), toComplex_sum_fin (fun k => trA5 k ^ 2),
    ico_sum_trace, ico_sum_trace_sq, ZOP.toComplex_zero]
  refine ⟨by simp, ?_⟩
  simp [ZOP.toComplex]
  norm_num

theorem ico_mul_transpose (g : icoGroup) : icoTriplet g * (icoTriplet g)ᵀ = 1 := by
  obtain ⟨R, hR, hg⟩ := g.2
  have hO := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp hR.1).1
  change ((g : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) *
    ((g : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ = 1
  rw [hg, ← Matrix.transpose_map, ← map_ofReal_mul]
  have : R * star R = 1 := hO
  rw [Matrix.star_eq_conjTranspose] at this
  have hT : Rᴴ = Rᵀ := by
    ext i j
    simp
  rw [hT] at this
  rw [this]
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

theorem icoTriplet_mem (g : icoGroup) : icoTriplet g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  (g : Matrix.specialUnitaryGroup (Fin 3) ℂ).2

theorem ico_finrank (ord : LinearOrder (Fin 3 × Fin 2)) :
    Module.finrank ℂ ↥(Edge.vertexInvariants icoTriplet ord) = 8 := by
  have hcard : Fintype.card icoGroup = 60 := by
    rw [← Nat.card_eq_fintype_card, card_icoGroup]
  have h := finrank_of_sums icoTriplet icoTriplet_mem ord 0 60 60 ico_sums.1
    (by simp only [ico_conj_trace, map_zero]; exact ico_sums.1) ico_sums.2
    (by simp only [ico_conj_trace]; rw [ico_sums.2, map_ofNat])
    (by simp only [ico_conj_trace, ← sq]; exact ico_sums.2)
  rw [hcard] at h
  apply Nat.cast_injective (R := ℂ)
  rw [h]
  simp only [map_ofNat, map_zero]
  norm_num

/-- The colourless states of one vertex of Model II are spanned by the eight states. -/
theorem ico_span (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (eight ord)) = Edge.vertexInvariants icoTriplet ord :=
  span_eq_of_finrank _ (eight_linearIndependent ord) _
    (fun i g => gamma_eight ord (icoTriplet_mem g) (ico_mul_transpose g) i) (ico_finrank ord)

/-! ### The centre `ω 1` -/

/-- `ω 1`, a matrix of `SU(3)`. -/
noncomputable def omegaOne : Matrix (Fin 3) (Fin 3) ℂ := Exact.omega • 1

theorem omegaOne_mem : omegaOne ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  have := omega_pow_smul_mem 1 (Submonoid.one_mem (Matrix.specialUnitaryGroup (Fin 3) ℂ))
  rwa [pow_one] at this

theorem omega_ne_one : Exact.omega ≠ 1 := by
  intro h
  have := Exact.omega_sq_add
  rw [h] at this
  norm_num at this

theorem omega_sq_ne_one : Exact.omega ^ 2 ≠ 1 := by
  intro h
  have := Exact.omega_sq_add
  rw [h] at this
  have h2 : Exact.omega = -2 := by linear_combination this
  rw [h2] at h
  norm_num at h

theorem conj_omega_sq : conj (Exact.omega ^ 2) = Exact.omega := by
  rw [map_pow, Exact.conj_omega]
  linear_combination Exact.omega_sq_add

/-- The factor by which `ω 1` multiplies each of the eight states: `ω` to the number of quarks. -/
noncomputable def omegaEig : Fin 8 → ℂ := ![1, Exact.omega ^ 2, 1, 1, 1, 1, Exact.omega, 1]

theorem gamma_omega (ord : LinearOrder (Fin 3 × Fin 2)) (i : Fin 8) :
    Fock.vertexGamma ord omegaOne *ᵥ eight ord i = omegaEig i • eight ord i := by
  have hdet : omegaOne.det = 1 := det_eq_one omegaOne_mem
  have hT : omegaOne * omegaOneᵀ = Exact.omega ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [omegaOne, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, one_mul, sq]
  fin_cases i
  · change Fock.vertexGamma ord omegaOne *ᵥ empty = omegaEig 0 • empty
    rw [empty, gamma_ket_empty]
    simp [omegaEig]
  · change Fock.vertexGamma ord omegaOne *ᵥ pair ord = omegaEig 1 • pair ord
    rw [gamma_pair, hT, pair, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_eq_single c']
    · simp [omegaEig]
    · intro c'' _ hc
      simp [Matrix.one_apply_ne (Ne.symm hc)]
    · simp
  · change Fock.vertexGamma ord omegaOne *ᵥ quartet ord 0 = omegaEig 2 • quartet ord 0
    rw [gamma_quartet, hdet]
    simp [omegaEig]
  · change Fock.vertexGamma ord omegaOne *ᵥ quartet ord 1 = omegaEig 3 • quartet ord 1
    rw [gamma_quartet, hdet]
    simp [omegaEig]
  · change Fock.vertexGamma ord omegaOne *ᵥ quartet ord 2 = omegaEig 4 • quartet ord 2
    rw [gamma_quartet, hdet]
    simp [omegaEig]
  · change Fock.vertexGamma ord omegaOne *ᵥ quartet ord 3 = omegaEig 5 • quartet ord 3
    rw [gamma_quartet, hdet]
    simp [omegaEig]
  · change Fock.vertexGamma ord omegaOne *ᵥ holes ord = omegaEig 6 • holes ord
    rw [gamma_holes ord (mem_unitary omegaOne_mem), hT, hdet, one_pow, one_smul, holes,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_eq_single c']
    · simp [omegaEig, conj_omega_sq]
    · intro c'' _ hc
      simp [Matrix.one_apply_ne (Ne.symm hc)]
    · simp
  · change Fock.vertexGamma ord omegaOne *ᵥ full = omegaEig 7 • full
    rw [gamma_full, hdet]
    simp [omegaEig]

/-- The place of each of the six among the eight. -/
def sixToEight : Fin 6 → Fin 8 := ![0, 2, 3, 4, 5, 7]

theorem six_eq (ord : LinearOrder (Fin 3 × Fin 2)) (j : Fin 6) :
    six ord j = eight ord (sixToEight j) := by
  fin_cases j <;> simp [six, eight, sixToEight]

theorem sixToEight_injective : Function.Injective sixToEight := by
  have h : ∀ a b : Fin 6, sixToEight a = sixToEight b → a = b := by decide
  exact fun a b => h a b

theorem six_linearIndependent (ord : LinearOrder (Fin 3 × Fin 2)) :
    LinearIndependent ℂ (six ord) := by
  have e : six ord = eight ord ∘ sixToEight := funext (six_eq ord)
  rw [e]
  exact (eight_linearIndependent ord).comp sixToEight sixToEight_injective

/-- A vector of the span of the eight that `ω 1` fixes lies in the span of the six. -/
theorem mem_span_six_of_fixed (ord : LinearOrder (Fin 3 × Fin 2)) {v : Finset (Fin 3 × Fin 2) → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range (eight ord)))
    (hω : Fock.vertexGamma ord omegaOne *ᵥ v = v) :
    v ∈ Submodule.span ℂ (Set.range (six ord)) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have hfix : ∑ i, (c i * omegaEig i - c i) • eight ord i = 0 := by
    rw [Matrix.mulVec_sum] at hω
    simp only [Matrix.mulVec_smul, gamma_omega, smul_smul] at hω
    simp only [sub_smul, Finset.sum_sub_distrib, hω, sub_self]
  have hc := Fintype.linearIndependent_iff.mp (eight_linearIndependent ord) _ hfix
  have h1 : c 1 = 0 := by
    have := hc 1
    simp only [omegaEig, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    have h' : c 1 * (Exact.omega ^ 2 - 1) = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr omega_sq_ne_one)
  have h6 : c 6 = 0 := by
    have := hc 6
    simp only [omegaEig] at this
    have h' : c 6 * (Exact.omega - 1) = 0 := by
      have e : (![1, Exact.omega ^ 2, 1, 1, 1, 1, Exact.omega, 1] : Fin 8 → ℂ) 6 = Exact.omega :=
        rfl
      rw [e] at this
      linear_combination this
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr omega_ne_one)
  rw [Fin.sum_univ_eight]
  simp only [h1, h6, zero_smul, add_zero]
  have hm : ∀ j : Fin 6, eight ord (sixToEight j) ∈ Submodule.span ℂ (Set.range (six ord)) :=
    fun j => Submodule.subset_span ⟨j, six_eq ord j⟩
  have h0 : eight ord 0 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 0
  have h2 : eight ord 2 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 1
  have h3 : eight ord 3 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 2
  have h4 : eight ord 4 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 3
  have h5 : eight ord 5 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 4
  have h7 : eight ord 7 ∈ Submodule.span ℂ (Set.range (six ord)) := hm 5
  exact add_mem (add_mem (add_mem (add_mem (add_mem (Submodule.smul_mem _ _ h0)
    (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)) (Submodule.smul_mem _ _ h4))
    (Submodule.smul_mem _ _ h5)) (Submodule.smul_mem _ _ h7)

/-! ### `SU(3)`, `C₃ × A₅` and Valentiner's group -/

/-- The six states are invariants of every colour group in `SU(3)`. -/
theorem span_six_le {H : Type*} [Group H] (ρ : H →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ h, ρ h ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (six ord)) ≤ Edge.vertexInvariants ρ ord := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩ h
  exact gamma_six ord (hρ h) i

/-- The colourless states of one vertex for `SU(3)`: the span of the six. -/
theorem su3_span (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (six ord)) = Edge.vertexInvariants su3Triplet ord := by
  refine le_antisymm (span_six_le su3Triplet (fun g => g.2) ord) fun v hv => ?_
  refine mem_span_six_of_fixed ord ?_ (hv ⟨omegaOne, omegaOne_mem⟩)
  rw [cube_span]
  intro h
  exact hv (h : Matrix.specialUnitaryGroup (Fin 3) ℂ)

theorem c3a5Triplet_ico (g : icoGroup) : c3a5Triplet (1, g) = icoTriplet g := by
  simp [c3a5Triplet, C3A5.triplet, icoTriplet]

theorem c3a5Triplet_omega : c3a5Triplet (Multiplicative.ofAdd 1, 1) = omegaOne := by
  have h : Exact.omega ^ ZMod.val (1 : ZMod 3) = Exact.omega := by
    rw [show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one]
  simpa [c3a5Triplet, C3A5.triplet, omegaOne] using h

theorem c3a5Triplet_mem (x : C3A5) : c3a5Triplet x ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  (C3A5.triplet x).2

/-- The colourless states of one vertex for `C₃ × A₅`: the span of the six. -/
theorem c3a5_span (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (six ord)) = Edge.vertexInvariants c3a5Triplet ord := by
  refine le_antisymm (span_six_le c3a5Triplet c3a5Triplet_mem ord) fun v hv => ?_
  have hω := hv (Multiplicative.ofAdd 1, 1)
  rw [c3a5Triplet_omega] at hω
  refine mem_span_six_of_fixed ord ?_ hω
  rw [ico_span]
  intro g
  have := hv (1, g)
  rwa [c3a5Triplet_ico] at this

/-- An element of `C₃ × A₅` as an element of Valentiner's group. -/
noncomputable def c3a5ToValentiner (x : C3A5) : valentiner :=
  ⟨C3A5.triplet x, Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)⟩

theorem valentinerTriplet_c3a5 (x : C3A5) :
    valentinerTriplet (c3a5ToValentiner x) = c3a5Triplet x := rfl

theorem valentinerTriplet_mem (g : valentiner) :
    valentinerTriplet g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  (g : Matrix.specialUnitaryGroup (Fin 3) ℂ).2

/-- The colourless states of one vertex for Valentiner's group: the span of the six. -/
theorem valentiner_span (ord : LinearOrder (Fin 3 × Fin 2)) :
    Submodule.span ℂ (Set.range (six ord)) = Edge.vertexInvariants valentinerTriplet ord := by
  refine le_antisymm (span_six_le valentinerTriplet valentinerTriplet_mem ord) fun v hv => ?_
  rw [c3a5_span]
  intro x
  have := hv (c3a5ToValentiner x)
  rwa [valentinerTriplet_c3a5] at this

theorem finrank_span_six (ord : LinearOrder (Fin 3 × Fin 2)) :
    Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (six ord))) = 6 := by
  rw [finrank_span_eq_card (six_linearIndependent ord), Fintype.card_fin]

end Vertex

end Artform
