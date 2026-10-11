import ArtformTextbook.Ch12.EdgeProd
import ArtformTextbook.Ch12.SpectrumCert

/-!
# The zero-flux sector of one edge with two slots

* Products of invariants of the two ends are zero-flux states: the gauge pairs act factor by
  factor (`Edge.secondQuant_diag_prod`).
* The products of the eight states (the cube group, the icosahedral group) and of the six
  (`SU(3)`, `C₃ × A₅`, Valentiner's group) are independent, and the zero-flux sector of each model
  has the dimension of their number, `64` or `36` (Theorem 11.15 for the real triplets, the
  inclusion of the invariants of a subgroup otherwise): they span it.
* In the book's order the products are lists of masks, the products of the lists of the two ends
  (`Edge.tensorV`), so the kernel computes with them.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open FockCalc Spin

namespace Edge

/-! ### Products are zero-flux states -/

variable {G : Type*} [Group G]

theorem pairHom_prod (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (hx hy : G)
    (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    pairHom ρ bookOrd (hx, hy) *ᵥ prod u w =
      prod (Fock.vertexGamma Vertex.bookOrd (ρ hx) *ᵥ u)
        (Fock.vertexGamma Vertex.bookOrd (ρ hy) *ᵥ w) :=
  secondQuant_diag_prod _ _ u w

/-- The product of invariants of the two ends, at every link value, is a zero-flux state. -/
theorem const_prod_mem_zeroFlux (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    {u w : Finset (Fin 3 × Fin 2) → ℂ} (hu : u ∈ vertexInvariants ρ Vertex.bookOrd)
    (hw : w ∈ vertexInvariants ρ Vertex.bookOrd) :
    (fun _ : G => prod u w) ∈ zeroFlux ρ bookOrd := by
  rw [mem_zeroFlux_iff]
  refine ⟨fun _ => rfl, fun h => ?_⟩
  rw [show h = (h.1, h.2) from rfl, pairHom_prod]
  rw [hu h.1, hw h.2]

/-! ### Products as lists -/

/-- The product of a list at `x` and a list at `y`: the mask of `y` shifted by six bits. -/
def tensorV (u w : Vec) : Vec := u.flatMap fun p => w.map fun q => (64 * q.1 + p.1, p.2 * q.2)

theorem decode_tensor {k₁ : ℕ} (hk : k₁ < 64) (k₂ : ℕ) :
    decode code (64 * k₂ + k₁) = (decode Vertex.code k₁).disjSum (decode Vertex.code k₂) := by
  ext m
  rcases m with m | m
  · simp only [mem_decode, Finset.inl_mem_disjSum]
    have h := Nat.testBit_two_pow_mul_add k₂ (i := 6) (by norm_num; omega) (code (Sum.inl m))
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
    rw [h, ite_eq_left]
    · rfl
    · exact Vertex.code_lt m
  · simp only [mem_decode, Finset.inr_mem_disjSum]
    have h := Nat.testBit_two_pow_mul_add k₂ (i := 6) (by norm_num; omega) (code (Sum.inr m))
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
    rw [h, ite_eq_right]
    · simp [code]
    · simp [code]

theorem prod_ket_toFock {k : ℕ} (hk : k < 64) (w : Vec) :
    prod (Fock.ket (decode Vertex.code k)) (Vec.toFock Vertex.code w) =
      Vec.toFock code (w.map fun q => (64 * q.1 + k, q.2)) := by
  induction w with
  | nil => funext n; simp [prod, Vec.toFock]
  | cons q w ih =>
    rw [Vec.toFock_cons, prod_add_right, ih, List.map_cons, Vec.toFock_cons, prod_smul_right,
      prod_ket, decode_tensor hk]

theorem prod_toFock (u w : Vec) (hu : ∀ p ∈ u, p.1 < 64) :
    prod (Vec.toFock Vertex.code u) (Vec.toFock Vertex.code w) = Vec.toFock code (tensorV u w) := by
  induction u with
  | nil => funext n; simp [prod, Vec.toFock, tensorV]
  | cons p u ih =>
    have e : tensorV (p :: u) w =
        Vec.smul p.2 (w.map fun q => (64 * q.1 + p.1, q.2)) ++ tensorV u w := by
      simp only [tensorV, List.flatMap_cons, Vec.smul, List.map_map, Function.comp_def]
    rw [Vec.toFock_cons, prod_add_left, prod_smul_left, prod_ket_toFock (hu p List.mem_cons_self),
      ih (fun q hq => hu q (List.mem_cons_of_mem _ hq)), e, Vec.toFock_append, Vec.toFock_smul]

/-! ### The product bases -/

/-- The place `(a, b)` of the product numbered `8 a + b`. -/
def pairOf (j : Fin 64) : Fin 8 × Fin 8 := (⟨j / 8, by omega⟩, ⟨j % 8, by omega⟩)

/-- The place `(a, b)` of the product of the six numbered `6 a + b`. -/
def pairOf36 (j : Fin 36) : Fin 6 × Fin 6 := (⟨j / 6, by omega⟩, ⟨j % 6, by omega⟩)

/-- The sixty-four products of the eight states, numbered `8 a + b`. -/
noncomputable def B64 (j : Fin 64) : Finset (Mode (Fin 3) (Fin 2)) → ℂ := eightProd (pairOf j)

/-- The thirty-six products of the six states, numbered `6 a + b`. -/
noncomputable def B36 (j : Fin 36) : Finset (Mode (Fin 3) (Fin 2)) → ℂ := sixProd (pairOf36 j)

/-- The product numbered `j` as a list. -/
def basisVec (j : ℕ) : Vec :=
  tensorV (Vertex.eightVec ⟨j / 8 % 8, Nat.mod_lt _ (by norm_num)⟩)
    (Vertex.eightVec ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩)

/-- The state numbered `a` among the six, as a list. -/
def sixVec (a : ℕ) : Vec := Vertex.eightVec (Vertex.sixToEight ⟨a % 6, Nat.mod_lt _ (by norm_num)⟩)

/-- The product of the six numbered `j` as a list. -/
def basisVec36 (j : ℕ) : Vec := tensorV (sixVec (j / 6)) (sixVec (j % 6))

theorem eightVec_lt : ∀ i : Fin 8, ∀ p ∈ Vertex.eightVec i, p.1 < 64 := by decide

theorem B64_eq (j : Fin 64) : B64 j = Vec.toFock code (basisVec j) := by
  rw [B64, eightProd, Vertex.eight_eq, Vertex.eight_eq, prod_toFock _ _ (eightVec_lt _)]
  congr 3
  simp only [pairOf, Fin.mk.injEq]
  omega

theorem six_toFock (a : Fin 6) :
    Vertex.six Vertex.bookOrd a = Vec.toFock Vertex.code (sixVec a) := by
  rw [Vertex.six_eq, Vertex.eight_eq, sixVec]
  congr 3
  exact Fin.ext (Nat.mod_eq_of_lt a.2).symm

theorem sixVec_lt (a : ℕ) : ∀ p ∈ sixVec a, p.1 < 64 := eightVec_lt _

theorem B36_eq (j : Fin 36) : B36 j = Vec.toFock code (basisVec36 j) := by
  rw [B36, sixProd, pairOf36, six_toFock, six_toFock, prod_toFock _ _ (sixVec_lt _)]
  rfl

/-- The pivot masks of the products. -/
def pivot64 (j : ℕ) : ℕ := 64 * Vertex.pivot ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩ +
  Vertex.pivot ⟨j / 8 % 8, Nat.mod_lt _ (by norm_num)⟩

theorem pivot64_spec : ∀ i j : Fin 64,
    Vec.sumAt 12 (pivot64 j) (basisVec i) = 0 ↔ i ≠ j := by
  decide +kernel

theorem B64_linearIndependent : LinearIndependent ℂ B64 := by
  have h := Vec.linearIndependent numbering (fun j : Fin 64 => basisVec j)
    (fun j => pivot64 j) (fun j => by revert j; decide) pivot64_spec
  convert h using 1
  funext j
  exact B64_eq j

/-- The pivot masks of the products of the six. -/
def pivot36 (j : ℕ) : ℕ :=
  64 * Vertex.pivot (Vertex.sixToEight ⟨j % 6 % 6, Nat.mod_lt _ (by norm_num)⟩) +
    Vertex.pivot (Vertex.sixToEight ⟨j / 6 % 6, Nat.mod_lt _ (by norm_num)⟩)

theorem pivot36_spec : ∀ i j : Fin 36,
    Vec.sumAt 12 (pivot36 j) (basisVec36 i) = 0 ↔ i ≠ j := by
  decide +kernel

theorem B36_linearIndependent : LinearIndependent ℂ B36 := by
  have h := Vec.linearIndependent numbering (fun j : Fin 36 => basisVec36 j)
    (fun j => pivot36 j) (fun j => by revert j; decide) pivot36_spec
  convert h using 1
  funext j
  exact B36_eq j

/-! ### The zero-flux sectors -/

/-- A coefficient table placed at every link value: a constant state. -/
def constLin (G : Type*) :
    (Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) (Fin 2)) → ℂ) :=
  LinearMap.pi fun _ => LinearMap.id

theorem constLin_apply (G : Type*) (v : Finset (Mode (Fin 3) (Fin 2)) → ℂ) :
    constLin G v = fun _ => v := rfl

theorem constLin_injective (G : Type*) [Group G] : Function.Injective (constLin G) :=
  fun _ _ h => congrFun h (1 : G)

/-- Coefficients over the sixty-four products, to the coefficient table they combine. -/
noncomputable def Φ64 : (Fin 64 → ℂ) →ₗ[ℂ] (Finset (Mode (Fin 3) (Fin 2)) → ℂ) :=
  Fintype.linearCombination ℂ B64

/-- Coefficients over the thirty-six products of the six, to the coefficient table. -/
noncomputable def Φ36 : (Fin 36 → ℂ) →ₗ[ℂ] (Finset (Mode (Fin 3) (Fin 2)) → ℂ) :=
  Fintype.linearCombination ℂ B36

theorem injective_of_li {n : ℕ} {v : Fin n → Finset (Mode (Fin 3) (Fin 2)) → ℂ}
    (hv : LinearIndependent ℂ v) : Function.Injective (Fintype.linearCombination ℂ v) := by
  intro a b h
  have h' : ∑ i, (a - b) i • v i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← Fintype.linearCombination_apply, ← Fintype.linearCombination_apply, h, sub_self]
  funext i
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hv _ h' i)

theorem Φ64_injective : Function.Injective Φ64 := injective_of_li B64_linearIndependent

theorem Φ36_injective : Function.Injective Φ36 := injective_of_li B36_linearIndependent

theorem finrank_zeroFlux_sq [Finite G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    Module.finrank ℂ ↥(zeroFlux ρ bookOrd) =
      Module.finrank ℂ ↥(vertexInvariants ρ Vertex.bookOrd) ^ 2 := by
  have := Fintype.ofFinite G
  apply Nat.cast_injective (R := ℂ)
  push_cast
  rw [finrank_zeroFlux, finrank_vertexInvariants, Fintype.card_fin, sq]

/-- A zero-flux sector spanned by products: `n` independent constant states inside a sector of
dimension `n`. -/
theorem range_eq_zeroFlux [Finite G] {n : ℕ} (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (Φ : (Fin n → ℂ) →ₗ[ℂ] (Finset (Mode (Fin 3) (Fin 2)) → ℂ)) (hΦ : Function.Injective Φ)
    (hmem : ∀ a, (fun _ : G => Φ a) ∈ zeroFlux ρ bookOrd)
    (hdim : Module.finrank ℂ ↥(zeroFlux ρ bookOrd) = n) :
    LinearMap.range (constLin G ∘ₗ Φ) = zeroFlux ρ bookOrd := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact hmem a
  · rw [LinearMap.finrank_range_of_inj (fun a b h => hΦ (constLin_injective G h)),
      Module.finrank_fin_fun, hdim]

theorem mem_zeroFlux_of_invariants (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) {n : ℕ}
    {v : Fin n → Finset (Mode (Fin 3) (Fin 2)) → ℂ}
    (hv : ∀ i, (fun _ : G => v i) ∈ zeroFlux ρ bookOrd) (a : Fin n → ℂ) :
    (fun _ : G => Fintype.linearCombination ℂ v a) ∈ zeroFlux ρ bookOrd := by
  rw [Fintype.linearCombination_apply]
  have : (fun _ : G => ∑ i, a i • v i) = ∑ i, a i • (fun _ : G => v i) := by
    funext U
    simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv i)

/-- The products of the eight are zero-flux states for a group fixing the eight. -/
theorem B64_mem (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (h8 : ∀ i, Vertex.eight Vertex.bookOrd i ∈ vertexInvariants ρ Vertex.bookOrd) (j : Fin 64) :
    (fun _ : G => B64 j) ∈ zeroFlux ρ bookOrd :=
  const_prod_mem_zeroFlux ρ (h8 _) (h8 _)

/-- The products of the six are zero-flux states for a group fixing the six. -/
theorem B36_mem (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (h6 : ∀ i, Vertex.six Vertex.bookOrd i ∈ vertexInvariants ρ Vertex.bookOrd) (j : Fin 36) :
    (fun _ : G => B36 j) ∈ zeroFlux ρ bookOrd :=
  const_prod_mem_zeroFlux ρ (h6 _) (h6 _)

theorem eight_mem_cube (i : Fin 8) :
    Vertex.eight Vertex.bookOrd i ∈ vertexInvariants cubeTriplet Vertex.bookOrd := by
  rw [← Vertex.cube_span]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem eight_mem_ico (i : Fin 8) :
    Vertex.eight Vertex.bookOrd i ∈ vertexInvariants icoTriplet Vertex.bookOrd := by
  rw [← Vertex.ico_span]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The zero-flux sector of Model I: the constant states over the span of the sixty-four
products. -/
theorem zeroFlux_cube :
    LinearMap.range (constLin cubeGroup ∘ₗ Φ64) = zeroFlux cubeTriplet bookOrd :=
  range_eq_zeroFlux cubeTriplet Φ64 Φ64_injective
    (mem_zeroFlux_of_invariants cubeTriplet (B64_mem cubeTriplet eight_mem_cube))
    (by rw [finrank_zeroFlux_sq, Vertex.cube_finrank]; norm_num)

/-- The zero-flux sector of Model II: the constant states over the span of the sixty-four
products. -/
theorem zeroFlux_ico :
    LinearMap.range (constLin icoGroup ∘ₗ Φ64) = zeroFlux icoTriplet bookOrd :=
  range_eq_zeroFlux icoTriplet Φ64 Φ64_injective
    (mem_zeroFlux_of_invariants icoTriplet (B64_mem icoTriplet eight_mem_ico))
    (by rw [finrank_zeroFlux_sq, Vertex.ico_finrank]; norm_num)

theorem six_mem {H : Type*} [Group H] (ρ : H →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ h, ρ h ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (i : Fin 6) :
    Vertex.six Vertex.bookOrd i ∈ vertexInvariants ρ Vertex.bookOrd := fun h =>
  Vertex.gamma_six Vertex.bookOrd (hρ h) i

/-- The zero-flux sector of Refinement I: the constant states over the span of the thirty-six
products of the six. -/
theorem zeroFlux_c3a5 :
    LinearMap.range (constLin C3A5 ∘ₗ Φ36) = zeroFlux c3a5Triplet bookOrd :=
  range_eq_zeroFlux c3a5Triplet Φ36 Φ36_injective
    (mem_zeroFlux_of_invariants c3a5Triplet
      (B36_mem c3a5Triplet (six_mem c3a5Triplet Vertex.c3a5Triplet_mem)))
    (by rw [finrank_zeroFlux_sq, ← Vertex.c3a5_span, Vertex.finrank_span_six]; norm_num)

/-- The zero-flux sector of Refinement II: the constant states over the span of the thirty-six
products of the six. -/
theorem zeroFlux_valentiner :
    LinearMap.range (constLin valentiner ∘ₗ Φ36) = zeroFlux valentinerTriplet bookOrd :=
  range_eq_zeroFlux valentinerTriplet Φ36 Φ36_injective
    (mem_zeroFlux_of_invariants valentinerTriplet
      (B36_mem valentinerTriplet (six_mem valentinerTriplet Vertex.valentinerTriplet_mem)))
    (by rw [finrank_zeroFlux_sq, ← Vertex.valentiner_span, Vertex.finrank_span_six]; norm_num)

/-- The zero-flux sector of `SU(3)`: the constant states over the span of the thirty-six
products of the six. Every zero-flux state of `SU(3)` is one of `C₃ × A₅`, a subgroup. -/
theorem zeroFlux_su3 :
    LinearMap.range (constLin (Matrix.specialUnitaryGroup (Fin 3) ℂ) ∘ₗ Φ36) =
      zeroFlux su3Triplet bookOrd := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact mem_zeroFlux_of_invariants su3Triplet (B36_mem su3Triplet (six_mem su3Triplet
      (fun g => g.2))) a
  · intro ψ hψ
    rw [mem_zeroFlux_iff] at hψ
    have hc : (fun _ : C3A5 => ψ 1) ∈ zeroFlux c3a5Triplet bookOrd := by
      rw [mem_zeroFlux_iff]
      exact ⟨fun _ => rfl, fun h => hψ.2 (C3A5.triplet h.1, C3A5.triplet h.2)⟩
    rw [← zeroFlux_c3a5] at hc
    obtain ⟨a, ha⟩ := hc
    refine ⟨a, ?_⟩
    funext U
    rw [hψ.1 U]
    exact congrFun ha 1

end Edge

end Artform
