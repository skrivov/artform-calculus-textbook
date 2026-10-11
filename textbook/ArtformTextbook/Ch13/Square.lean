import Mathlib.GroupTheory.CommutingProbability
import Mathlib.GroupTheory.GroupAction.CardCommute
import ArtformTextbook.Ch11.ThereAndBack
import ArtformTextbook.Ch11.Averaging
import ArtformTextbook.Ch13.Statements.Square

/-!
# The empty square (Proposition 13.5, Theorem 13.6)

* **Gauge fixing.** The gauge change `h_{x₀} = 1`, `h_{x₁} = U₄U₃U₂`, `h_{x₂} = U₄U₃`,
  `h_{x₃} = U₄` carries the links to `F` on the first link and `1` on the others
  (`EmptySquare.gaugeAct_fix`), and a gauge change multiplies `F` by `h_{x₀}` on both sides
  (`EmptySquare.face_gaugeAct`). So a colourless state is `U ↦ f(F)` with `f(g)` its value at the
  table with `g` on the first link, and `f` is a class function; every class function gives one
  (`EmptySquare.stateEquiv`).
* **Two bases.** The class indicators and, for a complete family, the characters are bases of the
  class functions: the indicators by their supports, the characters because they are orthonormal
  (Proposition 11.5) and span (Theorem 11.6). Carried to the states they give the two bases of the
  square.
* **Energies.** On each link the character `χ_ρ(F)` is a table `g ↦ χ_ρ(a g b) = Tr(ρ(b a) ρ(g))`
  in the block of `ρ`, which the convolution of Definition 11.9 multiplies by `E(ρ)`; four links
  give `4E(ρ)`. `B_U` multiplies a class indicator by its value on the class.
* **The tensor matrix.** By Proposition 11.5 and the character of a tensor product,
  `N_{ρσ} = ⟨χ_ρ, χ χ_σ⟩` and `N_{σρ} = ⟨χ_ρ, χ̄ χ_σ⟩`; expanding the class function
  `(3 - Re χ) χ_σ` in the orthonormal characters gives `B`, and `χ χ_ρ = Σ_σ N_{σρ} χ_σ`,
  `χ̄ χ_ρ = Σ_σ N_{ρσ} χ_σ` give the eigenvectors.
* **The four models.** A group with `k` classes has `k |G|` commuting pairs: `120 = 5 · 24` for the
  cube group and `300 = 5 · 60` for the icosahedral group; `C₃ × A₅` has `3 · 5` classes and
  Valentiner's group the seventeen of its class table. The cube's table `N` is the pairing
  `⟨χ_b, χ χ_{b'}⟩` of the rows of `fig:mt-s4-characters`, an exact sum over the twenty-four
  rotations. A complete family of the cube group carries the five characters of the table
  (`EmptySquare.exists_labelling`): the trivial representation, the sign, the triplet and the sign
  times the triplet have characters of norm one, so each is the character of a member, and the
  tensor square of the triplet, `1 + 2 + 3_s + 3_r`, leaves the fifth member the character `2`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

namespace EmptySquare

open ColourGroups

variable {G : Type*} [Group G]

/-! ### The holonomy of the face -/

theorem face_eq (U : squareCanvas.skeleton.LinkTable G) :
    face U = U ((3 : Fin 4), true) * U ((2 : Fin 4), true) * U ((1 : Fin 4), true) *
      U ((0 : Fin 4), true) := by
  simp [face, Canvas.curvature, mul_assoc]

theorem linkTable_ext {U V : squareCanvas.skeleton.LinkTable G}
    (h : ∀ e : Fin 4, U (e, true) = V (e, true)) : U = V := by
  cases U with
  | mk u hu =>
  cases V with
  | mk v hv =>
  congr
  funext ⟨e, b⟩
  cases b
  · have h1 := hu (e, true)
    have h2 := hv (e, true)
    change u (e, false) = (u (e, true))⁻¹ at h1
    change v (e, false) = (v (e, true))⁻¹ at h2
    rw [h1, h2]
    exact congrArg (·⁻¹) (h e)
  · exact h e

/-- A gauge change conjugates the holonomy of the face by its value at `x₀`. -/
theorem face_gaugeAct (h : squareCanvas.V → G) (U : squareCanvas.skeleton.LinkTable G) :
    face (Skeleton.gaugeAct h U) = h 0 * face U * (h 0)⁻¹ := by
  rw [face_eq, face_eq]
  simp only [Skeleton.gaugeAct]
  change h (3 + 1) * U ((3 : Fin 4), true) * (h 3)⁻¹ * (h (2 + 1) * U ((2 : Fin 4), true) *
    (h 2)⁻¹) * (h (1 + 1) * U ((1 : Fin 4), true) * (h 1)⁻¹) *
      (h (0 + 1) * U ((0 : Fin 4), true) * (h 0)⁻¹) = _
  rw [show (3 + 1 : Fin 4) = 0 from rfl, show (2 + 1 : Fin 4) = 3 from rfl,
    show (1 + 1 : Fin 4) = 2 from rfl, show (0 + 1 : Fin 4) = 1 from rfl]
  group

theorem gaugeAct_apply_true (h : squareCanvas.V → G) (U : squareCanvas.skeleton.LinkTable G)
    (e : Fin 4) : Skeleton.gaugeAct h U (e, true) = h (e + 1) * U (e, true) * (h e)⁻¹ := rfl

theorem squareTable_apply (g : G) (e : Fin 4) :
    squareTable g (e, true) = if e = 0 then g else 1 := rfl

theorem face_squareTable (g : G) : face (squareTable g) = g := by
  rw [face_eq, squareTable_apply, squareTable_apply, squareTable_apply, squareTable_apply]
  simp

/-- **Gauge fixing on the square**: `h_{x₀} = 1`, `h_{x₁} = U₄U₃U₂`, `h_{x₂} = U₄U₃`, `h_{x₃} = U₄`
carry the links to `F` on the first link and `1` on the others. -/
theorem gaugeAct_fix (U : squareCanvas.skeleton.LinkTable G) :
    Skeleton.gaugeAct (![1, U ((3 : Fin 4), true) * U ((2 : Fin 4), true) * U ((1 : Fin 4), true),
      U ((3 : Fin 4), true) * U ((2 : Fin 4), true), U ((3 : Fin 4), true)] : Fin 4 → G) U =
      squareTable (face U) := by
  refine linkTable_ext fun e => ?_
  rw [gaugeAct_apply_true, squareTable_apply, face_eq]
  fin_cases e <;> simp

/-- A constant gauge change conjugates the value on the first link. -/
theorem gaugeAct_const_squareTable (k g : G) :
    Skeleton.gaugeAct (fun _ : squareCanvas.V => k) (squareTable g) =
      squareTable (k * g * k⁻¹) := by
  refine linkTable_ext fun e => ?_
  change k * squareTable g (e, true) * k⁻¹ = _
  rw [squareTable_apply, squareTable_apply]
  split_ifs <;> group

/-! ### Colourless states are class functions of `F` -/

/-- A colourless state takes at `U` its value at the table with `F` on the first link. -/
theorem eq_face {ψ : squareCanvas.skeleton.LinkTable G → ℂ}
    (hψ : ψ ∈ squareCanvas.gaugeInvariants G) (U : squareCanvas.skeleton.LinkTable G) :
    ψ U = ψ (squareTable (face U)) := by
  rw [← gaugeAct_fix U]
  exact (hψ _ U).symm

/-- **`f ↦ (U ↦ f(F))`**, a linear isomorphism from the class functions onto the colourless
states of the square; its inverse reads a state at the tables with `g` on the first link. -/
def stateEquiv : ↥(classFunctions G) ≃ₗ[ℂ] ↥(squareCanvas.gaugeInvariants G) where
  toFun f := ⟨fun U => (f : G → ℂ) (face U), fun h U => by
    change (f : G → ℂ) (face (Skeleton.gaugeAct h U)) = (f : G → ℂ) (face U)
    rw [face_gaugeAct]
    exact f.2 (h 0) (face U)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ := ⟨fun g => (ψ : squareCanvas.skeleton.LinkTable G → ℂ) (squareTable g), fun k g => by
    change (ψ : squareCanvas.skeleton.LinkTable G → ℂ) (squareTable (k * g * k⁻¹)) =
      (ψ : squareCanvas.skeleton.LinkTable G → ℂ) (squareTable g)
    rw [← gaugeAct_const_squareTable]
    exact ψ.2 _ _⟩
  left_inv f := Subtype.ext (funext fun g => by
    change (f : G → ℂ) (face (squareTable g)) = _
    rw [face_squareTable])
  right_inv ψ := Subtype.ext (funext fun U => (eq_face ψ.2 U).symm)

theorem stateEquiv_apply (f : ↥(classFunctions G)) (U : squareCanvas.skeleton.LinkTable G) :
    (stateEquiv f : squareCanvas.skeleton.LinkTable G → ℂ) U = (f : G → ℂ) (face U) := rfl

/-! ### Two bases of the class functions -/

/-- A class function takes the same value on conjugate elements. -/
theorem classFun_eq {f : G → ℂ} (hf : f ∈ classFunctions G) {a b : G} (hab : IsConj a b) :
    f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  exact (hf c a).symm

theorem isConj_out (g : G) : IsConj g (ConjClasses.mk g).out :=
  ConjClasses.mk_eq_mk_iff_isConj.mp (Quotient.out_eq (ConjClasses.mk g)).symm

open Classical in
/-- The indicator of a class, as a class function. -/
noncomputable def ind (c : ConjClasses G) : ↥(classFunctions G) :=
  ⟨fun g => if ConjClasses.mk g = c then 1 else 0, fun h U => by
    change (if ConjClasses.mk (h * U * h⁻¹) = c then (1 : ℂ) else 0) =
      if ConjClasses.mk U = c then 1 else 0
    rw [show ConjClasses.mk (h * U * h⁻¹) = ConjClasses.mk U from
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)]⟩

theorem ind_apply_self (g : G) : (ind (ConjClasses.mk g) : G → ℂ) g = 1 :=
  ite_eq_left rfl

omit [Group G] in
/-- A family of tables is independent when each has a point where it alone is not zero. -/
theorem linearIndependent_of_points {ι β : Type*} (v : ι → β → ℂ) (p : ι → β)
    (hoff : ∀ i j, i ≠ j → v i (p j) = 0) (hdiag : ∀ i, v i (p i) ≠ 0) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have h := congrFun hc (p j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hoff i j hij, mul_zero])
    (fun h' => absurd hj h')] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag j)

open Classical in
theorem ind_out (c c' : ConjClasses G) :
    (ind c : G → ℂ) c'.out = if c' = c then 1 else 0 := by
  change (if ConjClasses.mk c'.out = c then (1 : ℂ) else 0) = _
  rw [show ConjClasses.mk c'.out = c' from Quotient.out_eq c']

theorem ind_linearIndependent : LinearIndependent ℂ (ind (G := G)) := by
  refine LinearIndependent.of_comp (classFunctions G).subtype ?_
  refine linearIndependent_of_points _ (fun c => c.out) (fun c c' hcc' => ?_) (fun c => ?_)
  · change (ind c : G → ℂ) c'.out = 0
    rw [ind_out, ite_eq_right (Ne.symm hcc')]
  · change (ind c : G → ℂ) c.out ≠ 0
    rw [ind_out, ite_eq_left rfl]
    exact one_ne_zero

/-- A class function is the sum of its values times the class indicators. -/
theorem eq_sum_ind [Fintype (ConjClasses G)] (f : ↥(classFunctions G)) :
    f = ∑ c, (f : G → ℂ) c.out • ind c := by
  classical
  refine Subtype.ext (funext fun g => ?_)
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  change (f : G → ℂ) g = ∑ c, (f : G → ℂ) c.out * (if ConjClasses.mk g = c then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact classFun_eq f.2 (isConj_out g)

/-- The class indicators span the class functions. -/
theorem ind_span [Finite G] : ⊤ ≤ Submodule.span ℂ (Set.range (ind (G := G))) := by
  classical
  have := Fintype.ofFinite (ConjClasses G)
  intro f _
  rw [eq_sum_ind f]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

/-- The magnetic basis of the class functions: the class indicators. -/
noncomputable def indBasis [Finite G] : Module.Basis (ConjClasses G) ℂ ↥(classFunctions G) :=
  Module.Basis.mk ind_linearIndependent ind_span

/-! ### The electric basis: characters of a complete family -/

section Characters

variable {G : Type} [Group G] {ι : Type} {d : ι → ℕ} {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}

/-- The character of a representation, as a class function. -/
noncomputable def chi {V : Type*} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) :
    ↥(classFunctions G) :=
  ⟨τ.character, Blocks.isClassFunction_character τ⟩

open Classical in
/-- The characters of a complete family are orthonormal (Proposition 11.5). -/
theorem orth [Fintype G] (hσ : IsCompleteFamily σ) (i j : ι) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, (σ i).character g * conj ((σ j).character g) =
      if i = j then 1 else 0 := by
  rw [Blocks.sum_char_mul_conj_char σ hσ.1 hσ.2.1 i j]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · rw [mul_zero]

/-- The pairing of a character with a combination of the characters picks its coefficient. -/
theorem pair_sum [Fintype G] [Fintype ι] (hσ : IsCompleteFamily σ) (c : ι → ℂ) (j : ι) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, (∑ i, c i * (σ i).character g) * conj ((σ j).character g) =
      c j := by
  classical
  have h1 : ∑ g, (∑ i, c i * (σ i).character g) * conj ((σ j).character g) =
      ∑ i, c i * ∑ g, (σ i).character g * conj ((σ j).character g) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => by rw [mul_left_comm, orth hσ]]
  simp

theorem chi_linearIndependent [Finite G] [Finite ι] (hσ : IsCompleteFamily σ) :
    LinearIndependent ℂ (fun i => chi (σ i)) := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h : ∀ g, ∑ i, c i * (σ i).character g = 0 := fun g => by
    have := congrFun (congrArg Subtype.val hc) g
    simpa [chi] using this
  rw [← pair_sum hσ c j]
  simp [h]

/-- The characters of a complete family span the class functions (Theorem 11.6). -/
theorem chi_span [Finite G] [Finite ι] (hσ : IsCompleteFamily σ) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => chi (σ i)) := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  intro f _
  obtain ⟨r, hr⟩ := Blocks.exists_eq_charComb σ hσ.1 hσ.2.1 hσ.2.2 f.2
  have hf : f = ∑ i, ((Fintype.card G : ℂ)⁻¹ * r i * d i) • chi (σ i) := by
    refine Subtype.ext (funext fun g => ?_)
    rw [Submodule.coe_sum, Finset.sum_apply, hr]
    simp only [Blocks.charComb, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, chi,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hf]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The electric basis of the class functions: the characters of a complete family. -/
noncomputable def charBasis [Finite G] [Finite ι] (hσ : IsCompleteFamily σ) :
    Module.Basis ι ℂ ↥(classFunctions G) :=
  Module.Basis.mk (chi_linearIndependent hσ) (chi_span hσ)

/-- A class function is the sum of the characters, each with its pairing with the function. -/
theorem eq_sum_pair [Fintype G] [Fintype ι] (hσ : IsCompleteFamily σ) {f : G → ℂ}
    (hf : f ∈ classFunctions G) :
    f = ∑ r, ((Fintype.card G : ℂ)⁻¹ * ∑ g, f g * conj ((σ r).character g)) •
      (σ r).character := by
  have hspan := chi_span hσ (Submodule.mem_top (x := ⟨f, hf⟩))
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨c, hc⟩ := hspan
  have hfun : f = fun g => ∑ i, c i * (σ i).character g := by
    funext g
    have := congrFun (congrArg Subtype.val hc) g
    simpa [chi] using this.symm
  have hcoef : ∀ r, (Fintype.card G : ℂ)⁻¹ * ∑ g, f g * conj ((σ r).character g) = c r := by
    intro r
    rw [hfun]
    exact pair_sum hσ c r
  simp only [hcoef]
  funext g
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact congrFun hfun g

end Characters

/-! ### The electric energy on the characters -/

theorem setLink_apply (U : squareCanvas.skeleton.LinkTable G) (j : Fin 4) (g : G) (e : Fin 4) :
    squareCanvas.setLink U j g (e, true) = if e = j then g else U (e, true) := by
  change Function.update (fun e' => U (e', true)) j g e = _
  rw [Function.update_apply]

theorem setLink_self (U : squareCanvas.skeleton.LinkTable G) (j : Fin 4) :
    squareCanvas.setLink U j (U (j, true)) = U := by
  refine linkTable_ext fun e => ?_
  rw [setLink_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- With the other links fixed, the holonomy is `a g b` in the value `g` of one link. -/
theorem face_setLink (U : squareCanvas.skeleton.LinkTable G) (j : Fin 4) :
    ∃ a b : G, ∀ g, face (squareCanvas.setLink U j g) = a * g * b := by
  fin_cases j
  · exact ⟨U ((3 : Fin 4), true) * U ((2 : Fin 4), true) * U ((1 : Fin 4), true), 1, fun g => by
      rw [face_eq, setLink_apply, setLink_apply, setLink_apply, setLink_apply]
      simp⟩
  · exact ⟨U ((3 : Fin 4), true) * U ((2 : Fin 4), true), U ((0 : Fin 4), true), fun g => by
      rw [face_eq, setLink_apply, setLink_apply, setLink_apply, setLink_apply]
      simp⟩
  · exact ⟨U ((3 : Fin 4), true), U ((1 : Fin 4), true) * U ((0 : Fin 4), true), fun g => by
      rw [face_eq, setLink_apply, setLink_apply, setLink_apply, setLink_apply]
      simp [mul_assoc]⟩
  · exact ⟨1, U ((2 : Fin 4), true) * U ((1 : Fin 4), true) * U ((0 : Fin 4), true), fun g => by
      rw [face_eq, setLink_apply, setLink_apply, setLink_apply, setLink_apply]
      simp [mul_assoc]⟩

/-- **Every link in block `ρ`**: with the other links fixed, `χ_ρ(F)` is a table over the value
of the link in the block of `ρ`, `g ↦ χ_ρ(a g b) = Tr(ρ(b a) ρ(g))`. -/
theorem charState_setLink_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (U : squareCanvas.skeleton.LinkTable G) (j : Fin 4) :
    (fun g => charState τ (squareCanvas.setLink U j g)) ∈ block τ := by
  obtain ⟨a, b, hab⟩ := face_setLink U j
  refine mem_block.mpr ⟨τ (b * a), funext fun g => ?_⟩
  change LinearMap.trace ℂ V (τ (b * a) * τ g) = τ.character (face (squareCanvas.setLink U j g))
  rw [hab, Representation.char_mul_comm τ b (a * g), ← map_mul, mul_assoc]
  rfl

section Electric

variable {G : Type} [Group G] [Fintype G] {ι : Type} [Fintype ι] {d : ι → ℕ}
  {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}

theorem tableConv_eq_convolution (k ψ : G → ℂ) : tableConv k ψ = convolution k *ᵥ ψ := by
  funext V
  rw [Blocks.convolution_mulVec_apply, Blocks.sum_conv_eq_sum_leftWrite, Edge.tableConv_apply]
  simp only [leftWrite_apply, smul_eq_mul]

/-- The electric energy of Definition 11.9 multiplies the block of `σ i` by `E(σ i)`. -/
theorem electricEnergy_block (hσ : IsCompleteFamily σ) (E : ι → ℚ) (i : ι) {f : G → ℂ}
    (hf : f ∈ block (σ i)) : electricEnergy σ E f = (E i : ℂ) • f := by
  rw [electricEnergy, ThereAndBack.energyKernel_eq_charComb, tableConv_eq_convolution,
    Blocks.convolution_charComb σ hσ.1 hσ.2.1 _ i hf]

theorem onLink_charState (hσ : IsCompleteFamily σ) (E : ι → ℚ) (i : ι) (j : Fin 4) :
    squareCanvas.onLink (electricEnergy σ E) j (charState (σ i)) =
      (E i : ℂ) • charState (σ i) := by
  funext U
  change electricEnergy σ E (fun g => charState (σ i) (squareCanvas.setLink U j g))
    (U (j, true)) = _
  rw [electricEnergy_block hσ E i (charState_setLink_mem (σ i) U j), Pi.smul_apply,
    Pi.smul_apply, setLink_self]

/-- **The electric energy is diagonal on the characters**, with the value `4κE(ρ)`. -/
theorem electric_charState (hσ : IsCompleteFamily σ) (E : ι → ℚ) (κ : ℝ) (i : ι) :
    (κ : ℂ) • electric (electricEnergy σ E) (charState (σ i)) =
      ((4 * κ * (E i : ℝ) : ℝ) : ℂ) • charState (σ i) := by
  have h : electric (electricEnergy σ E) (charState (σ i)) =
      (4 * (E i : ℂ)) • charState (σ i) := by
    simp only [electric, onLink_charState hσ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  rw [h, smul_smul]
  congr 1
  push_cast
  ring

end Electric

/-! ### The magnetic term on the class indicators -/

theorem trace_isConj (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) {a b : G} (h : IsConj a b) :
    (ρ a).trace = (ρ b).trace := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  rw [map_mul, map_mul, Matrix.trace_mul_cycle, ← map_mul, ← map_mul, inv_mul_cancel, one_mul]

/-- **`B_U` is diagonal on the class indicators**, with the value `β(3 - Re χ(C))`. -/
theorem magnetic_classState (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (β : ℝ) (c : ConjClasses G)
    (g : G) (hg : ConjClasses.mk g = c) :
    magnetic ρ β (classState c) = ((β * (3 - (ρ g).trace.re) : ℝ) : ℂ) • classState c := by
  classical
  funext U
  simp only [magnetic, classState, Pi.smul_apply, smul_eq_mul]
  split_ifs with hU
  · rw [trace_isConj ρ (ConjClasses.mk_eq_mk_iff_isConj.mp (hU.trans hg.symm))]
  · rw [mul_zero, mul_zero]

/-- **The character table is the change of basis**: `χ_ρ(F) = Σ_C χ_ρ(g_C) 1_C(F)`. -/
theorem charState_eq_sum [Fintype (ConjClasses G)] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (g : ConjClasses G → G) (hg : ∀ c, ConjClasses.mk (g c) = c) :
    charState τ = ∑ c, τ.character (g c) • classState c := by
  classical
  funext U
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, classState, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact classFun_eq (Blocks.isClassFunction_character τ)
    (ConjClasses.mk_eq_mk_iff_isConj.mp (hg _).symm)

/-! ### The number of classes of the four models -/

section Classes

open Exact

/-- The number of classes from the number of commuting pairs, `|{(g, h) : gh = hg}| = k |G|`. -/
theorem card_conjClasses_of {H : Type*} [Group H] {n m : ℕ} (hn : 0 < n) (hH : Nat.card H = n)
    (hc : Nat.card {p : H × H // Commute p.1 p.2} = m * n) : Nat.card (ConjClasses H) = m := by
  have h := card_comm_eq_card_conjClasses_mul_card H
  rw [hc, hH] at h
  exact (Nat.eq_of_mul_eq_mul_right hn h).symm

theorem cubeElt_commute_iff (k l : Fin 24) :
    Commute (cubeElt k) (cubeElt l) ↔
      M3Z.mul (cubeE k) (cubeE l) = M3Z.mul (cubeE l) (cubeE k) := by
  have hmat : ∀ a b : Fin 24, (((cubeElt a * cubeElt b : cubeGroup) :
      Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
        M3Z.toMat (M3Z.mul (cubeE a) (cubeE b)) := fun a b => by
    rw [M3Z.toMat_mul]
    rfl
  constructor
  · intro h
    apply M3Z.toMat_injective
    rw [← hmat, ← hmat, h.eq]
  · intro h
    change cubeElt k * cubeElt l = cubeElt l * cubeElt k
    apply Subtype.ext
    apply Subtype.ext
    rw [hmat, hmat, h]

theorem cube_commuting : (Finset.univ.filter fun q : Fin 24 × Fin 24 =>
    M3Z.mul (cubeE q.1) (cubeE q.2) = M3Z.mul (cubeE q.2) (cubeE q.1)).card = 120 := by
  decide +kernel

/-- The cube group has five classes. -/
theorem card_conjClasses_cube : Nat.card (ConjClasses cubeGroup) = 5 := by
  refine card_conjClasses_of (n := 24) (by norm_num) card_cubeGroup ?_
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodCongr cubeEquiv cubeEquiv)
    fun q : Fin 24 × Fin 24 => (cubeElt_commute_iff q.1 q.2).symm),
    Nat.card_eq_fintype_card, Fintype.card_subtype, cube_commuting]

theorem icoElt_commute_iff (k l : Fin 60) :
    Commute (icoElt k) (icoElt l) ↔ a5Mul k l = a5Mul l k := by
  change icoElt k * icoElt l = icoElt l * icoElt k ↔ _
  rw [← icoElt_mul, ← icoElt_mul]
  exact icoElt_injective.eq_iff

theorem ico_commuting : (Finset.univ.filter fun q : Fin 60 × Fin 60 =>
    a5Mul q.1 q.2 = a5Mul q.2 q.1).card = 300 := by
  decide +kernel

/-- The icosahedral group has five classes. -/
theorem card_conjClasses_ico : Nat.card (ConjClasses icoGroup) = 5 := by
  refine card_conjClasses_of (n := 60) (by norm_num) card_icoGroup ?_
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodCongr icoEquiv icoEquiv)
    fun q : Fin 60 × Fin 60 => (icoElt_commute_iff q.1 q.2).symm),
    Nat.card_eq_fintype_card, Fintype.card_subtype, ico_commuting]

/-- `C₃ × A₅` has fifteen classes: three times five. -/
theorem card_conjClasses_C3A5 : Nat.card (ConjClasses C3A5) = 15 := by
  have h := commProb_def' C3A5
  rw [commProb_prod, commProb_eq_one, one_mul, commProb_def', card_conjClasses_ico,
    card_icoGroup, card_C3A5] at h
  have h' : (Nat.card (ConjClasses C3A5) : ℚ) = 15 := by
    field_simp at h
    push_cast at h
    linarith
  exact_mod_cast h'

/-- Valentiner's group has seventeen classes. -/
theorem card_conjClasses_valentiner : Nat.card (ConjClasses valentiner) = 17 := by
  rw [Nat.card_congr classEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

end Classes

/-! ### The number of colourless states -/

theorem finrank_states [Finite G] :
    Module.finrank ℂ ↥(squareCanvas.gaugeInvariants G) = Nat.card (ConjClasses G) :=
  (LinearEquiv.finrank_eq stateEquiv).symm.trans (Module.finrank_eq_nat_card_basis indBasis)

/-! ### The tensor matrix (Theorem 13.6) -/

section Tensor

variable {G : Type} [Group G] {ι : Type} {d : ι → ℕ} {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}
  (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)

theorem character_tripletRep (g : G) : (Edge.tripletRep ρ).character g = (ρ g).trace :=
  Matrix.trace_toLin'_eq (ρ g)

theorem trace_conj' (h U : G) : (ρ (h * U * h⁻¹)).trace = (ρ U).trace :=
  trace_isConj ρ (isConj_iff.mpr ⟨h⁻¹, by group⟩)

/-- **`N_{ρσ} = ⟨χ_ρ, χ χ_σ⟩`** (Proposition 11.5 and the character of a tensor product). -/
theorem tensorMult_eq [Fintype G] (hσ : IsCompleteFamily σ) (r s : ι) :
    (tensorMult ρ (σ r) (σ s) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace * (σ s).character g * conj ((σ r).character g) := by
  rw [tensorMult, (mtAverage G).2.2 _ _ ((Edge.tripletRep ρ).tprod (σ s)) (σ r) (hσ.1 r),
    Representation.char_tensor]
  simp only [Pi.mul_apply, character_tripletRep]

/-- `χ`, `χ̄` and their products with a character are class functions. -/
theorem trace_mem : (fun g => (ρ g).trace) ∈ classFunctions G := fun h U => trace_conj' ρ h U

theorem conj_trace_mem : (fun g => conj (ρ g).trace) ∈ classFunctions G := fun h U => by
  change conj (ρ (h * U * h⁻¹)).trace = conj (ρ U).trace
  rw [trace_conj']

theorem classFun_mul_mem {f f' : G → ℂ} (hf : f ∈ classFunctions G)
    (hf' : f' ∈ classFunctions G) : (fun g => f g * f' g) ∈ classFunctions G := fun h U => by
  change f (h * U * h⁻¹) * f' (h * U * h⁻¹) = f U * f' U
  rw [hf h U, hf' h U]

/-- A class function of `F` is the sum of the characters of `F`, each with its pairing. -/
theorem state_eq_sum [Fintype G] [Fintype ι] (hσ : IsCompleteFamily σ) {f : G → ℂ}
    (hf : f ∈ classFunctions G) :
    (fun U : squareCanvas.skeleton.LinkTable G => f (face U)) =
      ∑ r, ((Fintype.card G : ℂ)⁻¹ * ∑ g, f g * conj ((σ r).character g)) • charState (σ r) := by
  funext U
  conv_lhs => rw [eq_sum_pair hσ hf]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, charState]

/-- The conjugate pairing: `⟨χ_ρ, χ̄ χ_σ⟩ = N_{σρ}`. -/
theorem conj_pair [Fintype G] (hσ : IsCompleteFamily σ) (r s : ι) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ρ g).trace * (σ s).character g *
        conj ((σ r).character g) = (tensorMult ρ (σ s) (σ r) : ℂ) := by
  have h := tensorMult_eq ρ hσ s r
  rw [← Complex.conj_natCast (tensorMult ρ (σ s) (σ r)), h, map_mul, map_inv₀,
    Complex.conj_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

open Classical in
/-- **The magnetic term in the electric basis**: `B_U χ_σ(F) = Σ_ρ B_{ρσ} χ_ρ(F)` with
`B_{ρσ} = β(3 δ_{ρσ} - (N_{ρσ} + N_{σρ})/2)`. -/
theorem magnetic_charState [Finite G] [Fintype ι] (hσ : IsCompleteFamily σ) (β : ℝ) (s : ι) :
    magnetic ρ β (charState (σ s)) =
      ∑ r, ((β : ℂ) * (3 * (if r = s then 1 else 0) -
        ((tensorMult ρ (σ r) (σ s) : ℂ) + tensorMult ρ (σ s) (σ r)) / 2)) •
          charState (σ r) := by
  have := Fintype.ofFinite G
  have hf : (fun g => ((β * (3 - (ρ g).trace.re) : ℝ) : ℂ) * (σ s).character g) ∈
      classFunctions G := fun h U => by
    change ((β * (3 - (ρ (h * U * h⁻¹)).trace.re) : ℝ) : ℂ) * (σ s).character (h * U * h⁻¹) =
      ((β * (3 - (ρ U).trace.re) : ℝ) : ℂ) * (σ s).character U
    rw [trace_conj' ρ h U, Blocks.isClassFunction_character (σ s) h U]
  have h1 := state_eq_sum hσ hf
  change (fun U => ((β * (3 - (ρ (face U)).trace.re) : ℝ) : ℂ) * (σ s).character (face U)) = _
  rw [h1]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have hre : ∀ g, (((β * (3 - (ρ g).trace.re) : ℝ) : ℂ)) =
      (β : ℂ) * (3 - ((ρ g).trace + conj (ρ g).trace) / 2) := fun g => by
    rw [← Complex.re_eq_add_conj]
    push_cast
    ring
  simp only [hre]
  have e : ∀ g, (β : ℂ) * (3 - ((ρ g).trace + conj (ρ g).trace) / 2) * (σ s).character g *
      conj ((σ r).character g) = (β : ℂ) * (3 * ((σ s).character g * conj ((σ r).character g)) -
        ((ρ g).trace * (σ s).character g * conj ((σ r).character g) +
          conj (ρ g).trace * (σ s).character g * conj ((σ r).character g)) / 2) :=
    fun g => by ring
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_add_distrib]
  have o := orth hσ s r
  have n1 := tensorMult_eq ρ hσ r s
  have n2 := conj_pair ρ hσ r s
  rw [show (if r = s then (1 : ℂ) else 0) = if s = r then 1 else 0 by
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1]
  rw [← o, n1, ← n2]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- `χ χ_ρ = Σ_σ N_{σρ} χ_σ` at every element. -/
theorem trace_mul_char [Finite G] [Fintype ι] (hσ : IsCompleteFamily σ) (r : ι) (g : G) :
    (ρ g).trace * (σ r).character g =
      ∑ s, (tensorMult ρ (σ s) (σ r) : ℂ) * (σ s).character g := by
  have := Fintype.ofFinite G
  have h := congrFun (eq_sum_pair hσ (classFun_mul_mem (trace_mem ρ)
    (Blocks.isClassFunction_character (σ r)))) g
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, tensorMult_eq ρ hσ]

/-- `χ̄ χ_ρ = Σ_σ N_{ρσ} χ_σ` at every element. -/
theorem conj_trace_mul_char [Finite G] [Fintype ι] (hσ : IsCompleteFamily σ) (r : ι) (g : G) :
    conj (ρ g).trace * (σ r).character g =
      ∑ s, (tensorMult ρ (σ r) (σ s) : ℂ) * (σ s).character g := by
  have := Fintype.ofFinite G
  have h := congrFun (eq_sum_pair hσ (classFun_mul_mem (conj_trace_mem ρ)
    (Blocks.isClassFunction_character (σ r)))) g
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← conj_pair ρ hσ s r]

/-- **The columns of the character table are eigenvectors** of `(N + Nᵀ)/2`, with the
eigenvalues `Re χ(C)`. -/
theorem column_eigen [Finite G] [Fintype ι] (hσ : IsCompleteFamily σ) (g : G) (r : ι) :
    ∑ s, ((tensorMult ρ (σ r) (σ s) : ℂ) + tensorMult ρ (σ s) (σ r)) / 2 * (σ s).character g =
      ((ρ g).trace.re : ℂ) * (σ r).character g := by
  have h1 := trace_mul_char ρ hσ r g
  have h2 := conj_trace_mul_char ρ hσ r g
  rw [Complex.re_eq_add_conj]
  have e : ∑ s, ((tensorMult ρ (σ r) (σ s) : ℂ) + tensorMult ρ (σ s) (σ r)) / 2 *
      (σ s).character g = ((∑ s, (tensorMult ρ (σ r) (σ s) : ℂ) * (σ s).character g) +
        ∑ s, (tensorMult ρ (σ s) (σ r) : ℂ) * (σ s).character g) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, ← h1, ← h2]
  ring

/-- The column of the character table at an element is not zero: the indicator of its class is
a combination of the characters. -/
theorem column_ne_zero [Finite G] [Finite ι] (hσ : IsCompleteFamily σ) (g : G) :
    (fun s => (σ s).character g) ≠ 0 := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  intro h0
  have h := congrFun (eq_sum_pair hσ (ind (ConjClasses.mk g)).2) g
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul, show ∀ s, (σ s).character g = 0 from
    fun s => congrFun h0 s, mul_zero, Finset.sum_const_zero] at h
  rw [ind_apply_self] at h
  exact one_ne_zero h

/-- For a real triplet `N` is symmetric. -/
theorem tensorMult_symm [Finite G] (hσ : IsCompleteFamily σ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (r s : ι) :
    tensorMult ρ (σ r) (σ s) = tensorMult ρ (σ s) (σ r) := by
  have := Fintype.ofFinite G
  have hc : ∀ g, conj (ρ g).trace = (ρ g).trace := fun g => by
    simp only [Matrix.trace, Matrix.diag, map_sum, hreal]
  have h := conj_pair ρ hσ r s
  simp only [hc] at h
  rw [← tensorMult_eq ρ hσ] at h
  exact_mod_cast h

open Classical in
/-- **The energy law in the electric basis**: `4κ diag(E) + B`. -/
theorem energy_charState [Fintype G] [Fintype ι] (hσ : IsCompleteFamily σ) (E : ι → ℚ)
    (κ β : ℝ) (s : ι) :
    energy (electricEnergy σ E) κ ρ β (charState (σ s)) =
      ∑ r, (4 * (κ : ℂ) * (E s : ℂ) * (if r = s then 1 else 0) +
        (β : ℂ) * (3 * (if r = s then 1 else 0) -
          ((tensorMult ρ (σ r) (σ s) : ℂ) + tensorMult ρ (σ s) (σ r)) / 2)) •
        charState (σ r) := by
  rw [energy, electric_charState hσ, magnetic_charState ρ hσ]
  simp only [add_smul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  congr 1
  push_cast
  ring

end Tensor

end EmptySquare

open EmptySquare ColourGroups Classical in
/-- **Proposition 13.5** (colourless states of the empty square). With no matter, a colourless
state of the square is a class function of `F`, as many as the classes: `5`, `5`, `15` and `17`
for the four models. The class indicators are a basis on which `B_U` is diagonal with the values
`β(3 - Re χ(C))`; the characters `χ_ρ(F)` are a basis on which the electric energy is diagonal
with the values `4κE(ρ)`, every link in block `ρ`; the character table changes one into the
other. -/
@[book "prop:ml-square-states"]
theorem mlSquareStates : Statement.mlSquareStates := by
  refine ⟨fun G _ => ⟨stateEquiv, fun f U => rfl⟩, fun G _ _ => finrank_states,
    finrank_states.trans card_conjClasses_cube, finrank_states.trans card_conjClasses_ico,
    finrank_states.trans card_conjClasses_C3A5, finrank_states.trans card_conjClasses_valentiner,
    fun G _ _ ρ => ⟨⟨indBasis.map stateEquiv, fun c => ?_⟩, fun β c g hg =>
      magnetic_classState ρ β c g hg⟩,
    fun G _ _ ι _ d σ hσ => ⟨⟨(charBasis hσ).map stateEquiv, fun i => ?_⟩,
      fun E κ i => electric_charState hσ E κ i, fun i U j => charState_setLink_mem (σ i) U j,
      fun g hg i => charState_eq_sum (σ i) g hg⟩⟩
  · rw [Module.Basis.map_apply, indBasis, Module.Basis.mk_apply]
    rfl
  · rw [Module.Basis.map_apply, charBasis, Module.Basis.mk_apply]
    rfl

namespace EmptySquare

/-! ### The cube group -/

section Cube

open ColourGroups Exact

theorem cube_N_sum (b b' : CubeBlock) :
    ∑ k : Fin 24, M3Z.trace (cubeE k) * cubeTabZ b' (cubeClassZ (cubeE k)) *
      ZOP.conj (cubeTabZ b (cubeClassZ (cubeE k))) = ⟨24 * (cubeN b b' : ℤ), 0, 0, 0⟩ := by
  cases b <;> cases b' <;> decide +kernel

/-- **For the cube group `N` is the table** of `fig:ml-square-table`, read through the
characters. -/
theorem cube_N (b b' : CubeBlock) :
    classPairing cubeGroup (fun g => colourChar cubeGroup g * cubeChar b' g) (cubeChar b) =
      (cubeN b b' : ℂ) := by
  rw [classPairing, groupAvg_cubeGroup]
  have e : ∑ k : Fin 24, colourChar cubeGroup (cubeElt k) * cubeChar b' (cubeElt k) *
      conj (cubeChar b (cubeElt k)) = ZOP.toComplex (∑ k : Fin 24, M3Z.trace (cubeE k) *
        cubeTabZ b' (cubeClassZ (cubeE k)) * ZOP.conj (cubeTabZ b (cubeClassZ (cubeE k)))) := by
    rw [toComplex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [char_cubeElt, cubeChar_cubeElt, cubeChar_cubeElt, ZOP.toComplex_mul, ZOP.toComplex_mul,
      ZOP.toComplex_conj]
  rw [e, cube_N_sum]
  simp [ZOP.toComplex]

variable {ι : Type} [Fintype ι] {d : ι → ℕ}
  {σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ)}

/-- A complete family of the cube group has five members: as many as the classes. -/
theorem card_family_cube (hσ : IsCompleteFamily σ) : Fintype.card ι = 5 := by
  have h := Module.finrank_eq_card_basis ((charBasis hσ).map stateEquiv)
  rw [finrank_states, card_conjClasses_cube] at h
  exact h.symm

omit [Fintype ι] in
/-- When the members carry the characters of the blocks, `N` is the table. -/
theorem tensorMult_cube (hσ : IsCompleteFamily σ) (lab : ι → CubeBlock)
    (hlab : ∀ i, (σ i).character = cubeChar (lab i)) (r s : ι) :
    tensorMult cubeTriplet (σ r) (σ s) = cubeN (lab r) (lab s) := by
  have h := tensorMult_eq cubeTriplet hσ r s
  rw [hlab r, hlab s] at h
  have h2 := cube_N (lab r) (lab s)
  rw [classPairing, groupAvg, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype] at h2
  exact_mod_cast h.trans h2

end Cube

end EmptySquare

namespace EmptySquare

/-! ### The five blocks of the cube group

Every complete family of the cube group carries the five characters of the table
(`fig:mt-s4-characters`): the characters of the trivial representation, of the sign, of the
triplet and of the sign times the triplet have norm one, so by Proposition 11.5 each is the
character of one member; the tensor square of the triplet, `1 + 2 + 3_s + 3_r`, gives the fifth.
-/

section CubeBlocks

open ColourGroups Exact

/-- The index of the product of two of the twenty-four rotations. -/
def mulIdx (k l : Fin 24) : Fin 24 :=
  ((List.finRange 24).find? fun m => decide (cubeE m = M3Z.mul (cubeE k) (cubeE l))).getD 0

theorem cubeE_mulIdx : ∀ k l : Fin 24, cubeE (mulIdx k l) = M3Z.mul (cubeE k) (cubeE l) := by
  decide +kernel

theorem cubeElt_mul (k l : Fin 24) : cubeElt k * cubeElt l = cubeElt (mulIdx k l) := by
  apply Subtype.ext
  apply Subtype.ext
  change M3Z.toMat (cubeE k) * M3Z.toMat (cubeE l) = M3Z.toMat (cubeE (mulIdx k l))
  rw [cubeE_mulIdx, M3Z.toMat_mul]

theorem one_eq_cubeElt : (1 : cubeGroup) = cubeElt 0 := by
  apply Subtype.ext
  apply Subtype.ext
  change (1 : Matrix (Fin 3) (Fin 3) ℂ) = M3Z.toMat (cubeE 0)
  rw [show cubeE 0 = M3Z.scalar 1 by decide, M3Z.toMat_scalar, ZOP.toComplex_one, one_smul]

theorem sign_mul_table : ∀ k l : Fin 24, cubeTabZ .sign (cubeClassZ (cubeE (mulIdx k l))) =
    cubeTabZ .sign (cubeClassZ (cubeE k)) * cubeTabZ .sign (cubeClassZ (cubeE l)) := by
  decide +kernel

/-- The sign of the cube group, `S₄ → {±1}`, read off the table. -/
noncomputable def sgnHom : cubeGroup →* ℂ where
  toFun := cubeChar .sign
  map_one' := by
    rw [one_eq_cubeElt, cubeChar_cubeElt, show cubeTabZ .sign (cubeClassZ (cubeE 0)) = 1 by decide,
      ZOP.toComplex_one]
  map_mul' g h := by
    obtain ⟨k, rfl⟩ := cubeElt_surjective g
    obtain ⟨l, rfl⟩ := cubeElt_surjective h
    rw [cubeElt_mul, cubeChar_cubeElt, cubeChar_cubeElt, cubeChar_cubeElt, sign_mul_table,
      ZOP.toComplex_mul]

/-- The sign as a representation on `ℂ`. -/
noncomputable def signRep : Representation ℂ cubeGroup (Fin 1 → ℂ) :=
  (Algebra.lsmul ℂ ℂ (Fin 1 → ℂ)).toMonoidHom.comp sgnHom

/-- The sign times the triplet, `3_s`, on `ℂ³`. -/
noncomputable def threeSRep : Representation ℂ cubeGroup (Fin 3 → ℂ) where
  toFun g := sgnHom g • Edge.tripletRep cubeTriplet g
  map_one' := by rw [map_one, map_one, one_smul]
  map_mul' g h := by rw [map_mul, map_mul, smul_mul_smul_comm]

theorem character_trivial (g : cubeGroup) :
    (Representation.trivial ℂ cubeGroup (Fin 1 → ℂ)).character g = cubeChar .one g := by
  rw [Representation.character, Representation.trivial, MonoidHom.one_apply, LinearMap.trace_one,
    Module.finrank_fin_fun, Nat.cast_one]
  unfold cubeChar
  cases cubeClassOf g <;> rfl

theorem character_signRep (g : cubeGroup) : signRep.character g = cubeChar .sign g := by
  change LinearMap.trace ℂ (Fin 1 → ℂ) (Algebra.lsmul ℂ ℂ (Fin 1 → ℂ) (sgnHom g)) = _
  rw [show Algebra.lsmul ℂ ℂ (Fin 1 → ℂ) (sgnHom g) = sgnHom g • LinearMap.id from rfl,
    map_smul, LinearMap.trace_id, Module.finrank_fin_fun, smul_eq_mul, Nat.cast_one, mul_one]
  rfl

theorem trace_threeR_table : ∀ k : Fin 24,
    M3Z.trace (cubeE k) = cubeTabZ .threeR (cubeClassZ (cubeE k)) := by
  decide +kernel

theorem colourChar_cube (g : cubeGroup) : colourChar cubeGroup g = cubeChar .threeR g := by
  obtain ⟨k, rfl⟩ := cubeElt_surjective g
  rw [char_cubeElt, cubeChar_cubeElt, trace_threeR_table]

theorem character_tripletRep_cube (g : cubeGroup) :
    (Edge.tripletRep cubeTriplet).character g = cubeChar .threeR g := by
  rw [character_tripletRep, ← colourChar_cube]
  rfl

theorem character_threeSRep (g : cubeGroup) : threeSRep.character g = cubeChar .threeS g := by
  change LinearMap.trace ℂ (Fin 3 → ℂ) (sgnHom g • Edge.tripletRep cubeTriplet g) = _
  rw [map_smul, smul_eq_mul]
  change sgnHom g * (Edge.tripletRep cubeTriplet).character g = _
  rw [character_tripletRep_cube]
  change cubeCharTable .sign (cubeClassOf g) * cubeCharTable .threeR (cubeClassOf g) =
    cubeCharTable .threeS (cubeClassOf g)
  cases cubeClassOf g <;> norm_num [cubeCharTable]

theorem character_tensorSq (g : cubeGroup) :
    ((Edge.tripletRep cubeTriplet).tprod (Edge.tripletRep cubeTriplet)).character g =
      cubeChar .one g + cubeChar .two g + cubeChar .threeS g + cubeChar .threeR g := by
  rw [Representation.char_tensor, Pi.mul_apply, character_tripletRep_cube]
  obtain ⟨k, rfl⟩ := cubeElt_surjective g
  simp only [cubeChar_cubeElt]
  rw [← trace_threeR_table, ← ZOP.toComplex_mul, ← ZOP.toComplex_add, ← ZOP.toComplex_add,
    ← ZOP.toComplex_add, ← (cube_sym k).1]
  congr 1
  ring

theorem character_tensorSq' :
    ((Edge.tripletRep cubeTriplet).tprod (Edge.tripletRep cubeTriplet)).character =
      cubeChar .one + cubeChar .two + cubeChar .threeS + cubeChar .threeR :=
  funext character_tensorSq

theorem cube_orth_sum (b b' : CubeBlock) :
    ∑ k : Fin 24,
      cubeTabZ b (cubeClassZ (cubeE k)) * ZOP.conj (cubeTabZ b' (cubeClassZ (cubeE k))) =
        if b = b' then ⟨24, 0, 0, 0⟩ else ⟨0, 0, 0, 0⟩ := by
  cases b <;> cases b' <;> decide +kernel

/-- The rows of the character table are orthonormal. -/
theorem cube_orth (b b' : CubeBlock) :
    (Fintype.card cubeGroup : ℂ)⁻¹ * ∑ g, cubeChar b g * conj (cubeChar b' g) =
      if b = b' then 1 else 0 := by
  rw [← Equiv.sum_comp cubeEquiv]
  have e : ∑ k : Fin 24, cubeChar b (cubeEquiv k) * conj (cubeChar b' (cubeEquiv k)) =
      ZOP.toComplex (∑ k : Fin 24,
        cubeTabZ b (cubeClassZ (cubeE k)) * ZOP.conj (cubeTabZ b' (cubeClassZ (cubeE k)))) := by
    rw [toComplex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show cubeEquiv k = cubeElt k from rfl, cubeChar_cubeElt, cubeChar_cubeElt,
      ZOP.toComplex_mul, ZOP.toComplex_conj]
  rw [e, cube_orth_sum, show Fintype.card cubeGroup = 24 by
    rw [← Nat.card_eq_fintype_card, card_cubeGroup]]
  split_ifs <;> simp [ZOP.toComplex]

/-- A representation's character is the sum of the characters of a complete family, each
counted as many times as it occurs (Proposition 11.5). -/
theorem char_eq_sum_mult {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι] {d : ι → ℕ}
    {τ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)} (hτ : IsCompleteFamily τ) {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Representation ℂ G V) :
    W.character = ∑ i, (Module.finrank ℂ ((τ i).IntertwiningMap W) : ℂ) • (τ i).character := by
  have := Fintype.ofFinite G
  conv_lhs => rw [eq_sum_pair hτ (Blocks.isClassFunction_character W)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(mtAverage G).2.2 V _ W (τ i) (hτ.1 i)]

/-- **A character of norm one is the character of a member** of a complete family. -/
theorem exists_char_eq {G : Type} [Group G] [Fintype G] {ι : Type} [Finite ι] {d : ι → ℕ}
    {τ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)} (hτ : IsCompleteFamily τ) {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Representation ℂ G V)
    (h1 : (Fintype.card G : ℂ)⁻¹ * ∑ g, W.character g * conj (W.character g) = 1) :
    ∃ i, (τ i).character = W.character := by
  classical
  have := Fintype.ofFinite ι
  set m : ι → ℕ := fun i => Module.finrank ℂ ((τ i).IntertwiningMap W) with hm
  have hW := char_eq_sum_mult hτ W
  have hWg : ∀ g, W.character g = ∑ i, (m i : ℂ) * (τ i).character g := fun g => by
    rw [hW, Finset.sum_apply]
    rfl
  have hnorm : ∑ i, ((m i ^ 2 : ℕ) : ℂ) = 1 := by
    rw [← h1]
    simp only [hWg]
    have : ∀ g, (∑ i, (m i : ℂ) * (τ i).character g) * conj (∑ j, (m j : ℂ) * (τ j).character g) =
        ∑ j, (m j : ℂ) * ((∑ i, (m i : ℂ) * (τ i).character g) * conj ((τ j).character g)) := by
      intro g
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_natCast]
      ring
    simp only [this]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, pair_sum hτ]
    push_cast
    ring
  have hnat : ∑ i, m i ^ 2 = 1 := by exact_mod_cast hnorm
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hnat]; exact one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => m j ^ 2) (Finset.mem_univ i)
  rw [hnat] at hsplit
  have hmi : m i ^ 2 = 1 := by
    have : 1 ≤ m i ^ 2 := Nat.one_le_iff_ne_zero.mpr hi
    omega
  have hrest : ∑ j ∈ Finset.univ.erase i, m j ^ 2 = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  have hmi1 : m i = 1 := by
    rcases Nat.lt_or_ge (m i) 2 with h | h
    · interval_cases (m i) <;> simp_all
    · nlinarith
  refine ⟨i, funext fun g => ?_⟩
  rw [hWg, Finset.sum_eq_single i (fun j _ hj => by
    rw [pow_eq_zero_iff two_ne_zero |>.mp (hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)),
      Nat.cast_zero, zero_mul]) (fun h => absurd (Finset.mem_univ i) h), hmi1, Nat.cast_one,
    one_mul]

end CubeBlocks

section Identify

open ColourGroups

variable {ι : Type} {d : ι → ℕ} {σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ)}

theorem norm_row (b : CubeBlock) :
    (Fintype.card cubeGroup : ℂ)⁻¹ * ∑ g, cubeChar b g * conj (cubeChar b g) = 1 := by
  rw [cube_orth, ite_eq_left rfl]

theorem row_ne {b b' : CubeBlock} (h : b ≠ b') : cubeChar b ≠ cubeChar b' := fun he => by
  have := cube_orth b b'
  rw [he, norm_row, ite_eq_right h] at this
  exact one_ne_zero this

/-- The multiplicity of a member with the character of a block in the tensor square of the
triplet: `⟨χ_b, 1 + 2 + 3_s + 3_r⟩`. -/
theorem mult_tensorSq (i : ι) (b : CubeBlock) (hi : (σ i).character = cubeChar b)
    (hσ : IsCompleteFamily σ) :
    (Module.finrank ℂ ((σ i).IntertwiningMap
        ((Edge.tripletRep cubeTriplet).tprod (Edge.tripletRep cubeTriplet))) : ℂ) =
      (if CubeBlock.one = b then 1 else 0) + (if CubeBlock.two = b then 1 else 0) +
        (if CubeBlock.threeS = b then 1 else 0) + (if CubeBlock.threeR = b then 1 else 0) := by
  rw [(mtAverage cubeGroup).2.2 _ _ _ (σ i) (hσ.1 i), hi]
  simp only [character_tensorSq, add_mul, Finset.sum_add_distrib, mul_add]
  rw [cube_orth, cube_orth, cube_orth, cube_orth]

/-- **Every complete family of the cube group carries the five characters of the table**, one
member for each block. -/
theorem exists_labelling [Finite ι] (hσ : IsCompleteFamily σ) :
    ∃ lab : ι → CubeBlock, ∀ i, (σ i).character = cubeChar (lab i) := by
  classical
  have := Fintype.ofFinite ι
  have e1 : (Representation.trivial ℂ cubeGroup (Fin 1 → ℂ)).character = cubeChar .one :=
    funext character_trivial
  have esg : signRep.character = cubeChar .sign := funext character_signRep
  have e3s : threeSRep.character = cubeChar .threeS := funext character_threeSRep
  have e3r : (Edge.tripletRep cubeTriplet).character = cubeChar .threeR :=
    funext character_tripletRep_cube
  obtain ⟨i1, h1⟩ := exists_char_eq hσ (Representation.trivial ℂ cubeGroup (Fin 1 → ℂ))
    (by rw [e1]; exact norm_row .one)
  obtain ⟨isg, hsg⟩ := exists_char_eq hσ signRep (by rw [esg]; exact norm_row .sign)
  obtain ⟨i3s, h3s⟩ := exists_char_eq hσ threeSRep (by rw [e3s]; exact norm_row .threeS)
  obtain ⟨i3r, h3r⟩ := exists_char_eq hσ (Edge.tripletRep cubeTriplet)
    (by rw [e3r]; exact norm_row .threeR)
  rw [e1] at h1
  rw [esg] at hsg
  rw [e3s] at h3s
  rw [e3r] at h3r
  have dist : ∀ {i j : ι} {b b' : CubeBlock}, (σ i).character = cubeChar b →
      (σ j).character = cubeChar b' → b ≠ b' → i ≠ j := fun hi hj hbb' hij =>
    row_ne hbb' (hi.symm.trans (hij ▸ hj))
  set S : Finset ι := {i1, isg, i3s, i3r} with hS
  have hS4 : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (dist h3s h3r (by decide))]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dist hsg h3s (by decide), dist hsg h3r (by decide)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dist h1 hsg (by decide), dist h1 h3s (by decide), dist h1 h3r (by decide)⟩
  have h5 := card_family_cube hσ
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    have := congrArg Finset.card (Finset.eq_univ_of_forall hne)
    rw [Finset.card_univ, h5, hS4] at this
    exact absurd this (by norm_num)
  have huniv : insert c S = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_insert_of_notMem hc, hS4, h5])
  -- the tensor square of the triplet gives the fifth member
  set m : ι → ℕ := fun i => Module.finrank ℂ ((σ i).IntertwiningMap
    ((Edge.tripletRep cubeTriplet).tprod (Edge.tripletRep cubeTriplet))) with hm
  have hW := char_eq_sum_mult hσ ((Edge.tripletRep cubeTriplet).tprod (Edge.tripletRep cubeTriplet))
  have m1 : (m i1 : ℂ) = 1 := by rw [hm, mult_tensorSq i1 .one h1 hσ]; norm_num
  have msg : (m isg : ℂ) = 0 := by rw [hm, mult_tensorSq isg .sign hsg hσ]; norm_num
  have m3s : (m i3s : ℂ) = 1 := by rw [hm, mult_tensorSq i3s .threeS h3s hσ]; norm_num
  have m3r : (m i3r : ℂ) = 1 := by rw [hm, mult_tensorSq i3r .threeR h3r hσ]; norm_num
  have hcS : c ≠ i1 ∧ c ≠ isg ∧ c ≠ i3s ∧ c ≠ i3r := by
    simpa [hS, not_or] using hc
  have h2 : (m c : ℂ) • (σ c).character = cubeChar .two := by
    have hsum := hW
    rw [← huniv, Finset.sum_insert hc, hS, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_pair (dist h3s h3r (by decide))] at hsum
    · rw [character_tensorSq'] at hsum
      change (m c : ℂ) • (σ c).character = _
      rw [h1, hsg, h3s, h3r, m1, msg, m3s, m3r] at hsum
      simp only [one_smul, zero_smul, zero_add] at hsum
      funext g
      have := congrFun hsum g
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dist hsg h3s (by decide), dist hsg h3r (by decide)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dist h1 hsg (by decide), dist h1 h3s (by decide), dist h1 h3r (by decide)⟩
  have hmc : (m c : ℂ) = 1 := by
    have hn := norm_row .two
    rw [← h2] at hn
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_natCast] at hn
    have : (m c : ℂ) ^ 2 * ((Fintype.card cubeGroup : ℂ)⁻¹ *
        ∑ g, (σ c).character g * conj ((σ c).character g)) = 1 := by
      rw [← hn, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [orth hσ c c, ite_eq_left rfl, mul_one] at this
    have hnat : m c ^ 2 = 1 := by exact_mod_cast this
    rw [pow_eq_one_iff_of_nonneg (Nat.zero_le _) two_ne_zero] at hnat
    rw [hnat, Nat.cast_one]
  rw [hmc, one_smul] at h2
  refine ⟨fun i => if i = i1 then .one else if i = isg then .sign else if i = i3s then .threeS
    else if i = i3r then .threeR else .two, fun i => ?_⟩
  have hi : i ∈ insert c S := huniv ▸ Finset.mem_univ i
  simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hi
  dsimp only
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [ite_eq_right hcS.1, ite_eq_right hcS.2.1, ite_eq_right hcS.2.2.1,
      ite_eq_right hcS.2.2.2, h2]
  · rw [ite_eq_left rfl, h1]
  · rw [ite_eq_right (dist hsg h1 (by decide)), ite_eq_left rfl, hsg]
  · rw [ite_eq_right (dist h3s h1 (by decide)), ite_eq_right (dist h3s hsg (by decide)),
      ite_eq_left rfl, h3s]
  · rw [ite_eq_right (dist h3r h1 (by decide)), ite_eq_right (dist h3r hsg (by decide)),
      ite_eq_right (dist h3r h3s (by decide)), ite_eq_left rfl, h3r]

end Identify

end EmptySquare


open EmptySquare ColourGroups Classical in
/-- **Theorem 13.6** (the magnetic term in the electric basis). In the electric basis
`B_{ρσ} = β(3 δ_{ρσ} - (N_{ρσ} + N_{σρ})/2)` with `N_{ρσ}` the multiplicity of `ρ` in `3 ⊗ σ`;
for a real triplet `N` is symmetric and `B = β(3 - N)`. The columns of the character table are
the eigenvectors of `(N + Nᵀ)/2` with the eigenvalues `Re χ(C)`. For the cube group `N` is the
table of `fig:ml-square-table`, and the energy law of the empty square is the `5 × 5` matrix
`4κ diag(E) + β(3 - N)`. -/
@[book "thm:ml-square-matrix"]
theorem mlSquareMatrix : Statement.mlSquareMatrix := by
  refine ⟨fun G _ _ ρ ι _ d σ hσ => ⟨fun β s => magnetic_charState ρ hσ β s,
    fun hreal => ⟨fun r s => tensorMult_symm ρ hσ hreal r s, fun β s => ?_⟩,
    fun g => ⟨column_ne_zero hσ g, fun r => column_eigen ρ hσ g r⟩,
    fun E κ β s => energy_charState ρ hσ E κ β s⟩, cube_N,
    fun ι _ d σ hσ => ⟨card_family_cube hσ, exists_labelling hσ, fun lab hlab =>
      ⟨tensorMult_cube hσ lab hlab, fun E κ β s => ?_⟩⟩⟩
  · rw [magnetic_charState ρ hσ β s]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tensorMult_symm ρ hσ hreal s r]
    congr 1
    ring
  · rw [energy_charState cubeTriplet hσ E κ β s]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tensorMult_symm cubeTriplet hσ cubeTriplet_real s r, tensorMult_cube hσ lab hlab r s]
    congr 1
    ring

/-! ## Non-vacuity -/

section NonVacuity

open EmptySquare ColourGroups

/-- Proposition 13.5 on the book's cube group: the empty square has five colourless states, and
the class indicators are a basis on which `B_U` is diagonal. -/
example : Module.finrank ℂ ↥(squareCanvas.gaugeInvariants cubeGroup) = 5 ∧
    ∃ b : Module.Basis (ConjClasses cubeGroup) ℂ ↥(squareCanvas.gaugeInvariants cubeGroup),
      ∀ c, (b c : squareCanvas.skeleton.LinkTable cubeGroup → ℂ) = classState c :=
  ⟨mlSquareStates.2.2.1, (mlSquareStates.2.2.2.2.2.2.1 cubeGroup cubeTriplet).1⟩

/-- The hypotheses of Proposition 13.5 and Theorem 13.6 are met on the cube group with its
triplet: a complete family of irreducible representations exists (Theorem 11.4), its characters
of `F` are a basis of the colourless states of the square, and its members can be named by the
five blocks of the character table so that each carries its block's character; then `N` is the
table of `fig:ml-square-table`. -/
example : ∃ (n : ℕ) (d : Fin n → ℕ) (σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ))
    (lab : Fin n → CubeBlock), IsCompleteFamily σ ∧
      (∃ b : Module.Basis (Fin n) ℂ ↥(squareCanvas.gaugeInvariants cubeGroup),
        ∀ i, (b i : squareCanvas.skeleton.LinkTable cubeGroup → ℂ) = charState (σ i)) ∧
      (∀ i, (σ i).character = cubeChar (lab i)) ∧
      ∀ r s, tensorMult cubeTriplet (σ r) (σ s) = cubeN (lab r) (lab s) := by
  obtain ⟨n, d, σ, h1, h2, h3⟩ := (mtBlocks cubeGroup).1
  have hσ : IsCompleteFamily σ := ⟨h1, h2, h3⟩
  obtain ⟨lab, hlab⟩ := exists_labelling hσ
  exact ⟨n, d, σ, lab, hσ, (mlSquareStates.2.2.2.2.2.2.2 cubeGroup (Fin n) d σ hσ).1, hlab,
    ((mlSquareMatrix.2.2 (Fin n) d σ hσ).2.2 lab hlab).1⟩

end NonVacuity

end Artform
