import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.CardCommute
import ArtformTextbook.Ch05.Holonomy
import ArtformTextbook.Ch11.Colourless
import ArtformTextbook.Ch12.Groups
import ArtformTextbook.Ch13.Statements.Census

/-!
# The census of a canvas (Theorem 13.11)

The proof is the book's: the number of invariants is the average of the trace over the gauge
group `G^V` (Proposition 11.5), here in the form of Burnside's lemma for coefficient tables.

* **Averaging.** A finite group `H` acts on a finite set `X` and on a space of coefficient tables
  `N → ℂ` by matrices `Γ(h)`. The tables `ψ : X → (N → ℂ)` with `ψ(h • x) = Γ(h) ψ(x)`, supported
  on labels `p` that every `Γ(h)` respects, number `(1/|H|) Σ_h |Fix(h)| Σ_{n ∈ p} Γ(h)_{nn}`
  (`Census.finrank_covariant`): they are the invariants of `H` acting on the tables over `X × N`.
* **The fixed link tables.** A link table is fixed by `h` when `h_{t(e)} U_e h_{s(e)}⁻¹ = U_e` on
  every edge, that is `U_e h_{s(e)} U_e⁻¹ = h_{t(e)}`; on one edge there are `|C_G(h_{s(e)})|`
  such `U_e` when `h_{s(e)}` and `h_{t(e)}` are conjugate, and none otherwise
  (`Census.card_conjugators`). On a connected canvas the product over the edges is therefore
  `|C_G(C)|^E` when every `h_v` lies in one class `C`, and zero otherwise.
* **The matter.** The trace of `Γ(h)` on the tables with `n` quarks is the coefficient of `z^n`
  in `det(1 + z D(h))` (`Ch11/Minors.lean`), with `D(h)` block diagonal: `Π_v det(1 + z ρ(h_v))^d`.
* **Summing over a class.** Summing `Π_v f(h_v)` over the `|C|^V` choices with every `h_v ∈ C`
  gives `(|C| f(g_C))^V` for a class function `f`, and `|C| |C_G(C)| = |G|`.
-/

namespace Artform

open scoped Matrix

open Polynomial

namespace Census

/-! ### Averaging over a finite group -/

section Averaging

/-- The coefficient tables over `X` with values in `N → ℂ` that are covariant,
`ψ(h • x) = Γ(h) ψ(x)`. -/
def covariant {H X N : Type*} [Fintype N] (act : H → X → X) (Γ : H → Matrix N N ℂ) :
    Submodule ℂ (X → N → ℂ) where
  carrier := {ψ | ∀ h x, ψ (act h x) = Γ h *ᵥ ψ x}
  add_mem' {ψ φ} hψ hφ h x := by
    simp only [Set.mem_ofPred_eq] at hψ hφ
    simp only [Pi.add_apply, hψ, hφ, Matrix.mulVec_add]
  zero_mem' h x := by simp
  smul_mem' c ψ hψ h x := by
    simp only [Set.mem_ofPred_eq] at hψ
    simp only [Pi.smul_apply, hψ, Matrix.mulVec_smul]

theorem mem_covariant {H X N : Type*} [Fintype N] {act : H → X → X} {Γ : H → Matrix N N ℂ}
    {ψ : X → N → ℂ} : ψ ∈ covariant act Γ ↔ ∀ h x, ψ (act h x) = Γ h *ᵥ ψ x := Iff.rfl

/-- The coefficient tables over `X` whose values are supported on the labels `p`. -/
def supported (X : Type*) {N : Type*} (p : N → Prop) : Submodule ℂ (X → N → ℂ) where
  carrier := {ψ | ∀ x n, ψ x n ≠ 0 → p n}
  add_mem' {ψ φ} hψ hφ x n hn := by
    by_cases h : ψ x n = 0
    · exact hφ x n (by simpa [h] using hn)
    · exact hψ x n h
  zero_mem' x n hn := absurd rfl hn
  smul_mem' c ψ hψ x n hn := hψ x n (right_ne_zero_of_mul hn)

theorem mem_supported {X N : Type*} {p : N → Prop} {ψ : X → N → ℂ} :
    ψ ∈ supported X p ↔ ∀ x n, ψ x n ≠ 0 → p n := Iff.rfl

/-- Tables over `X × N` are tables over `X` with values in `N → ℂ`. -/
def curryEquiv (X N : Type*) : (X × N → ℂ) ≃ₗ[ℂ] (X → N → ℂ) where
  toFun v x n := v (x, n)
  invFun ψ z := ψ z.1 z.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {H X N : Type*} [Group H] (act : H → X → X) (act_one : ∀ x, act 1 x = x)
  (act_mul : ∀ h k x, act (h * k) x = act h (act k x))

include act_one act_mul in
theorem act_inv_act (h : H) (x : X) : act h⁻¹ (act h x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

include act_one act_mul in
theorem act_act_inv (h : H) (x : X) : act h (act h⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- The action of `H` on the tables over `X × N`: the coefficient at `(x, n)` moves to `h • x`,
transformed by `Γ(h)`. -/
noncomputable def permRep [Fintype X] [DecidableEq X] [Fintype N] [DecidableEq N]
    (Γ : H →* Matrix N N ℂ) : H →* Matrix (X × N) (X × N) ℂ where
  toFun h := Matrix.of fun y z => if y.1 = act h z.1 then Γ h y.2 z.2 else 0
  map_one' := by
    ext y z
    simp only [Matrix.of_apply, act_one, map_one, Matrix.one_apply, Prod.ext_iff]
    by_cases h1 : y.1 = z.1
    · simp [h1]
    · simp [h1]
  map_mul' h k := by
    ext y z
    simp only [Matrix.of_apply, Matrix.mul_apply, map_mul, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (act k z.1)]
    · by_cases hy : y.1 = act h (act k z.1)
      · simp [hy, act_mul]
      · simp [hy, act_mul]
    · intro x _ hx
      refine Finset.sum_eq_zero fun n _ => ?_
      simp [hx]
    · simp

theorem permRep_mulVec [Fintype X] [DecidableEq X] [Fintype N] [DecidableEq N]
    (Γ : H →* Matrix N N ℂ) (h : H) (v : X × N → ℂ) (y : X × N) :
    (permRep act act_one act_mul Γ h *ᵥ v) y = (Γ h *ᵥ fun n => v (act h⁻¹ y.1, n)) y.2 := by
  simp only [Matrix.mulVec, dotProduct, permRep, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (act h⁻¹ y.1)]
  · simp [act_act_inv act act_one act_mul h y.1]
  · intro x _ hx
    refine Finset.sum_eq_zero fun n _ => ?_
    refine ite_eq_right fun hxy => hx ?_
    rw [hxy, act_inv_act act act_one act_mul]
  · simp

include act_one act_mul in
/-- **Averaging.** The covariant tables supported on `p` number
`(1/|H|) Σ_h |Fix(h)| Σ_{n ∈ p} Γ(h)_{nn}`. -/
theorem finrank_covariant [Fintype H] [Fintype X] [DecidableEq X] [Fintype N] [DecidableEq N]
    (Γ : H →* Matrix N N ℂ) (p : N → Prop) [DecidablePred p]
    (hp : ∀ h n' n, Γ h n' n ≠ 0 → (p n' ↔ p n)) :
    (Module.finrank ℂ ↥(covariant act Γ ⊓ supported X p) : ℂ) =
      (Fintype.card H : ℂ)⁻¹ * ∑ h, (Fintype.card {x // act h x = x} : ℂ) *
        ∑ n ∈ Finset.univ.filter p, Γ h n n := by
  set R := permRep act act_one act_mul Γ with hR
  let Z : Submodule ℂ (X × N → ℂ) :=
    { carrier := {v | ∀ z, v z ≠ 0 → p z.2}
      add_mem' := fun {v w} hv hw z hz => by
        by_cases h : v z = 0
        · exact hw z (by simpa [h] using hz)
        · exact hv z h
      zero_mem' := fun z hz => absurd rfl hz
      smul_mem' := fun c v hv z hz => hv z (right_ne_zero_of_mul hz) }
  have hRp : ∀ h z' z, R h z' z ≠ 0 → (p z'.2 ↔ p z.2) := by
    intro h z' z hne
    simp only [hR, permRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply] at hne
    split_ifs at hne with h1
    · exact hp h _ _ hne
    · exact absurd rfl hne
  have key := Fock.finrank_inf_fixedSub R (fun z => p z.2) Z (fun v => Iff.rfl) hRp
  have hmap : (Z ⊓ Fock.fixedSub R).map (curryEquiv X N : (X × N → ℂ) →ₗ[ℂ] (X → N → ℂ)) =
      covariant act Γ ⊓ supported X p := by
    ext ψ
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨v, ⟨hvZ, hvR⟩, rfl⟩
      refine ⟨fun h x => ?_, fun x n hn => hvZ (x, n) hn⟩
      funext n
      have := congrFun (hvR h) (act h x, n)
      rw [permRep_mulVec, act_inv_act act act_one act_mul] at this
      exact this.symm
    · rintro ⟨hcov, hsupp⟩
      refine ⟨(curryEquiv X N).symm ψ, ⟨fun z hz => hsupp z.1 z.2 hz, fun h => ?_⟩,
        (curryEquiv X N).apply_symm_apply ψ⟩
      funext y
      rw [permRep_mulVec]
      have := hcov h (act h⁻¹ y.1)
      rw [act_act_inv act act_one act_mul] at this
      exact (congrFun this y.2).symm
  have heq := LinearEquiv.finrank_eq ((curryEquiv X N).ofSubmodules _ _ hmap)
  rw [← heq, key]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  have hx : ∀ x : X, (∑ n : N, if p n then R h (x, n) (x, n) else 0) =
      if act h x = x then ∑ n ∈ Finset.univ.filter p, Γ h n n else 0 := by
    intro x
    simp only [hR, permRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply]
    by_cases hfix : act h x = x
    · rw [ite_eq_left hfix, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ite_eq_left hfix.symm]
    · rw [ite_eq_right hfix]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [ite_eq_right (Ne.symm hfix), ite_self]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [hx]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_subtype]

end Averaging

/-! ### Fixed link tables -/

section Links

variable {G : Type*} [Group G]

/-- A link table is given by its values on the stored edges. -/
def linkEquiv (K : Canvas) (G : Type*) [Group G] : K.skeleton.LinkTable G ≃ (K.E → G) where
  toFun U e := U (e, true)
  invFun u := Skeleton.LinkTable.ofGraph u
  left_inv U := by
    ext ⟨e, b⟩
    cases b
    · exact (U.reversal (e, true)).symm
    · rfl
  right_inv u := rfl

/-- The link tables of a canvas over a finite group form a finite type. -/
noncomputable instance (K : Canvas) (G : Type*) [Group G] [Fintype G] :
    Fintype (K.skeleton.LinkTable G) :=
  Fintype.ofEquiv _ (linkEquiv K G).symm

theorem fix_iff (a b x : G) : a * x * b⁻¹ = x ↔ x * b * x⁻¹ = a := by
  constructor
  · intro h
    calc x * b * x⁻¹ = a * x * b⁻¹ * b * x⁻¹ := by rw [h]
      _ = a := by group
  · intro h
    rw [← h]
    group

/-- A link table is fixed by a gauge change exactly when `U_e h_{s(e)} U_e⁻¹ = h_{t(e)}` on every
stored edge. -/
theorem gaugeAct_eq_self_iff {K : Canvas} (h : K.V → G) (U : K.skeleton.LinkTable G) :
    Skeleton.gaugeAct h U = U ↔
      ∀ e, U (e, true) * h (K.src e) * (U (e, true))⁻¹ = h (K.tgt e) := by
  constructor
  · intro hU e
    have := congrArg (fun W : K.skeleton.LinkTable G => W (e, true)) hU
    exact (fix_iff _ _ _).mp this
  · intro hU
    ext ⟨e, b⟩
    have he := (fix_iff _ _ _).mpr (hU e)
    cases b
    · have hrev : U (e, false) = (U (e, true))⁻¹ := U.reversal (e, true)
      change h (K.src e) * U (e, false) * (h (K.tgt e))⁻¹ = U (e, false)
      rw [hrev]
      conv_rhs => rw [← he]
      group
    · exact he

/-- The link tables fixed by `h` number `Π_e |{x : x h_{s(e)} x⁻¹ = h_{t(e)}}|`. -/
theorem card_fixed [Finite G] {K : Canvas} (h : K.V → G) :
    Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} =
      ∏ e : K.E, Nat.card {x : G // x * h (K.src e) * x⁻¹ = h (K.tgt e)} := by
  rw [← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun e (x : G) => x * h (K.src e) * x⁻¹ = h (K.tgt e)))]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun U => Skeleton.gaugeAct h U = U)
    (q := fun u : K.E → G => ∀ e, u e * h (K.src e) * (u e)⁻¹ = h (K.tgt e))
    (linkEquiv K G) fun U => gaugeAct_eq_self_iff h U)

/-- Conjugate elements have centralizers of the same size. -/
theorem card_centralizer_of_isConj {z y : G} (hzy : IsConj z y) :
    Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {z}) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzy
  refine Nat.card_congr
    { toFun := fun w => ⟨c⁻¹ * w * c, ?_⟩
      invFun := fun w => ⟨c * w * c⁻¹, ?_⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc] }
  · have hw := Subgroup.mem_centralizer_iff.mp w.2 (c * z * c⁻¹) rfl
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    subst ht
    calc t * (c⁻¹ * ↑w * c) = c⁻¹ * ((c * t * c⁻¹) * ↑w) * c := by group
      _ = c⁻¹ * (↑w * (c * t * c⁻¹)) * c := by rw [hw]
      _ = c⁻¹ * ↑w * c * t := by group
  · have hw := Subgroup.mem_centralizer_iff.mp w.2 z rfl
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    subst ht
    calc c * z * c⁻¹ * (c * ↑w * c⁻¹) = c * (z * ↑w) * c⁻¹ := by group
      _ = c * (↑w * z) * c⁻¹ := by rw [hw]
      _ = c * ↑w * c⁻¹ * (c * z * c⁻¹) := by group

/-- **One edge.** When `y` is conjugate to `z`, the elements carrying `z` to `y` by conjugation
number `|C_G(z)|`. -/
theorem card_conjugators_of_isConj {z y : G} (hzy : IsConj z y) :
    Nat.card {x : G // x * z * x⁻¹ = y} = Nat.card (Subgroup.centralizer {z}) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hzy
  refine Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x, ?_⟩
      invFun := fun w => ⟨c * w, ?_⟩
      left_inv := fun x => by ext; simp
      right_inv := fun w => by ext; simp }
  · refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hcx : c * z * c⁻¹ = (x : G) * z * (x : G)⁻¹ := hc.trans x.2.symm
    calc z * (c⁻¹ * ↑x) = c⁻¹ * (c * z * c⁻¹) * c * (c⁻¹ * ↑x) := by group
      _ = c⁻¹ * ((x : G) * z * (x : G)⁻¹) * c * (c⁻¹ * ↑x) := by rw [hcx]
      _ = c⁻¹ * ↑x * z := by group
  · have hw := Subgroup.mem_centralizer_iff.mp w.2 z rfl
    calc c * ↑w * z * (c * ↑w)⁻¹ = c * (↑w * z) * (↑w)⁻¹ * c⁻¹ := by group
      _ = c * (z * ↑w) * (↑w)⁻¹ * c⁻¹ := by rw [hw]
      _ = c * z * c⁻¹ := by group
      _ = y := hc

/-- **One edge.** When `y` is not conjugate to `z`, no element carries `z` to `y`. -/
theorem card_conjugators_of_not {z y : G} (hzy : ¬ IsConj z y) :
    Nat.card {x : G // x * z * x⁻¹ = y} = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun x => hzy (isConj_iff.mpr ⟨x.1, x.2⟩)⟩

/-- Along a path whose every edge joins conjugate elements, the ends are conjugate. -/
theorem isConj_of_path {X : Skeleton} (h : X.V → G)
    (hne : ∀ e, IsConj (h (X.src e)) (h (X.tgt e))) {u v : X.V} (γ : X.Path u v) :
    IsConj (h u) (h v) := by
  induction γ with
  | nil => exact IsConj.refl _
  | cons e γ ih => exact ih.trans (hne e)

/-- On the transport skeleton of a canvas, every oriented edge joins conjugate elements when every
stored edge does. -/
theorem isConj_oriented {K : Canvas} (h : K.V → G)
    (hne : ∀ e, IsConj (h (K.src e)) (h (K.tgt e))) (e : K.skeleton.E) :
    IsConj (h (K.skeleton.src e)) (h (K.skeleton.tgt e)) := by
  obtain ⟨e', b⟩ := e
  cases b
  · exact (hne e').symm
  · exact hne e'

/-- On a connected canvas, when every `h_v` is conjugate to `h_{v₀}`, the link tables fixed by
`h` number `|C_G(h_{v₀})|^E`. -/
theorem card_fixed_of_conj [Finite G] {K : Canvas} (v₀ : K.V) (h : K.V → G)
    (hall : ∀ v, IsConj (h v₀) (h v)) :
    Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} =
      Nat.card (Subgroup.centralizer {h v₀}) ^ Fintype.card K.E := by
  rw [card_fixed, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [card_conjugators_of_isConj (((hall (K.src e)).symm).trans (hall (K.tgt e))),
    card_centralizer_of_isConj (hall (K.src e))]

/-- On a connected canvas, when some `h_v` is not conjugate to `h_{v₀}`, no link table is fixed
by `h`. -/
theorem card_fixed_of_not_conj [Finite G] {K : Canvas} (hK : K.skeleton.Connected) (v₀ : K.V)
    (h : K.V → G) (hall : ¬ ∀ v, IsConj (h v₀) (h v)) :
    Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} = 0 := by
  have hedge : ∃ e : K.E, ¬ IsConj (h (K.src e)) (h (K.tgt e)) := by
    by_contra hne
    exact hall fun v => isConj_of_path (X := K.skeleton) h
      (isConj_oriented h fun e => not_not.mp fun h' => hne ⟨e, h'⟩) (hK v₀ v).some
  obtain ⟨e, he⟩ := hedge
  rw [card_fixed]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (card_conjugators_of_not he)

end Links

/-! ### Summing over the classes -/

section Classes

variable {G : Type*} [Group G] [Fintype G]

/-- A class and the centralizer of one of its elements: `|C| |C_G(g)| = |G|`. -/
theorem card_class_mul_card_centralizer [DecidableRel (IsConj : G → G → Prop)] (z : G) :
    (Finset.univ.filter fun y => IsConj z y).card * Nat.card (Subgroup.centralizer {z}) =
      Fintype.card G := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := fun x : G => x * z * x⁻¹)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.card_eq_sum_ones, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hc : (Finset.univ.filter fun a : G => a * z * a⁻¹ = y).card =
      Nat.card {x : G // x * z * x⁻¹ = y} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  by_cases hzy : IsConj z y
  · rw [ite_eq_left hzy, one_mul, card_conjugators_of_isConj hzy]
  · rw [ite_eq_right hzy, card_conjugators_of_not hzy]

/-- The classes as fibres: the elements of the class of `g c` are those `x` with `[x] = c`. -/
theorem filter_mk_eq [DecidableEq (ConjClasses G)]
    [DecidableRel (IsConj : G → G → Prop)] (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) (c : ConjClasses G) :
    (Finset.univ.filter fun x => ConjClasses.mk x = c) =
      Finset.univ.filter fun x => IsConj (g c) x := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← ConjClasses.mk_eq_mk_iff_isConj, hg, eq_comm]

/-- `|C| |C_G(g_C)| = |G|` for every class `C`. -/
theorem card_fibre_mul_card_centralizer [DecidableEq (ConjClasses G)]
    (g : ConjClasses G → G) (hg : ∀ c, ConjClasses.mk (g c) = c) (c : ConjClasses G) :
    (Finset.univ.filter fun x => ConjClasses.mk x = c).card *
      Nat.card (Subgroup.centralizer {g c}) = Fintype.card G := by
  classical
  rw [filter_mk_eq g hg, card_class_mul_card_centralizer]

/-- **Summing over a class.** The sum over the gauge changes `h ∈ G^V`, weighted by
`|C_G(h_{v₀})|^E` when every `h_v` is conjugate to `h_{v₀}` and by zero otherwise, of
`Π_v f(h_v)` for a class function `f`, is `Σ_C |C_G(g_C)|^E |C|^V f(g_C)^V`. -/
theorem sum_classes {A : Type*} [CommRing A] [Algebra ℂ A] [Fintype (ConjClasses G)]
    [DecidableEq (ConjClasses G)] {V : Type*} [Fintype V] [DecidableEq V] (v₀ : V) (E : ℕ)
    (f : G → A) (hf : ∀ x y, IsConj x y → f x = f y) (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) (w : (V → G) → ℂ)
    (hw1 : ∀ h, (∀ v, IsConj (h v₀) (h v)) →
      w h = (Nat.card (Subgroup.centralizer {h v₀}) : ℂ) ^ E)
    (hw0 : ∀ h, ¬ (∀ v, IsConj (h v₀) (h v)) → w h = 0) :
    ∑ h : V → G, w h • ∏ v, f (h v) =
      ∑ c : ConjClasses G, ((Nat.card (Subgroup.centralizer {g c}) : ℂ) ^ E *
        ((Finset.univ.filter fun x => ConjClasses.mk x = c).card : ℂ) ^ Fintype.card V) •
          f (g c) ^ Fintype.card V := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun h : V → G => ConjClasses.mk (h v₀))]
  refine Finset.sum_congr rfl fun c _ => ?_
  set T : Finset G := Finset.univ.filter fun x => ConjClasses.mk x = c with hT
  have hpi : ∀ h : V → G, (if ConjClasses.mk (h v₀) = c then w h • ∏ v, f (h v) else 0) =
      if h ∈ Fintype.piFinset (fun _ => T) then
        (Nat.card (Subgroup.centralizer {g c}) : ℂ) ^ E • ∏ v, f (h v) else 0 := by
    intro h
    simp only [Fintype.mem_piFinset, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hall : ∀ v, ConjClasses.mk (h v) = c
    · have hconj : ∀ v, IsConj (h v₀) (h v) := fun v => by
        rw [← ConjClasses.mk_eq_mk_iff_isConj, hall v₀, hall v]
      have hc : IsConj (g c) (h v₀) := by
        rw [← ConjClasses.mk_eq_mk_iff_isConj, hall v₀, hg]
      rw [ite_eq_left (hall v₀), ite_eq_left hall, hw1 h hconj,
        card_centralizer_of_isConj hc]
    · rw [ite_eq_right hall]
      by_cases h0 : ConjClasses.mk (h v₀) = c
      · rw [ite_eq_left h0]
        have hnot : ¬ ∀ v, IsConj (h v₀) (h v) := fun hconj => hall fun v => by
          rw [← h0, ConjClasses.mk_eq_mk_iff_isConj]
          exact (hconj v).symm
        rw [hw0 h hnot, zero_smul]
      · rw [ite_eq_right h0]
  rw [Finset.sum_filter, Finset.sum_congr rfl fun h _ => hpi h, ← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun h : V → G => h ∈ Fintype.piFinset (fun _ => T)) =
      Fintype.piFinset (fun _ => T) := by
    ext h
    simp
  rw [hfilter, ← Finset.smul_sum, ← Finset.prod_univ_sum, Finset.prod_const, Finset.card_univ]
  have hsum : ∑ x ∈ T, f x = (T.card : ℂ) • f (g c) := by
    rw [Nat.cast_smul_eq_nsmul ℂ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hT, Finset.mem_filter] at hx
    refine hf _ _ ?_
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hx.2, hg]
  rw [hsum, smul_pow, smul_smul]

/-- The weight of a class: `(1/|G|^V) |C_G(g_C)|^E |C|^V = |C_G(g_C)|^{E-V}`. -/
theorem weight_eq (cardG cardC cardS : ℕ) (hC : cardC ≠ 0) (hS : cardS ≠ 0)
    (h : cardS * cardC = cardG) (E V : ℕ) :
    ((cardG : ℂ) ^ V)⁻¹ * ((cardC : ℂ) ^ E * (cardS : ℂ) ^ V) =
      (cardC : ℂ) ^ ((E : ℤ) - V) := by
  subst h
  have hC' : (cardC : ℂ) ≠ 0 := by exact_mod_cast hC
  have hS' : (cardS : ℂ) ≠ 0 := by exact_mod_cast hS
  rw [zpow_sub₀ hC', zpow_natCast, zpow_natCast]
  push_cast
  field_simp
  ring

/-- The class of `g_C` is not empty. -/
theorem card_fibre_ne_zero [DecidableEq (ConjClasses G)]
    (g : ConjClasses G → G) (hg : ∀ c, ConjClasses.mk (g c) = c) (c : ConjClasses G) :
    (Finset.univ.filter fun x => ConjClasses.mk x = c).card ≠ 0 :=
  Finset.card_ne_zero.mpr ⟨g c, by simp [hg]⟩

omit [Fintype G] in
/-- A centralizer is not empty. -/
theorem card_centralizer_ne_zero [Finite G] (z : G) : Nat.card (Subgroup.centralizer {z}) ≠ 0 :=
  Nat.card_pos.ne'

end Classes

/-! ### The matter of a canvas -/

section Matter

variable {G : Type*} [Group G] {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S]
  [DecidableEq S]

omit [Fintype S] in
theorem gaugeMatrix_one (K : Canvas) (ρ : G →* Matrix C C ℂ) :
    K.gaugeMatrix (S := S) ρ 1 = 1 := by
  rw [Canvas.gaugeMatrix]
  simp only [Pi.one_apply, map_one, Matrix.one_kronecker_one]
  exact Matrix.blockDiagonal_one

theorem gaugeMatrix_mul (K : Canvas) (ρ : G →* Matrix C C ℂ) (h k : K.V → G) :
    K.gaugeMatrix (S := S) ρ (h * k) = K.gaugeMatrix ρ h * K.gaugeMatrix ρ k := by
  rw [Canvas.gaugeMatrix, Canvas.gaugeMatrix, Canvas.gaugeMatrix, ← Matrix.blockDiagonal_mul]
  congr 1
  funext v
  rw [Pi.mul_apply, map_mul, Fock.kron_one_mul]

/-- The colour rotations of the matter of a canvas, a homomorphism of the gauge group. -/
noncomputable def matterHom (K : Canvas) (ρ : G →* Matrix C C ℂ)
    (ord : LinearOrder (K.Mode C S)) :
    (K.V → G) →* Matrix (Finset (K.Mode C S)) (Finset (K.Mode C S)) ℂ where
  toFun h := K.matterGauge ρ ord h
  map_one' := by rw [Canvas.matterGauge, gaugeMatrix_one, Fock.secondQuant_one]
  map_mul' h k := by
    simp only [Canvas.matterGauge]
    rw [gaugeMatrix_mul, Fock.secondQuant_mul]

/-- `det(1 + z D(h)) = Π_v det(1 + z ρ(h_v))^d`. -/
theorem det_one_add_gaugeMatrix (K : Canvas) (ρ : G →* Matrix C C ℂ) (h : K.V → G) :
    (1 + (X : ℂ[X]) • (K.gaugeMatrix (S := S) ρ h).map Polynomial.C).det =
      ∏ v, (1 + (X : ℂ[X]) • (ρ (h v)).map Polynomial.C).det ^ Fintype.card S := by
  rw [Canvas.gaugeMatrix, Matrix.blockDiagonal_map _ _ (map_zero _),
    ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_add,
    Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply]
  rw [Edge.kron_one_map_smul, Edge.det_one_add_kron_one]

/-- The trace of `Γ(h)` on the tables with `n` quarks is the coefficient of `z^n` in
`Π_v det(1 + z ρ(h_v))^d`. -/
theorem sum_numberSector_matterGauge (K : Canvas) (ρ : G →* Matrix C C ℂ)
    (ord : LinearOrder (K.Mode C S)) (h : K.V → G) (n : ℕ) :
    ∑ m ∈ Finset.univ.filter (fun m : Finset (K.Mode C S) => m.card = n),
        K.matterGauge ρ ord h m m =
      (∏ v, (1 + (X : ℂ[X]) • (ρ (h v)).map Polynomial.C).det ^ Fintype.card S).coeff n := by
  rw [Edge.filter_card_eq_powersetCard, Canvas.matterGauge,
    Fock.sum_powersetCard_secondQuant_diag, det_one_add_gaugeMatrix]

/-- `det(1 + z ρ(g))` depends on the class of `g`. -/
theorem det_one_add_conj (ρ : G →* Matrix C C ℂ) {x y : G} (hxy : IsConj x y) :
    (1 + (X : ℂ[X]) • (ρ x).map Polynomial.C).det =
      (1 + (X : ℂ[X]) • (ρ y).map Polynomial.C).det := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  have hinv : (ρ c).map Polynomial.C * (ρ c⁻¹).map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have hinv' : (ρ c⁻¹).map Polynomial.C * (ρ c).map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have h : 1 + (X : ℂ[X]) • (ρ (c * x * c⁻¹)).map Polynomial.C =
      (ρ c).map Polynomial.C * (1 + (X : ℂ[X]) • (ρ x).map Polynomial.C) *
        (ρ c⁻¹).map Polynomial.C := by
    rw [map_mul, map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [h, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hinv',
    Matrix.det_one, one_mul]

end Matter

/-! ### The census -/

section Census

variable {G : Type*} [Group G] [Fintype G]

/-- **Averaging over the gauge group of a canvas.** The covariant tables supported on `p` number
`(1/|G|^V) Σ_h |Fix(h)| Σ_{n ∈ p} Γ(h)_{nn}`, `Fix(h)` the link tables fixed by `h`. -/
theorem finrank_canvas (K : Canvas) {N : Type*} [Fintype N] [DecidableEq N]
    (Γ : (K.V → G) →* Matrix N N ℂ) (p : N → Prop) [DecidablePred p]
    (hp : ∀ h n' n, Γ h n' n ≠ 0 → (p n' ↔ p n)) :
    (Module.finrank ℂ ↥(covariant (Skeleton.gaugeAct (X := K.skeleton)) Γ ⊓
        supported (K.skeleton.LinkTable G) p) : ℂ) =
      ((Fintype.card G : ℂ) ^ Fintype.card K.V)⁻¹ * ∑ h : K.V → G,
        (Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} : ℂ) *
          ∑ n ∈ Finset.univ.filter p, Γ h n n := by
  classical
  rw [finrank_covariant (Skeleton.gaugeAct (X := K.skeleton)) Skeleton.gaugeAct_one
    (fun h k U => (Skeleton.gaugeAct_gaugeAct h k U).symm) Γ p hp, Fintype.card_fun]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Nat.card_eq_fintype_card]

end Census

/-! ### Theorem 13.11 -/

section Theorems

variable {G : Type*} [Group G] [Fintype G]

/-- The sum over the gauge changes, grouped by classes and divided by `|G|^V`. -/
theorem average_classes {A : Type*} [CommRing A] [Algebra ℂ A] [Fintype (ConjClasses G)]
    (K : Canvas) (v₀ : K.V) (hK : K.skeleton.Connected)
    (f : G → A) (hf : ∀ x y, IsConj x y → f x = f y) (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) :
    ((Fintype.card G : ℂ) ^ Fintype.card K.V)⁻¹ • ∑ h : K.V → G,
        (Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} : ℂ) •
          ∏ v, f (h v) =
      ∑ c : ConjClasses G, ((Nat.card (Subgroup.centralizer {g c}) : ℂ) ^
        ((Fintype.card K.E : ℤ) - Fintype.card K.V)) • f (g c) ^ Fintype.card K.V := by
  classical
  rw [sum_classes v₀ (Fintype.card K.E) f hf g hg _
    (fun h hall => by rw [card_fixed_of_conj v₀ h hall]; push_cast; rfl)
    (fun h hall => by rw [card_fixed_of_not_conj hK v₀ h hall, Nat.cast_zero]),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul]
  congr 1
  exact weight_eq (Fintype.card G) _ _ (card_centralizer_ne_zero (g c))
    (card_fibre_ne_zero g hg c) (card_fibre_mul_card_centralizer g hg c) _ _

open Classical in
/-- Theorem 13.11, first part: the colourless states with `n` quarks. -/
theorem census_matter {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
    (ρ : G →* Matrix C C ℂ) (K : Canvas) (hV : Nonempty K.V) (hK : K.skeleton.Connected)
    (ord : LinearOrder (K.Mode C S)) (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) (n : ℕ) :
    (Module.finrank ℂ ↥(K.colourless ρ ord ⊓
        Edge.stateSector (K.skeleton.LinkTable G) (Fock.numberSector (K.Mode C S) n)) : ℂ) =
      (∑ c : ConjClasses G, ((Nat.card (Subgroup.centralizer {g c}) : ℂ) ^
          ((Fintype.card K.E : ℤ) - Fintype.card K.V)) •
        (1 + (X : ℂ[X]) • (ρ (g c)).map Polynomial.C).det ^
          (Fintype.card S * Fintype.card K.V)).coeff n := by
  obtain ⟨v₀⟩ := hV
  have hsub : K.colourless ρ ord ⊓
      Edge.stateSector (K.skeleton.LinkTable G) (Fock.numberSector (K.Mode C S) n) =
      covariant (Skeleton.gaugeAct (X := K.skeleton)) (matterHom K ρ ord) ⊓
        supported (K.skeleton.LinkTable G) (fun m : Finset (K.Mode C S) => m.card = n) := by
    ext ψ
    simp only [Submodule.mem_inf, Edge.stateSector, Submodule.mem_pi, Set.mem_univ,
      true_implies, Fock.mem_numberSector, mem_supported]
    rfl
  set f : G → ℂ[X] := fun x => (1 + (X : ℂ[X]) • (ρ x).map Polynomial.C).det ^ Fintype.card S
    with hf
  have hfc : ∀ x y, IsConj x y → f x = f y := fun x y hxy => by
    simp only [hf, det_one_add_conj ρ hxy]
  rw [hsub, finrank_canvas K (matterHom K ρ ord) _
    (fun h n' m hne => by rw [Fock.secondQuant_card_eq ord _ hne])]
  have htr : ∀ h : K.V → G, ∑ m ∈ Finset.univ.filter (fun m : Finset (K.Mode C S) => m.card = n),
      matterHom K ρ ord h m m = (∏ v, f (h v)).coeff n := fun h =>
    sum_numberSector_matterGauge K ρ ord h n
  simp only [htr]
  have hcoeff : ∀ h : K.V → G,
      (Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} : ℂ) *
        (∏ v, f (h v)).coeff n =
      ((Nat.card {U : K.skeleton.LinkTable G // Skeleton.gaugeAct h U = U} : ℂ) •
        ∏ v, f (h v)).coeff n := fun h => by
    rw [Polynomial.coeff_smul, smul_eq_mul]
  simp only [hcoeff]
  have hsmul : ∀ (r : ℂ) (P : ℂ[X]), r * P.coeff n = (r • P).coeff n := fun r P => by
    rw [Polynomial.coeff_smul, smul_eq_mul]
  rw [← Polynomial.finsetSum_coeff, hsmul, average_classes K v₀ hK f hfc g hg]
  simp only [hf, ← pow_mul]

omit [Fintype G] in
/-- Theorem 13.11, without matter. -/
theorem census_noMatter [Finite G] [Fintype (ConjClasses G)] (K : Canvas)
    (hV : Nonempty K.V) (hK : K.skeleton.Connected) (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) :
    (Module.finrank ℂ ↥(K.gaugeInvariants G) : ℂ) =
      ∑ c : ConjClasses G, (Nat.card (Subgroup.centralizer {g c}) : ℂ) ^
        ((Fintype.card K.E : ℤ) - Fintype.card K.V) := by
  have := Fintype.ofFinite G
  obtain ⟨v₀⟩ := hV
  let e : (K.skeleton.LinkTable G → ℂ) ≃ₗ[ℂ] (K.skeleton.LinkTable G → Unit → ℂ) :=
    { toFun := fun ψ U _ => ψ U
      invFun := fun ψ U => ψ U ()
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmap : (K.gaugeInvariants G).map (e : (K.skeleton.LinkTable G → ℂ) →ₗ[ℂ] _) =
      covariant (Skeleton.gaugeAct (X := K.skeleton))
        (1 : (K.V → G) →* Matrix Unit Unit ℂ) ⊓
        supported (K.skeleton.LinkTable G) (fun _ : Unit => True) := by
    ext ψ
    simp only [Submodule.mem_map, Submodule.mem_inf, mem_covariant, mem_supported,
      MonoidHom.one_apply, Matrix.one_mulVec]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨fun h U => by funext u; exact hφ h U, fun _ _ _ => trivial⟩
    · rintro ⟨hcov, -⟩
      refine ⟨fun U => ψ U (), fun h U => congrFun (hcov h U) (), ?_⟩
      funext U u
      rfl
  rw [LinearEquiv.finrank_eq (e.ofSubmodules _ _ hmap),
    finrank_canvas K (1 : (K.V → G) →* Matrix Unit Unit ℂ) (fun _ => True)
      (fun _ _ _ _ => Iff.rfl)]
  have h1 : ∀ h : K.V → G, ∑ n ∈ Finset.univ.filter (fun _ : Unit => True),
      (1 : (K.V → G) →* Matrix Unit Unit ℂ) h n n = ∏ _v : K.V, (1 : ℂ) := fun h => by
    simp
  simp only [h1, ← smul_eq_mul (a := (Nat.card _ : ℂ))]
  rw [← smul_eq_mul, average_classes K v₀ hK (fun _ => (1 : ℂ)) (fun _ _ _ => rfl) g hg]
  simp

omit [Fintype G] in
/-- Theorem 13.11 on a tree: one state. -/
theorem census_tree [Finite G] (K : Canvas) (hV : Nonempty K.V) (hK : K.skeleton.Connected)
    (hE : Fintype.card K.E + 1 = Fintype.card K.V) :
    Module.finrank ℂ ↥(K.gaugeInvariants G) = 1 := by
  classical
  have := Fintype.ofFinite G
  have h := census_noMatter K hV hK (fun c : ConjClasses G => c.out) (fun c => Quotient.out_eq c)
  have hexp : (Fintype.card K.E : ℤ) - Fintype.card K.V = -1 := by omega
  rw [hexp] at h
  have hsum : ∑ c : ConjClasses G, (Nat.card (Subgroup.centralizer {c.out}) : ℂ) ^ (-1 : ℤ) =
      1 := by
    have hcard : ∀ c : ConjClasses G, (Nat.card (Subgroup.centralizer {c.out}) : ℂ) ^ (-1 : ℤ) =
        ((Finset.univ.filter fun x => ConjClasses.mk x = c).card : ℂ) / Fintype.card G := by
      intro c
      have h1 := card_fibre_mul_card_centralizer (fun c : ConjClasses G => c.out)
        (fun c => Quotient.out_eq c) c
      have hC : (Nat.card (Subgroup.centralizer {c.out}) : ℂ) ≠ 0 := by
        exact_mod_cast card_centralizer_ne_zero c.out
      have hS : ((Finset.univ.filter fun x => ConjClasses.mk x = c).card : ℂ) ≠ 0 := by
        exact_mod_cast card_fibre_ne_zero (fun c : ConjClasses G => c.out)
          (fun c => Quotient.out_eq c) c
      rw [zpow_neg_one, ← h1]
      push_cast
      field_simp
    simp only [hcard]
    rw [← Finset.sum_div, ← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise
      (fun _ _ => Finset.mem_univ _), Finset.card_univ]
    have : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact div_self this
  rw [hsum] at h
  exact_mod_cast h

omit [Fintype G] in
/-- Theorem 13.11 on a canvas with a single loop: one state per class. -/
theorem census_loop [Finite G] (K : Canvas) (hV : Nonempty K.V) (hK : K.skeleton.Connected)
    (hE : Fintype.card K.E = Fintype.card K.V) :
    Module.finrank ℂ ↥(K.gaugeInvariants G) = Nat.card (ConjClasses G) := by
  classical
  have := Fintype.ofFinite G
  have h := census_noMatter K hV hK (fun c : ConjClasses G => c.out) (fun c => Quotient.out_eq c)
  rw [hE, sub_self] at h
  simp only [zpow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast h

/-- The class sum and the element sum: `|G| Σ_C |C_G(g_C)|^m = Σ_x |C_G(x)|^{m+1}`. -/
theorem sum_classes_pow [Fintype (ConjClasses G)] (g : ConjClasses G → G)
    (hg : ∀ c, ConjClasses.mk (g c) = c) (m : ℕ) :
    Fintype.card G * ∑ c : ConjClasses G, Nat.card (Subgroup.centralizer {g c}) ^ m =
      ∑ x : G, Nat.card (Subgroup.centralizer {x}) ^ (m + 1) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : G => ConjClasses.mk x), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hx : ∀ x ∈ Finset.univ.filter (fun x : G => ConjClasses.mk x = c),
      Nat.card (Subgroup.centralizer {x}) ^ (m + 1) =
        Nat.card (Subgroup.centralizer {g c}) ^ (m + 1) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [card_centralizer_of_isConj (z := g c) (y := x)
      (by rw [← ConjClasses.mk_eq_mk_iff_isConj, hx.2, hg])]
  rw [Finset.sum_congr rfl hx, Finset.sum_const, smul_eq_mul, pow_succ, ← mul_assoc,
    mul_comm _ (Nat.card _ ^ m), ← card_fibre_mul_card_centralizer g hg c]
  ring

omit [Fintype G] in
/-- `det(1 + D(h)) = Π_v det(1 + ρ(h_v))^d`. -/
theorem det_one_add_gaugeMatrix' {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (K : Canvas) (ρ : G →* Matrix C C ℂ) (h : K.V → G) :
    (1 + K.gaugeMatrix (S := S) ρ h).det = ∏ v, (1 + ρ (h v)).det ^ Fintype.card S := by
  rw [Canvas.gaugeMatrix, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_add,
    Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.add_apply, Pi.one_apply, Edge.det_one_add_kron_one]

omit [Fintype G] in
/-- Theorem 13.11, the zero-flux states: the one-vertex count to the power `V`. -/
theorem census_zeroFlux [Finite G] {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (ρ : G →* Matrix C C ℂ) (K : Canvas) (ord : LinearOrder (K.Mode C S))
    (ordv : LinearOrder (C × S)) :
    Module.finrank ℂ ↥(K.zeroFlux ρ ord) =
      Module.finrank ℂ ↥(Edge.vertexInvariants ρ ordv) ^ Fintype.card K.V := by
  classical
  have := Fintype.ofFinite G
  let U₀ : K.skeleton.LinkTable G := Skeleton.LinkTable.ofGraph fun _ => 1
  have hfix : ∀ ψ ∈ K.zeroFlux ρ ord, ψ U₀ ∈ Fock.fixedSub (matterHom K ρ ord) := by
    intro ψ hψ h
    have h1 := hψ.1 h U₀
    rw [hψ.2 (Skeleton.gaugeAct h U₀) U₀] at h1
    exact h1.symm
  have hconst : ∀ v ∈ Fock.fixedSub (matterHom K ρ ord),
      (fun _ : K.skeleton.LinkTable G => v) ∈ K.zeroFlux ρ ord := by
    intro v hv
    exact ⟨fun h U => (hv h).symm, fun _ _ => rfl⟩
  let e : ↥(K.zeroFlux ρ ord) ≃ₗ[ℂ] ↥(Fock.fixedSub (matterHom K ρ ord)) :=
    { toFun := fun ψ => ⟨ψ.1 U₀, hfix ψ.1 ψ.2⟩
      invFun := fun v => ⟨fun _ => v.1, hconst v.1 v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun ψ => Subtype.ext (funext fun U => ψ.2.2 U₀ U)
      right_inv := fun _ => rfl }
  apply Nat.cast_injective (R := ℂ)
  rw [LinearEquiv.finrank_eq e, Fock.finrank_fixedSub, Nat.cast_pow,
    Edge.finrank_vertexInvariants ρ ordv, Fintype.card_fun]
  have htr : ∀ h : K.V → G, (matterHom K ρ ord h).trace =
      ∏ v, (1 + ρ (h v)).det ^ Fintype.card S := fun h => by
    rw [show matterHom K ρ ord h = Fock.secondQuant ord (K.gaugeMatrix ρ h) from rfl,
      Fock.trace_secondQuant, det_one_add_gaugeMatrix']
  simp only [htr]
  rw [← Fintype.prod_sum (fun (_ : K.V) (g : G) => (1 + ρ g).det ^ Fintype.card S),
    Finset.prod_const, Finset.card_univ, mul_pow, Nat.cast_pow, inv_pow]

/-! ### The cube -/

/-- The cube is connected: paths from the corner `0` reach every corner. -/
theorem cube_connected : Canvas.cube.skeleton.Connected := by
  refine Skeleton.connected_of_base (X := Canvas.cube.skeleton) (0 : Fin 8) fun v => ?_
  have step : ∀ e : Canvas.cube.skeleton.E,
      Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (Canvas.cube.skeleton.src e)) →
        Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (Canvas.cube.skeleton.tgt e)) :=
    fun e h => ⟨.cons e h.some⟩
  have p0 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (0 : Fin 8)) := ⟨.nil _⟩
  have p1 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (1 : Fin 8)) :=
    step ((8 : Fin 12), true) p0
  have p2 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (2 : Fin 8)) :=
    step ((4 : Fin 12), true) p0
  have p3 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (3 : Fin 8)) :=
    step ((5 : Fin 12), true) p1
  have p4 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (4 : Fin 8)) :=
    step ((0 : Fin 12), true) p0
  have p5 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (5 : Fin 8)) :=
    step ((1 : Fin 12), true) p1
  have p6 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (6 : Fin 8)) :=
    step ((2 : Fin 12), true) p2
  have p7 : Nonempty (Canvas.cube.skeleton.Path (0 : Fin 8) (7 : Fin 8)) :=
    step ((3 : Fin 12), true) p3
  change Fin 8 at v
  fin_cases v
  exacts [p0, p1, p2, p3, p4, p5, p6, p7]

theorem card_cube_V : Fintype.card Canvas.cube.V = 8 := rfl

theorem card_cube_E : Fintype.card Canvas.cube.E = 12 := rfl

open ColourGroups Exact in
/-- The rotations of the cube that commute with the rotation `k`, counted on the matrices. -/
def centCount (k : Fin 24) : ℕ :=
  (Finset.univ.filter fun l : Fin 24 =>
    M3Z.mul (cubeE k) (cubeE l) = M3Z.mul (cubeE l) (cubeE k)).card

theorem centCount_sum : ∑ k : Fin 24, centCount k ^ 5 = 8075160 := by
  decide +kernel

open ColourGroups Exact in
theorem cubeElt_mul_comm_iff (k l : Fin 24) :
    cubeElt k * cubeElt l = cubeElt l * cubeElt k ↔
      M3Z.mul (cubeE k) (cubeE l) = M3Z.mul (cubeE l) (cubeE k) := by
  have hmat : ∀ a b : Fin 24, (((cubeElt a * cubeElt b : cubeGroup) :
      Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
        M3Z.toMat (M3Z.mul (cubeE a) (cubeE b)) := fun a b => by
    rw [M3Z.toMat_mul]
    rfl
  constructor
  · intro h
    apply M3Z.toMat_injective
    rw [← hmat, ← hmat, h]
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    rw [hmat, hmat, h]

open ColourGroups in
theorem card_centralizer_cubeElt (k : Fin 24) :
    Nat.card (Subgroup.centralizer {cubeElt k}) = centCount k := by
  rw [centCount, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv (p := fun w => w ∈ Subgroup.centralizer {cubeElt k})
    cubeEquiv.symm fun w => ?_)
  obtain ⟨l, rfl⟩ := cubeEquiv.surjective w
  rw [Equiv.symm_apply_apply, Subgroup.mem_centralizer_singleton_iff]
  change cubeElt l * cubeElt k = cubeElt k * cubeElt l ↔ _
  rw [eq_comm, cubeElt_mul_comm_iff]

open ColourGroups in
/-- Theorem 13.11 on the cube: `336 465` colourless states of the cube group without matter. -/
theorem census_cube : Module.finrank ℂ ↥(Canvas.cube.gaugeInvariants cubeGroup) = 336465 := by
  classical
  have h := census_noMatter Canvas.cube ⟨(0 : Fin 8)⟩ cube_connected
    (fun c : ConjClasses cubeGroup => c.out) (fun c => Quotient.out_eq c)
  have hE : (Fintype.card Canvas.cube.E : ℤ) - Fintype.card Canvas.cube.V = (4 : ℕ) := by
    rw [card_cube_E, card_cube_V]
    norm_num
  rw [hE] at h
  simp only [zpow_natCast] at h
  have hsum : ∑ c : ConjClasses cubeGroup, Nat.card (Subgroup.centralizer {c.out}) ^ 4 =
      336465 := by
    have h1 := sum_classes_pow (fun c : ConjClasses cubeGroup => c.out)
      (fun c => Quotient.out_eq c) 4
    rw [← Equiv.sum_comp cubeEquiv] at h1
    have h2 : ∀ k : Fin 24, Nat.card (Subgroup.centralizer {cubeEquiv k}) ^ (4 + 1) =
        centCount k ^ 5 := fun k => by
      rw [show cubeEquiv k = cubeElt k from rfl, card_centralizer_cubeElt]
    simp only [h2, centCount_sum] at h1
    have hcard : Fintype.card cubeGroup = 24 := by
      rw [← Nat.card_eq_fintype_card, card_cubeGroup]
    rw [hcard] at h1
    omega
  have hC : (∑ c : ConjClasses cubeGroup,
      (Nat.card (Subgroup.centralizer {c.out}) : ℂ) ^ 4) = ((336465 : ℕ) : ℂ) := by
    rw [← hsum]
    push_cast
    rfl
  rw [hC] at h
  exact_mod_cast h

end Theorems

end Census

open Census

/-- **Theorem 13.11** (census of a canvas). On a connected canvas with `V` vertices, `E` edges and
`d` slots at every vertex, the number of colourless states with `n` quarks is the coefficient of
`z^n` in `Σ_C |C_G(C)|^{E-V} det(1 + z g_C)^{dV}`. Without matter the count is
`Σ_C |C_G(C)|^{E-V}`: one state on a tree, one per class on a canvas with a single loop, and
`336 465` for the cube group on the cube. The zero-flux states number the one-vertex count to the
power `V`. -/
@[book "thm:ml-canvas-census"]
theorem mlCanvasCensus : Statement.mlCanvasCensus := by
  classical
  exact
  ⟨fun _ _ _ _ _ _ _ _ _ ρ K hV hK ord g hg n => census_matter ρ K hV hK ord g hg n,
    fun _ _ _ K hV hK g hg => census_noMatter K hV hK g hg,
    fun _ _ _ K hV hK hE => census_tree K hV hK hE,
    fun _ _ _ K hV hK hE => census_loop K hV hK hE,
    census_cube,
    fun _ _ _ _ _ _ _ _ _ ρ K ord ordv => census_zeroFlux ρ K ord ordv⟩

/-! ## Non-vacuity -/

section NonVacuity

/-- An order of the modes of the cube with two slots at every vertex. -/
@[instance_reducible]
noncomputable def cubeTwoSlotOrder : LinearOrder (Canvas.cube.Mode (Fin 3) (Fin 2)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- The hypotheses of Theorem 13.11 are met on the book's canvas, the cube, with Model I, the cube
group: the cube has a vertex and is connected, and the representatives `c.out` lie in their
classes. -/
example : Nonempty Canvas.cube.V ∧ Canvas.cube.skeleton.Connected ∧
    ∀ c : ConjClasses cubeGroup, ConjClasses.mk c.out = c :=
  ⟨⟨(0 : Fin 8)⟩, cube_connected, fun c => Quotient.out_eq c⟩

/-- Theorem 13.11 on the cube with the cube group, its triplet and two slots at every vertex: the
colourless states with no quark. -/
example :=
  mlCanvasCensus.1 cubeGroup (Fin 3) (Fin 2) cubeTriplet Canvas.cube ⟨(0 : Fin 8)⟩
    cube_connected cubeTwoSlotOrder (fun c => c.out) (fun c => Quotient.out_eq c) 0

/-- Theorem 13.11 on the cube without matter: `336 465` states for the cube group. -/
example : Module.finrank ℂ ↥(Canvas.cube.gaugeInvariants cubeGroup) = 336465 :=
  mlCanvasCensus.2.2.2.2.1

/-- One vertex and no edge: the smallest tree. -/
def pointCanvas : Canvas where
  V := Unit
  E := Empty
  F := Empty
  src e := e.elim
  tgt e := e.elim
  boundary f := f.elim
  closed f := f.elim

/-- The tree hypotheses of Theorem 13.11 are met by one vertex with no edge, and the cube group
has one colourless state there. -/
example : Module.finrank ℂ ↥(pointCanvas.gaugeInvariants cubeGroup) = 1 :=
  mlCanvasCensus.2.2.1 cubeGroup pointCanvas ⟨()⟩
    (fun u v => by cases u; cases v; exact ⟨@Skeleton.Path.nil pointCanvas.skeleton ()⟩) rfl

/-- The square of Chapter 12 is connected: one loop. -/
theorem square_connected : ColourGroups.squareCanvas.skeleton.Connected := by
  refine Skeleton.connected_of_base (X := ColourGroups.squareCanvas.skeleton) (0 : Fin 4)
    fun v => ?_
  have step : ∀ e : ColourGroups.squareCanvas.skeleton.E,
      Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4)
        (ColourGroups.squareCanvas.skeleton.src e)) →
      Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4)
        (ColourGroups.squareCanvas.skeleton.tgt e)) :=
    fun e h => ⟨.cons e h.some⟩
  have p0 : Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4) (0 : Fin 4)) :=
    ⟨.nil _⟩
  have p1 : Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4) (1 : Fin 4)) :=
    step ((0 : Fin 4), true) p0
  have p2 : Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4) (2 : Fin 4)) :=
    step ((1 : Fin 4), true) p1
  have p3 : Nonempty (ColourGroups.squareCanvas.skeleton.Path (0 : Fin 4) (3 : Fin 4)) :=
    step ((2 : Fin 4), true) p2
  change Fin 4 at v
  fin_cases v
  exacts [p0, p1, p2, p3]

/-- The single-loop hypotheses of Theorem 13.11 are met by the square: it is connected with four
vertices and four edges, and the cube group has one colourless state per class there. -/
example : Module.finrank ℂ ↥(ColourGroups.squareCanvas.gaugeInvariants cubeGroup) =
    Nat.card (ConjClasses cubeGroup) :=
  mlCanvasCensus.2.2.2.1 cubeGroup ColourGroups.squareCanvas ⟨(0 : Fin 4)⟩ square_connected rfl

end NonVacuity

end Artform
