import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.OfMap
import ArtformTextbook.Ch03.Statements.Recognition

/-!
# Recognition (Propositions 3.11, 3.12, 3.22 and 3.45)

The book calls these proofs checks of the definitions, and so they are. Proposition 3.22 is
where every variable of a template occurring in an atom is used: equal atom images then cover
equal sets of positions.
-/

namespace Artform

/-! ## Shared positive patterns (Proposition 3.11) -/

namespace Instantiation

variable {R : RecognitionProfile} {K : PositiveTemplate R} {G G₁ G₂ : ProfiledState R}

theorem comparison_apply (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂)
    (p : Set.range j₁) : j₁.comparison j₂ p = j₂ ((Equiv.ofInjective j₁ j₁.injective).symm p) :=
  rfl

/-- The comparison `j₂ ∘ j₁⁻¹` sends `j₁ x` to `j₂ x`. -/
theorem comparison_rangeFactorization (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂)
    (x : K.Var) : j₁.comparison j₂ (Set.rangeFactorization j₁ x) = j₂ x := by
  rw [comparison_apply]
  exact congrArg j₂ (Equiv.ofInjective_symm_apply j₁.injective x)

/-- `j₂ ∘ j₁⁻¹`, on `j₁(E_K)`, is a sort-preserving injection. -/
theorem comparison_isPartialComparison (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂) :
    IsPartialComparison G₁ G₂ (Set.range j₁) (j₁.comparison j₂) := by
  refine ⟨j₂.injective.comp (Equiv.ofInjective j₁ j₁.injective).symm.injective, fun p => ?_⟩
  rw [comparison_apply, j₂.sort_eq, ← j₁.sort_eq, Equiv.apply_ofInjective_symm j₁.injective p]

/-- Every atom of `j₁*(𝒜_K)` is credited to `j₂ ∘ j₁⁻¹`. -/
theorem map_mem_creditedAtoms (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂)
    {α : Atom R K.Var} (hα : α ∈ K.atoms) :
    α.map j₁ ∈ creditedAtoms G₁ G₂ (Set.range j₁) (j₁.comparison j₂) := by
  refine ⟨j₁.atoms_sub ⟨α, hα, rfl⟩, α.map (Set.rangeFactorization j₁), ?_, ?_⟩
  · rw [Atom.map_map]
    rfl
  · rw [Atom.map_map]
    have h : j₁.comparison j₂ ∘ Set.rangeFactorization j₁ = j₂ :=
      funext (comparison_rangeFactorization j₁ j₂)
    rw [h]
    exact j₂.atoms_sub ⟨α, hα, rfl⟩

end Instantiation

namespace PartialComparison

variable {R : RecognitionProfile} {G₁ G₂ : ProfiledState R} (F : PartialComparison G₁ G₂)

/-- The active positions of `F`, as positions of `G₁`. -/
abbrev activeVal : F.active → G₁.Pos := fun x => ((x : F.dom) : G₁.Pos)

theorem activeVal_injective : Function.Injective F.activeVal :=
  Subtype.val_injective.comp Subtype.val_injective

/-- A credited atom is the renaming of an atom over the active positions. -/
theorem exists_active_of_credited {α : Atom R G₁.Pos} (hα : α ∈ F.credited) :
    ∃ β : Atom R F.active, β.map F.activeVal = α := by
  obtain ⟨-, β₀, hβ₀, -⟩ := id hα
  have hvars : β₀.vars ⊆ F.active := by
    intro p hp
    refine ⟨α, hα, ?_⟩
    rw [← hβ₀, Atom.vars_map]
    exact ⟨p, hp, rfl⟩
  obtain ⟨β, hβ⟩ := Atom.exists_map_val hvars
  refine ⟨β, ?_⟩
  rw [← hβ₀, ← hβ, Atom.map_map]
  rfl

/-- The positive template `K_F` of a comparison that credits an atom: its variables are the
active positions, renamed, and its atoms are the credited atoms, transported. -/
def template (h : F.credited.Nonempty) : PositiveTemplate R where
  Var := F.active
  sort x := G₁.sort (F.activeVal x)
  atoms := {β | β.map F.activeVal ∈ F.credited}
  atoms_finite := Set.toFinite _
  atoms_nonempty := by
    obtain ⟨α, hα⟩ := h
    obtain ⟨β, hβ⟩ := F.exists_active_of_credited hα
    exact ⟨β, show β.map F.activeVal ∈ F.credited by rw [hβ]; exact hα⟩
  covers x := by
    obtain ⟨α, hα, hx⟩ : ∃ α ∈ F.credited, F.activeVal x ∈ α.vars := x.2
    obtain ⟨β, hβ⟩ := F.exists_active_of_credited hα
    refine ⟨β, show β.map F.activeVal ∈ F.credited by rw [hβ]; exact hα, ?_⟩
    rw [← hβ, Atom.vars_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [F.activeVal_injective hyx] at hy

/-- The renaming instantiates `K_F` in `G₁`. -/
def inst₁ (h : F.credited.Nonempty) : Instantiation (F.template h) G₁ where
  toFun := F.activeVal
  isInstantiation := by
    refine ⟨F.activeVal_injective, fun _ => rfl, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    exact hβ.1

/-- `F` after the renaming instantiates `K_F` in `G₂`. -/
def inst₂ (h : F.credited.Nonempty) : Instantiation (F.template h) G₂ where
  toFun := fun x : F.active => F.toFun x
  isInstantiation := by
    refine ⟨F.isPartialComparison.1.comp Subtype.val_injective,
      fun x : F.active => F.isPartialComparison.2 x, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨-, β', hβ', hβ'2⟩ := hβ
    have hβ'' : β' = Atom.map (Subtype.val : F.active → F.dom) β :=
      Atom.map_injective Subtype.val_injective (hβ'.trans (Atom.map_map _ _ β).symm)
    subst hβ''
    exact (congrArg (· ∈ G₂.posReduct)
      (Atom.map_map (Subtype.val : F.active → F.dom) F.toFun β)).mp hβ'2

end PartialComparison

/-- **Proposition 3.11** (shared positive pattern). Two instantiations of one template give a
partial positive comparison crediting the instantiated atoms, and a comparison crediting an atom
gives a template with two instantiations. -/
@[book "prop:shared-positive-pattern-book"]
theorem sharedPositivePattern : Statement.sharedPositivePattern := by
  intro R G₁ G₂
  refine ⟨fun K j₁ j₂ => ⟨j₁.comparison_isPartialComparison j₂, ?_⟩, fun F h => ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    exact j₁.map_mem_creditedAtoms j₂ hα
  · exact ⟨F.template h, Equiv.refl _, F.inst₁ h, F.inst₂ h, fun _ => rfl, rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl⟩

/-! ## Partial profile isomorphisms (Proposition 3.12) -/

section PartialIso

variable {R : RecognitionProfile} {G₁ G₂ : ProfiledState R} {D : Set G₁.Pos} {D' : Set G₂.Pos}

/-- Tables that agree through a sort-preserving injection make it a strong occurrence of the
restriction, with the identity label map. -/
theorem isStrongOccurrence_of_tablesAgree {f : D → G₂.Pos} (hinj : Function.Injective f)
    (hsort : ∀ x, G₂.sort (f x) = G₁.sort x) (h : TablesAgree G₁ G₂ D f) :
    IsStrongOccurrence (G₁.restrict D) G₂ 1 f where
  injective := hinj
  sort_eq := hsort
  preserves r t ht := (h.1 r t).trans ht
  reflects r t ht := (h.1 r t).symm.trans ht
  agrees a t := by
    refine (h.2 a t).trans ?_
    change G₁.chan a (Subtype.val ∘ t) =
      Option.map (fun x => (1 : R.Relabel) • x) (G₁.chan a (Subtype.val ∘ t))
    simp

/-- Tables that agree through `f` make `f` credit every atom of its domain. -/
theorem creditsEveryAtom_of_tablesAgree {f : D → G₂.Pos} (h : TablesAgree G₁ G₂ D f) :
    CreditsEveryAtom G₁ G₂ D f := by
  intro α hα hvars
  obtain ⟨β, rfl⟩ := Atom.exists_map_val hvars
  refine ⟨hα, β, rfl, ?_⟩
  cases β with
  | rel r t =>
    change G₂.rel r (f ∘ t) = some true
    rw [h.1 r t]
    exact hα
  | chan a v t =>
    change G₂.chan a (f ∘ t) = some v
    rw [h.2 a t]
    exact hα

/-- On total tables, a sort-preserving bijection whose two directions credit every atom of
their domains makes the tables agree. -/
theorem tablesAgree_of_credits (F : D ≃ D') (hsort : ∀ x, G₂.sort (F x) = G₁.sort x)
    (htot₁ : G₁.TotalOn D) (htot₂ : G₂.TotalOn D')
    (hc : CreditsEveryAtom G₁ G₂ D (Subtype.val ∘ F))
    (hc' : CreditsEveryAtom G₂ G₁ D' (Subtype.val ∘ F.symm)) :
    TablesAgree G₁ G₂ D (Subtype.val ∘ F) := by
  have key₁ : ∀ α : Atom R D, α.map Subtype.val ∈ G₁.posReduct →
      α.map (Subtype.val ∘ F) ∈ G₂.posReduct := by
    intro α hα
    obtain ⟨-, β, hβ, hβ'⟩ := hc _ hα (by rw [Atom.vars_map]; rintro _ ⟨x, -, rfl⟩; exact x.2)
    rwa [Atom.map_injective Subtype.val_injective hβ] at hβ'
  have key₂ : ∀ α : Atom R D, α.map (Subtype.val ∘ F) ∈ G₂.posReduct →
      α.map Subtype.val ∈ G₁.posReduct := by
    intro α hα
    have hα' : (α.map F).map Subtype.val ∈ G₂.posReduct := by rwa [Atom.map_map]
    obtain ⟨-, β, hβ, hβ'⟩ :=
      hc' _ hα' (by rw [Atom.vars_map]; rintro _ ⟨x, -, rfl⟩; exact x.2)
    rw [Atom.map_injective Subtype.val_injective hβ, Atom.map_map] at hβ'
    convert hβ' using 2
    funext x
    simp
  refine ⟨fun r t => ?_, fun a t => ?_⟩
  · have k₁ := key₁ (Atom.rel r t)
    have k₂ := key₂ (Atom.rel r t)
    simp only [Atom.map_rel, ProfiledState.rel_mem_posReduct] at k₁ k₂
    by_cases hws : ∀ i, G₁.sort ((Subtype.val ∘ t) i) = R.relSort r i
    · obtain ⟨b₁, hb₁⟩ :=
        Option.ne_none_iff_exists'.mp (htot₁.1 r (Subtype.val ∘ t) (fun i => (t i).2) hws)
      obtain ⟨b₂, hb₂⟩ := Option.ne_none_iff_exists'.mp
        (htot₂.1 r ((Subtype.val ∘ F) ∘ t) (fun i => (F (t i)).2)
          (fun i => (hsort (t i)).trans (hws i)))
      rw [hb₁, hb₂] at k₁ k₂ ⊢
      cases b₁ <;> cases b₂ <;> simp_all
    · have h₁ : G₁.rel r (Subtype.val ∘ t) = none := by
        by_contra hne
        exact hws (G₁.rel_wellSorted r _ hne)
      have h₂ : G₂.rel r ((Subtype.val ∘ F) ∘ t) = none := by
        by_contra hne
        exact hws fun i => (hsort (t i)).symm.trans (G₂.rel_wellSorted r _ hne i)
      rw [h₁, h₂]
  · have k₁ := fun v => key₁ (Atom.chan a v t)
    have k₂ := fun v => key₂ (Atom.chan a v t)
    simp only [Atom.map_chan, ProfiledState.chan_mem_posReduct] at k₁ k₂
    cases h₁ : G₁.chan a (Subtype.val ∘ t) with
    | none =>
      cases h₂ : G₂.chan a ((Subtype.val ∘ F) ∘ t) with
      | none => rfl
      | some v =>
        have := k₂ v h₂
        rw [h₁] at this
        exact absurd this (by simp)
    | some v => exact k₁ v h₁

end PartialIso

/-- **Proposition 3.12** (partial profile isomorphism). Agreeing tables make `F` and `F⁻¹` strong
occurrences, and on total tables agreement is the same as each direction crediting every atom of
its domain. -/
@[book "prop:partial-profile-iso-book"]
theorem partialProfileIso : Statement.partialProfileIso := by
  intro R G₁ G₂ D D' F hsort htot₁ htot₂
  have hsort' : ∀ y, G₁.sort (F.symm y) = G₂.sort y := fun y => by
    rw [← hsort (F.symm y), Equiv.apply_symm_apply]
  refine ⟨fun h => ⟨isStrongOccurrence_of_tablesAgree
      (Subtype.val_injective.comp F.injective) hsort h.1,
    isStrongOccurrence_of_tablesAgree (Subtype.val_injective.comp F.symm.injective) hsort' h.2⟩,
    fun h => ⟨creditsEveryAtom_of_tablesAgree h.1, creditsEveryAtom_of_tablesAgree h.2⟩,
    fun h => ⟨tablesAgree_of_credits F hsort htot₁ htot₂ h.1 h.2,
      tablesAgree_of_credits F.symm hsort' htot₂ htot₁ h.2 h.1⟩⟩

/-! ## Positive occurrences (Proposition 3.22) -/

namespace Instantiation

variable {R : RecognitionProfile} {K : PositiveTemplate R} {G : ProfiledState R}

/-- The positions occurring in the atom image of an instantiation are its whole image. This is
where every variable occurring in an atom is used. -/
theorem vars_atomImage (j : Instantiation K G) :
    {p | ∃ α ∈ j.atomImage, p ∈ α.vars} = Set.range j := by
  ext p
  constructor
  · rintro ⟨_, ⟨α, -, rfl⟩, hp⟩
    rw [Atom.vars_map] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨α, hα, hx⟩ := K.covers x
    exact ⟨α.map j, ⟨α, hα, rfl⟩, by rw [Atom.vars_map]; exact ⟨x, hx, rfl⟩⟩

theorem atomImage_comp (j : Instantiation K G) (a : K.posAut) :
    (j.comp a).atomImage = j.atomImage := by
  change Atom.map (j ∘ ⇑(a : Equiv.Perm K.Var)) '' K.atoms = Atom.map j '' K.atoms
  rw [Atom.map_comp, Set.image_comp, a.2.2]

theorem eq_of_comp_eq (j : Instantiation K G) {a b : K.posAut} (h : j.comp a = j.comp b) :
    a = b :=
  Subtype.ext (Equiv.ext fun x => j.injective (congrArg (fun j' : Instantiation K G => j' x) h))

/-- Two instantiations with one atom image differ by an element of `Aut⁺_R(K)`. -/
theorem exists_comp_of_atomImage_eq {j j' : Instantiation K G}
    (h : j.atomImage = j'.atomImage) : ∃ a : K.posAut, j' = j.comp a := by
  have hr : Set.range j' = Set.range j := by rw [← vars_atomImage, ← vars_atomImage, h]
  let e : Equiv.Perm K.Var := (Equiv.ofInjective j' j'.injective).trans
    ((Set.equivOfEq hr).trans (Equiv.ofInjective j j.injective).symm)
  have he : ∀ x, j (e x) = j' x := fun x =>
    Equiv.apply_ofInjective_symm j.injective
      ((Set.equivOfEq hr) ((Equiv.ofInjective j' j'.injective) x))
  have hmem : e ∈ K.posAut := by
    change (∀ x, K.sort (e x) = K.sort x) ∧ Atom.map e '' K.atoms = K.atoms
    refine ⟨fun x => ?_, ?_⟩
    · rw [← j.sort_eq, he, j'.sort_eq]
    · have hje : (j : K.Var → G.Pos) ∘ e = j' := funext he
      apply Set.image_injective.mpr (Atom.map_injective j.injective)
      rw [← Set.image_comp, ← Atom.map_comp, hje]
      exact h.symm
  exact ⟨⟨e, hmem⟩, Instantiation.ext fun x => (he x).symm⟩

variable (K G) in
/-- `[j] ↦ aim_K(j)`, from positive occurrences onto instantiated atom sets. -/
noncomputable def occurrenceEquiv :
    PositiveOccurrence K G ≃ Set.range (fun j : Instantiation K G => j.atomImage) :=
  Equiv.ofBijective
    (Quotient.lift (fun j => ⟨j.atomImage, j, rfl⟩) fun j j' h => by
      obtain ⟨a, rfl⟩ := h
      exact Subtype.ext (atomImage_comp j a).symm)
    ⟨fun P Q => by
      induction P using Quotient.inductionOn with
      | h j =>
      induction Q using Quotient.inductionOn with
      | h j' =>
      intro h
      obtain ⟨a, ha⟩ := exists_comp_of_atomImage_eq (congrArg Subtype.val h)
      exact Quotient.sound ⟨a, ha⟩,
    by
      rintro ⟨S, j, rfl⟩
      exact ⟨PositiveOccurrence.mk j, rfl⟩⟩

end Instantiation

/-- **Proposition 3.22** (positive occurrences are atom images). The action of `Aut⁺_R(K)` on
instantiations is free, two instantiations have one atom image exactly when they differ by an
element of `Aut⁺_R(K)`, then unique, and `[j] ↦ aim_K(j)` is a bijection onto the instantiated
atom sets. -/
@[book "prop:atom-image-occurrence-book"]
theorem atomImageOccurrence : Statement.atomImageOccurrence := by
  intro R K G
  refine ⟨fun a j h => j.eq_of_comp_eq (h.trans j.comp_one.symm), fun j j' =>
    ⟨⟨Instantiation.exists_comp_of_atomImage_eq, ?_⟩, fun h => ?_⟩,
    Instantiation.occurrenceEquiv K G, fun j => rfl⟩
  · rintro ⟨a, rfl⟩
    exact (j.atomImage_comp a).symm
  · obtain ⟨a, ha⟩ := Instantiation.exists_comp_of_atomImage_eq h
    exact ⟨a, ha, fun b hb => j.eq_of_comp_eq (hb.symm.trans ha)⟩

/-! ## Reference markings (Proposition 3.45) -/

/-- The pulled-back marking at `j₁ y` is the reference marking at `j₂ y`. -/
theorem Marking.pullback_apply {R : RecognitionProfile} {K : PositiveTemplate R}
    {G₁ G₂ : ProfiledState R} {N : Type} (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂)
    (lam : Marking (Set.range j₂) N) (y : K.Var) (h : j₁ y ∈ Set.range j₁) :
    Marking.pullback j₁ j₂ lam ⟨j₁ y, h⟩ = lam (Set.rangeFactorization j₂ y) :=
  congrArg lam (Subtype.ext (j₁.comparison_rangeFactorization j₂ y))

/-- **Proposition 3.45** (reference marking along a comparison). The pulled-back marking is a
marking of `j_s(E_K)`; replacing `j_s` by `j_s ∘ a` replaces it by `λ_v ∘ j_v ∘ a⁻¹ ∘ j_s⁻¹`;
and it is unchanged exactly when `λ_v ∘ j_v` is. -/
@[book "prop:reference-marking-pullback-book"]
theorem referenceMarkingPullback : Statement.referenceMarkingPullback := by
  intro R K Gs Gv js jv N lv
  have key : ∀ (a : K.posAut) (y : K.Var) (h : js y ∈ Set.range (js.comp a)),
      Marking.pullback (js.comp a) jv lv ⟨js y, h⟩ =
        lv (Set.rangeFactorization jv ((a : Equiv.Perm K.Var)⁻¹ y)) := by
    intro a y h
    have hp : (⟨js y, h⟩ : Set.range (js.comp a)) =
        ⟨js.comp a ((a : Equiv.Perm K.Var)⁻¹ y), Set.mem_range_self _⟩ :=
      Subtype.ext (by simp)
    rw [hp, Marking.pullback_apply]
  refine ⟨fun p => ⟨_, rfl⟩, fun a => ⟨EquivLike.range_comp _ _, fun p h h' => ?_⟩,
    fun a => ⟨fun H => funext fun z => ?_, fun H p h h' => ?_⟩⟩
  · obtain ⟨y, rfl⟩ := h'
    exact (key a y h).trans (congrArg
      (fun w => lv (Set.rangeFactorization jv ((a : Equiv.Perm K.Var)⁻¹ w)))
      (Equiv.ofInjective_symm_apply js.injective y).symm)
  · have H' := H (js ((a : Equiv.Perm K.Var) z)) ⟨z, rfl⟩ ⟨_, rfl⟩
    have e1 := key a ((a : Equiv.Perm K.Var) z) ⟨z, rfl⟩
    have e2 := Marking.pullback_apply js jv lv ((a : Equiv.Perm K.Var) z) ⟨_, rfl⟩
    have h3 := e1.symm.trans (H'.trans e2)
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h3
    exact h3.symm
  · obtain ⟨y, rfl⟩ := h'
    refine (key a y h).trans (Eq.trans ?_ (Marking.pullback_apply js jv lv y _).symm)
    have H' := congrFun H ((a : Equiv.Perm K.Var)⁻¹ y)
    simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at H'
    exact H'.symm

/-! ## Non-vacuity -/

/-- The palette of the pinwheel. -/
private inductive Colour where
  | gold
  | blue
  | blank
  deriving DecidableEq

private instance : Fintype Colour :=
  Fintype.ofList [.gold, .blue, .blank] fun c => by cases c <;> simp

/-- The palette profile of Section 3.3 on the faces of the canvas of squares: one sort, one
relation (two faces share an edge), one channel (the palette), and no relabelling. -/
private abbrev paletteProfile : RecognitionProfile where
  PosSort := Unit
  Rel := Unit
  relArity _ := 2
  relSort _ _ := ()
  Chan := Unit
  chanArity _ := 1
  chanSort _ _ := ()
  Val _ := Colour
  Relabel := Unit
  relabelAction _ :=
    { smul := fun _ c => c, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }

/-- The pinwheel (Figure 3.2): the centre `(2, 2)` is gold, four arms of three faces are blue,
and the other faces are blank. Faces are addressed `(c, r)`. -/
private def pinwheelColour (f : Fin 5 × Fin 5) : Colour :=
  if f = (2, 2) then .gold
  else if f ∈ ({(1, 2), (0, 2), (0, 3), (2, 1), (2, 0), (1, 0), (3, 2), (4, 2), (4, 1), (2, 3),
      (2, 4), (3, 4)} : Finset (Fin 5 × Fin 5)) then .blue
  else .blank

/-- Two faces of the canvas of squares share an edge when their addresses differ by one in
exactly one place. -/
private def shareEdge (f g : Fin 5 × Fin 5) : Bool :=
  decide ((f.1 = g.1 ∧ (f.2.val + 1 = g.2.val ∨ g.2.val + 1 = f.2.val)) ∨
    (f.2 = g.2 ∧ (f.1.val + 1 = g.1.val ∨ g.1.val + 1 = f.1.val)))

/-- The pinwheel read through the palette profile: positions are the twenty-five faces. -/
private abbrev pinwheel : ProfiledState paletteProfile where
  Pos := Fin 5 × Fin 5
  sort _ := ()
  rel := fun (_ : Unit) (t : Fin 2 → Fin 5 × Fin 5) => some (shareEdge (t 0) (t 1))
  chan := fun (_ : Unit) (t : Fin 1 → Fin 5 × Fin 5) => some (pinwheelColour (t 0))
  rel_wellSorted _ _ _ _ := rfl
  chan_wellSorted _ _ _ _ := rfl

/-- The three face variables of the elbow: the corner `c`, the east face `e`, the north face
`n`. -/
private inductive ElbowVar where
  | c
  | e
  | n
  deriving DecidableEq

private instance : Fintype ElbowVar :=
  Fintype.ofList [.c, .e, .n] fun x => by cases x <;> simp

/-- The palette-only elbow template `K_E` (Figure 3.5): `blue(c)`, `blue(e)`, `blue(n)`,
`adj(c, e)`, `adj(c, n)`. -/
private def elbowAtoms : Set (Atom paletteProfile ElbowVar) :=
  {Atom.chan () Colour.blue (![ElbowVar.c] : Fin 1 → ElbowVar),
    Atom.chan () Colour.blue (![ElbowVar.e] : Fin 1 → ElbowVar),
    Atom.chan () Colour.blue (![ElbowVar.n] : Fin 1 → ElbowVar),
    Atom.rel () (![ElbowVar.c, ElbowVar.e] : Fin 2 → ElbowVar),
    Atom.rel () (![ElbowVar.c, ElbowVar.n] : Fin 2 → ElbowVar)}

/-- The elbow template. -/
private def elbow : PositiveTemplate paletteProfile where
  Var := ElbowVar
  sort _ := ()
  atoms := elbowAtoms
  atoms_finite := Set.toFinite _
  atoms_nonempty := ⟨_, Set.mem_insert _ _⟩
  covers x := by
    cases x
    · exact ⟨_, Set.mem_insert _ _, ⟨(0 : Fin 1), rfl⟩⟩
    · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _), ⟨(0 : Fin 1), rfl⟩⟩
    · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
        ⟨(0 : Fin 1), rfl⟩⟩

/-- A map of the elbow's variables is an instantiation in the pinwheel when it is injective and
its three faces are blue, with the corner sharing an edge with the other two. -/
private theorem isInstantiation_elbow (j : ElbowVar → Fin 5 × Fin 5) (hj : Function.Injective j)
    (hc : pinwheelColour (j .c) = .blue) (he : pinwheelColour (j .e) = .blue)
    (hn : pinwheelColour (j .n) = .blue) (hce : shareEdge (j .c) (j .e) = true)
    (hcn : shareEdge (j .c) (j .n) = true) : IsInstantiation elbow pinwheel j := by
  refine ⟨hj, fun _ => rfl, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  rcases hα with rfl | rfl | rfl | rfl | rfl
  · exact congrArg some hc
  · exact congrArg some he
  · exact congrArg some hn
  · exact congrArg some hce
  · exact congrArg some hcn

/-- The west arm: corner `(0, 2)`, east face `(1, 2)`, north face `(0, 3)` (Figure 3.5). -/
private def westArm : Instantiation elbow pinwheel where
  toFun := fun | .c => (0, 2) | .e => (1, 2) | .n => (0, 3)
  isInstantiation := isInstantiation_elbow _
    (fun x y => by cases x <;> cases y <;> decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- The south arm: corner `(2, 0)`, with `(2, 1)` and `(1, 0)` beside it. -/
private def southArm : Instantiation elbow pinwheel where
  toFun := fun | .c => (2, 0) | .e => (2, 1) | .n => (1, 0)
  isInstantiation := isInstantiation_elbow _
    (fun x y => by cases x <;> cases y <;> decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- Proposition 3.11: the elbow has instantiations in the pinwheel, one in each of two arms, and
the comparison of the west arm with the south arm credits an atom. -/
example : ∃ F : PartialComparison pinwheel pinwheel, F.credited.Nonempty := by
  obtain ⟨hF, hcred⟩ := (sharedPositivePattern paletteProfile pinwheel pinwheel).1 elbow
    westArm southArm
  exact ⟨⟨_, _, hF⟩, _, hcred ⟨_, Set.mem_insert _ _, rfl⟩⟩

/-- The west arm and the south arm as one bijection `F : D → D'` of their faces. -/
private noncomputable def westToSouth : Set.range westArm ≃ Set.range southArm :=
  (Equiv.ofInjective westArm westArm.injective).symm.trans
    (Equiv.ofInjective southArm southArm.injective)

private theorem westToSouth_apply (x : ElbowVar) :
    (westToSouth (Set.rangeFactorization westArm x)).1 = southArm x := by
  simp only [westToSouth, Equiv.trans_apply]
  rw [show (Equiv.ofInjective westArm westArm.injective).symm (Set.rangeFactorization westArm x) =
    x from Equiv.ofInjective_symm_apply _ x]
  rfl

private theorem westToSouth_symm_apply (x : ElbowVar) :
    (westToSouth.symm (Set.rangeFactorization southArm x)).1 = westArm x := by
  simp only [westToSouth, Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [show (Equiv.ofInjective southArm southArm.injective).symm
    (Set.rangeFactorization southArm x) = x from Equiv.ofInjective_symm_apply _ x]
  rfl

/-- A tuple of faces of an arm is the image of a tuple of the elbow's variables. -/
private theorem exists_tuple_of_range (j : Instantiation elbow pinwheel) {n : ℕ}
    (t : Fin n → Set.range j) : ∃ u : Fin n → ElbowVar, t = Set.rangeFactorization j ∘ u :=
  ⟨(Equiv.ofInjective j j.injective).symm ∘ t,
    funext fun i => Subtype.ext (Equiv.apply_ofInjective_symm j.injective (t i)).symm⟩

/-- Proposition 3.12: two arms of the pinwheel are partial profile isomorphs under the palette
profile. The bijection of their faces is sort-preserving, the tables are total, and they agree
through it in both directions. -/
example : (∀ x, pinwheel.sort (westToSouth x) = pinwheel.sort x) ∧
    pinwheel.TotalOn (Set.range westArm) ∧ pinwheel.TotalOn (Set.range southArm) ∧
    TablesAgree pinwheel pinwheel (Set.range westArm) (Subtype.val ∘ westToSouth) ∧
    TablesAgree pinwheel pinwheel (Set.range southArm) (Subtype.val ∘ westToSouth.symm) := by
  have htot : ∀ D : Set (Fin 5 × Fin 5), pinwheel.TotalOn D := fun _ =>
    ⟨fun _ _ _ _ => Option.some_ne_none _, fun _ _ _ _ => Option.some_ne_none _⟩
  have hF : ∀ {n : ℕ} (u : Fin n → ElbowVar),
      (Subtype.val ∘ westToSouth) ∘ (Set.rangeFactorization westArm ∘ u) = southArm ∘ u :=
    fun u => funext fun i => westToSouth_apply (u i)
  have hF' : ∀ {n : ℕ} (u : Fin n → ElbowVar),
      (Subtype.val ∘ westToSouth.symm) ∘ (Set.rangeFactorization southArm ∘ u) = westArm ∘ u :=
    fun u => funext fun i => westToSouth_symm_apply (u i)
  refine ⟨fun _ => rfl, htot _, htot _, ⟨fun r t => ?_, fun a t => ?_⟩,
    ⟨fun r t => ?_, fun a t => ?_⟩⟩
  · obtain ⟨u, rfl⟩ := exists_tuple_of_range westArm t
    rw [hF]
    change pinwheel.rel r (southArm ∘ u) = pinwheel.rel r (westArm ∘ u)
    revert u
    cases r
    decide
  · obtain ⟨u, rfl⟩ := exists_tuple_of_range westArm t
    rw [hF]
    change pinwheel.chan a (southArm ∘ u) = pinwheel.chan a (westArm ∘ u)
    revert u
    cases a
    decide
  · obtain ⟨u, rfl⟩ := exists_tuple_of_range southArm t
    rw [hF']
    change pinwheel.rel r (westArm ∘ u) = pinwheel.rel r (southArm ∘ u)
    revert u
    cases r
    decide
  · obtain ⟨u, rfl⟩ := exists_tuple_of_range southArm t
    rw [hF']
    change pinwheel.chan a (westArm ∘ u) = pinwheel.chan a (southArm ∘ u)
    revert u
    cases a
    decide

/-- Proposition 3.22: the elbow has an instantiation in the pinwheel. -/
example : Nonempty (Instantiation elbow pinwheel) := ⟨westArm⟩

/-- Names for the faces of an arm. -/
private inductive ArmPart where
  | corner
  | stem
  | hook

/-- Proposition 3.45: a reference marking of the south arm's faces, pulled back along the
comparison of the west arm with the south arm, names the west arm's corner as a corner. -/
example : Marking.pullback westArm southArm
    (fun p => if (p.1 : Fin 5 × Fin 5) = (2, 0) then ArmPart.corner else ArmPart.stem)
    (Set.rangeFactorization westArm ElbowVar.c) = ArmPart.corner :=
  (Marking.pullback_apply westArm southArm _ ElbowVar.c _).trans rfl

end Artform
