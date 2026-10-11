import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Set
import ArtformTextbook.Meta.Book

/-!
# Recognizing a pattern (Sections 3.1, 3.3 and 3.5, and the studio of Section 3.10)

What a match may see (a recognition profile), the states it reads, strong occurrences and the
automorphism group they give, positive templates with their instantiations, partial positive
comparisons, positive occurrences, and the markings of the studio.

A state is read through a profile: each position has a sort; each selected relation gives each
tuple of positions a verdict, `some true` (it holds) or `some false` (it fails), or none; and each
selected channel gives each tuple a value or none. Positions are addresses, as in Definition 3.2;
recognition reads only the positions, so the cells they present are not recorded in a state.
-/

namespace Artform

/-- **Definition 3.2** (position presentation). A position presentation of a form `F` is a
finite set `pos(F)` together with a typed map `π_F : pos(F) → cells(F)` naming, for each visible
address, the carried cell it presents. The form is given here by its type of cells. -/
@[book "def:position-presentation"]
structure PositionPresentation (Cell : Type) where
  /-- The positions `pos(F)`. -/
  Pos : Type
  [finitePos : Finite Pos]
  /-- The map `π_F`, naming the cell that each position presents. -/
  toCell : Pos → Cell

/-- **Definition 3.6** (recognition profile). A recognition profile selects what a match may see:
* a finite family of sorts of position, which a match must preserve;
* the relations among positions that the match reads, each relating a fixed number of positions,
  with a declared sort for each place;
* the finite-valued labels and state channels it reads, each read at a tuple of positions of
  declared sorts;
* the allowed action on directional or palette labels: a group of relabellings acting on the
  values of every channel. A profile that allows no action has the trivial group.

The selected relations and channels are finitely many, as the positive reduct of Definition 3.9,
"the finite set of atoms true in `G`", requires. -/
@[book "def:recognition-profile"]
structure RecognitionProfile where
  /-- The sorts of position. -/
  PosSort : Type
  [finitePosSort : Finite PosSort]
  /-- The selected relations. -/
  Rel : Type
  [finiteRel : Finite Rel]
  /-- The number of positions that a relation relates. -/
  relArity : Rel → ℕ
  /-- The sort declared for each place of a relation. -/
  relSort : (r : Rel) → Fin (relArity r) → PosSort
  /-- The selected labels and state channels. -/
  Chan : Type
  [finiteChan : Finite Chan]
  /-- The number of positions at which a channel is read. -/
  chanArity : Chan → ℕ
  /-- The sort declared for each place of a channel. -/
  chanSort : (a : Chan) → Fin (chanArity a) → PosSort
  /-- The values of each channel; there are finitely many. -/
  Val : Chan → Type
  [finiteVal : ∀ a, Finite (Val a)]
  /-- The allowed relabellings of directional or palette labels. -/
  Relabel : Type
  [relabelGroup : Group Relabel]
  [relabelAction : ∀ a, MulAction Relabel (Val a)]

attribute [instance] RecognitionProfile.finitePosSort RecognitionProfile.finiteRel
  RecognitionProfile.finiteChan RecognitionProfile.finiteVal RecognitionProfile.relabelGroup
  RecognitionProfile.relabelAction

variable {R : RecognitionProfile}

/-- **Definition 3.7** (recognition pattern); the same data make a *state profiled by `R`*, the
term of Definitions 3.9 and 3.10. Finitely many positions, each of a sort, with all the
observations that the profile selects: every selected relation gives each tuple of positions a
verdict, `some true` (holds) or `some false` (fails), or no verdict (`none`); every selected
channel gives each tuple a value or none. The legality condition is that verdicts and values are
given only on well-sorted tuples, whose positions have the sorts that the relation or channel
declares. -/
@[book "def:recognition-pattern-book"]
structure ProfiledState (R : RecognitionProfile) where
  /-- The positions. -/
  Pos : Type
  [finitePos : Finite Pos]
  /-- The sort of each position. -/
  sort : Pos → R.PosSort
  /-- The verdict of each selected relation on each tuple of positions. -/
  rel : (r : R.Rel) → (Fin (R.relArity r) → Pos) → Option Bool
  /-- The value of each selected channel on each tuple of positions. -/
  chan : (a : R.Chan) → (Fin (R.chanArity a) → Pos) → Option (R.Val a)
  /-- Verdicts are given only on well-sorted tuples. -/
  rel_wellSorted : ∀ r t, rel r t ≠ none → ∀ i, sort (t i) = R.relSort r i
  /-- Values are given only on well-sorted tuples. -/
  chan_wellSorted : ∀ a t, chan a t ≠ none → ∀ i, sort (t i) = R.chanSort a i

attribute [instance] ProfiledState.finitePos

/-- A recognition pattern under `R` (Definition 3.7). -/
abbrev RecognitionPattern (R : RecognitionProfile) : Type 1 := ProfiledState R

/-! ## Atoms -/

/-- An atom over a set `X` of positions or variables (Definition 3.9): `R(x₁, …, x_k)` for a
selected relation `R`, or `[a = v](x₁, …, x_k)` for a selected channel `a` and a value `v`. -/
inductive Atom (R : RecognitionProfile) (X : Type) : Type where
  /-- The atom `r(x₁, …, x_k)`. -/
  | rel (r : R.Rel) (args : Fin (R.relArity r) → X)
  /-- The atom `[a = v](x₁, …, x_k)`. -/
  | chan (a : R.Chan) (v : R.Val a) (args : Fin (R.chanArity a) → X)

namespace Atom

variable {X Y Z : Type}

/-- Renaming the positions or variables of an atom by `f`: the atom `f_*(α)`. -/
def map (f : X → Y) : Atom R X → Atom R Y
  | rel r t => rel r (f ∘ t)
  | chan a v t => chan a v (f ∘ t)

/-- The positions or variables occurring in an atom. -/
def vars : Atom R X → Set X
  | rel _ t => Set.range t
  | chan _ _ t => Set.range t

@[simp] theorem map_rel (f : X → Y) (r : R.Rel) (t : Fin (R.relArity r) → X) :
    (rel r t).map f = rel r (f ∘ t) := rfl

@[simp] theorem map_chan (f : X → Y) (a : R.Chan) (v : R.Val a) (t : Fin (R.chanArity a) → X) :
    (chan a v t).map f = chan a v (f ∘ t) := rfl

@[simp] theorem map_id (α : Atom R X) : α.map id = α := by
  cases α <;> rfl

@[simp] theorem map_id' (α : Atom R X) : α.map (fun x => x) = α := map_id α

theorem map_map (f : X → Y) (g : Y → Z) (α : Atom R X) : (α.map f).map g = α.map (g ∘ f) := by
  cases α <;> rfl

theorem map_comp (f : X → Y) (g : Y → Z) : map (R := R) (g ∘ f) = map g ∘ map f :=
  funext fun α => (map_map f g α).symm

theorem map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (map (R := R) f) := by
  intro α β h
  cases α with
  | rel r t =>
    cases β with
    | rel r' t' =>
      simp only [map_rel, rel.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      exact congrArg (rel r) (funext fun i => hf (congrFun h i))
    | chan => simp at h
  | chan a v t =>
    cases β with
    | rel => simp at h
    | chan a' v' t' =>
      simp only [map_chan, chan.injEq] at h
      obtain ⟨rfl, h, h'⟩ := h
      rw [heq_eq_eq] at h h'
      subst h
      exact congrArg (chan a v) (funext fun i => hf (congrFun h' i))

theorem vars_map (f : X → Y) (α : Atom R X) : (α.map f).vars = f '' α.vars := by
  cases α <;> simp [map, vars, Set.range_comp]

theorem map_congr {f g : X → Y} {α : Atom R X} (h : ∀ x ∈ α.vars, f x = g x) :
    α.map f = α.map g := by
  cases α with
  | rel r t =>
    exact congrArg (rel r) (funext fun i => h (t i) ⟨i, rfl⟩)
  | chan a v t =>
    exact congrArg (chan a v) (funext fun i => h (t i) ⟨i, rfl⟩)

/-- An atom whose positions all lie in a set `D` is the renaming of an atom over `D`. -/
theorem exists_map_val {D : Set X} {α : Atom R X} (h : α.vars ⊆ D) :
    ∃ β : Atom R D, β.map Subtype.val = α := by
  cases α with
  | rel r t => exact ⟨rel r fun i => ⟨t i, h ⟨i, rfl⟩⟩, rfl⟩
  | chan a v t => exact ⟨chan a v fun i => ⟨t i, h ⟨i, rfl⟩⟩, rfl⟩

/-- An atom written as its relation or channel, value and tuple. -/
def code : Atom R X →
    (Σ r : R.Rel, Fin (R.relArity r) → X) ⊕ (Σ a : R.Chan, R.Val a × (Fin (R.chanArity a) → X))
  | rel r t => .inl ⟨r, t⟩
  | chan a v t => .inr ⟨a, v, t⟩

theorem code_injective : Function.Injective (code (R := R) (X := X)) := by
  intro α β h
  cases α with
  | rel r t =>
    cases β with
    | rel r' t' =>
      simp only [code, Sum.inl.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      rw [h]
    | chan => simp [code] at h
  | chan a v t =>
    cases β with
    | rel => simp [code] at h
    | chan a' v' t' =>
      simp only [code, Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq, Prod.mk.injEq] at h
      rw [h.1, h.2]

/-- Over finitely many positions there are finitely many atoms. -/
instance [Finite X] : Finite (Atom R X) := Finite.of_injective _ code_injective

end Atom

/-! ## States and the positive reduct -/

namespace ProfiledState

/-- Whether an atom is true in a profiled state: a relation atom when the relation holds on its
tuple, a channel atom `[a = v](x₁, …, x_k)` when the channel takes the value `v` there. -/
def Holds (G : ProfiledState R) : Atom R G.Pos → Prop
  | .rel r t => G.rel r t = some true
  | .chan a v t => G.chan a t = some v

/-- **Definition 3.9** (positive reduct). The set `At⁺_R(G)` of atoms true in `G`: one atom
`R(x₁, …, x_k)` for each selected relation `R` and each tuple of positions on which it holds,
and one atom `[a = v](x₁, …, x_k)` for each selected channel `a` and each tuple at which it
takes the value `v`. Sorts are types of position and are not atoms. -/
@[book "def:positive-feature-template-book"]
def posReduct (G : ProfiledState R) : Set (Atom R G.Pos) := {α | G.Holds α}

@[simp] theorem rel_mem_posReduct (G : ProfiledState R) (r : R.Rel)
    (t : Fin (R.relArity r) → G.Pos) : Atom.rel r t ∈ G.posReduct ↔ G.rel r t = some true :=
  Iff.rfl

@[simp] theorem chan_mem_posReduct (G : ProfiledState R) (a : R.Chan) (v : R.Val a)
    (t : Fin (R.chanArity a) → G.Pos) : Atom.chan a v t ∈ G.posReduct ↔ G.chan a t = some v :=
  Iff.rfl

/-- The restriction `G|D` of a profiled state to a set `D` of its positions: the positions of
`D`, with their sorts, and the verdicts and values of `G` on tuples of positions of `D`. -/
def restrict (G : ProfiledState R) (D : Set G.Pos) : ProfiledState R where
  Pos := D
  sort := G.sort ∘ Subtype.val
  rel r t := G.rel r (Subtype.val ∘ t)
  chan a t := G.chan a (Subtype.val ∘ t)
  rel_wellSorted r t h i := G.rel_wellSorted r (Subtype.val ∘ t) h i
  chan_wellSorted a t h i := G.chan_wellSorted a (Subtype.val ∘ t) h i

/-- Every selected relation and channel is total on a set `D` of positions: every well-sorted
tuple of positions of `D` has a verdict or a value. -/
def TotalOn (G : ProfiledState R) (D : Set G.Pos) : Prop :=
  (∀ (r : R.Rel) (t : Fin (R.relArity r) → G.Pos), (∀ i, t i ∈ D) →
      (∀ i, G.sort (t i) = R.relSort r i) → G.rel r t ≠ none) ∧
  (∀ (a : R.Chan) (t : Fin (R.chanArity a) → G.Pos), (∀ i, t i ∈ D) →
      (∀ i, G.sort (t i) = R.chanSort a i) → G.chan a t ≠ none)

end ProfiledState

/-! ## Strong occurrences and the automorphism group -/

/-- **Definition 3.8** (strong occurrence). A map `w` from the positions of `P` to those of `X`,
read with the label map `g` declared from the profile's allowed action, is a strong occurrence
(a strong match) when it is injective and sort-preserving and
1. all selected relations are preserved: a relation that holds on a tuple of `P` holds on its
   image;
2. they are reflected on the image: a relation that holds on the image of a tuple held on the
   tuple in `P`;
3. selected labels and channel values agree through the declared label map: at the image of a
   tuple, a channel has the value of `P` moved by `g`, and it has a value exactly when `P` has
   one there.

A rigid occurrence declares the identity, `g = 1`. -/
@[book "def:strong-occurrence"]
structure IsStrongOccurrence (P X : ProfiledState R) (g : R.Relabel) (w : P.Pos → X.Pos) :
    Prop where
  injective : Function.Injective w
  sort_eq : ∀ p, X.sort (w p) = P.sort p
  preserves : ∀ (r : R.Rel) (t : Fin (R.relArity r) → P.Pos),
    P.rel r t = some true → X.rel r (w ∘ t) = some true
  reflects : ∀ (r : R.Rel) (t : Fin (R.relArity r) → P.Pos),
    X.rel r (w ∘ t) = some true → P.rel r t = some true
  agrees : ∀ (a : R.Chan) (t : Fin (R.chanArity a) → P.Pos),
    X.chan a (w ∘ t) = (P.chan a t).map (g • ·)

namespace IsStrongOccurrence

/-- The identity is a strong occurrence of a state in itself, with the identity label map. -/
theorem id (X : ProfiledState R) : IsStrongOccurrence X X 1 id where
  injective := Function.injective_id
  sort_eq _ := rfl
  preserves _ _ h := h
  reflects _ _ h := h
  agrees a t := by simp

/-- Strong occurrences compose, and so do their label maps. -/
theorem comp {P X Y : ProfiledState R} {g g' : R.Relabel} {w : P.Pos → X.Pos}
    {w' : X.Pos → Y.Pos} (h : IsStrongOccurrence P X g w) (h' : IsStrongOccurrence X Y g' w') :
    IsStrongOccurrence P Y (g' * g) (w' ∘ w) where
  injective := h'.injective.comp h.injective
  sort_eq p := (h'.sort_eq (w p)).trans (h.sort_eq p)
  preserves r t ht := h'.preserves r (w ∘ t) (h.preserves r t ht)
  reflects r t ht := h.reflects r t (h'.reflects r (w ∘ t) ht)
  agrees a t := by
    rw [Function.comp_assoc, h'.agrees a (w ∘ t), h.agrees a t, Option.map_map]
    congr 1
    funext v
    simp [mul_smul]

end IsStrongOccurrence

/-- **Definition 3.8** (strong occurrence): the type `Occurrence_R(P, X)` of strong occurrences
of `P` in `X`, each with its declared label map. -/
@[book "def:strong-occurrence"]
def Occurrence (P X : ProfiledState R) : Type :=
  {o : R.Relabel × (P.Pos → X.Pos) // IsStrongOccurrence P X o.1 o.2}

namespace Occurrence

variable {X : ProfiledState R}

@[ext] theorem ext {o o' : Occurrence X X} (h : o.1 = o'.1) : o = o' := Subtype.ext h

/-- Strong self-occurrences form a monoid under composition, `o * o'` being `o` after `o'`. -/
instance : Monoid (Occurrence X X) where
  mul o o' := ⟨(o.1.1 * o'.1.1, o.1.2 ∘ o'.1.2), o'.2.comp o.2⟩
  one := ⟨(1, id), IsStrongOccurrence.id X⟩
  mul_assoc o o' o'' := ext (Prod.ext (mul_assoc _ _ _) rfl)
  one_mul o := ext (Prod.ext (one_mul _) rfl)
  mul_one o := ext (Prod.ext (mul_one _) rfl)

end Occurrence

/-- **Definition 3.20** (automorphism group). For a pattern `X` and profile `R`, the
automorphism group `Aut_R(X)` is the group of invertible members of `Occurrence_R(X, X)`. -/
@[book "nolabel:03-pattern-geometry:automorphism-group"]
abbrev Aut (X : ProfiledState R) : Type := (Occurrence X X)ˣ

/-! ## Positive templates and their instantiations -/

/-- **Definition 3.9** (positive template). A positive template `K = (E_K, 𝒜_K)` is a finite
sorted set of variables `E_K` together with a nonempty finite set `𝒜_K` of atoms over them,
every variable occurring in at least one atom. -/
@[book "def:positive-feature-template-book"]
structure PositiveTemplate (R : RecognitionProfile) where
  /-- The variables `E_K`. -/
  Var : Type
  [finiteVar : Finite Var]
  /-- The sort of each variable. -/
  sort : Var → R.PosSort
  /-- The atoms `𝒜_K`. -/
  atoms : Set (Atom R Var)
  atoms_finite : atoms.Finite
  atoms_nonempty : atoms.Nonempty
  /-- Every variable occurs in at least one atom. -/
  covers : ∀ x, ∃ α ∈ atoms, x ∈ α.vars

attribute [instance] PositiveTemplate.finiteVar

/-- **Definition 3.9** (positive instantiation). A positive instantiation of `K` in `G` is a
sort-preserving injection `j : E_K ↪ pos(G)` with `j_*(𝒜_K) ⊆ At⁺_R(G)`, where `j_*` renames
the variables of each atom by `j`. -/
@[book "def:positive-feature-template-book"]
def IsInstantiation (K : PositiveTemplate R) (G : ProfiledState R) (j : K.Var → G.Pos) : Prop :=
  Function.Injective j ∧ (∀ x, G.sort (j x) = K.sort x) ∧ Atom.map j '' K.atoms ⊆ G.posReduct

/-- **Definition 3.9** (positive instantiation): the type `Instantiation_R(K, G)` of positive
instantiations of `K` in `G`. -/
@[book "def:positive-feature-template-book"]
structure Instantiation (K : PositiveTemplate R) (G : ProfiledState R) where
  /-- The map of variables to positions. -/
  toFun : K.Var → G.Pos
  isInstantiation : IsInstantiation K G toFun

namespace Instantiation

variable {K : PositiveTemplate R} {G G₁ G₂ : ProfiledState R}

instance : CoeFun (Instantiation K G) (fun _ => K.Var → G.Pos) := ⟨Instantiation.toFun⟩

@[ext] theorem ext {j j' : Instantiation K G} (h : ∀ x, j x = j' x) : j = j' := by
  cases j; cases j'
  congr
  exact funext h

theorem injective (j : Instantiation K G) : Function.Injective j := j.isInstantiation.1

theorem sort_eq (j : Instantiation K G) (x : K.Var) : G.sort (j x) = K.sort x :=
  j.isInstantiation.2.1 x

theorem atoms_sub (j : Instantiation K G) : Atom.map j '' K.atoms ⊆ G.posReduct :=
  j.isInstantiation.2.2

/-- The comparison `F = j₂ ∘ j₁⁻¹` of two instantiations of one template, defined on `j₁(E_K)`
(Proposition 3.11; the studio of Section 3.10). -/
noncomputable def comparison (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂) :
    Set.range j₁ → G₂.Pos :=
  j₂ ∘ (Equiv.ofInjective j₁ j₁.injective).symm

end Instantiation

/-! ## Partial positive comparisons -/

/-- **Definition 3.10** (partial positive comparison), the defining condition: a map `F` from a
subset `D ⊆ pos(G₁)`, its domain, into `pos(G₂)` is a partial positive comparison
`G₁ ⇀ G₂` when it is a sort-preserving injection. -/
@[book "def:partial-positive-comparison"]
def IsPartialComparison (G₁ G₂ : ProfiledState R) (D : Set G₁.Pos) (F : D → G₂.Pos) : Prop :=
  Function.Injective F ∧ ∀ x, G₂.sort (F x) = G₁.sort x

/-- **Definition 3.10** (credited atoms). An atom of `At⁺_R(G₁)` whose positions all lie in `D`
is credited to `F` when its image under `F` is an atom of `At⁺_R(G₂)`. The credited atoms form
the set `Pres⁺_R(F)`. An atom with all its positions in `D` is the renaming `β.map val` of an
atom `β` over `D`, and its image under `F` is `β.map F`. -/
@[book "def:partial-positive-comparison"]
def creditedAtoms (G₁ G₂ : ProfiledState R) (D : Set G₁.Pos) (F : D → G₂.Pos) :
    Set (Atom R G₁.Pos) :=
  {α | α ∈ G₁.posReduct ∧ ∃ β : Atom R D, β.map Subtype.val = α ∧ β.map F ∈ G₂.posReduct}

/-- `F` credits every atom of its domain: every atom of `At⁺_R(G₁)` whose positions all lie in
`D` is credited to `F`. -/
def CreditsEveryAtom (G₁ G₂ : ProfiledState R) (D : Set G₁.Pos) (F : D → G₂.Pos) : Prop :=
  ∀ α ∈ G₁.posReduct, α.vars ⊆ D → α ∈ creditedAtoms G₁ G₂ D F

/-- **Definition 3.10** (partial positive comparison) `F : G₁ ⇀ G₂`: a sort-preserving
injection from a subset `D ⊆ pos(G₁)`, its domain, into `pos(G₂)`. -/
@[book "def:partial-positive-comparison"]
structure PartialComparison (G₁ G₂ : ProfiledState R) where
  /-- The domain `D`. -/
  dom : Set G₁.Pos
  /-- The map. -/
  toFun : dom → G₂.Pos
  isPartialComparison : IsPartialComparison G₁ G₂ dom toFun

namespace PartialComparison

variable {G₁ G₂ : ProfiledState R}

/-- The credited atoms `Pres⁺_R(F)` (Definition 3.10). -/
def credited (F : PartialComparison G₁ G₂) : Set (Atom R G₁.Pos) :=
  creditedAtoms G₁ G₂ F.dom F.toFun

/-- The active positions of `F` (Definition 3.10): the positions occurring in its credited
atoms, as elements of its domain. -/
def active (F : PartialComparison G₁ G₂) : Set F.dom :=
  {p | ∃ α ∈ F.credited, (p : G₁.Pos) ∈ α.vars}

end PartialComparison

/-- The selected tables of `G₁` on `D` agree with those of `G₂` through `F`: every tuple of
positions of `D` has the same verdict under each selected relation, and the same value under
each selected channel, as its image under `F`. -/
def TablesAgree (G₁ G₂ : ProfiledState R) (D : Set G₁.Pos) (F : D → G₂.Pos) : Prop :=
  (∀ (r : R.Rel) (t : Fin (R.relArity r) → D), G₂.rel r (F ∘ t) = G₁.rel r (Subtype.val ∘ t)) ∧
  (∀ (a : R.Chan) (t : Fin (R.chanArity a) → D), G₂.chan a (F ∘ t) = G₁.chan a (Subtype.val ∘ t))

/-! ## Template symmetry and positive occurrences -/

namespace PositiveTemplate

/-- **Definition 3.21** (template symmetry). The positive automorphism group `Aut⁺_R(K)` of a
positive template: the sort-preserving bijections `a : E_K → E_K` with `a_*(𝒜_K) = 𝒜_K`. -/
@[book "def:positive-occurrence-book"]
def posAut (K : PositiveTemplate R) : Subgroup (Equiv.Perm K.Var) where
  carrier := {a | (∀ x, K.sort (a x) = K.sort x) ∧ Atom.map a '' K.atoms = K.atoms}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x => (ha (b x)).trans (hb x), ?_⟩
    rw [Equiv.Perm.coe_mul, Atom.map_comp, Set.image_comp, hb', ha']
  one_mem' := ⟨fun _ => rfl, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x => ?_, ?_⟩
    · have h := ha (a⁻¹ x)
      rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
      exact h.symm
    · have hinv : ∀ α : Atom R K.Var, Atom.map ⇑a⁻¹ (Atom.map ⇑a α) = α := fun α => by
        rw [Atom.map_map]
        convert Atom.map_id α
        funext x
        simp
      calc Atom.map ⇑a⁻¹ '' K.atoms = Atom.map ⇑a⁻¹ '' (Atom.map ⇑a '' K.atoms) := by rw [ha']
        _ = K.atoms := by
          rw [Set.image_image]
          conv_rhs => rw [← Set.image_id K.atoms]
          exact Set.image_congr fun α _ => hinv α

end PositiveTemplate

namespace Instantiation

variable {K : PositiveTemplate R} {G : ProfiledState R}

/-- `Aut⁺_R(K)` acts on `Instantiation_R(K, G)` by precomposition, `j ↦ j ∘ a`. -/
def comp (j : Instantiation K G) (a : K.posAut) : Instantiation K G where
  toFun := j ∘ (a : Equiv.Perm K.Var)
  isInstantiation := by
    refine ⟨j.injective.comp (a : Equiv.Perm K.Var).injective, fun x => ?_, ?_⟩
    · exact (j.sort_eq _).trans (a.2.1 x)
    · rw [Atom.map_comp, Set.image_comp, a.2.2]
      exact j.atoms_sub

@[simp] theorem comp_apply (j : Instantiation K G) (a : K.posAut) (x : K.Var) :
    j.comp a x = j ((a : Equiv.Perm K.Var) x) := rfl

theorem comp_one (j : Instantiation K G) : j.comp 1 = j := ext fun _ => rfl

theorem comp_comp (j : Instantiation K G) (a b : K.posAut) : (j.comp a).comp b = j.comp (a * b) :=
  ext fun _ => rfl

/-- **Definition 3.21** (atom image). The atom image of an instantiation is the set
`aim_K(j) = j_*(𝒜_K) ⊆ At⁺_R(G)` of the atoms of `G` that it instantiates. -/
@[book "def:positive-occurrence-book"]
def atomImage (j : Instantiation K G) : Set (Atom R G.Pos) := Atom.map j '' K.atoms

/-- Two instantiations lie in one orbit of the action of `Aut⁺_R(K)` when one is the other
precomposed with an element of `Aut⁺_R(K)`. -/
def orbitSetoid (K : PositiveTemplate R) (G : ProfiledState R) : Setoid (Instantiation K G) where
  r j j' := ∃ a : K.posAut, j' = j.comp a
  iseqv := by
    refine ⟨fun j => ⟨1, (comp_one j).symm⟩, ?_, ?_⟩
    · rintro j j' ⟨a, rfl⟩
      exact ⟨a⁻¹, by rw [comp_comp, mul_inv_cancel, comp_one]⟩
    · rintro j j' j'' ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a * b, comp_comp j a b⟩

end Instantiation

/-- **Definition 3.21** (positive occurrence). A positive occurrence of `K` in `G` is an orbit of
the action of `Aut⁺_R(K)` on `Instantiation_R(K, G)`; the set of occurrences is
`Occurrence⁺_R(K, G) = Instantiation_R(K, G) / Aut⁺_R(K)`. -/
@[book "def:positive-occurrence-book"]
def PositiveOccurrence (K : PositiveTemplate R) (G : ProfiledState R) : Type :=
  Quotient (Instantiation.orbitSetoid K G)

/-- The positive occurrence `[j]` of an instantiation: its orbit. -/
def PositiveOccurrence.mk {K : PositiveTemplate R} {G : ProfiledState R}
    (j : Instantiation K G) : PositiveOccurrence K G :=
  Quotient.mk _ j

/-! ## Markings (Section 3.10) -/

/-- A marking of a set `S` of positions by a set `N` of names (the studio of Section 3.10): a
name for each position of `S`, `λ : Π_{y : S} N`. A marking is a further layer of state; it is
not part of the profile. -/
abbrev Marking {P : Type} (S : Set P) (N : Type) : Type := S → N

/-- The marking `λ ∘ F` pulled back along the comparison `F = j₂ ∘ j₁⁻¹` of two instantiations of
one template: a marking of `j₁(E_K)`, read through `F` from a marking `λ` of `j₂(E_K)`. -/
noncomputable def Marking.pullback {K : PositiveTemplate R} {G₁ G₂ : ProfiledState R} {N : Type}
    (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂) (lam : Marking (Set.range j₂) N) :
    Marking (Set.range j₁) N :=
  fun p => lam ⟨j₁.comparison j₂ p, Set.mem_range_self _⟩

end Artform
