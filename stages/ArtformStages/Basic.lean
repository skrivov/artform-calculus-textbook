import Mathlib

/-!
# Stages

The core of the stage algebra of the research ledger on a layered universe
(`STAGE-ALGEBRA.md` in the author's workspace, physics/ledgers/multilayered-universe/;
the definitions are the charter's D1 and D2 and THEORY.md's §3).

* A **stage** on a list of acts is a list of rules. A *walk* is acts made one after
  another, each of which can be undone: an element of the free group on the acts. A
  rule says that a walk is rest. A rule "the walks `u` and `v` are the same" is the
  walk `u * v⁻¹`.
* The **rest** of a stage is the walks that its rules make rest: the normal closure of
  the rules. The **world** of a stage is its laws, the walks up to the rules.
* `C` is **over** `S` when everything at rest in `C` is at rest in `S`. Forgetting then
  sends each law of `C` to its law in `S`.
* **Lay** adds rules, and **add** adds an act with no rule about it.
-/

namespace Artform.Stages

open Subgroup

variable {α : Type*}

/-- A stage on the acts `α`: its rules. A rule is a walk that is laid as rest. -/
structure Stage (α : Type*) where
  /-- The rules: the walks that are laid as rest. -/
  rules : Set (FreeGroup α)

namespace Stage

variable (S : Stage α)

/-- The rest of a stage: the walks that its rules make rest. -/
def rest : Subgroup (FreeGroup α) := normalClosure S.rules

instance : S.rest.Normal := normalClosure_normal

theorem rules_subset_rest : S.rules ⊆ S.rest := subset_normalClosure

/-- The world of a stage: its laws, the walks up to the rules. -/
abbrev World : Type _ := PresentedGroup S.rules

/-- The law of a walk. -/
def law : FreeGroup α →* S.World := PresentedGroup.mk S.rules

theorem law_surjective : Function.Surjective S.law := PresentedGroup.mk_surjective S.rules

theorem law_eq_one_iff {w : FreeGroup α} : S.law w = 1 ↔ w ∈ S.rest :=
  PresentedGroup.mk_eq_one_iff

theorem ker_law : S.law.ker = S.rest := by
  ext w
  exact S.law_eq_one_iff

/-- Two walks are one law exactly when one, followed by the other undone, is rest. -/
theorem law_eq_law_iff {u v : FreeGroup α} : S.law u = S.law v ↔ u * v⁻¹ ∈ S.rest := by
  rw [← S.law_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]

/-- The stage whose rules are all the walks of a given subgroup. -/
def ofRest (K : Subgroup (FreeGroup α)) : Stage α := ⟨K⟩

@[simp]
theorem rest_ofRest (K : Subgroup (FreeGroup α)) [K.Normal] : (ofRest K).rest = K :=
  normalClosure_eq_self K

/-! ### Over, and forgetting -/

/-- `C` is over `S`: everything at rest in `C` is at rest in `S`. -/
def IsOver (C S : Stage α) : Prop := C.rest ≤ S.rest

variable {S} {C : Stage α}

theorem isOver_iff : C.IsOver S ↔ C.rest ≤ S.rest := Iff.rfl

theorem isOver_iff_rules : C.IsOver S ↔ C.rules ⊆ S.rest :=
  show normalClosure C.rules ≤ S.rest ↔ _ from normalClosure_subset_iff.symm

/-- Forgetting: each law of a stage over `S` has its law in `S`. -/
def forget (h : C.IsOver S) : C.World →* S.World :=
  QuotientGroup.map C.rest S.rest (MonoidHom.id _) fun _ hx => h hx

@[simp]
theorem forget_law (h : C.IsOver S) (w : FreeGroup α) : forget h (C.law w) = S.law w :=
  rfl

/-- **T1(a).** Forgetting reaches every law. -/
theorem forget_surjective (h : C.IsOver S) : Function.Surjective (forget h) := by
  intro x
  obtain ⟨w, rfl⟩ := S.law_surjective x
  exact ⟨C.law w, rfl⟩

/-- The kept laws of `C` over `S`: what the walks at rest in `S` do in `C`. -/
def keptLaws (C S : Stage α) : Subgroup C.World := S.rest.map C.law

theorem mem_keptLaws {k : C.World} : k ∈ keptLaws C S ↔ ∃ n ∈ S.rest, C.law n = k :=
  Subgroup.mem_map

/-- **T1(b).** The kept laws are the laws that forgetting sends to rest. -/
theorem ker_forget (h : C.IsOver S) : (forget h).ker = keptLaws C S := by
  ext k
  obtain ⟨w, rfl⟩ := C.law_surjective k
  rw [MonoidHom.mem_ker, forget_law, S.law_eq_one_iff, mem_keptLaws]
  refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
  rintro ⟨n, hn, hnw⟩
  have h1 : n * w⁻¹ ∈ S.rest := h (C.law_eq_law_iff.mp hnw)
  simpa using S.rest.mul_mem (S.rest.inv_mem h1) hn

/-- **T1(c).** A stage over `S` has as many laws as `S`, times the kept laws. -/
theorem card_world (h : C.IsOver S) :
    Nat.card C.World = Nat.card S.World * Nat.card (keptLaws C S) := by
  rw [← ker_forget h, card_eq_card_quotient_mul_card_subgroup (forget h).ker]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (forget_surjective h)).toEquiv

/-! ### Lay -/

variable (S) in
/-- Lay: the rules of `S`, and those of `R` as well. -/
def lay (R : Set (FreeGroup α)) : Stage α := ⟨S.rules ∪ R⟩

theorem rest_lay (R : Set (FreeGroup α)) : (S.lay R).rest = S.rest ⊔ normalClosure R :=
  normalClosure_union _ _

/-- `S` is over what is laid on it: laying leaves fewer laws. -/
theorem isOver_lay (R : Set (FreeGroup α)) : S.IsOver (S.lay R) := by
  rw [IsOver, rest_lay]
  exact le_sup_left

/-- **Rule 1.** Obeying twice is obeying once. -/
theorem lay_lay (R R' : Set (FreeGroup α)) : (S.lay R).lay R' = S.lay (R ∪ R') :=
  congrArg Stage.mk (Set.union_assoc S.rules R R')

/-- **Rule 1.** Obeying two lists of rules, in either order, leaves the same at rest. -/
theorem rest_lay_comm (R R' : Set (FreeGroup α)) :
    ((S.lay R).lay R').rest = ((S.lay R').lay R).rest := by
  rw [lay_lay, lay_lay, Set.union_comm]

/-- **Rule 2.** Over `S`, obeying the rules of `S` gives `S` back. -/
theorem rest_lay_rules (h : C.IsOver S) : (C.lay S.rules).rest = S.rest := by
  have h' : C.rest ≤ S.rest := h
  rw [rest_lay]
  change C.rest ⊔ S.rest = S.rest
  exact sup_eq_right.mpr h'

/-- Laying is the first stage in which the rules hold: a choice of a law for each act,
under which the old rules and the new ones are rest, extends in one way. -/
theorem lay_first {G : Type*} [Group G] (R : Set (FreeGroup α)) (f : α → G)
    (hS : ∀ r ∈ S.rules, FreeGroup.lift f r = 1) (hR : ∀ r ∈ R, FreeGroup.lift f r = 1) :
    ∃! φ : (S.lay R).World →* G, ∀ a, φ ((S.lay R).law (FreeGroup.of a)) = f a := by
  have h : ∀ r ∈ (S.lay R).rules, FreeGroup.lift f r = 1 := by
    rintro r (hr | hr)
    exacts [hS r hr, hR r hr]
  refine ⟨PresentedGroup.toGroup h, fun a => PresentedGroup.toGroup.of h, fun φ hφ => ?_⟩
  exact PresentedGroup.ext fun a => (hφ a).trans (PresentedGroup.toGroup.of h).symm

/-! ### Add -/

variable (S) in
/-- Add: one more act, and no rule about it. The old acts are `some a`, the new one `none`. -/
def add : Stage (Option α) := ⟨FreeGroup.map some '' S.rules⟩

/-- **Rule 6.** Adding an act and obeying rules that do not use it, in either order. -/
theorem add_lay (R : Set (FreeGroup α)) : (S.lay R).add = S.add.lay (FreeGroup.map some '' R) :=
  congrArg Stage.mk (Set.image_union _ _ _)

variable (S) in
/-- The laws of `S` in the stage with one more act. -/
def addHom : S.World →* S.add.World :=
  QuotientGroup.map S.rest S.add.rest (FreeGroup.map some) <| by
    refine normalClosure_le_normal fun r hr => ?_
    exact S.add.rules_subset_rest ⟨r, hr, rfl⟩

@[simp]
theorem addHom_law (w : FreeGroup α) : S.addHom (S.law w) = S.add.law (FreeGroup.map some w) :=
  rfl

variable (S) in
/-- Sending the new act to rest gives the old stage back. -/
def addRetract : S.add.World →* S.World :=
  PresentedGroup.toGroup (f := fun o : Option α => o.elim 1 fun a => S.law (FreeGroup.of a)) <| by
    rintro _ ⟨r, hr, rfl⟩
    have : (FreeGroup.lift fun o : Option α => o.elim 1 fun a => S.law (FreeGroup.of a)).comp
        (FreeGroup.map some) = S.law := by
      ext a
      simp
    rw [← MonoidHom.comp_apply, this]
    exact S.law_eq_one_iff.mpr (S.rules_subset_rest hr)

theorem addRetract_addHom (x : S.World) : S.addRetract (S.addHom x) = x := by
  obtain ⟨w, rfl⟩ := S.law_surjective x
  induction w using FreeGroup.induction_on with
  | one => rw [map_one, map_one, map_one]
  | of a =>
    rw [addHom_law, FreeGroup.map.of]
    exact PresentedGroup.toGroup.of _
  | inv_of a ih => rw [map_inv, map_inv, map_inv, ih]
  | mul u v hu hv => rw [map_mul, map_mul, map_mul, hu, hv]

/-- Adding an act changes no old equality: two laws of `S` that are one law in the stage
with one more act are one law. -/
theorem addHom_injective : Function.Injective S.addHom :=
  Function.LeftInverse.injective addRetract_addHom

end Stage

end Artform.Stages
