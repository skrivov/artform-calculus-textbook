import ArtformStages.Basic

/-!
# Carries, and keep

* `C` is a **carry** over `S` when it is over `S` and any two kept laws pass each other
  (THEORY.md §3.3).
* **Theorem A**, in its form with commutators: `C` is a carry over `S` exactly when what is
  at rest in `C` lies between the commutators of the walks at rest in `S`, and those walks.
* **Keep**: the richest carry obeys only that the closed walks of `S` pass each other.
  *Kept in common*, it obeys that the walks at rest in `S` pass every walk.
* The rules of the algebra that concern keep (the stage algebra's rules 2, 3 and 4), and
  the sense in which each strength is the first stage in which its equation holds.
-/

namespace Artform.Stages

open Subgroup

variable {α : Type*}

/-- For normal subgroups, the commutators of `A ⊔ B` with itself, together with `B`, are the
commutators of `A` with itself, together with `B`. -/
theorem commutator_sup_self_sup {G : Type*} [Group G] (A B : Subgroup G) [A.Normal] [B.Normal] :
    ⁅A ⊔ B, A ⊔ B⁆ ⊔ B = ⁅A, A⁆ ⊔ B := by
  rw [commutator_sup_left, commutator_sup_right, commutator_sup_right]
  refine le_antisymm (sup_le (sup_le (sup_le le_sup_left ?_) (sup_le ?_ ?_)) le_sup_right)
    (sup_le_sup_right (le_sup_of_le_left le_sup_left) B)
  · exact le_sup_of_le_right (commutator_le_left B A)
  · exact le_sup_of_le_right (commutator_le_right A B)
  · exact le_sup_of_le_right (commutator_le_left B B)

namespace Stage

variable {S C : Stage α}

/-- `C` is a carry over `S`: it is over `S`, and any two kept laws pass each other. -/
def IsCarry (C S : Stage α) : Prop :=
  C.IsOver S ∧ ∀ k ∈ keptLaws C S, ∀ k' ∈ keptLaws C S, k * k' = k' * k

/-- **Theorem A** (with commutators). `C` is a carry over `S` exactly when the rest of `C`
lies between the commutators of the rest of `S` and the rest of `S`. -/
theorem isCarry_iff : C.IsCarry S ↔ ⁅S.rest, S.rest⁆ ≤ C.rest ∧ C.rest ≤ S.rest := by
  constructor
  · rintro ⟨hover, hpass⟩
    refine ⟨commutator_le.mpr fun n hn m hm => ?_, hover⟩
    have h := hpass _ (mem_keptLaws.mpr ⟨n, hn, rfl⟩) _ (mem_keptLaws.mpr ⟨m, hm, rfl⟩)
    rw [← C.law_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  · rintro ⟨hcomm, hover⟩
    refine ⟨hover, fun k hk k' hk' => ?_⟩
    obtain ⟨n, hn, rfl⟩ := mem_keptLaws.mp hk
    obtain ⟨m, hm, rfl⟩ := mem_keptLaws.mp hk'
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, C.law_eq_one_iff]
    exact hcomm (commutator_mem_commutator hn hm)

/-- **Theorem B** (with commutators). Every normal subgroup between the commutators of the
rest of `S` and the rest of `S` is the rest of a carry over `S`. With Theorem A, the carries
over `S` are these subgroups. -/
theorem isCarry_ofRest {K : Subgroup (FreeGroup α)} [K.Normal] (h₁ : ⁅S.rest, S.rest⁆ ≤ K)
    (h₂ : K ≤ S.rest) : (ofRest K).IsCarry S := by
  rw [isCarry_iff, rest_ofRest]
  exact ⟨h₁, h₂⟩

/-! ### Keep -/

variable (S) in
/-- Keep, the richest carry: the closed walks of `S` pass each other, and nothing more is
asked. This is `keep(S; 0)`, which keeps the whole trail. -/
def keep : Stage α := ofRest ⁅S.rest, S.rest⁆

@[simp]
theorem rest_keep : S.keep.rest = ⁅S.rest, S.rest⁆ := rest_ofRest _

theorem keep_isCarry : S.keep.IsCarry S :=
  isCarry_ofRest le_rfl (commutator_le_left _ _)

/-- The richest carry is over every carry. -/
theorem keep_isOver_of_isCarry (h : C.IsCarry S) : S.keep.IsOver C := by
  rw [isOver_iff, rest_keep]
  exact (isCarry_iff.mp h).1

variable (S) in
/-- Kept in common: the walks at rest in `S` pass every walk. -/
def keepCommon : Stage α := ofRest ⁅(⊤ : Subgroup (FreeGroup α)), S.rest⁆

@[simp]
theorem rest_keepCommon : S.keepCommon.rest = ⁅(⊤ : Subgroup (FreeGroup α)), S.rest⁆ :=
  rest_ofRest _

theorem keepCommon_isCarry : S.keepCommon.IsCarry S :=
  isCarry_ofRest (commutator_mono le_top le_rfl) (commutator_le_right _ _)

/-- Kept in common, a kept law passes every law. -/
theorem keepCommon_central {k : S.keepCommon.World} (hk : k ∈ keptLaws S.keepCommon S)
    (x : S.keepCommon.World) : x * k = k * x := by
  obtain ⟨n, hn, rfl⟩ := mem_keptLaws.mp hk
  obtain ⟨w, rfl⟩ := S.keepCommon.law_surjective x
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    S.keepCommon.law_eq_one_iff, rest_keepCommon]
  exact commutator_mem_commutator (mem_top w) hn

/-- The four strengths, in order: kept each face by itself, kept in common, obeyed. -/
theorem keep_isOver_keepCommon : S.keep.IsOver S.keepCommon := by
  rw [isOver_iff, rest_keep, rest_keepCommon]
  exact commutator_mono le_top le_rfl

theorem keepCommon_isOver : S.keepCommon.IsOver S := keepCommon_isCarry.1

/-! ### The rules of the algebra -/

/-- **Rule 2.** Keeping, and then obeying what was kept, changes nothing. -/
theorem rest_lay_keep : (S.keep.lay S.rules).rest = S.rest :=
  rest_lay_rules keep_isCarry.1

/-- **Rule 2**, for any carry. -/
theorem rest_lay_of_isCarry (h : C.IsCarry S) : (C.lay S.rules).rest = S.rest :=
  rest_lay_rules h.1

/-- **Rule 3.** Obeying, and then keeping, gives the stage back exactly when what was
obeyed passes: `S` is a carry over what is laid on it exactly when, in `S`, the walks that
the laying puts at rest pass each other. -/
theorem isCarry_lay_iff (R : Set (FreeGroup α)) :
    S.IsCarry (S.lay R) ↔ ⁅(S.lay R).rest, (S.lay R).rest⁆ ≤ S.rest := by
  rw [isCarry_iff]
  exact and_iff_left (isOver_lay R)

variable (S) in
/-- Keep every rule of `S`, each face by itself, except the rules of `R`, which stay rest. -/
def keepExcept (R : Set (FreeGroup α)) : Stage α := ofRest (⁅S.rest, S.rest⁆ ⊔ normalClosure R)

@[simp]
theorem rest_keepExcept (R : Set (FreeGroup α)) :
    (S.keepExcept R).rest = ⁅S.rest, S.rest⁆ ⊔ normalClosure R :=
  rest_ofRest _

/-- **Rule 4.** Obeying one rule and keeping another can be done in either order: keeping
`r` over the stage of `r` and `s`, with `s` obeyed, leaves the same at rest as keeping `r`
over the stage of `r` alone and then laying `s`. -/
theorem rest_keepExcept_union (r s : Set (FreeGroup α)) :
    ((Stage.mk (r ∪ s)).keepExcept s).rest = ((Stage.mk r).keep.lay s).rest := by
  have h1 : (Stage.mk (r ∪ s)).rest = normalClosure r ⊔ normalClosure s := normalClosure_union r s
  have h2 : (Stage.mk r).rest = normalClosure r := rfl
  rw [rest_keepExcept, rest_lay, rest_keep, h1, h2]
  exact commutator_sup_self_sup _ _

/-! ### Each strength is a first thing -/

/-- Keep is the first stage in which the closed walks of `S` pass each other: a choice of a
law for each act, under which the walks at rest in `S` pass each other, extends in one way. -/
theorem keep_first {G : Type*} [Group G] (f : α → G)
    (h : ∀ n ∈ S.rest, ∀ m ∈ S.rest,
      FreeGroup.lift f n * FreeGroup.lift f m = FreeGroup.lift f m * FreeGroup.lift f n) :
    ∃! φ : S.keep.World →* G, ∀ a, φ (S.keep.law (FreeGroup.of a)) = f a := by
  have hr : ∀ r ∈ S.keep.rules, FreeGroup.lift f r = 1 := by
    intro r hr
    have hle : ⁅S.rest, S.rest⁆ ≤ (FreeGroup.lift f).ker := by
      refine commutator_le.mpr fun n hn m hm => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h n hn m hm
    exact hle hr
  refine ⟨PresentedGroup.toGroup hr, fun a => PresentedGroup.toGroup.of hr, fun φ hφ => ?_⟩
  exact PresentedGroup.ext fun a => (hφ a).trans (PresentedGroup.toGroup.of hr).symm

/-- In the richest carry itself the closed walks of `S` pass each other. -/
theorem keep_pass {n m : FreeGroup α} (hn : n ∈ S.rest) (hm : m ∈ S.rest) :
    S.keep.law n * S.keep.law m = S.keep.law m * S.keep.law n := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, S.keep.law_eq_one_iff,
    rest_keep]
  exact commutator_mem_commutator hn hm

/-- Kept in common is the first stage in which the walks at rest in `S` pass every walk. -/
theorem keepCommon_first {G : Type*} [Group G] (f : α → G)
    (h : ∀ w, ∀ n ∈ S.rest,
      FreeGroup.lift f w * FreeGroup.lift f n = FreeGroup.lift f n * FreeGroup.lift f w) :
    ∃! φ : S.keepCommon.World →* G, ∀ a, φ (S.keepCommon.law (FreeGroup.of a)) = f a := by
  have hr : ∀ r ∈ S.keepCommon.rules, FreeGroup.lift f r = 1 := by
    intro r hr
    have hle : ⁅(⊤ : Subgroup (FreeGroup α)), S.rest⁆ ≤ (FreeGroup.lift f).ker := by
      refine commutator_le.mpr fun w _ n hn => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h w n hn
    exact hle hr
  refine ⟨PresentedGroup.toGroup hr, fun a => PresentedGroup.toGroup.of hr, fun φ hφ => ?_⟩
  exact PresentedGroup.ext fun a => (hφ a).trans (PresentedGroup.toGroup.of hr).symm

end Stage

end Artform.Stages
