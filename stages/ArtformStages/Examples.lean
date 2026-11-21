import ArtformStages.KeepTrail

/-!
# Examples: the count and the wheel, and two rules by example

* The **count** is one act and no rule. The **wheel** of `p` is one act, and the rule
  that `p` steps are rest. Keeping the whole trail over a wheel gives the count again:
  the charter's smallest case.
* **Rule 5.** A carry over a carry need not be a carry: over the stage with everything at
  rest, the wheel of two is a carry; the six orders of three things are a carry over that
  wheel; and they are no carry over the stage with everything at rest.
* **Rule 7.** Adding an act and keeping cannot be done in either order.
-/

namespace Artform.Stages

open Subgroup

open scoped commutatorElement

namespace Stage

/-! ### The count and the wheel -/

/-- The count: one act, and no rule. -/
def count : Stage Unit := ⟨∅⟩

/-- The wheel of `p` places: one act, and the rule that `p` steps are rest. -/
def wheel (p : ℕ) : Stage Unit := ⟨{FreeGroup.of () ^ p}⟩

theorem rest_count : count.rest = ⊥ := normalClosure_empty

/-- The walks of one act are the steps of that act, forward or back. -/
theorem exists_zpow (w : FreeGroup Unit) : ∃ k : ℤ, w = FreeGroup.of () ^ k := by
  induction w using FreeGroup.induction_on with
  | one => exact ⟨0, (zpow_zero _).symm⟩
  | of a => exact ⟨1, (zpow_one _).symm⟩
  | inv_of a ih => exact ⟨-1, (zpow_neg_one _).symm⟩
  | mul x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, (zpow_add _ m n).symm⟩

/-- Walks of one act pass each other. -/
theorem mul_comm_unit (x y : FreeGroup Unit) : x * y = y * x := by
  obtain ⟨m, rfl⟩ := exists_zpow x
  obtain ⟨n, rfl⟩ := exists_zpow y
  rw [← zpow_add, ← zpow_add, add_comm]

/-- On one act, commutators of walks are rest already: there is nothing to keep but
the count. -/
theorem commutator_unit (H K : Subgroup (FreeGroup Unit)) : ⁅H, K⁆ = ⊥ := by
  rw [eq_bot_iff, commutator_le]
  intro a _ b _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm_unit a b

/-- **The smallest case.** Keeping the whole trail over a wheel gives the count: the same
walks are rest. -/
theorem rest_keep_wheel (p : ℕ) : (wheel p).keep.rest = count.rest := by
  rw [rest_keep, rest_count]
  exact commutator_unit _ _

/-- The count is a carry over every wheel. -/
theorem count_isCarry_wheel (p : ℕ) : count.IsCarry (wheel p) := by
  rw [isCarry_iff, rest_count, commutator_unit]
  exact ⟨le_rfl, bot_le⟩

/-! ### Rule 5: a carry over a carry need not be a carry -/

/-- Two acts, read as the exchange of the first two of three things and of the last two. -/
def orders : FreeGroup Bool →* Equiv.Perm (Fin 3) :=
  FreeGroup.lift fun b => if b then Equiv.swap 0 1 else Equiv.swap 1 2

/-- The stage with everything at rest. -/
def allRest : Stage Bool := ofRest ⊤

/-- The sign of an order: a wheel of two. -/
def signWheel : Stage Bool := ofRest ((alternatingGroup (Fin 3)).comap orders)

/-- The six orders of three things. -/
def sixOrders : Stage Bool := ofRest orders.ker

theorem signWheel_isCarry : signWheel.IsCarry allRest := by
  rw [isCarry_iff, signWheel, allRest, rest_ofRest, rest_ofRest]
  refine ⟨commutator_le.mpr fun x _ y _ => ?_, le_top⟩
  rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup, map_commutatorElement,
    map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

theorem sixOrders_isCarry : sixOrders.IsCarry signWheel := by
  rw [isCarry_iff, sixOrders, signWheel, rest_ofRest, rest_ofRest]
  refine ⟨commutator_le.mpr fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have h : ∀ a b : Equiv.Perm (Fin 3), Equiv.Perm.sign a = 1 →
        Equiv.Perm.sign b = 1 → a * b = b * a := by decide
    exact h _ _ (Equiv.Perm.mem_alternatingGroup.mp hx) (Equiv.Perm.mem_alternatingGroup.mp hy)
  · rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _

theorem sixOrders_not_isCarry : ¬ sixOrders.IsCarry allRest := by
  rw [isCarry_iff, sixOrders, allRest, rest_ofRest, rest_ofRest]
  rintro ⟨h, -⟩
  have hc := h (commutator_mem_commutator (mem_top (FreeGroup.of true))
    (mem_top (FreeGroup.of false)))
  rw [MonoidHom.mem_ker, map_commutatorElement] at hc
  have hne : ⁅orders (FreeGroup.of true), orders (FreeGroup.of false)⁆ ≠ 1 := by
    simp only [orders, FreeGroup.lift_apply_of]
    decide
  exact hne hc

/-- **Rule 5.** A carry over a carry need not be a carry. -/
theorem carry_of_carry_need_not_be_carry :
    ∃ S C₁ C₂ : Stage Bool, C₁.IsCarry S ∧ C₂.IsCarry C₁ ∧ ¬ C₂.IsCarry S :=
  ⟨allRest, signWheel, sixOrders, signWheel_isCarry, sixOrders_isCarry, sixOrders_not_isCarry⟩

/-! ### Rule 7: adding an act and keeping, in the two orders -/

/-- A reading of the wheel of two with one more act, in the orders of four things, under
which a round of the wheel and the same round carried by the new act do not pass. -/
def reading : FreeGroup (Option Unit) →* Equiv.Perm (Fin 4) :=
  FreeGroup.lift fun o => o.elim (Equiv.swap 2 3) fun _ => Equiv.swap 0 1 * Equiv.swap 1 2

/-- The round of the wheel of two, among the walks of the stage with one more act. -/
def round : FreeGroup (Option Unit) := FreeGroup.of (some ()) ^ 2

/-- The same round, made after the new act and before that act undone. -/
def roundCarried : FreeGroup (Option Unit) :=
  FreeGroup.of none * round * (FreeGroup.of none)⁻¹

theorem round_mem : round ∈ (wheel 2).add.rest :=
  (wheel 2).add.rules_subset_rest ⟨FreeGroup.of () ^ 2, rfl, by simp [round]⟩

theorem commutator_round_ne_one : ⁅round, roundCarried⁆ ≠ 1 := by
  intro h
  have h1 : reading ⁅round, roundCarried⁆ = 1 := by rw [h, map_one]
  have h2 : reading ⁅round, roundCarried⁆ ≠ 1 := by
    simp only [round, roundCarried, reading, map_commutatorElement, map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, Option.elim]
    decide
  exact h2 h1

/-- **Rule 7.** Adding an act and keeping cannot be done in either order: over the wheel
of two, keeping after adding makes a walk rest that adding after keeping does not. -/
theorem keep_add_ne_add_keep : (wheel 2).add.keep.rest ≠ (wheel 2).keep.add.rest := by
  intro h
  have h1 : ⁅round, roundCarried⁆ ∈ (wheel 2).add.keep.rest := by
    rw [rest_keep]
    exact commutator_mem_commutator round_mem
      ((inferInstance : (wheel 2).add.rest.Normal).conj_mem _ round_mem _)
  have h2 : (wheel 2).keep.add.rest = ⊥ := by
    rw [eq_bot_iff]
    refine normalClosure_le_normal ?_
    rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ (⁅(wheel 2).rest, (wheel 2).rest⁆ : Subgroup (FreeGroup Unit)) := hr
    rw [commutator_unit, Subgroup.mem_bot] at hr'
    rw [hr', map_one]
    exact one_mem _
  rw [h, h2, Subgroup.mem_bot] at h1
  exact commutator_round_ne_one h1

end Stage

end Artform.Stages
