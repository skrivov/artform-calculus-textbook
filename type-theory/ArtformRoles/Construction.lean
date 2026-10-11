import ArtformRoles.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Constructions: data with roles and graded dependencies

Section 3 of the paper. A construction is a family of data items, each with a
role, and a grade for each direct dependency of one item on another: `free`
for ordinary use, `gated` for use through a gate that keeps a record of what was
assumed, `absent` for no use.

* `Valid D`: every direct dependency meets the policy `D`.
* `Valid.reach`, `pathClosed_of_reach`: checking each direct dependency
  suffices exactly when the policy is path closed.
* `no_reach_of_rendering`: nothing outside the rendering depends on a reading.
* `crosses_gate`: every dependency that the policy gates crosses a gate whose
  record reaches the result.
* `Evaluation.eq_of_agree`: values computed only from live dependencies; the
  firewall, frame stability and presentation independence as statements about
  values (`firewall`, `frame_stable`, `form_stable`).
-/

namespace Artform.Roles

open Grade

/-- A construction: items of `V`, each with a role, and the grade of each
direct dependency of one item (the second argument) on another (the first). -/
structure Construction (V : Type*) where
  role : V → Role
  edge : V → V → Grade

namespace Construction

variable {V : Type*} (c : Construction V)

/-- `c.Reach g u v`: a chain of direct dependencies from `u` to `v`, each of
grade at most `g`. `Reach free` follows ordinary uses only; `Reach gated`
follows every live dependency. -/
inductive Reach (g : Grade) : V → V → Prop
  | refl (v : V) : Reach g v v
  | tail {u w v : V} : Reach g u w → c.edge w v ≤ g → Reach g u v

/-- Every direct dependency meets its demand under the policy `D`. -/
def Valid (D : Role → Role → Grade) : Prop :=
  ∀ u v, D (c.role u) (c.role v) ≤ c.edge u v

variable {c}

theorem Reach.trans {g : Grade} {u w v : V} (p : c.Reach g u w) (q : c.Reach g w v) :
    c.Reach g u v := by
  induction q with
  | refl => exact p
  | tail _ e ih => exact .tail ih e

theorem Reach.mono {g h : Grade} (hgh : g ≤ h) {u v : V} (p : c.Reach g u v) :
    c.Reach h u v := by
  induction p with
  | refl => exact .refl _
  | tail _ e ih => exact .tail ih (by rw [le_def] at *; omega)

/-- **Local to global.** Under a path-closed policy, a construction whose
direct dependencies are valid satisfies the policy along every chain. -/
theorem Valid.reach {D : Role → Role → Grade} (hD : PathClosed D)
    (hself : ∀ σ, D σ σ = .free) (h : c.Valid D) {g : Grade} {u v : V}
    (p : c.Reach g u v) : D (c.role u) (c.role v) ≤ g := by
  induction p with
  | refl => rw [hself]; exact free_le g
  | @tail w v _ e ih =>
    have h1 := hD (c.role u) (c.role w) (c.role v)
    have h2 := h w v
    rw [le_def] at *
    simp only [toNat_seq] at h1
    omega

/-- **Path closure is necessary.** If checking direct dependencies sufficed for
every construction on three items, the policy is path closed. -/
theorem pathClosed_of_reach {D : Role → Role → Grade}
    (hD : ∀ c : Construction (Fin 3), c.Valid D →
      ∀ (g : Grade) (u v : Fin 3), c.Reach g u v → D (c.role u) (c.role v) ≤ g) :
    PathClosed D := by
  intro σ τ ρ
  let c : Construction (Fin 3) :=
    { role := ![σ, τ, ρ]
      edge := fun i j =>
        if i = 0 ∧ j = 1 then D σ τ else if i = 1 ∧ j = 2 then D τ ρ else .absent }
  have hc : c.Valid D := by
    intro i j
    change D (![σ, τ, ρ] i) (![σ, τ, ρ] j) ≤
      (if i = 0 ∧ j = 1 then D σ τ else if i = 1 ∧ j = 2 then D τ ρ else .absent)
    split_ifs with h1 h2
    · obtain ⟨rfl, rfl⟩ := h1; exact le_def.mpr le_rfl
    · obtain ⟨rfl, rfl⟩ := h2; exact le_def.mpr le_rfl
    · exact le_absent _
  have p : c.Reach (seq (D σ τ) (D τ ρ)) 0 2 := by
    refine .tail (w := 1) (.tail (w := 0) (.refl 0) ?_) ?_
    · change D σ τ ≤ seq (D σ τ) (D τ ρ)
      rw [le_def, toNat_seq]; omega
    · change D τ ρ ≤ seq (D σ τ) (D τ ρ)
      rw [le_def, toNat_seq]; omega
  exact hD c hc _ 0 2 p

section Book

variable (h : c.Valid demand)
include h

/-- Under the book's policy, every chain meets the policy. -/
theorem reach_demand {g : Grade} {u v : V} (p : c.Reach g u v) :
    demand (c.role u) (c.role v) ≤ g :=
  Valid.reach demand_pathClosed demand_self h p

/-- **Firewall.** No live chain leads from a reading to anything that is not a
rendering. -/
theorem no_reach_of_rendering {u v : V} (hu : c.role u = .rendering)
    (hv : c.role v ≠ .rendering) : ¬ c.Reach .gated u v := by
  intro p
  have hp := reach_demand h p
  have hR : demand (c.role u) (c.role v) = .absent := by
    rw [hu]; revert hv; cases c.role v <;> decide
  rw [hR] at hp
  exact absurd hp (by decide)

/-- **Mediation.** Where the policy gates a dependency, no chain of ordinary
uses carries it. -/
theorem no_free_reach {u v : V} (hd : demand (c.role u) (c.role v) = .gated) :
    ¬ c.Reach .free u v := by
  intro p
  have := reach_demand h p
  rw [hd] at this
  exact absurd this (by decide)

omit h in
/-- A live chain either uses ordinary dependencies only, or crosses a gate. -/
theorem Reach.free_or_gate {u v : V} (p : c.Reach .gated u v) :
    c.Reach .free u v ∨
      ∃ w w', c.Reach .gated u w ∧ c.edge w w' = .gated ∧ c.Reach .gated w' v := by
  induction p with
  | refl => exact .inl (.refl _)
  | @tail w v p e ih =>
    by_cases hf : c.edge w v = .free
    · rcases ih with q | ⟨a, b, q1, hab, q2⟩
      · exact .inl (.tail q (by rw [hf]; decide))
      · exact .inr ⟨a, b, q1, hab, .tail q2 e⟩
    · have hg : c.edge w v = .gated := by
        revert e hf; cases c.edge w v <;> decide
      exact .inr ⟨w, v, p, hg, .refl v⟩

/-- **Records.** Every live dependency that the policy gates crosses a gate
edge, and the gate's record reaches the result along a live chain. -/
theorem crosses_gate {u v : V} (hd : demand (c.role u) (c.role v) = .gated)
    (p : c.Reach .gated u v) :
    ∃ w w', c.Reach .gated u w ∧ c.edge w w' = .gated ∧ c.Reach .gated w' v := by
  rcases p.free_or_gate with q | hq
  · exact absurd q (no_free_reach h hd)
  · exact hq

end Book

/-! ## Values -/

/-- An evaluation of a construction: each item computes its value from the
values of the items it depends on live, and from nothing else. -/
structure Evaluation (c : Construction V) (α : Type*) where
  compute : V → (V → α) → α
  local_ : ∀ v (x y : V → α), (∀ u, c.edge u v ≤ .gated → x u = y u) →
    compute v x = compute v y

/-- A valuation is consistent with an evaluation when every item has the value
it computes. -/
def Evaluation.Consistent {α : Type*} (e : c.Evaluation α) (x : V → α) : Prop :=
  ∀ v, x v = e.compute v x

/-- An acyclic construction: live dependencies go up a rank. -/
def Acyclic (c : Construction V) (rank : V → ℕ) : Prop :=
  ∀ u v, c.edge u v ≤ .gated → rank u < rank v

/-- **Determination.** Let `U` be a set of items, and let two evaluations
compute alike on `U`. If every live dependency of an item of `U` on an item
outside `U` carries the same value in two consistent valuations, the two
valuations agree on `U`. -/
theorem Evaluation.eq_of_agree {α : Type*} {rank : V → ℕ} (hc : c.Acyclic rank)
    (U : V → Prop) (e e' : c.Evaluation α) (hU : ∀ v, U v → e.compute v = e'.compute v)
    {x y : V → α} (hx : e.Consistent x) (hy : e'.Consistent y)
    (hcross : ∀ u v, U v → ¬ U u → c.edge u v ≤ .gated → x u = y u) :
    ∀ v, U v → x v = y v := by
  suffices H : ∀ n, ∀ v, rank v = n → U v → x v = y v from fun v hv => H _ v rfl hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv
    rw [hx v, hy v, hU v hv]
    apply e'.local_
    intro u hu
    by_cases huU : U u
    · exact ih (rank u) (hn ▸ hc u v hu) u rfl huU
    · exact hcross u v hv huU hu

/-- The frame's items: forms and presentations. -/
def IsFrame (σ : Role) : Prop := σ = .form ∨ σ = .presentation

theorem gated_le_demand_into_frame {σ ρ : Role} (hσ : ¬ IsFrame σ) (hρ : IsFrame ρ) :
    Grade.gated ≤ demand σ ρ := by
  unfold IsFrame at hσ hρ; revert hσ hρ; cases σ <;> cases ρ <;> decide

theorem gated_le_demand_into_form {σ : Role} (hσ : σ ≠ .form) :
    Grade.gated ≤ demand σ .form := by
  revert hσ; cases σ <;> decide

theorem eq_gated {a : Grade} (h1 : Grade.gated ≤ a) (h2 : a ≤ Grade.gated) : a = .gated := by
  revert h1 h2; cases a <;> decide

section Values

variable (h : c.Valid demand)
include h

/-- **Firewall, for values.** Replacing every renderer, with everything else
kept, changes no value outside the rendering. -/
theorem firewall {α : Type*} {rank : V → ℕ} (hc : c.Acyclic rank)
    (e e' : c.Evaluation α)
    (hU : ∀ v, c.role v ≠ .rendering → e.compute v = e'.compute v)
    {x y : V → α} (hx : e.Consistent x) (hy : e'.Consistent y) :
    ∀ v, c.role v ≠ .rendering → x v = y v := by
  refine Evaluation.eq_of_agree hc (fun v => c.role v ≠ .rendering) e e' hU hx hy ?_
  intro u v hv hu huv
  exact absurd (.tail (.refl u) huv) (no_reach_of_rendering h (not_not.mp hu) hv)

/-- **Frame stability, for values.** The frame's items have the same values in
any two runs that compute the frame alike and agree on what crosses the gates
into the frame: witnesses, scripts and readings change the frame only through
recorded gates. -/
theorem frame_stable {α : Type*} {rank : V → ℕ} (hc : c.Acyclic rank)
    (e e' : c.Evaluation α)
    (hU : ∀ v, IsFrame (c.role v) → e.compute v = e'.compute v)
    {x y : V → α} (hx : e.Consistent x) (hy : e'.Consistent y)
    (hrec : ∀ u v, IsFrame (c.role v) → c.edge u v = .gated → x u = y u) :
    ∀ v, IsFrame (c.role v) → x v = y v := by
  refine Evaluation.eq_of_agree hc (fun v => IsFrame (c.role v)) e e' hU hx hy ?_
  intro u v hv hu huv
  apply hrec u v hv
  have hd := h u v
  have hg := gated_le_demand_into_frame hu hv
  exact eq_gated (by rw [le_def] at *; omega) huv

/-- **Presentation independence, for values.** A form has the same value in
any two runs that compute forms alike and agree on what crosses the gates into
forms: a form never depends on how it is addressed except on the record. -/
theorem form_stable {α : Type*} {rank : V → ℕ} (hc : c.Acyclic rank)
    (e e' : c.Evaluation α)
    (hU : ∀ v, c.role v = .form → e.compute v = e'.compute v)
    {x y : V → α} (hx : e.Consistent x) (hy : e'.Consistent y)
    (hrec : ∀ u v, c.role v = .form → c.edge u v = .gated → x u = y u) :
    ∀ v, c.role v = .form → x v = y v := by
  refine Evaluation.eq_of_agree hc (fun v => c.role v = .form) e e' hU hx hy ?_
  intro u v hv hu huv
  apply hrec u v hv
  have hd := h u v
  have hg := gated_le_demand_into_form hu
  rw [hv] at hd
  exact eq_gated (by rw [le_def] at *; omega) huv

end Values

end Construction

end Artform.Roles
