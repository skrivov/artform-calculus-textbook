import ArtformRoles.Calculus.Syntax
import Mathlib.Order.BoundedOrder.Basic

/-!
# Effects

Section 6.1 of the paper. Grades are ordered `free < gated < absent`; the sum
`⊕` of the paper is the minimum `⊓` and the product `⊗` is the maximum `⊔`
(`Grade.seq` and `Grade.alt` of `ArtformRoles.Basic`). An effect gives a grade
to every atom: a variable of the context or a public declaration of the
signature. Effects are ordered pointwise, and their lattice operations are
Mathlib's operations on functions.

* `Eff.unit z`: grade `0` at `z` and `∞` elsewhere (the paper's `𝟙_z`).
* `Eff.scale q ε`: the product `q ⊗ ε`.
* `Eff.unbind ε`: the restriction `ε ∖ x` that deletes the nearest bound
  variable and renumbers the others.
* `Eff.act n M ε`: the matrix action `M ⋆ ε` of a simultaneous substitution
  (equation (3) of the paper), for a context of `n` variables whose `i`-th
  variable is replaced by a term of effect `M i`.
-/

namespace Artform.Roles

namespace Grade

instance : LinearOrder Grade where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := Nat.le_refl a.toNat
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge a b := by
    change a.toNat < b.toNat ↔ a.toNat ≤ b.toNat ∧ ¬b.toNat ≤ a.toNat
    omega
  le_antisymm _ _ h₁ h₂ := toNat_injective (Nat.le_antisymm h₁ h₂)
  le_total a b := Nat.le_total a.toNat b.toNat
  toDecidableLE := fun _ _ => inferInstance
  min := alt
  max := seq
  min_def _ _ := rfl
  max_def _ _ := rfl

instance : BoundedOrder Grade where
  top := absent
  le_top := le_absent
  bot := free
  bot_le := free_le

theorem top_eq : (⊤ : Grade) = absent := rfl
theorem bot_eq : (⊥ : Grade) = free := rfl
theorem seq_eq_sup (a b : Grade) : seq a b = a ⊔ b := rfl
theorem alt_eq_inf (a b : Grade) : alt a b = a ⊓ b := rfl

theorem free_lt_gated : free < gated := by decide
theorem gated_lt_absent : gated < absent := by decide

/-- A grade below `∞`: the path it measures is live. -/
theorem lt_absent_iff (a : Grade) : a < absent ↔ a = free ∨ a = gated := by
  cases a <;> decide

end Grade

namespace Calculus

/-- The atoms an effect grades: a variable of the context, or component `k` of
the signature entry `i` (a family, a constant or a gate). -/
inductive Atom
  | var (i : ℕ)
  | decl (i k : ℕ)
  deriving DecidableEq, Repr

/-- An effect: a grade for every atom. Atoms out of scope have grade `∞`. -/
abbrev Eff := Atom → Grade

namespace Eff

/-- The paper's `𝟙_z`: grade `0` at `z`, `∞` elsewhere. -/
def unit (z : Atom) : Eff := fun y => if y = z then ⊥ else ⊤

/-- The product `q ⊗ ε`. -/
def scale (q : Grade) (ε : Eff) : Eff := fun z => q ⊔ ε z

/-- The restriction `ε ∖ x` deleting the nearest bound variable; the other
variables are renumbered. -/
def unbind (ε : Eff) : Eff
  | .var i => ε (.var (i + 1))
  | .decl i k => ε (.decl i k)

/-- The effect of a context grown by one variable: the new variable `var 0`
is not used. -/
def bind (ε : Eff) : Eff
  | .var 0 => ⊤
  | .var (i + 1) => ε (.var i)
  | .decl i k => ε (.decl i k)

/-- The part of an effect on the signature's declarations. -/
def declPart (ε : Eff) : Eff
  | .var _ => ⊤
  | .decl i k => ε (.decl i k)

/-- The variable part of the matrix action: `⨅_{i < n} ε(var i) ⊗ M i`. -/
def actVars : ℕ → (ℕ → Eff) → Eff → Eff
  | 0, _, _ => ⊤
  | n + 1, M, ε => scale (ε (.var 0)) (M 0) ⊓ actVars n (fun i => M (i + 1)) (unbind ε)

/-- The matrix action `M ⋆ ε` of a substitution on the variables `0, …, n-1`,
the term put for `var i` having effect `M i` (equation (3) of the paper). The
signature components of `ε` are kept unchanged. -/
def act (n : ℕ) (M : ℕ → Eff) (ε : Eff) : Eff := declPart ε ⊓ actVars n M ε

/-- The effects of a substitution moved under a binder: the bound variable is
kept, and the other effects are those of the shifted terms. -/
def upM (M : ℕ → Eff) : ℕ → Eff
  | 0 => unit (.var 0)
  | i + 1 => bind (M i)

/-- Every variable from `n` on has grade `∞`. -/
def VarsBelow (n : ℕ) (ε : Eff) : Prop := ∀ i, n ≤ i → ε (.var i) = ⊤

@[simp] theorem unit_self (z : Atom) : unit z z = ⊥ := by simp [unit]

theorem unit_ne {y z : Atom} (h : y ≠ z) : unit z y = ⊤ := by simp [unit, h]

@[simp] theorem scale_apply (q : Grade) (ε : Eff) (z : Atom) : scale q ε z = q ⊔ ε z := rfl

@[simp] theorem unbind_var (ε : Eff) (i : ℕ) : unbind ε (.var i) = ε (.var (i + 1)) := rfl

@[simp] theorem unbind_decl (ε : Eff) (i k : ℕ) : unbind ε (.decl i k) = ε (.decl i k) := rfl

@[simp] theorem bind_var_zero (ε : Eff) : bind ε (.var 0) = ⊤ := rfl

@[simp] theorem bind_var_succ (ε : Eff) (i : ℕ) : bind ε (.var (i + 1)) = ε (.var i) := rfl

@[simp] theorem bind_decl (ε : Eff) (i k : ℕ) : bind ε (.decl i k) = ε (.decl i k) := rfl

@[simp] theorem declPart_var (ε : Eff) (i : ℕ) : declPart ε (.var i) = ⊤ := rfl

@[simp] theorem declPart_decl (ε : Eff) (i k : ℕ) :
    declPart ε (.decl i k) = ε (.decl i k) := rfl

@[simp] theorem unbind_bind (ε : Eff) : unbind (bind ε) = ε := by
  funext z; cases z <;> rfl

theorem unbind_inf (ε η : Eff) : unbind (ε ⊓ η) = unbind ε ⊓ unbind η := by
  funext z; cases z <;> rfl

theorem unbind_scale (q : Grade) (ε : Eff) : unbind (scale q ε) = scale q (unbind ε) := by
  funext z; cases z <;> rfl

theorem unbind_top : unbind (⊤ : Eff) = ⊤ := by
  funext z; cases z <;> rfl

theorem unbind_mono {ε η : Eff} (h : ε ≤ η) : unbind ε ≤ unbind η := by
  intro z; cases z <;> exact h _

theorem scale_mono {q q' : Grade} {ε η : Eff} (hq : q ≤ q') (h : ε ≤ η) :
    scale q ε ≤ scale q' η := fun z => sup_le_sup hq (h z)

theorem scale_inf (q : Grade) (ε η : Eff) : scale q (ε ⊓ η) = scale q ε ⊓ scale q η := by
  funext z; exact sup_inf_left _ _ _

theorem scale_scale (q r : Grade) (ε : Eff) : scale q (scale r ε) = scale (q ⊔ r) ε := by
  funext z; simp [sup_assoc]

theorem scale_free (ε : Eff) : scale ⊥ ε = ε := by
  funext z; simp

theorem scale_top (ε : Eff) : scale ⊤ ε = ⊤ := by
  funext z; simp

theorem le_scale (q : Grade) (ε : Eff) : ε ≤ scale q ε := fun _ => le_sup_right

theorem scale_top_right (q : Grade) : scale q ⊤ = ⊤ := by
  funext z; simp


/-! ### The matrix action -/

theorem unbind_unit_var_zero : unbind (unit (.var 0)) = ⊤ := by
  funext z; cases z <;> simp [unbind, unit]

theorem unbind_unit_var_succ (i : ℕ) : unbind (unit (.var (i + 1))) = unit (.var i) := by
  funext z; cases z <;> simp [unbind, unit]

theorem unbind_unit_decl (a k : ℕ) : unbind (unit (.decl a k)) = unit (.decl a k) := by
  funext z; cases z <;> simp [unbind, unit]

theorem bind_unit_var (i : ℕ) : bind (unit (.var i)) = unit (.var (i + 1)) := by
  funext z
  cases z with
  | var j =>
    cases j with
    | zero => simp [bind, unit]
    | succ j => simp [bind, unit]
  | decl a k => simp [bind, unit]

theorem declPart_inf (ε η : Eff) : declPart (ε ⊓ η) = declPart ε ⊓ declPart η := by
  funext z; cases z <;> simp [declPart]

theorem declPart_scale (q : Grade) (ε : Eff) : declPart (scale q ε) = scale q (declPart ε) := by
  funext z; cases z <;> simp [declPart]

theorem declPart_top : declPart (⊤ : Eff) = ⊤ := by
  funext z; cases z <;> rfl

theorem declPart_unit_var (i : ℕ) : declPart (unit (.var i)) = ⊤ := by
  funext z; cases z <;> simp [declPart, unit]

theorem declPart_unit_decl (a k : ℕ) : declPart (unit (.decl a k)) = unit (.decl a k) := by
  funext z; cases z <;> simp [declPart, unit]

theorem declPart_unbind (ε : Eff) : declPart (unbind ε) = unbind (declPart ε) := by
  funext z; cases z <;> rfl

theorem declPart_mono {ε η : Eff} (h : ε ≤ η) : declPart ε ≤ declPart η := by
  intro z; cases z
  · exact le_rfl
  · exact h _

theorem actVars_top (n : ℕ) (M : ℕ → Eff) : actVars n M ⊤ = ⊤ := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih => simp [actVars, unbind_top, ih, scale_top]

theorem actVars_inf (n : ℕ) (M : ℕ → Eff) (ε η : Eff) :
    actVars n M (ε ⊓ η) = actVars n M ε ⊓ actVars n M η := by
  induction n generalizing M ε η with
  | zero => simp [actVars]
  | succ n ih =>
    have h₁ : scale ((ε ⊓ η) (.var 0)) (M 0) = scale (ε (.var 0)) (M 0) ⊓
        scale (η (.var 0)) (M 0) := by
      funext z; simp [sup_inf_right]
    simp only [actVars, unbind_inf, ih, h₁]
    ac_rfl

theorem actVars_scale (n : ℕ) (M : ℕ → Eff) (q : Grade) (ε : Eff) :
    actVars n M (scale q ε) = scale q (actVars n M ε) := by
  induction n generalizing M ε with
  | zero => exact (scale_top_right q).symm
  | succ n ih =>
    have h₁ : scale (scale q ε (.var 0)) (M 0) = scale q (scale (ε (.var 0)) (M 0)) := by
      funext z; simp [sup_assoc]
    simp only [actVars, unbind_scale, ih, h₁, scale_inf]

theorem actVars_mono (n : ℕ) (M : ℕ → Eff) {ε η : Eff} (h : ε ≤ η) :
    actVars n M ε ≤ actVars n M η := by
  induction n generalizing M ε η with
  | zero => exact le_rfl
  | succ n ih =>
    exact inf_le_inf (scale_mono (h _) le_rfl) (ih _ (unbind_mono h))

theorem actVars_unit_var {n i : ℕ} (hi : i < n) (M : ℕ → Eff) :
    actVars n M (unit (.var i)) = M i := by
  induction n generalizing i M with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp [actVars, unbind_unit_var_zero, actVars_top, scale_free]
    | succ i =>
      have h₀ : unit (.var (i + 1)) (.var 0) = ⊤ := unit_ne (by simp)
      simp [actVars, h₀, unbind_unit_var_succ, ih (by omega : i < n), scale_top]

theorem actVars_unit_decl (n : ℕ) (M : ℕ → Eff) (a k : ℕ) :
    actVars n M (unit (.decl a k)) = ⊤ := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
    have h₀ : unit (.decl a k) (.var 0) = ⊤ := unit_ne (by simp)
    simp [actVars, h₀, unbind_unit_decl, ih, scale_top]

theorem act_inf (n : ℕ) (M : ℕ → Eff) (ε η : Eff) :
    act n M (ε ⊓ η) = act n M ε ⊓ act n M η := by
  simp only [act, declPart_inf, actVars_inf]; ac_rfl

theorem act_scale (n : ℕ) (M : ℕ → Eff) (q : Grade) (ε : Eff) :
    act n M (scale q ε) = scale q (act n M ε) := by
  simp only [act, declPart_scale, actVars_scale, scale_inf]

theorem act_top (n : ℕ) (M : ℕ → Eff) : act n M ⊤ = ⊤ := by
  simp [act, declPart_top, actVars_top]

theorem act_mono (n : ℕ) (M : ℕ → Eff) {ε η : Eff} (h : ε ≤ η) : act n M ε ≤ act n M η :=
  inf_le_inf (declPart_mono h) (actVars_mono n M h)

theorem act_unit_var {n i : ℕ} (hi : i < n) (M : ℕ → Eff) : act n M (unit (.var i)) = M i := by
  simp [act, declPart_unit_var, actVars_unit_var hi]

theorem act_unit_decl (n : ℕ) (M : ℕ → Eff) (a k : ℕ) :
    act n M (unit (.decl a k)) = unit (.decl a k) := by
  simp [act, declPart_unit_decl, actVars_unit_decl]

theorem actVars_bind_var_zero (n : ℕ) (M : ℕ → Eff) (ε : Eff) :
    actVars n (fun i => bind (M i)) ε (.var 0) = ⊤ := by
  induction n generalizing M ε with
  | zero => rfl
  | succ n ih =>
    simp only [actVars, Pi.inf_apply, scale_apply, bind_var_zero, le_top, sup_of_le_right,
      ih (fun i => M (i + 1)), inf_idem]

theorem unbind_actVars_bind (n : ℕ) (M : ℕ → Eff) (ε : Eff) :
    unbind (actVars n (fun i => bind (M i)) ε) = actVars n M ε := by
  induction n generalizing M ε with
  | zero => exact unbind_top
  | succ n ih =>
    simp only [actVars, unbind_inf, unbind_scale, unbind_bind, ih (fun i => M (i + 1))]

/-- Under a binder, the matrix action of the moved substitution restricts to the
action of the substitution on the restricted effect. -/
theorem unbind_act_upM (n : ℕ) (M : ℕ → Eff) (θ : Eff) :
    unbind (act (n + 1) (upM M) θ) = act n M (unbind θ) := by
  simp only [act, actVars, upM, unbind_inf, unbind_scale, unbind_unit_var_zero,
    scale_top_right, top_inf_eq, unbind_actVars_bind, declPart_unbind]

/-- The moved substitution keeps the bound variable's grade. -/
theorem act_upM_var_zero (n : ℕ) (M : ℕ → Eff) (θ : Eff) :
    act (n + 1) (upM M) θ (.var 0) = θ (.var 0) := by
  simp only [act, actVars, Pi.inf_apply, declPart_var, top_inf_eq, scale_apply, upM,
    unit_self, actVars_bind_var_zero, inf_top_eq]
  exact sup_eq_left.mpr bot_le

theorem upM_unit (ξ : ℕ → ℕ) :
    upM (fun i => unit (.var (ξ i))) = fun i => unit (.var (Exp.upRen ξ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact bind_unit_var _

end Eff

end Calculus

end Artform.Roles
