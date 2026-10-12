import ArtformRoles.Basic

/-!
# The syntax of the calculus

Section 6.3 of the paper *Five Roles for Artforms* (`type-theory/paper/`).
Types and terms share one syntax `Exp`, with de Bruijn indices: `var 0` is the
nearest binder. The binders are the codomain of `pi`, the second component of
`sigma`, and the body of `lam`.

* A family application `a(t₁, …, tₙ)` is `fam a args`, a gate term
  `gate_g(d⃗; s)` is `gate g ds s`, and a node `node_g(d⃗; t, e)` is
  `node g ℓ ds t e`. Argument lists are written in `Exp` itself with `nil` and
  `cons`, first argument first, so that `Exp` is an ordinary inductive type.
  Only argument positions hold `nil` and `cons`; the typing rules give them no
  other use.
* Families, gates and nodes name their signature entry by its position.
  A constant `const i k` is component `k` of entry `i`: the constant of a
  primitive is component `0`; a certificate bundle has its payload, event and
  origin as components `0`, `1`, `2`; an exact attestation has its event and
  origin as components `0`, `1`.
* `node g ℓ ds t e` carries a label `ℓ`, the metatheoretic label of
  Definition 7.1 (residual record trace). Typing ignores it, the record rule
  writes `0`, and only the labelled reduction of `ArtformRoles.Calculus.Records`
  chooses it.

The renaming `ren` and substitution `subst` act on free variables, and the
lemmas below are the usual laws of a de Bruijn syntax.
-/

namespace Artform.Roles.Calculus

/-- The expressions of the calculus: its types and terms. -/
inductive Exp : Type
  | var (i : ℕ)
  | const (i k : ℕ)
  | fam (a : ℕ) (args : Exp)
  | event
  | origin (A e t : Exp)
  | stamped (σ : Role) (A : Exp)
  | pi (q : Grade) (σ : Role) (A B : Exp)
  | sigma (ρ : Role) (A B : Exp)
  | lam (q : Grade) (σ : Role) (A t : Exp)
  | app (t u : Exp)
  | pair (t u : Exp)
  | fst (t : Exp)
  | snd (t : Exp)
  | stamp (t e o : Exp)
  | gate (g : ℕ) (ds s : Exp)
  | node (g ℓ : ℕ) (ds t e : Exp)
  | nil
  | cons (t ts : Exp)
  deriving DecidableEq, Repr

namespace Exp

/-! ## Renaming -/

/-- A renaming moved under a binder. -/
def upRen (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => ξ i + 1

@[simp] theorem upRen_zero (ξ : ℕ → ℕ) : upRen ξ 0 = 0 := rfl
@[simp] theorem upRen_succ (ξ : ℕ → ℕ) (i : ℕ) : upRen ξ (i + 1) = ξ i + 1 := rfl

/-- Rename the free variables of an expression. -/
def ren (ξ : ℕ → ℕ) : Exp → Exp
  | var i => var (ξ i)
  | const i k => const i k
  | fam a args => fam a (ren ξ args)
  | event => event
  | origin A e t => origin (ren ξ A) (ren ξ e) (ren ξ t)
  | stamped σ A => stamped σ (ren ξ A)
  | pi q σ A B => pi q σ (ren ξ A) (ren (upRen ξ) B)
  | sigma ρ A B => sigma ρ (ren ξ A) (ren (upRen ξ) B)
  | lam q σ A t => lam q σ (ren ξ A) (ren (upRen ξ) t)
  | app t u => app (ren ξ t) (ren ξ u)
  | pair t u => pair (ren ξ t) (ren ξ u)
  | fst t => fst (ren ξ t)
  | snd t => snd (ren ξ t)
  | stamp t e o => stamp (ren ξ t) (ren ξ e) (ren ξ o)
  | gate g ds s => gate g (ren ξ ds) (ren ξ s)
  | node g ℓ ds t e => node g ℓ (ren ξ ds) (ren ξ t) (ren ξ e)
  | nil => nil
  | cons t ts => cons (ren ξ t) (ren ξ ts)

theorem upRen_comp (ξ ζ : ℕ → ℕ) : upRen ζ ∘ upRen ξ = upRen (ζ ∘ ξ) := by
  funext i; cases i <;> rfl

theorem upRen_id : upRen id = id := by
  funext i; cases i <;> rfl

theorem ren_ren (ξ ζ : ℕ → ℕ) (t : Exp) : ren ζ (ren ξ t) = ren (ζ ∘ ξ) t := by
  induction t generalizing ξ ζ <;> simp_all [ren, upRen_comp]

theorem ren_id (t : Exp) : ren id t = t := by
  induction t <;> simp_all [ren, upRen_id]

/-- Shift every free variable up by one. -/
abbrev shift (t : Exp) : Exp := ren Nat.succ t

/-! ## Substitution -/

/-- A substitution moved under a binder. -/
def up (σ : ℕ → Exp) : ℕ → Exp
  | 0 => var 0
  | i + 1 => ren Nat.succ (σ i)

@[simp] theorem up_zero (σ : ℕ → Exp) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : ℕ → Exp) (i : ℕ) : up σ (i + 1) = ren Nat.succ (σ i) := rfl

/-- Substitute for the free variables of an expression. -/
def subst (σ : ℕ → Exp) : Exp → Exp
  | var i => σ i
  | const i k => const i k
  | fam a args => fam a (subst σ args)
  | event => event
  | origin A e t => origin (subst σ A) (subst σ e) (subst σ t)
  | stamped ρ A => stamped ρ (subst σ A)
  | pi q ρ A B => pi q ρ (subst σ A) (subst (up σ) B)
  | sigma ρ A B => sigma ρ (subst σ A) (subst (up σ) B)
  | lam q ρ A t => lam q ρ (subst σ A) (subst (up σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | pair t u => pair (subst σ t) (subst σ u)
  | fst t => fst (subst σ t)
  | snd t => snd (subst σ t)
  | stamp t e o => stamp (subst σ t) (subst σ e) (subst σ o)
  | gate g ds s => gate g (subst σ ds) (subst σ s)
  | node g ℓ ds t e => node g ℓ (subst σ ds) (subst σ t) (subst σ e)
  | nil => nil
  | cons t ts => cons (subst σ t) (subst σ ts)

theorem up_ren_comm (ξ : ℕ → ℕ) (σ : ℕ → Exp) :
    ren (upRen ξ) ∘ up σ = up (ren ξ ∘ σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [up, ren_ren]; rfl

theorem ren_subst (ξ : ℕ → ℕ) (σ : ℕ → Exp) (t : Exp) :
    ren ξ (subst σ t) = subst (ren ξ ∘ σ) t := by
  induction t generalizing ξ σ <;> simp_all [ren, subst, ← up_ren_comm]

theorem up_comp_upRen (σ : ℕ → Exp) (ξ : ℕ → ℕ) : up σ ∘ upRen ξ = up (σ ∘ ξ) := by
  funext i; cases i <;> rfl

theorem subst_ren (σ : ℕ → Exp) (ξ : ℕ → ℕ) (t : Exp) :
    subst σ (ren ξ t) = subst (σ ∘ ξ) t := by
  induction t generalizing σ ξ <;> simp_all [ren, subst, ← up_comp_upRen]

theorem up_subst_comm (σ τ : ℕ → Exp) :
    subst (up τ) ∘ up σ = up (subst τ ∘ σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Function.comp_apply, up_succ, subst_ren, ren_subst]
    rfl

theorem subst_subst (σ τ : ℕ → Exp) (t : Exp) :
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t generalizing σ τ <;> simp_all [subst, ← up_subst_comm]

theorem up_var : up var = var := by
  funext i; cases i <;> rfl

@[simp] theorem subst_var (t : Exp) : subst var t = t := by
  induction t <;> simp_all [subst, up_var]

theorem upRen_var (ξ : ℕ → ℕ) : up (var ∘ ξ) = var ∘ upRen ξ := by
  funext i; cases i <;> rfl

theorem ren_eq_subst (ξ : ℕ → ℕ) (t : Exp) : ren ξ t = subst (var ∘ ξ) t := by
  induction t generalizing ξ <;> simp_all [ren, subst, upRen_var]

theorem subst_ext {σ τ : ℕ → Exp} (h : ∀ i, σ i = τ i) (t : Exp) : subst σ t = subst τ t := by
  rw [funext h]

/-! ## Single substitution -/

/-- The substitution that puts `u` for `var 0` and lowers the other variables. -/
def inst1 (u : Exp) : ℕ → Exp
  | 0 => u
  | i + 1 => var i

@[simp] theorem inst1_zero (u : Exp) : inst1 u 0 = u := rfl
@[simp] theorem inst1_succ (u : Exp) (i : ℕ) : inst1 u (i + 1) = var i := rfl

/-- `t[u/x]`: put `u` for the nearest bound variable of `t`. -/
abbrev inst (t u : Exp) : Exp := subst (inst1 u) t

theorem inst1_comp_succ (u : Exp) : inst1 u ∘ Nat.succ = var := by
  funext i; rfl

/-- Substitution commutes with instantiation. -/
theorem subst_inst (σ : ℕ → Exp) (t u : Exp) :
    subst σ (inst t u) = inst (subst (up σ) t) (subst σ u) := by
  simp only [inst, subst_subst]
  refine subst_ext (fun i => ?_) t
  cases i with
  | zero => rfl
  | succ i => simp [subst, subst_ren, inst1_comp_succ]

/-- Renaming commutes with instantiation. -/
theorem ren_inst (ξ : ℕ → ℕ) (t u : Exp) :
    ren ξ (inst t u) = inst (ren (upRen ξ) t) (ren ξ u) := by
  rw [ren_eq_subst, ren_eq_subst, ren_eq_subst, subst_inst, upRen_var]

/-- Instantiating a shifted expression gives it back. -/
@[simp] theorem inst_shift (t u : Exp) : inst (shift t) u = t := by
  simp only [inst, shift, subst_ren]
  exact subst_var t

/-- Substitutions moved under `k` binders. -/
def upN : ℕ → (ℕ → Exp) → ℕ → Exp
  | 0, σ => σ
  | k + 1, σ => up (upN k σ)

/-- Renamings moved under `k` binders. -/
def upRenN : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, ξ => ξ
  | k + 1, ξ => upRen (upRenN k ξ)

/-! ## Free variables -/

/-- Every free variable of the expression is below `n`. -/
def Below (n : ℕ) : Exp → Prop
  | var i => i < n
  | const _ _ => True
  | fam _ args => Below n args
  | event => True
  | origin A e t => Below n A ∧ Below n e ∧ Below n t
  | stamped _ A => Below n A
  | pi _ _ A B => Below n A ∧ Below (n + 1) B
  | sigma _ A B => Below n A ∧ Below (n + 1) B
  | lam _ _ A t => Below n A ∧ Below (n + 1) t
  | app t u => Below n t ∧ Below n u
  | pair t u => Below n t ∧ Below n u
  | fst t => Below n t
  | snd t => Below n t
  | stamp t e o => Below n t ∧ Below n e ∧ Below n o
  | gate _ ds s => Below n ds ∧ Below n s
  | node _ _ ds t e => Below n ds ∧ Below n t ∧ Below n e
  | nil => True
  | cons t ts => Below n t ∧ Below n ts

/-- Closed expressions: no free variable. -/
abbrev Closed (t : Exp) : Prop := Below 0 t

theorem up_congr {n : ℕ} {σ τ : ℕ → Exp} (h : ∀ i < n, σ i = τ i) :
    ∀ i < n + 1, up σ i = up τ i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => simp [h i (by omega)]

theorem subst_congr_below {n : ℕ} {σ τ : ℕ → Exp} (h : ∀ i < n, σ i = τ i) {t : Exp}
    (ht : Below n t) : subst σ t = subst τ t := by
  induction t generalizing n σ τ with
  | var i => exact h i ht
  | const => rfl
  | fam a args ih => simp only [Below] at ht; simp only [subst, ih h ht]
  | event => rfl
  | origin A e t ihA ihe iht =>
    simp only [Below] at ht; simp only [subst, ihA h ht.1, ihe h ht.2.1, iht h ht.2.2]
  | stamped ρ A ih => simp only [Below] at ht; simp only [subst, ih h ht]
  | pi q ρ A B ihA ihB =>
    simp only [Below] at ht; simp only [subst, ihA h ht.1, ihB (up_congr h) ht.2]
  | sigma ρ A B ihA ihB =>
    simp only [Below] at ht; simp only [subst, ihA h ht.1, ihB (up_congr h) ht.2]
  | lam q ρ A t ihA iht =>
    simp only [Below] at ht; simp only [subst, ihA h ht.1, iht (up_congr h) ht.2]
  | app t u iht ihu => simp only [Below] at ht; simp only [subst, iht h ht.1, ihu h ht.2]
  | pair t u iht ihu => simp only [Below] at ht; simp only [subst, iht h ht.1, ihu h ht.2]
  | fst t ih => simp only [Below] at ht; simp only [subst, ih h ht]
  | snd t ih => simp only [Below] at ht; simp only [subst, ih h ht]
  | stamp t e o iht ihe iho =>
    simp only [Below] at ht; simp only [subst, iht h ht.1, ihe h ht.2.1, iho h ht.2.2]
  | gate g ds s ihd ihs => simp only [Below] at ht; simp only [subst, ihd h ht.1, ihs h ht.2]
  | node g ℓ ds t e ihd iht ihe =>
    simp only [Below] at ht; simp only [subst, ihd h ht.1, iht h ht.2.1, ihe h ht.2.2]
  | nil => rfl
  | cons t ts iht ihts => simp only [Below] at ht; simp only [subst, iht h ht.1, ihts h ht.2]

/-- A closed expression is unchanged by every substitution. -/
theorem subst_closed {σ : ℕ → Exp} {t : Exp} (ht : Closed t) : subst σ t = t := by
  rw [subst_congr_below (τ := var) (fun _ h => absurd h (Nat.not_lt_zero _)) ht, subst_var]

/-- A closed expression is unchanged by every renaming. -/
theorem ren_closed {ξ : ℕ → ℕ} {t : Exp} (ht : Closed t) : ren ξ t = t := by
  rw [ren_eq_subst, subst_closed ht]

theorem below_mono {m n : ℕ} (hmn : m ≤ n) {t : Exp} (ht : Below m t) : Below n t := by
  induction t generalizing m n with
  | var i => exact lt_of_lt_of_le ht hmn
  | const => trivial
  | fam a args ih => exact ih hmn ht
  | event => trivial
  | origin A e t ihA ihe iht => exact ⟨ihA hmn ht.1, ihe hmn ht.2.1, iht hmn ht.2.2⟩
  | stamped ρ A ih => exact ih hmn ht
  | pi q ρ A B ihA ihB => exact ⟨ihA hmn ht.1, ihB (by omega) ht.2⟩
  | sigma ρ A B ihA ihB => exact ⟨ihA hmn ht.1, ihB (by omega) ht.2⟩
  | lam q ρ A t ihA iht => exact ⟨ihA hmn ht.1, iht (by omega) ht.2⟩
  | app t u iht ihu => exact ⟨iht hmn ht.1, ihu hmn ht.2⟩
  | pair t u iht ihu => exact ⟨iht hmn ht.1, ihu hmn ht.2⟩
  | fst t ih => exact ih hmn ht
  | snd t ih => exact ih hmn ht
  | stamp t e o iht ihe iho => exact ⟨iht hmn ht.1, ihe hmn ht.2.1, iho hmn ht.2.2⟩
  | gate g ds s ihd ihs => exact ⟨ihd hmn ht.1, ihs hmn ht.2⟩
  | node g ℓ ds t e ihd iht ihe => exact ⟨ihd hmn ht.1, iht hmn ht.2.1, ihe hmn ht.2.2⟩
  | nil => trivial
  | cons t ts iht ihts => exact ⟨iht hmn ht.1, ihts hmn ht.2⟩

end Exp

end Artform.Roles.Calculus
