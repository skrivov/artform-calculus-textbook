import ArtformRoles.Calculus.Adequacy

/-!
# Records: labelled reduction, persistence and ancestry

Definition 7.1 (residual record trace) and §9.2 of the paper: Lemma 9.5
(record persistence), Lemma 9.6 (public node ancestry) and Theorem 9.7
(static–dynamic gate adequacy).

* Positions and occurrences: `Exp.children`, `Exp.at`, `Occurs`.
* Labels: `Exp.unlabel` writes `0` for every node label. Typing and reduction
  work on erased terms; a labelled term is the paper's instrumented term.
* Labelled reduction `LStep τ`: the record contraction with tag
  `Tag.record ℓ e` writes the label `ℓ` and stores the event `e`; the other
  steps have tag `Tag.plain`. Erasing labels gives reduction
  (`LStep.erase`), and every reduction of an erased term is the erasure of a
  labelled step with any chosen label (`LStep.lift`); a reduction sequence can
  be instrumented with fresh labels (`LSteps.instrument`).
* `Exp.events`: the event support. It contains the event field of every
  private node, including a node nested inside another node's event field.
* `Cross`: the residual record trace `cross↓(π, n)`.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Children, positions and occurrences -/

/-- The immediate subexpressions of an expression, in order. -/
def Exp.children : Exp → List Exp
  | var _ | const _ _ | event | nil => []
  | fam _ args => [args]
  | origin A e t => [A, e, t]
  | stamped _ A => [A]
  | pi _ _ A B => [A, B]
  | sigma _ A B => [A, B]
  | lam _ _ A t => [A, t]
  | app t u => [t, u]
  | pair t u => [t, u]
  | fst t => [t]
  | snd t => [t]
  | stamp t e o => [t, e, o]
  | gate _ ds s => [ds, s]
  | node _ _ ds t e => [ds, t, e]
  | cons t ts => [t, ts]

/-- The subexpression at a position, a list of child indices. -/
def Exp.at : Exp → List ℕ → Option Exp
  | t, [] => some t
  | t, i :: is => match t.children[i]? with
    | some c => c.at is
    | none => none

/-- `Occurs u t`: `u` occurs in `t`. -/
inductive Occurs (u : Exp) : Exp → Prop
  | refl : Occurs u u
  | child {t c : Exp} : c ∈ t.children → Occurs u c → Occurs u t

theorem Occurs.trans {u v w : Exp} (h₁ : Occurs u v) (h₂ : Occurs v w) : Occurs u w := by
  induction h₂ with
  | refl => exact h₁
  | child hc _ ih => exact .child hc ih

theorem Exp.at_occurs {t u : Exp} {pos : List ℕ} (h : t.at pos = some u) : Occurs u t := by
  induction pos generalizing t with
  | nil => cases h; exact .refl
  | cons i is ih =>
    simp only [Exp.at] at h
    split at h
    · next c hc => exact .child (List.mem_of_getElem? hc) (ih h)
    · cases h

/-! ## Erasing labels -/

/-- Erase the labels: every node gets the label `0`. -/
def Exp.unlabel : Exp → Exp
  | var i => var i
  | const i k => const i k
  | fam a args => fam a args.unlabel
  | event => event
  | origin A e t => origin A.unlabel e.unlabel t.unlabel
  | stamped σ A => stamped σ A.unlabel
  | pi q σ A B => pi q σ A.unlabel B.unlabel
  | sigma ρ A B => sigma ρ A.unlabel B.unlabel
  | lam q σ A t => lam q σ A.unlabel t.unlabel
  | app t u => app t.unlabel u.unlabel
  | pair t u => pair t.unlabel u.unlabel
  | fst t => fst t.unlabel
  | snd t => snd t.unlabel
  | stamp t e o => stamp t.unlabel e.unlabel o.unlabel
  | gate g ds s => gate g ds.unlabel s.unlabel
  | node g _ ds t e => node g 0 ds.unlabel t.unlabel e.unlabel
  | nil => nil
  | cons t ts => cons t.unlabel ts.unlabel

theorem Exp.unlabel_ren (ξ : ℕ → ℕ) (t : Exp) : (t.ren ξ).unlabel = t.unlabel.ren ξ := by
  induction t generalizing ξ <;> simp_all [Exp.ren, Exp.unlabel]

theorem Exp.unlabel_up (σ : ℕ → Exp) : Exp.unlabel ∘ up σ = up (Exp.unlabel ∘ σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [Exp.unlabel_ren]

theorem Exp.unlabel_subst (σ : ℕ → Exp) (t : Exp) :
    (t.subst σ).unlabel = t.unlabel.subst (Exp.unlabel ∘ σ) := by
  induction t generalizing σ <;> simp_all [Exp.subst, Exp.unlabel, Exp.unlabel_up]

theorem Exp.unlabel_inst (t u : Exp) : (t.inst u).unlabel = t.unlabel.inst u.unlabel := by
  rw [Exp.unlabel_subst]
  congr 1
  funext i
  cases i <;> rfl

theorem Exp.children_unlabel (t : Exp) : t.unlabel.children = t.children.map Exp.unlabel := by
  cases t <;> rfl

theorem Exp.at_unlabel (t : Exp) (pos : List ℕ) :
    t.unlabel.at pos = (t.at pos).map Exp.unlabel := by
  induction pos generalizing t with
  | nil => rfl
  | cons i is ih =>
    simp only [Exp.at, Exp.children_unlabel, List.getElem?_map]
    cases t.children[i]? with
    | none => rfl
    | some c => exact ih c

theorem Exp.unlabel_eq_node {x : Exp} {g ℓ : ℕ} {ds a e : Exp}
    (h : x.unlabel = .node g ℓ ds a e) : ∃ ℓ' ds' a' e', x = .node g ℓ' ds' a' e' := by
  cases x <;> simp only [Exp.unlabel, reduceCtorEq] at h
  case node g' ℓ' ds' a' e' =>
    obtain ⟨rfl, -⟩ := Exp.node.inj h
    exact ⟨ℓ', ds', a', e', rfl⟩

/-! ## Labelled reduction -/

/-- The tag of a labelled step: a plain step, or the record contraction that
writes the label `ℓ` and stores the event `e`. -/
inductive Tag
  | plain
  | record (ℓ : ℕ) (e : Exp)
  deriving DecidableEq

/-- The label written by a step, if any. -/
def Tag.label? : Tag → Option ℕ
  | .plain => none
  | .record ℓ _ => some ℓ

/-- The four primitive contractions, labelled (Definition 7.1). -/
inductive LContr : Tag → Exp → Exp → Prop
  | beta {q σ A t u} : LContr .plain (.app (.lam q σ A t) u) (t.inst u)
  | fstPair {t u} : LContr .plain (.fst (.pair t u)) t
  | sndPair {t u} : LContr .plain (.snd (.pair t u)) u
  | record {g ds t e o ℓ} : LContr (.record ℓ e) (.gate g ds (.stamp t e o)) (.node g ℓ ds t e)

/-- Labelled reduction: the compatible closure of the labelled contractions. -/
inductive LStep : Tag → Exp → Exp → Prop
  | contr {τ t t'} : LContr τ t t' → LStep τ t t'
  | fam {τ a args args'} : LStep τ args args' → LStep τ (.fam a args) (.fam a args')
  | origin₁ {τ A A' e t} : LStep τ A A' → LStep τ (.origin A e t) (.origin A' e t)
  | origin₂ {τ A e e' t} : LStep τ e e' → LStep τ (.origin A e t) (.origin A e' t)
  | origin₃ {τ A e t t'} : LStep τ t t' → LStep τ (.origin A e t) (.origin A e t')
  | stamped {τ σ A A'} : LStep τ A A' → LStep τ (.stamped σ A) (.stamped σ A')
  | pi₁ {τ q σ A A' B} : LStep τ A A' → LStep τ (.pi q σ A B) (.pi q σ A' B)
  | pi₂ {τ q σ A B B'} : LStep τ B B' → LStep τ (.pi q σ A B) (.pi q σ A B')
  | sigma₁ {τ ρ A A' B} : LStep τ A A' → LStep τ (.sigma ρ A B) (.sigma ρ A' B)
  | sigma₂ {τ ρ A B B'} : LStep τ B B' → LStep τ (.sigma ρ A B) (.sigma ρ A B')
  | lam₁ {τ q σ A A' t} : LStep τ A A' → LStep τ (.lam q σ A t) (.lam q σ A' t)
  | lam₂ {τ q σ A t t'} : LStep τ t t' → LStep τ (.lam q σ A t) (.lam q σ A t')
  | app₁ {τ t t' u} : LStep τ t t' → LStep τ (.app t u) (.app t' u)
  | app₂ {τ t u u'} : LStep τ u u' → LStep τ (.app t u) (.app t u')
  | pair₁ {τ t t' u} : LStep τ t t' → LStep τ (.pair t u) (.pair t' u)
  | pair₂ {τ t u u'} : LStep τ u u' → LStep τ (.pair t u) (.pair t u')
  | fst {τ t t'} : LStep τ t t' → LStep τ (.fst t) (.fst t')
  | snd {τ t t'} : LStep τ t t' → LStep τ (.snd t) (.snd t')
  | stamp₁ {τ t t' e o} : LStep τ t t' → LStep τ (.stamp t e o) (.stamp t' e o)
  | stamp₂ {τ t e e' o} : LStep τ e e' → LStep τ (.stamp t e o) (.stamp t e' o)
  | stamp₃ {τ t e o o'} : LStep τ o o' → LStep τ (.stamp t e o) (.stamp t e o')
  | gate₁ {τ g ds ds' s} : LStep τ ds ds' → LStep τ (.gate g ds s) (.gate g ds' s)
  | gate₂ {τ g ds s s'} : LStep τ s s' → LStep τ (.gate g ds s) (.gate g ds s')
  | node₁ {τ g ℓ ds ds' t e} : LStep τ ds ds' → LStep τ (.node g ℓ ds t e) (.node g ℓ ds' t e)
  | node₂ {τ g ℓ ds t t' e} : LStep τ t t' → LStep τ (.node g ℓ ds t e) (.node g ℓ ds t' e)
  | node₃ {τ g ℓ ds t e e'} : LStep τ e e' → LStep τ (.node g ℓ ds t e) (.node g ℓ ds t e')
  | cons₁ {τ t t' ts} : LStep τ t t' → LStep τ (.cons t ts) (.cons t' ts)
  | cons₂ {τ t ts ts'} : LStep τ ts ts' → LStep τ (.cons t ts) (.cons t ts')

/-- Labelled reduction in any number of steps, with its tags in order. -/
inductive LSteps : List Tag → Exp → Exp → Prop
  | refl {t} : LSteps [] t t
  | tail {τs τ t u v} : LSteps τs t u → LStep τ u v → LSteps (τs ++ [τ]) t v

/-- Labelled reduction in any number of steps, tags forgotten. -/
abbrev LReds : Exp → Exp → Prop := Relation.ReflTransGen (fun u v => ∃ τ, LStep τ u v)

theorem LSteps.lreds {τs : List Tag} {t u : Exp} (h : LSteps τs t u) : LReds t u := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact .tail ih ⟨_, hs⟩

/-- Labelled reduction erases to reduction. -/
theorem LStep.erase {τ : Tag} {t t' : Exp} (h : LStep τ t t') : Step t.unlabel t'.unlabel := by
  induction h with
  | contr hc =>
    cases hc with
    | beta => simp only [Exp.unlabel, Exp.unlabel_inst]; exact .beta
    | fstPair => exact .fstPair
    | sndPair => exact .sndPair
    | record => exact .record
  | fam _ ih => exact .fam ih
  | origin₁ _ ih => exact .origin₁ ih
  | origin₂ _ ih => exact .origin₂ ih
  | origin₃ _ ih => exact .origin₃ ih
  | stamped _ ih => exact .stamped ih
  | pi₁ _ ih => exact .pi₁ ih
  | pi₂ _ ih => exact .pi₂ ih
  | sigma₁ _ ih => exact .sigma₁ ih
  | sigma₂ _ ih => exact .sigma₂ ih
  | lam₁ _ ih => exact .lam₁ ih
  | lam₂ _ ih => exact .lam₂ ih
  | app₁ _ ih => exact .app₁ ih
  | app₂ _ ih => exact .app₂ ih
  | pair₁ _ ih => exact .pair₁ ih
  | pair₂ _ ih => exact .pair₂ ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | stamp₁ _ ih => exact .stamp₁ ih
  | stamp₂ _ ih => exact .stamp₂ ih
  | stamp₃ _ ih => exact .stamp₃ ih
  | gate₁ _ ih => exact .gate₁ ih
  | gate₂ _ ih => exact .gate₂ ih
  | node₁ _ ih => exact .node₁ ih
  | node₂ _ ih => exact .node₂ ih
  | node₃ _ ih => exact .node₃ ih
  | cons₁ _ ih => exact .cons₁ ih
  | cons₂ _ ih => exact .cons₂ ih

theorem LReds.erase {t t' : Exp} (h : LReds t t') : Steps t.unlabel t'.unlabel := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨τ, hs⟩ := hs; exact .tail ih hs.erase

/-- A reduction step is a labelled step whose record contractions write `0`. -/
theorem Step.lstep {t t' : Exp} (h : Step t t') : ∃ τ, LStep τ t t' := by
  induction h with
  | beta => exact ⟨_, .contr .beta⟩
  | fstPair => exact ⟨_, .contr .fstPair⟩
  | sndPair => exact ⟨_, .contr .sndPair⟩
  | record => exact ⟨_, .contr .record⟩
  | fam _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .fam h⟩
  | origin₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .origin₁ h⟩
  | origin₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .origin₂ h⟩
  | origin₃ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .origin₃ h⟩
  | stamped _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .stamped h⟩
  | pi₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .pi₁ h⟩
  | pi₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .pi₂ h⟩
  | sigma₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .sigma₁ h⟩
  | sigma₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .sigma₂ h⟩
  | lam₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .lam₁ h⟩
  | lam₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .lam₂ h⟩
  | app₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .app₁ h⟩
  | app₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .app₂ h⟩
  | pair₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .pair₁ h⟩
  | pair₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .pair₂ h⟩
  | fst _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .fst h⟩
  | snd _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .snd h⟩
  | stamp₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .stamp₁ h⟩
  | stamp₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .stamp₂ h⟩
  | stamp₃ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .stamp₃ h⟩
  | gate₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .gate₁ h⟩
  | gate₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .gate₂ h⟩
  | node₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .node₁ h⟩
  | node₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .node₂ h⟩
  | node₃ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .node₃ h⟩
  | cons₁ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .cons₁ h⟩
  | cons₂ _ ih => obtain ⟨τ, h⟩ := ih; exact ⟨τ, .cons₂ h⟩

/-- A labelled step has an unlabelled counterpart from the same term. -/
theorem LStep.step {τ : Tag} {t t' : Exp} (h : LStep τ t t') : ∃ t'', Step t t'' := by
  induction h with
  | contr hc =>
    cases hc with
    | beta => exact ⟨_, .beta⟩
    | fstPair => exact ⟨_, .fstPair⟩
    | sndPair => exact ⟨_, .sndPair⟩
    | record => exact ⟨_, .record⟩
  | fam _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .fam h⟩
  | origin₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .origin₁ h⟩
  | origin₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .origin₂ h⟩
  | origin₃ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .origin₃ h⟩
  | stamped _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .stamped h⟩
  | pi₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .pi₁ h⟩
  | pi₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .pi₂ h⟩
  | sigma₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .sigma₁ h⟩
  | sigma₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .sigma₂ h⟩
  | lam₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .lam₁ h⟩
  | lam₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .lam₂ h⟩
  | app₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .app₁ h⟩
  | app₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .app₂ h⟩
  | pair₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .pair₁ h⟩
  | pair₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .pair₂ h⟩
  | fst _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .fst h⟩
  | snd _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .snd h⟩
  | stamp₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .stamp₁ h⟩
  | stamp₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .stamp₂ h⟩
  | stamp₃ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .stamp₃ h⟩
  | gate₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .gate₁ h⟩
  | gate₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .gate₂ h⟩
  | node₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .node₁ h⟩
  | node₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .node₂ h⟩
  | node₃ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .node₃ h⟩
  | cons₁ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .cons₁ h⟩
  | cons₂ _ ih => obtain ⟨_, h⟩ := ih; exact ⟨_, .cons₂ h⟩

/-- A normal term has no labelled step. -/
theorem Normal.no_lstep {t : Exp} (h : Normal t) {τ : Tag} {t' : Exp} : ¬LStep τ t t' :=
  fun hs => let ⟨_, h'⟩ := hs.step; h _ h'


/-! ## Instrumenting reduction with labels -/

/-- Every reduction step of an erased term is the erasure of a labelled step;
its record contraction, if any, writes the chosen label `ℓ`. -/
theorem LStep.lift (ℓ : ℕ) : ∀ (t : Exp) {s : Exp}, Step t.unlabel s →
    ∃ τ t', LStep τ t t' ∧ t'.unlabel = s ∧ (τ = .plain ∨ ∃ e, τ = .record ℓ e) := by
  intro t
  induction t with
  | var => intro s h; cases h
  | const => intro s h; cases h
  | event => intro s h; cases h
  | nil => intro s h; cases h
  | fam a args ih =>
    intro s h
    cases h with
    | fam hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ih hs
      exact ⟨τ, _, .fam h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | origin A e t ihA ihe iht =>
    intro s h
    cases h with
    | origin₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihA hs
      exact ⟨τ, _, .origin₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | origin₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihe hs
      exact ⟨τ, _, .origin₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | origin₃ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iht hs
      exact ⟨τ, _, .origin₃ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | stamped σ A ih =>
    intro s h
    cases h with
    | stamped hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ih hs
      exact ⟨τ, _, .stamped h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | pi q σ A B ihA ihB =>
    intro s h
    cases h with
    | pi₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihA hs
      exact ⟨τ, _, .pi₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | pi₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihB hs
      exact ⟨τ, _, .pi₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | sigma ρ A B ihA ihB =>
    intro s h
    cases h with
    | sigma₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihA hs
      exact ⟨τ, _, .sigma₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | sigma₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihB hs
      exact ⟨τ, _, .sigma₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | lam q σ A b ihA ihb =>
    intro s h
    cases h with
    | lam₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihA hs
      exact ⟨τ, _, .lam₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | lam₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihb hs
      exact ⟨τ, _, .lam₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | app f u ihf ihu =>
    intro s h
    simp only [Exp.unlabel] at h
    generalize hf : f.unlabel = f₀ at h
    cases h with
    | beta =>
      cases f with
      | lam q σ A b =>
        simp only [Exp.unlabel, Exp.lam.injEq] at hf
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
        exact ⟨.plain, b.inst u, .contr .beta, Exp.unlabel_inst b u, .inl rfl⟩
      | _ => simp [Exp.unlabel] at hf
    | app₁ hs =>
      subst hf
      obtain ⟨τ, f', h₁, h₂, h₃⟩ := ihf hs
      exact ⟨τ, .app f' u, .app₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | app₂ hs =>
      subst hf
      obtain ⟨τ, u', h₁, h₂, h₃⟩ := ihu hs
      exact ⟨τ, .app f u', .app₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | pair a b iha ihb =>
    intro s h
    cases h with
    | pair₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iha hs
      exact ⟨τ, _, .pair₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | pair₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihb hs
      exact ⟨τ, _, .pair₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | fst p ih =>
    intro s h
    simp only [Exp.unlabel] at h
    generalize hp : p.unlabel = p₀ at h
    cases h with
    | fstPair =>
      cases p with
      | pair a b =>
        simp only [Exp.unlabel, Exp.pair.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨.plain, a, .contr .fstPair, rfl, .inl rfl⟩
      | _ => simp [Exp.unlabel] at hp
    | fst hs =>
      subst hp
      obtain ⟨τ, p', h₁, h₂, h₃⟩ := ih hs
      exact ⟨τ, .fst p', .fst h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | snd p ih =>
    intro s h
    simp only [Exp.unlabel] at h
    generalize hp : p.unlabel = p₀ at h
    cases h with
    | sndPair =>
      cases p with
      | pair a b =>
        simp only [Exp.unlabel, Exp.pair.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨.plain, b, .contr .sndPair, rfl, .inl rfl⟩
      | _ => simp [Exp.unlabel] at hp
    | snd hs =>
      subst hp
      obtain ⟨τ, p', h₁, h₂, h₃⟩ := ih hs
      exact ⟨τ, .snd p', .snd h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | stamp a e o iha ihe iho =>
    intro s h
    cases h with
    | stamp₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iha hs
      exact ⟨τ, _, .stamp₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | stamp₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihe hs
      exact ⟨τ, _, .stamp₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | stamp₃ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iho hs
      exact ⟨τ, _, .stamp₃ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | gate g ds c ihds ihc =>
    intro s h
    simp only [Exp.unlabel] at h
    generalize hc : c.unlabel = c₀ at h
    cases h with
    | record =>
      cases c with
      | stamp a e o =>
        simp only [Exp.unlabel, Exp.stamp.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact ⟨.record ℓ e, .node g ℓ ds a e, .contr .record, rfl, .inr ⟨e, rfl⟩⟩
      | _ => simp [Exp.unlabel] at hc
    | gate₁ hs =>
      subst hc
      obtain ⟨τ, ds', h₁, h₂, h₃⟩ := ihds hs
      exact ⟨τ, .gate g ds' c, .gate₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | gate₂ hs =>
      subst hc
      obtain ⟨τ, c', h₁, h₂, h₃⟩ := ihc hs
      exact ⟨τ, .gate g ds c', .gate₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | node g ℓ' ds a e ihds iha ihe =>
    intro s h
    cases h with
    | node₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihds hs
      exact ⟨τ, _, .node₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | node₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iha hs
      exact ⟨τ, _, .node₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | node₃ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihe hs
      exact ⟨τ, _, .node₃ h₁, by simp [Exp.unlabel, h₂], h₃⟩
  | cons a as iha ihas =>
    intro s h
    cases h with
    | cons₁ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := iha hs
      exact ⟨τ, _, .cons₁ h₁, by simp [Exp.unlabel, h₂], h₃⟩
    | cons₂ hs =>
      obtain ⟨τ, t', h₁, h₂, h₃⟩ := ihas hs
      exact ⟨τ, _, .cons₂ h₁, by simp [Exp.unlabel, h₂], h₃⟩

theorem Normal.unlabel_iff {t : Exp} : Normal t.unlabel ↔ Normal t := by
  constructor
  · intro h t' hs
    obtain ⟨τ, hs'⟩ := hs.lstep
    exact h _ hs'.erase
  · intro h s hs
    obtain ⟨τ, t', h₁, -, -⟩ := LStep.lift 0 t hs
    exact h.no_lstep h₁


/-! ## Occurrences under renaming and substitution -/

theorem Exp.sizeOf_lt_of_mem_children {t c : Exp} (h : c ∈ t.children) :
    sizeOf c < sizeOf t := by
  cases t <;> simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
    (try rcases h with rfl | rfl | rfl) <;> simp <;> omega

/-- Induction over expressions through their children. -/
theorem Exp.childInduction {P : Exp → Prop} (h : ∀ t, (∀ c ∈ t.children, P c) → P t) :
    ∀ t, P t := by
  intro t
  induction hn : sizeOf t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    exact h t fun c hc => ih _ (hn ▸ Exp.sizeOf_lt_of_mem_children hc) c rfl

theorem Occurs.inv {u t : Exp} (h : Occurs u t) : u = t ∨ ∃ c ∈ t.children, Occurs u c := by
  cases h with
  | refl => exact .inl rfl
  | child hc h' => exact .inr ⟨_, hc, h'⟩

/-- A node of the gate `g` with label `ℓ` and event field `e` occurs in `t`. -/
def HasNode (g ℓ : ℕ) (e t : Exp) : Prop := ∃ ds a, Occurs (.node g ℓ ds a e) t

theorem HasNode.child {g ℓ : ℕ} {e t c : Exp} (hc : c ∈ t.children) (h : HasNode g ℓ e c) :
    HasNode g ℓ e t :=
  let ⟨ds, a, h⟩ := h; ⟨ds, a, .child hc h⟩

theorem HasNode.trans {g ℓ : ℕ} {e t u : Exp} (h : HasNode g ℓ e t) (ht : Occurs t u) :
    HasNode g ℓ e u :=
  let ⟨ds, a, h⟩ := h; ⟨ds, a, h.trans ht⟩

theorem HasNode.inv {g ℓ : ℕ} {e t : Exp} (h : HasNode g ℓ e t) :
    (∃ ds a, t = .node g ℓ ds a e) ∨ ∃ c ∈ t.children, HasNode g ℓ e c := by
  obtain ⟨ds, a, h⟩ := h
  rcases h.inv with h | ⟨c, hc, h⟩
  · exact .inl ⟨ds, a, h.symm⟩
  · exact .inr ⟨c, hc, ds, a, h⟩

theorem HasNode.not_var {g ℓ i : ℕ} {e : Exp} : ¬HasNode g ℓ e (.var i) := by
  intro h
  rcases h.inv with ⟨_, _, h⟩ | ⟨c, hc, _⟩
  · cases h
  · cases hc

theorem Exp.mem_children_ren {t c' : Exp} {ξ : ℕ → ℕ} (h : c' ∈ (t.ren ξ).children) :
    ∃ c ∈ t.children, ∃ ξ', c' = c.ren ξ' := by
  cases t <;> simp only [Exp.ren, Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
    rcases h with rfl | rfl | rfl <;> exact ⟨_, by simp [Exp.children], _, rfl⟩

theorem Exp.mem_children_subst {t c' : Exp} {σ : ℕ → Exp} (ht : ∀ i, t ≠ .var i)
    (h : c' ∈ (t.subst σ).children) : ∃ c ∈ t.children, c' = c.subst σ ∨ c' = c.subst (up σ) := by
  cases t with
  | var i => exact absurd rfl (ht i)
  | _ =>
    simp only [Exp.subst, Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at h
    all_goals rcases h with rfl | rfl | rfl <;> first
        | exact ⟨_, by simp [Exp.children], .inl rfl⟩
        | exact ⟨_, by simp [Exp.children], .inr rfl⟩

theorem Exp.ren_eq_node {t : Exp} {ξ : ℕ → ℕ} {g ℓ : ℕ} {ds a e : Exp}
    (h : t.ren ξ = .node g ℓ ds a e) : ∃ ds₀ a₀ e₀, t = .node g ℓ ds₀ a₀ e₀ ∧ e = e₀.ren ξ := by
  cases t <;> simp only [Exp.ren, reduceCtorEq] at h
  case node g' ℓ' ds' a' e' =>
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, rfl⟩ := h
    exact ⟨ds', a', e', rfl, rfl⟩

theorem Exp.subst_eq_node {t : Exp} {σ : ℕ → Exp} {g ℓ : ℕ} {ds a e : Exp}
    (h : t.subst σ = .node g ℓ ds a e) :
    (∃ i, t = .var i) ∨ ∃ ds₀ a₀ e₀, t = .node g ℓ ds₀ a₀ e₀ ∧ e = e₀.subst σ := by
  cases t <;> simp only [Exp.subst, reduceCtorEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case node g' ℓ' ds' a' e' =>
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, rfl⟩ := h
    exact .inr ⟨ds', a', e', rfl, rfl⟩

/-- A node of a renamed expression is a renamed node of the expression. -/
theorem HasNode.of_ren {g ℓ : ℕ} : ∀ (t : Exp) {ξ : ℕ → ℕ} {e : Exp},
    HasNode g ℓ e (t.ren ξ) → ∃ e₀, HasNode g ℓ e₀ t ∧ ∃ ξ', e = e₀.ren ξ' := by
  refine Exp.childInduction fun t ih ξ e h => ?_
  rcases h.inv with ⟨ds, a, heq⟩ | ⟨c', hc', h⟩
  · obtain ⟨ds₀, a₀, e₀, rfl, rfl⟩ := Exp.ren_eq_node heq
    exact ⟨e₀, ⟨ds₀, a₀, .refl⟩, ξ, rfl⟩
  · obtain ⟨c, hc, ξ', rfl⟩ := Exp.mem_children_ren hc'
    obtain ⟨e₀, h₀, ξ'', rfl⟩ := ih c hc h
    exact ⟨e₀, h₀.child hc, ξ'', rfl⟩

/-- A node of a substituted expression is a substituted node of the expression,
or a renamed node of one of the substituted terms. -/
theorem HasNode.of_subst {g ℓ : ℕ} : ∀ (t : Exp) {σ : ℕ → Exp} {e : Exp},
    HasNode g ℓ e (t.subst σ) →
      (∃ e₀, HasNode g ℓ e₀ t ∧ ∃ σ', e = e₀.subst σ') ∨
      (∃ i e₀, HasNode g ℓ e₀ (σ i) ∧ ∃ σ', e = e₀.subst σ') := by
  refine Exp.childInduction fun t ih σ e h => ?_
  by_cases hv : ∃ i, t = .var i
  · obtain ⟨i, rfl⟩ := hv
    exact .inr ⟨i, e, h, var, (Exp.subst_var e).symm⟩
  have hv' : ∀ i, t ≠ .var i := fun i h' => hv ⟨i, h'⟩
  rcases h.inv with ⟨ds, a, heq⟩ | ⟨c', hc', h⟩
  · rcases Exp.subst_eq_node heq with ⟨i, rfl⟩ | ⟨ds₀, a₀, e₀, rfl, rfl⟩
    · exact absurd rfl (hv' i)
    · exact .inl ⟨e₀, ⟨ds₀, a₀, .refl⟩, σ, rfl⟩
  · obtain ⟨c, hc, rfl | rfl⟩ := Exp.mem_children_subst hv' hc'
    · rcases ih c hc h with ⟨e₀, h₀, σ', rfl⟩ | ⟨i, e₀, h₀, σ', rfl⟩
      · exact .inl ⟨e₀, h₀.child hc, σ', rfl⟩
      · exact .inr ⟨i, e₀, h₀, σ', rfl⟩
    · rcases ih c hc h with ⟨e₀, h₀, σ', rfl⟩ | ⟨i, e₀, h₀, σ', rfl⟩
      · exact .inl ⟨e₀, h₀.child hc, σ', rfl⟩
      · cases i with
        | zero => exact absurd h₀ HasNode.not_var
        | succ j =>
          obtain ⟨e₁, h₁, ξ, rfl⟩ := HasNode.of_ren (σ j) h₀
          exact .inr ⟨j, e₁, h₁, _, Exp.subst_ren σ' ξ e₁⟩


/-! ## Labelled steps under substitution -/

theorem LStep.subst {τ : Tag} {t t' : Exp} (h : LStep τ t t') (σ : ℕ → Exp) :
    ∃ τ', LStep τ' (t.subst σ) (t'.subst σ) := by
  induction h generalizing σ with
  | contr hc =>
    cases hc with
    | beta => rw [Exp.subst_inst]; exact ⟨_, .contr .beta⟩
    | fstPair => exact ⟨_, .contr .fstPair⟩
    | sndPair => exact ⟨_, .contr .sndPair⟩
    | record => exact ⟨_, .contr .record⟩
  | fam _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .fam h⟩
  | origin₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .origin₁ h⟩
  | origin₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .origin₂ h⟩
  | origin₃ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .origin₃ h⟩
  | stamped _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .stamped h⟩
  | pi₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .pi₁ h⟩
  | pi₂ _ ih => obtain ⟨τ', h⟩ := ih (up σ); exact ⟨τ', .pi₂ h⟩
  | sigma₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .sigma₁ h⟩
  | sigma₂ _ ih => obtain ⟨τ', h⟩ := ih (up σ); exact ⟨τ', .sigma₂ h⟩
  | lam₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .lam₁ h⟩
  | lam₂ _ ih => obtain ⟨τ', h⟩ := ih (up σ); exact ⟨τ', .lam₂ h⟩
  | app₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .app₁ h⟩
  | app₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .app₂ h⟩
  | pair₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .pair₁ h⟩
  | pair₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .pair₂ h⟩
  | fst _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .fst h⟩
  | snd _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .snd h⟩
  | stamp₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .stamp₁ h⟩
  | stamp₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .stamp₂ h⟩
  | stamp₃ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .stamp₃ h⟩
  | gate₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .gate₁ h⟩
  | gate₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .gate₂ h⟩
  | node₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .node₁ h⟩
  | node₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .node₂ h⟩
  | node₃ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .node₃ h⟩
  | cons₁ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .cons₁ h⟩
  | cons₂ _ ih => obtain ⟨τ', h⟩ := ih σ; exact ⟨τ', .cons₂ h⟩

theorem LReds.subst {t t' : Exp} (h : LReds t t') (σ : ℕ → Exp) :
    LReds (t.subst σ) (t'.subst σ) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨τ, hs⟩ := hs; exact .tail ih (hs.subst σ)

/-- `e'` comes from `e` by a substitution followed by labelled reduction: the
reductions and substitutions that a node's event field undergoes along its
residuals (Lemma 9.5). -/
def EvDesc (e e' : Exp) : Prop := ∃ σ, LReds (e.subst σ) e'

theorem EvDesc.refl (e : Exp) : EvDesc e e := ⟨var, by rw [Exp.subst_var]⟩

theorem EvDesc.of_subst (e : Exp) (σ : ℕ → Exp) : EvDesc e (e.subst σ) := ⟨σ, .refl⟩

theorem EvDesc.of_lstep {τ : Tag} {e e' : Exp} (h : LStep τ e e') : EvDesc e e' :=
  ⟨var, by rw [Exp.subst_var]; exact .single ⟨τ, h⟩⟩

theorem EvDesc.trans {e₁ e₂ e₃ : Exp} (h₁ : EvDesc e₁ e₂) (h₂ : EvDesc e₂ e₃) : EvDesc e₁ e₃ := by
  obtain ⟨σ₁, h₁⟩ := h₁
  obtain ⟨σ₂, h₂⟩ := h₂
  refine ⟨Exp.subst σ₂ ∘ σ₁, ?_⟩
  rw [← Exp.subst_subst]
  exact (h₁.subst σ₂).trans h₂

/-- A closed event is reached by labelled reduction alone. -/
theorem EvDesc.closed {e e' : Exp} (h : EvDesc e e') (he : e.Closed) : LReds e e' := by
  obtain ⟨σ, h⟩ := h
  rwa [Exp.subst_closed he] at h

/-! ## Residuals of nodes -/

theorem residual_congr {τ : Tag} {u u' x x' : Exp} (hx : x ∈ u.children)
    (hchild : ∀ c ∈ u'.children, c = x' ∨ c ∈ u.children)
    (hself : ∀ g ℓ ds a e', u' = .node g ℓ ds a e' → ∃ e₀, HasNode g ℓ e₀ u ∧ EvDesc e₀ e')
    (ih : ∀ {g ℓ e'}, HasNode g ℓ e' x' →
      (∃ e₀, HasNode g ℓ e₀ x ∧ EvDesc e₀ e') ∨ τ = .record ℓ e')
    {g ℓ : ℕ} {e' : Exp} (hn : HasNode g ℓ e' u') :
    (∃ e₀, HasNode g ℓ e₀ u ∧ EvDesc e₀ e') ∨ τ = .record ℓ e' := by
  rcases hn.inv with ⟨ds, a, heq⟩ | ⟨c, hc, h⟩
  · exact .inl (hself g ℓ ds a e' heq)
  · rcases hchild c hc with rfl | hc'
    · rcases ih h with ⟨e₀, h₀, hd⟩ | h
      · exact .inl ⟨e₀, h₀.child hx, hd⟩
      · exact .inr h
    · exact .inl ⟨e', h.child hc', .refl e'⟩

/-- Every node after a labelled step is a residual of a node before it, its
event field obtained by substitution and reduction, or the node written by the
step's record contraction. -/
theorem LStep.residual {τ : Tag} {u u' : Exp} (h : LStep τ u u') :
    ∀ {g ℓ : ℕ} {e' : Exp}, HasNode g ℓ e' u' →
      (∃ e₀, HasNode g ℓ e₀ u ∧ EvDesc e₀ e') ∨ τ = .record ℓ e' := by
  induction h with
  | contr hc =>
    intro g ℓ e' hn
    cases hc with
    | @beta q σ A b w =>
      rcases HasNode.of_subst b hn with ⟨e₀, h₀, σ', rfl⟩ | ⟨i, e₀, h₀, σ', rfl⟩
      · exact .inl ⟨e₀, (h₀.child (t := .lam q σ A b) (by simp [Exp.children])).child
          (by simp [Exp.children]), .of_subst _ _⟩
      · cases i with
        | zero => exact .inl ⟨e₀, h₀.child (by simp [Exp.children]), .of_subst _ _⟩
        | succ j => exact absurd h₀ HasNode.not_var
    | fstPair =>
      refine .inl ⟨e', ?_, .refl _⟩
      refine HasNode.child (List.mem_singleton.mpr rfl) ?_
      exact HasNode.child (List.mem_cons_self ..) hn
    | sndPair =>
      refine .inl ⟨e', ?_, .refl _⟩
      refine HasNode.child (List.mem_singleton.mpr rfl) ?_
      exact HasNode.child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hn
    | record =>
      rcases hn.inv with ⟨ds₁, a₁, heq⟩ | ⟨c, hc, h⟩
      · simp only [Exp.node.injEq] at heq
        obtain ⟨-, rfl, -, -, rfl⟩ := heq
        exact .inr rfl
      · refine .inl ⟨e', ?_, .refl _⟩
        simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact HasNode.child (List.mem_cons_self ..) h
        · refine HasNode.child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_
          exact HasNode.child (List.mem_cons_self ..) h
        · refine HasNode.child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_
          exact HasNode.child (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h
  | fam _ ih | origin₁ _ ih | origin₂ _ ih | origin₃ _ ih | stamped _ ih | pi₁ _ ih | pi₂ _ ih
    | sigma₁ _ ih | sigma₂ _ ih | lam₁ _ ih | lam₂ _ ih | app₁ _ ih | app₂ _ ih | pair₁ _ ih
    | pair₂ _ ih | fst _ ih | snd _ ih | stamp₁ _ ih | stamp₂ _ ih | stamp₃ _ ih | gate₁ _ ih
    | gate₂ _ ih | cons₁ _ ih | cons₂ _ ih =>
    intro g ℓ e' hn
    exact residual_congr (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto)
      (fun _ _ _ _ _ h => by cases h) ih hn
  | @node₁ g₁ ℓ₁ ds ds' a e _ ih =>
    intro g ℓ e' hn
    refine residual_congr (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto) ?_ ih hn
    intro g' ℓ' ds₁ a₁ e₁ h
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, rfl⟩ := h
    exact ⟨e, ⟨ds, a, .refl⟩, .refl _⟩
  | @node₂ g₁ ℓ₁ ds a a' e _ ih =>
    intro g ℓ e' hn
    refine residual_congr (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto) ?_ ih hn
    intro g' ℓ' ds₁ a₁ e₁ h
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, rfl⟩ := h
    exact ⟨e, ⟨ds, a, .refl⟩, .refl _⟩
  | @node₃ g₁ ℓ₁ ds a e e₂ hs ih =>
    intro g ℓ e' hn
    refine residual_congr (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto) ?_ ih hn
    intro g' ℓ' ds₁ a₁ e₁ h
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, rfl⟩ := h
    exact ⟨e, ⟨ds, a, .refl⟩, .of_lstep hs⟩

/-- Every node at the end of a labelled reduction sequence descends from a node
of its start or from a record contraction of the sequence. -/
theorem LSteps.residual {τs : List Tag} {t n : Exp} (h : LSteps τs t n) :
    ∀ {g ℓ : ℕ} {e' : Exp}, HasNode g ℓ e' n →
      (∃ e₀, HasNode g ℓ e₀ t ∧ EvDesc e₀ e') ∨ ∃ e₀, Tag.record ℓ e₀ ∈ τs ∧ EvDesc e₀ e' := by
  induction h with
  | refl => intro g ℓ e' hn; exact .inl ⟨e', hn, .refl _⟩
  | tail _ hs ih =>
    intro g ℓ e' hn
    rcases hs.residual hn with ⟨e₁, h₁, hd₁⟩ | rfl
    · rcases ih h₁ with ⟨e₀, h₀, hd₀⟩ | ⟨e₀, h₀, hd₀⟩
      · exact .inl ⟨e₀, h₀, hd₀.trans hd₁⟩
      · exact .inr ⟨e₀, List.mem_append_left _ h₀, hd₀.trans hd₁⟩
    · exact .inr ⟨e', List.mem_append_right _ (List.mem_singleton_self _), .refl _⟩

/-! ## Public terms -/

theorem Exp.IsPublic.child {t c : Exp} (ht : t.IsPublic) (hc : c ∈ t.children) : c.IsPublic := by
  cases t <;> simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
    (try rcases hc with rfl | rfl | rfl) <;> simp_all [Exp.IsPublic]

theorem Exp.IsPublic.not_hasNode {g ℓ : ℕ} {e : Exp} :
    ∀ t : Exp, t.IsPublic → ¬HasNode g ℓ e t := by
  refine Exp.childInduction fun t ih ht hn => ?_
  rcases hn.inv with ⟨ds, a, rfl⟩ | ⟨c, hc, h⟩
  · exact ht
  · exact ih c hc (ht.child hc) h

theorem Exp.IsPublic.unlabel_eq {t : Exp} (ht : t.IsPublic) : t.unlabel = t := by
  induction t with
  | node => exact ht.elim
  | _ => simp_all [Exp.IsPublic, Exp.unlabel]

/-- **Lemma 9.6** (public node ancestry). Every private node at the end of a
labelled reduction sequence from a public term is a residual of a record
contraction of the sequence: its label is written by a record step, and its
event field comes from that step's stored event by substitution and
reduction. -/
theorem node_ancestry {τs : List Tag} {t n : Exp} (hpub : t.IsPublic) (h : LSteps τs t n)
    {g ℓ : ℕ} {e' : Exp} (hn : HasNode g ℓ e' n) :
    ∃ e₀, Tag.record ℓ e₀ ∈ τs ∧ EvDesc e₀ e' := by
  rcases h.residual hn with ⟨e₀, h₀, -⟩ | h
  · exact absurd h₀ (hpub.not_hasNode t)
  · exact h


/-! ## Normal subterms and unique normal forms -/

/-- A step of a child is a step of its parent. -/
theorem Step.of_child {t c c' : Exp} (hc : c ∈ t.children) (h : Step c c') :
    ∃ t', Step t t' := by
  cases t <;> simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
    (try rcases hc with rfl | rfl | rfl) <;>
    first
    | exact ⟨_, .fam h⟩ | exact ⟨_, .origin₁ h⟩ | exact ⟨_, .origin₂ h⟩ | exact ⟨_, .origin₃ h⟩
    | exact ⟨_, .stamped h⟩ | exact ⟨_, .pi₁ h⟩ | exact ⟨_, .pi₂ h⟩ | exact ⟨_, .sigma₁ h⟩
    | exact ⟨_, .sigma₂ h⟩ | exact ⟨_, .lam₁ h⟩ | exact ⟨_, .lam₂ h⟩ | exact ⟨_, .app₁ h⟩
    | exact ⟨_, .app₂ h⟩ | exact ⟨_, .pair₁ h⟩ | exact ⟨_, .pair₂ h⟩ | exact ⟨_, .fst h⟩
    | exact ⟨_, .snd h⟩ | exact ⟨_, .stamp₁ h⟩ | exact ⟨_, .stamp₂ h⟩ | exact ⟨_, .stamp₃ h⟩
    | exact ⟨_, .gate₁ h⟩ | exact ⟨_, .gate₂ h⟩ | exact ⟨_, .node₁ h⟩ | exact ⟨_, .node₂ h⟩
    | exact ⟨_, .node₃ h⟩ | exact ⟨_, .cons₁ h⟩ | exact ⟨_, .cons₂ h⟩

/-- Every subexpression of a normal expression is normal. -/
theorem Normal.of_occurs {t u : Exp} (ht : Normal t) (h : Occurs u t) : Normal u := by
  revert ht
  induction h with
  | refl => exact id
  | child hc _ ih =>
    intro ht
    exact ih fun c' hs => let ⟨_, h'⟩ := Step.of_child hc hs; ht _ h'

theorem Normal.eq_of_steps {b d : Exp} (hb : Normal b) (h : Steps b d) : b = d := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨_, hs, _⟩
  · exact h
  · exact absurd hs (hb _)

/-- An expression has at most one normal form. -/
theorem Steps.normal_unique {a b c : Exp} (hb : Steps a b) (hc : Steps a c) (nb : Normal b)
    (nc : Normal c) : b = c := by
  obtain ⟨d, h₁, h₂⟩ := Steps.confluent hb hc
  rw [nb.eq_of_steps h₁, nc.eq_of_steps h₂]

/-! ## Event support and the residual record trace -/

/-- The event support `events(n)` (§7.2): the event field of every private node.
It also collects the events of nodes nested inside an event field. -/
def Exp.events : Exp → List Exp
  | var _ | const _ _ | event | nil => []
  | fam _ args => args.events
  | stamped _ A | fst A | snd A => A.events
  | origin A e t | stamp A e t => A.events ++ e.events ++ t.events
  | pi _ _ A B | sigma _ A B | lam _ _ A B | app A B | pair A B | cons A B | gate _ A B =>
    A.events ++ B.events
  | node _ _ ds t e => e :: (ds.events ++ t.events ++ e.events)

theorem Exp.events_of_child {t c : Exp} (hc : c ∈ t.children) {x : Exp} (hx : x ∈ c.events) :
    x ∈ t.events := by
  cases t <;> simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
    (try rcases hc with rfl | rfl | rfl) <;> simp [Exp.events, hx]

/-- The event of every node of `t` is in the event support of `t`. -/
theorem HasNode.mem_events {g ℓ : ℕ} {e : Exp} : ∀ t : Exp, HasNode g ℓ e t → e ∈ t.events := by
  refine Exp.childInduction fun t ih hn => ?_
  rcases hn.inv with ⟨ds, a, rfl⟩ | ⟨c, hc, h⟩
  · simp [Exp.events]
  · exact Exp.events_of_child hc (ih c hc h)

/-- The event support is exactly the event fields of the nodes. -/
theorem Exp.mem_events_iff {t x : Exp} : x ∈ t.events ↔ ∃ g ℓ, HasNode g ℓ x t := by
  refine ⟨fun h => ?_, fun ⟨g, ℓ, h⟩ => h.mem_events t⟩
  induction t with
  | var | const | event | nil => simp [Exp.events] at h
  | fam a args ih =>
    obtain ⟨g, ℓ, h'⟩ := ih h
    exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
  | node g ℓ ds a e ihds iha ihe =>
    simp only [Exp.events, List.mem_cons, List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · exact ⟨g, ℓ, ds, a, .refl⟩
    · obtain ⟨g', ℓ', h'⟩ := ihds h; exact ⟨g', ℓ', h'.child (by simp [Exp.children])⟩
    · obtain ⟨g', ℓ', h'⟩ := iha h; exact ⟨g', ℓ', h'.child (by simp [Exp.children])⟩
    · obtain ⟨g', ℓ', h'⟩ := ihe h; exact ⟨g', ℓ', h'.child (by simp [Exp.children])⟩
  | stamped _ A ih | fst A ih | snd A ih =>
    obtain ⟨g, ℓ, h'⟩ := ih h
    exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
  | origin A e t ihA ihe iht | stamp A e t ihA ihe iht =>
    simp only [Exp.events, List.mem_append] at h
    rcases h with (h | h) | h
    · obtain ⟨g, ℓ, h'⟩ := ihA h; exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
    · obtain ⟨g, ℓ, h'⟩ := ihe h; exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
    · obtain ⟨g, ℓ, h'⟩ := iht h; exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
  | pi _ _ A B ihA ihB | sigma _ A B ihA ihB | lam _ _ A B ihA ihB | app A B ihA ihB
    | pair A B ihA ihB | cons A B ihA ihB | gate _ A B ihA ihB =>
    simp only [Exp.events, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨g, ℓ, h'⟩ := ihA h; exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩
    · obtain ⟨g, ℓ, h'⟩ := ihB h; exact ⟨g, ℓ, h'.child (by simp [Exp.children])⟩

/-- Erasing labels commutes with the event support. -/
theorem Exp.events_unlabel (t : Exp) : t.unlabel.events = t.events.map Exp.unlabel := by
  induction t <;> simp_all [Exp.events, Exp.unlabel]

/-- The labels written by a list of tags. -/
def recordLabels (τs : List Tag) : List ℕ := τs.filterMap Tag.label?

theorem mem_recordLabels {τs : List Tag} {ℓ : ℕ} {e : Exp} (h : Tag.record ℓ e ∈ τs) :
    ℓ ∈ recordLabels τs :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- With fresh labels, a label names one record contraction. -/
theorem record_unique {τs : List Tag} (h : (recordLabels τs).Nodup) {ℓ : ℕ} {e e₀ : Exp}
    (h₁ : Tag.record ℓ e ∈ τs) (h₂ : Tag.record ℓ e₀ ∈ τs) : e = e₀ := by
  induction τs with
  | nil => cases h₁
  | cons τ τs ih =>
    cases τ with
    | plain =>
      have h' : (recordLabels τs).Nodup := h
      rcases List.mem_cons.mp h₁ with h₁ | h₁
      · cases h₁
      rcases List.mem_cons.mp h₂ with h₂ | h₂
      · cases h₂
      exact ih h' h₁ h₂
    | record ℓ' e' =>
      have h' : (ℓ' :: recordLabels τs).Nodup := h
      obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp h'
      rcases List.mem_cons.mp h₁ with k₁ | k₁ <;> rcases List.mem_cons.mp h₂ with k₂ | k₂
      · cases k₁; cases k₂; rfl
      · cases k₁; exact absurd (mem_recordLabels k₂) hnot
      · cases k₂; exact absurd (mem_recordLabels k₁) hnot
      · exact ih hnd k₁ k₂

/-- The residual record trace `cross↓(π, n)` (Definition 7.1): the record
contraction of `π` with label `ℓ` stored the event `e`, and a residual of its
node occurs in `n` with the event field `e'`. -/
def Cross (τs : List Tag) (n : Exp) (ℓ : ℕ) (e e' : Exp) : Prop :=
  Tag.record ℓ e ∈ τs ∧ ∃ g, HasNode g ℓ e' n

/-- **Lemma 9.5** (record persistence). Let `π` be a labelled reduction sequence
from a public term, with fresh labels. If `(ℓ, e, e') ∈ cross↓(π, n)`, then a
residual node labelled `ℓ` occurs in `n` with the event field `e'`, and
`e' ∈ events(n)`. The field `e'` is obtained from `e` by a substitution and
labelled reduction; if `e` is closed, by reduction alone; and if moreover `n`
is normal, `e'` is the normal form of `e` (after erasing labels, which the
normal form of an expression determines uniquely: `Steps.normal_unique`). -/
theorem record_persistence {τs : List Tag} {t n : Exp} (hpub : t.IsPublic) (h : LSteps τs t n)
    (hfresh : (recordLabels τs).Nodup) {ℓ : ℕ} {e e' : Exp} (hc : Cross τs n ℓ e e') :
    (∃ g, HasNode g ℓ e' n) ∧ e' ∈ n.events ∧ EvDesc e e' ∧ (e.Closed → LReds e e') ∧
      (Normal n → e.Closed → Steps e.unlabel e'.unlabel ∧ Normal e'.unlabel) := by
  obtain ⟨hmem, g, hn⟩ := hc
  obtain ⟨e₀, h₀, hd⟩ := node_ancestry hpub h hn
  obtain rfl := record_unique hfresh hmem h₀
  refine ⟨⟨g, hn⟩, hn.mem_events n, hd, hd.closed, fun hnn hcl => ⟨(hd.closed hcl).erase, ?_⟩⟩
  obtain ⟨ds, a, hocc⟩ := hn
  exact Normal.unlabel_iff.mpr (hnn.of_occurs hocc).node.2.2


/-! ## Instrumenting a sequence with fresh labels -/

/-- All the node labels of `t` are below `N`. -/
def LabelsBelow (N : ℕ) (t : Exp) : Prop := ∀ g ℓ e, HasNode g ℓ e t → ℓ < N

theorem LabelsBelow.of_public {t : Exp} (ht : t.IsPublic) : LabelsBelow 0 t :=
  fun _ _ _ h => absurd h (ht.not_hasNode t)

/-- Instrumentation (Definition 7.1): every reduction sequence from the erasure
of `t` is the erasure of a labelled sequence from `t` whose record
contractions write fresh labels, distinct from each other and from the labels
of `t`. -/
theorem LSteps.instrument {t s : Exp} {N : ℕ} (hN : LabelsBelow N t) (h : Steps t.unlabel s) :
    ∃ τs n, LSteps τs t n ∧ n.unlabel = s ∧ (recordLabels τs).Nodup ∧
      ∀ ℓ ∈ recordLabels τs, N ≤ ℓ := by
  suffices H : ∃ τs n M, LSteps τs t n ∧ n.unlabel = s ∧ (recordLabels τs).Nodup ∧
      (∀ ℓ ∈ recordLabels τs, N ≤ ℓ ∧ ℓ < M) ∧ N ≤ M ∧ LabelsBelow M n by
    obtain ⟨τs, n, M, h₁, h₂, h₃, h₄, -, -⟩ := H
    exact ⟨τs, n, h₁, h₂, h₃, fun ℓ hℓ => (h₄ ℓ hℓ).1⟩
  induction h with
  | refl => exact ⟨[], t, N, .refl, rfl, List.nodup_nil, (fun _ h => by cases h), le_rfl, hN⟩
  | tail _ hs ih =>
    obtain ⟨τs, n, M, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih
    subst h₂
    obtain ⟨τ, n', hst, hun, hτ⟩ := LStep.lift M n hs
    have hbelow : LabelsBelow (M + 1) n' := by
      intro g ℓ e hn
      rcases hst.residual hn with ⟨e₀, h₀, -⟩ | rfl
      · exact Nat.lt_succ_of_lt (h₆ g ℓ e₀ h₀)
      · rcases hτ with h | ⟨e', h⟩ <;> cases h
        exact Nat.lt_succ_self _
    have hM : M ∉ recordLabels τs := fun h => lt_irrefl _ (h₄ M h).2
    refine ⟨τs ++ [τ], n', M + 1, .tail h₁ hst, hun, ?_, ?_, by omega, hbelow⟩
    · rcases hτ with rfl | ⟨e', rfl⟩
      · simp only [recordLabels, List.filterMap_append, List.filterMap_cons, Tag.label?,
          List.filterMap_nil, List.append_nil]
        exact h₃
      · simp only [recordLabels, List.filterMap_append, List.filterMap_cons, Tag.label?,
          List.filterMap_nil]
        exact List.nodup_append.mpr ⟨h₃, List.nodup_singleton M,
          fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact fun h => hM (h ▸ ha)⟩
    · rcases hτ with rfl | ⟨e', rfl⟩
      · intro ℓ hℓ
        simp only [recordLabels, List.filterMap_append, List.filterMap_cons, Tag.label?,
          List.filterMap_nil, List.append_nil] at hℓ
        exact ⟨(h₄ ℓ hℓ).1, Nat.lt_succ_of_lt (h₄ ℓ hℓ).2⟩
      · intro ℓ hℓ
        simp only [recordLabels, List.filterMap_append, List.filterMap_cons, Tag.label?,
          List.filterMap_nil, List.mem_append, List.mem_singleton] at hℓ
        rcases hℓ with hℓ | rfl
        · exact ⟨(h₄ ℓ hℓ).1, Nat.lt_succ_of_lt (h₄ ℓ hℓ).2⟩
        · exact ⟨h₅, Nat.lt_succ_self _⟩

/-! ## Losing a residual -/

theorem loses_congr {τ : Tag} {u u' x x' : Exp} {ℓ : ℕ} (hx : x ∈ u.children)
    (hx' : x' ∈ u'.children) (hchild : ∀ c ∈ u.children, c = x ∨ c ∈ u'.children)
    (hself : ∀ g ds a e, u = .node g ℓ ds a e → ∃ g' e', HasNode g' ℓ e' u')
    (ih : (∃ g e, HasNode g ℓ e x) → (¬∃ g e, HasNode g ℓ e x') →
      ∃ r r', Occurs r x ∧ LContr τ r r' ∧ (∃ g e, HasNode g ℓ e r) ∧
        ¬∃ g e, HasNode g ℓ e r')
    (hu : ∃ g e, HasNode g ℓ e u) (hu' : ¬∃ g e, HasNode g ℓ e u') :
    ∃ r r', Occurs r u ∧ LContr τ r r' ∧ (∃ g e, HasNode g ℓ e r) ∧
      ¬∃ g e, HasNode g ℓ e r' := by
  obtain ⟨g, e, hn⟩ := hu
  rcases hn.inv with ⟨ds, a, heq⟩ | ⟨c, hc, h⟩
  · exact absurd (hself g ds a e heq) hu'
  · rcases hchild c hc with rfl | hc'
    · obtain ⟨r, r', h₁, h₂, h₃, h₄⟩ :=
        ih ⟨g, e, h⟩ (fun ⟨g', e', h'⟩ => hu' ⟨g', e', h'.child hx'⟩)
      exact ⟨r, r', h₁.trans (.child hx .refl), h₂, h₃, h₄⟩
    · exact absurd ⟨g, e, h.child hc'⟩ hu'

/-- Lemma 9.5, last part: a residual of a node is lost only when a contraction
discards the subterm that holds it. If a node labelled `ℓ` occurs before a
labelled step and none occurs after it, the step contracts a redex that holds
such a node and whose contractum holds none. -/
theorem LStep.loses_label {τ : Tag} {u u' : Exp} (h : LStep τ u u') (ℓ : ℕ) :
    (∃ g e, HasNode g ℓ e u) → (¬∃ g e, HasNode g ℓ e u') →
      ∃ r r', Occurs r u ∧ LContr τ r r' ∧ (∃ g e, HasNode g ℓ e r) ∧
        ¬∃ g e, HasNode g ℓ e r' := by
  induction h with
  | contr hc => intro hu hu'; exact ⟨_, _, .refl, hc, hu, hu'⟩
  | fam _ ih | origin₁ _ ih | origin₂ _ ih | origin₃ _ ih | stamped _ ih | pi₁ _ ih | pi₂ _ ih
    | sigma₁ _ ih | sigma₂ _ ih | lam₁ _ ih | lam₂ _ ih | app₁ _ ih | app₂ _ ih | pair₁ _ ih
    | pair₂ _ ih | fst _ ih | snd _ ih | stamp₁ _ ih | stamp₂ _ ih | stamp₃ _ ih | gate₁ _ ih
    | gate₂ _ ih | cons₁ _ ih | cons₂ _ ih =>
    exact loses_congr (by simp [Exp.children]) (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto)
      (fun _ _ _ _ h => by cases h) ih
  | node₁ _ ih | node₂ _ ih | node₃ _ ih =>
    refine loses_congr (by simp [Exp.children]) (by simp [Exp.children])
      (by intro c hc; simp only [Exp.children, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢
          tauto) ?_ ih
    intro g ds a e h
    simp only [Exp.node.injEq] at h
    obtain ⟨rfl, rfl, -, -, -⟩ := h
    exact ⟨_, _, _, _, .refl⟩

/-! ## Positions of the nodes on a path -/

/-- The subject of a type, term or argument-list judgment. -/
def Judg.subject? : Judg → Option Exp
  | .ty _ _ A _ => some A
  | .tm _ _ t _ _ => some t
  | .spine _ ts _ _ => some ts
  | .tel .. => none

/-- Every node edge of the path enters a node of `s` at the edge's position. -/
def NodesAt (s : Exp) (p : Path) : Prop :=
  ∀ (k : ℕ) (e : Edge), p.edges[k]? = some e → ∀ g ℓ, e.kind.InNode g ℓ →
    ∃ ds a ev, s.at (p.pos.take k) = some (.node g ℓ ds a ev)

namespace NodesAt

theorem nil {s : Exp} : ∀ p ∈ ([] : List Path), NodesAt s p := fun _ h => by cases h

theorem leaf {s : Exp} (z : Atom) : ∀ p ∈ [(⟨z, []⟩ : Path)], NodesAt s p := by
  intro p hp k e hk
  rw [List.mem_singleton.mp hp] at hk
  simp at hk

theorem via {s s' : Exp} {e₀ : Edge} {ps : List Path} (hc : s.children[e₀.child]? = some s')
    (h₀ : ∀ g ℓ, e₀.kind.InNode g ℓ → ∃ ds a ev, s = .node g ℓ ds a ev)
    (hp : ∀ p ∈ ps, NodesAt s' p) : ∀ p ∈ ps.map (·.via e₀), NodesAt s p := by
  intro p hp' k e hk g ℓ hin
  obtain ⟨p, hpm, rfl⟩ := mem_map_via hp'
  cases k with
  | zero =>
    simp only [Path.edges_via, List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    obtain ⟨ds, a, ev, rfl⟩ := h₀ g ℓ hin
    exact ⟨ds, a, ev, rfl⟩
  | succ k =>
    simp only [Path.edges_via, List.getElem?_cons_succ] at hk
    obtain ⟨ds, a, ev, h⟩ := hp p hpm k e hk g ℓ hin
    refine ⟨ds, a, ev, ?_⟩
    simp only [Path.pos, Path.edges_via, List.map_cons, List.take_succ_cons, Exp.at, hc]
    exact h

theorem unbind {s : Exp} {ps : List Path} (hp : ∀ p ∈ ps, NodesAt s p) :
    ∀ p ∈ unbindPaths ps, NodesAt s p := by
  intro p hp' k e hk g ℓ hin
  obtain ⟨p', hp'', hed, -⟩ := mem_unbindPaths hp'
  have hpos : p.pos = p'.pos := by simp [Path.pos, hed]
  rw [hpos]
  exact hp p' hp'' k e (hed ▸ hk) g ℓ hin

theorem append {s : Exp} {ps qs : List Path} (h₁ : ∀ p ∈ ps, NodesAt s p)
    (h₂ : ∀ p ∈ qs, NodesAt s p) : ∀ p ∈ ps ++ qs, NodesAt s p := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h₁ p h
  · exact h₂ p h

theorem cons_leaf {s : Exp} {z : Atom} {ps : List Path} (h : ∀ p ∈ ps, NodesAt s p) :
    ∀ p ∈ (⟨z, []⟩ : Path) :: ps, NodesAt s p := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h'
  · exact leaf z _ (List.mem_singleton_self _)
  · exact h p h'

end NodesAt

/-- In every path of a derivation, each node edge enters a node of the
judgment's subject, at the position the path has reached. -/
theorem Deriv.nodesAt {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) {s : Exp}
    (hs : j.subject? = some s) : ∀ p ∈ d.paths, NodesAt s p := by
  have hno : ∀ {s : Exp} {k : EdgeKind}, (∀ g ℓ, ¬k.InNode g ℓ) →
      ∀ g ℓ, k.InNode g ℓ → ∃ ds a ev, s = .node g ℓ ds a ev :=
    fun h g ℓ h' => absurd h' (h g ℓ)
  have hord : ∀ g ℓ, ¬EdgeKind.InNode g ℓ .ord := fun _ _ h => h
  have hn : ∀ {g ℓ : ℕ} {ds t e : Exp} {k : EdgeKind},
      (∀ g' ℓ', k.InNode g' ℓ' → g' = g ∧ ℓ' = ℓ) →
        ∀ g' ℓ', k.InNode g' ℓ' → ∃ ds' a' ev', Exp.node g ℓ ds t e = .node g' ℓ' ds' a' ev' := by
    intro g ℓ ds t e k hk g' ℓ' h
    obtain ⟨rfl, rfl⟩ := hk g' ℓ' h
    exact ⟨ds, t, e, rfl⟩
  induction d generalizing s with
  | tyFam _ _ _ _ ih =>
    cases hs
    exact .cons_leaf (.via rfl (hno hord) (ih rfl))
  | tyEvent => exact .nil
  | tyOrigin _ _ _ _ _ ihA ihe iht =>
    cases hs
    exact .append (.append (.via rfl (hno hord) (ihA rfl)) (.via rfl (hno hord) (ihe rfl)))
      (.via rfl (hno hord) (iht rfl))
  | tyStamped _ _ _ _ ih =>
    cases hs
    exact .via rfl (hno hord) (ih rfl)
  | tyPi _ _ _ _ _ ihA ihB =>
    cases hs
    exact .append (.via rfl (hno fun _ _ h => h) (ihA rfl))
      (.unbind (.via rfl (hno hord) (ihB rfl)))
  | tySigma _ _ _ _ ihA ihB =>
    cases hs
    exact .append (.via rfl (hno hord) (ihA rfl)) (.unbind (.via rfl (hno hord) (ihB rfl)))
  | var => exact .leaf _
  | const => exact .leaf _
  | lam _ _ _ _ _ _ _ iht _ =>
    cases hs
    exact .unbind (.via rfl (hno hord) (iht rfl))
  | app _ _ _ _ _ _ ihf ihu _ =>
    cases hs
    exact .append (.via rfl (hno hord) (ihf rfl)) (.via rfl (hno fun _ _ h => h) (ihu rfl))
  | pair _ _ _ _ _ iht ihu _ =>
    cases hs
    exact .append (.via rfl (hno hord) (iht rfl)) (.via rfl (hno hord) (ihu rfl))
  | fst _ _ _ ihp _ =>
    cases hs
    exact .via rfl (hno hord) (ihp rfl)
  | snd _ _ _ _ ihp _ =>
    cases hs
    exact .via rfl (hno hord) (ihp rfl)
  | stamp _ _ _ _ _ _ iht ihe iho _ =>
    cases hs
    exact .append (.append (.via rfl (hno hord) (iht rfl)) (.via rfl (hno hord) (ihe rfl)))
      (.via rfl (hno hord) (iho rfl))
  | gate _ _ _ _ _ _ _ ihds ihs _ =>
    cases hs
    exact .cons_leaf (.append (.via rfl (hno fun _ _ h => h) (ihds rfl))
      (.via rfl (hno fun _ _ h => h) (ihs rfl)))
  | node _ _ _ _ _ _ _ _ ihds iht ihe _ =>
    cases hs
    exact .cons_leaf (.append (.append
      (.via rfl (hn fun _ _ h => ⟨h.1.symm, h.2.symm⟩) (ihds rfl))
      (.via rfl (hn fun _ _ h => ⟨h.1.symm, h.2.symm⟩) (iht rfl)))
      (.via rfl (hn fun _ _ h => ⟨h.1.symm, h.2.symm⟩) (ihe rfl)))
  | conv _ _ _ iht _ =>
    cases hs
    exact iht rfl
  | spineNil => exact .nil
  | spineCons _ _ _ iht ihts =>
    cases hs
    exact .append (.via rfl (hno hord) (iht rfl)) (.via rfl (hno hord) (ihts rfl))
  | telNil => cases hs
  | telCons => cases hs

/-! ## Theorem 9.7: static–dynamic gate adequacy -/

/-- **Theorem 9.7** (static–dynamic gate adequacy). Let `t` be a closed, public,
policy-valid term at a protected role `ρ` with a grade-free type `A`, and let
`π` be a labelled reduction sequence from `t` to a normal `n`. Then the erasure
of `n` has type `A` at `ρ` with a larger effect, and:
(i) in every derivation of the erasure of `n` at `ρ`, every path from an atom
of policy demand `1` passes through a private node,
and at that position `n` holds a residual node created by a record contraction
of `π`: its label is one that `π` wrote;
(ii) if `(ℓ, e, e') ∈ cross↓(π, n)`, then `e' ∈ events(n)`. -/
theorem gate_adequacy {S : Sig} (hS : SigWF S) {ρ : Role} {t A : Exp} {ε : Eff}
    (dt : Deriv S true (.tm [] ρ t A ε)) (hρ : ρ = .form ∨ ρ = .presentation)
    (hA : A.gradefree) (hpub : t.IsPublic) {τs : List Tag} {n : Exp} (hπ : LSteps τs t n)
    (hn : Normal n) :
    (∃ ε', ε ≤ ε' ∧ Derivable S true (.tm [] ρ n.unlabel A ε')) ∧
    (∀ C ε' (dn : Deriv S true (.tm [] ρ n.unlabel C ε')),
      ∀ p ∈ dn.paths, ∀ σ, roleOf S [] p.atom = some σ → demand σ ρ = .gated →
        ∃ k e, p.edges[k]? = some e ∧ e.kind.IsNode ∧
          ∃ g ℓ ds a ev, n.at (p.pos.take k) = some (.node g ℓ ds a ev) ∧
            ∃ e₀, Tag.record ℓ e₀ ∈ τs) ∧
    (∀ ℓ e e', Cross τs n ℓ e e' → e' ∈ n.events) := by
  have h0 : ∃ ε', ε ≤ ε' ∧ Derivable S true (.tm [] ρ n.unlabel A ε') := by
    have h := hπ.lreds.erase
    rw [hpub.unlabel_eq] at h
    exact dt.subject_reduction_steps hS (.nil hS) h
  refine ⟨h0, ?_, ?_⟩
  · intro C ε' dn p hp σ hσ hd
    have hn' : Normal n.unlabel := Normal.unlabel_iff.mpr hn
    obtain ⟨ε₀, -, ⟨dA⟩⟩ := h0
    have hC : (gskel C).GF := by
      rw [← (Deriv.gskel_unique _ dA dn).1]; exact gskel_gf hA
    obtain ⟨e, he, ⟨g, ℓ', hin⟩⟩ :=
      (dn.gradefree_mediation hS hn' hρ CtxGF.nil hC hp hσ).1 hd
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
    obtain ⟨ds, a, ev, hat⟩ := dn.nodesAt rfl p hp k e hk g ℓ' hin
    rw [Exp.at_unlabel] at hat
    obtain ⟨x, hx, hxu⟩ := Option.map_eq_some_iff.mp hat
    obtain ⟨ℓ, ds', a', ev', rfl⟩ := Exp.unlabel_eq_node hxu
    obtain ⟨e₀, he₀, -⟩ := node_ancestry hpub hπ ⟨ds', a', Exp.at_occurs hx⟩
    exact ⟨k, e, hk, ⟨g, ℓ', hin⟩, g, ℓ, ds', a', ev', hx, e₀, he₀⟩
  · rintro ℓ e e' ⟨-, g, hnode⟩
    exact hnode.mem_events n

/-- Confluence makes the normal form, and hence its event support, independent
of the normalization sequence (up to labels). -/
theorem normal_form_independent {τs₁ τs₂ : List Tag} {t n₁ n₂ : Exp} (h₁ : LSteps τs₁ t n₁)
    (h₂ : LSteps τs₂ t n₂) (hn₁ : Normal n₁) (hn₂ : Normal n₂) :
    n₁.unlabel = n₂.unlabel ∧ n₁.events.map Exp.unlabel = n₂.events.map Exp.unlabel := by
  have h := Steps.normal_unique h₁.lreds.erase h₂.lreds.erase (Normal.unlabel_iff.mpr hn₁)
    (Normal.unlabel_iff.mpr hn₂)
  exact ⟨h, by rw [← Exp.events_unlabel, ← Exp.events_unlabel, h]⟩


/-- An ordinary normalization sequence from a public term, instrumented with
fresh labels: Theorem 9.7 then applies to it. -/
theorem instrument_public {t n₀ : Exp} (hpub : t.IsPublic) (h : Steps t n₀) (hn₀ : Normal n₀) :
    ∃ τs n, LSteps τs t n ∧ n.unlabel = n₀ ∧ (recordLabels τs).Nodup ∧ Normal n := by
  obtain ⟨τs, n, h₁, h₂, h₃, -⟩ :=
    LSteps.instrument (s := n₀) (LabelsBelow.of_public hpub) (by rw [hpub.unlabel_eq]; exact h)
  exact ⟨τs, n, h₁, h₂, h₃, Normal.unlabel_iff.mp (h₂ ▸ hn₀)⟩

end Artform.Roles.Calculus
