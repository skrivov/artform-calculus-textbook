import ArtformRoles.Calculus.Reduction

/-!
# Confluence

Theorem 8.13 (confluence, `thm:confluence`) and Lemma 8.12 (local confluence,
`lem:local-confluence`) of the paper, for
raw reduction on all expressions, typed or not. The paper derives confluence of
typed reduction from strong normalization and local confluence by Newman's
lemma; here confluence is proved directly, by parallel reduction and its
complete development (Tait, Martin-Löf, Takahashi), so it holds without typing
and the typed statements are special cases.

* `PStep`: parallel reduction, which contracts any set of redexes present at
  once. A contraction discards the lambda annotation, the other component of a
  pair, or the origin of a stamp.
* `cd`: the complete development, which contracts every redex present.
* `PStep.triangle`: `t ⇒ u` implies `u ⇒ cd t`.
* `Steps.confluent`, `Conv.joinable` (Church–Rosser).
-/

namespace Artform.Roles.Calculus

open Exp

/-- Parallel reduction. -/
inductive PStep : Exp → Exp → Prop
  | var (i : ℕ) : PStep (.var i) (.var i)
  | const (i k : ℕ) : PStep (.const i k) (.const i k)
  | event : PStep .event .event
  | nil : PStep .nil .nil
  | fam {a args args'} : PStep args args' → PStep (.fam a args) (.fam a args')
  | origin {A A' e e' t t'} : PStep A A' → PStep e e' → PStep t t' →
      PStep (.origin A e t) (.origin A' e' t')
  | stamped {σ A A'} : PStep A A' → PStep (.stamped σ A) (.stamped σ A')
  | pi {q σ A A' B B'} : PStep A A' → PStep B B' → PStep (.pi q σ A B) (.pi q σ A' B')
  | sigma {ρ A A' B B'} : PStep A A' → PStep B B' → PStep (.sigma ρ A B) (.sigma ρ A' B')
  | lam {q σ A A' t t'} : PStep A A' → PStep t t' → PStep (.lam q σ A t) (.lam q σ A' t')
  | app {t t' u u'} : PStep t t' → PStep u u' → PStep (.app t u) (.app t' u')
  | pair {t t' u u'} : PStep t t' → PStep u u' → PStep (.pair t u) (.pair t' u')
  | fst {t t'} : PStep t t' → PStep (.fst t) (.fst t')
  | snd {t t'} : PStep t t' → PStep (.snd t) (.snd t')
  | stamp {t t' e e' o o'} : PStep t t' → PStep e e' → PStep o o' →
      PStep (.stamp t e o) (.stamp t' e' o')
  | gate {g ds ds' s s'} : PStep ds ds' → PStep s s' → PStep (.gate g ds s) (.gate g ds' s')
  | node {g ℓ ds ds' t t' e e'} : PStep ds ds' → PStep t t' → PStep e e' →
      PStep (.node g ℓ ds t e) (.node g ℓ ds' t' e')
  | cons {t t' ts ts'} : PStep t t' → PStep ts ts' → PStep (.cons t ts) (.cons t' ts')
  | beta {q σ A t t' u u'} : PStep t t' → PStep u u' →
      PStep (.app (.lam q σ A t) u) (t'.inst u')
  | fstPair {t t' u} : PStep t t' → PStep (.fst (.pair t u)) t'
  | sndPair {t u u'} : PStep u u' → PStep (.snd (.pair t u)) u'
  | record {g ds ds' t t' e e' o} : PStep ds ds' → PStep t t' → PStep e e' →
      PStep (.gate g ds (.stamp t e o)) (.node g 0 ds' t' e')

namespace PStep

theorem refl : ∀ t : Exp, PStep t t
  | .var i => .var i
  | .const i k => .const i k
  | .fam _ args => .fam (refl args)
  | .event => .event
  | .origin A e t => .origin (refl A) (refl e) (refl t)
  | .stamped _ A => .stamped (refl A)
  | .pi _ _ A B => .pi (refl A) (refl B)
  | .sigma _ A B => .sigma (refl A) (refl B)
  | .lam _ _ A t => .lam (refl A) (refl t)
  | .app t u => .app (refl t) (refl u)
  | .pair t u => .pair (refl t) (refl u)
  | .fst t => .fst (refl t)
  | .snd t => .snd (refl t)
  | .stamp t e o => .stamp (refl t) (refl e) (refl o)
  | .gate _ ds s => .gate (refl ds) (refl s)
  | .node _ _ ds t e => .node (refl ds) (refl t) (refl e)
  | .nil => .nil
  | .cons t ts => .cons (refl t) (refl ts)

theorem of_step {t t' : Exp} (h : Step t t') : PStep t t' := by
  induction h with
  | beta => exact .beta (refl _) (refl _)
  | fstPair => exact .fstPair (refl _)
  | sndPair => exact .sndPair (refl _)
  | record => exact .record (refl _) (refl _) (refl _)
  | fam _ ih => exact .fam ih
  | origin₁ _ ih => exact .origin ih (refl _) (refl _)
  | origin₂ _ ih => exact .origin (refl _) ih (refl _)
  | origin₃ _ ih => exact .origin (refl _) (refl _) ih
  | stamped _ ih => exact .stamped ih
  | pi₁ _ ih => exact .pi ih (refl _)
  | pi₂ _ ih => exact .pi (refl _) ih
  | sigma₁ _ ih => exact .sigma ih (refl _)
  | sigma₂ _ ih => exact .sigma (refl _) ih
  | lam₁ _ ih => exact .lam ih (refl _)
  | lam₂ _ ih => exact .lam (refl _) ih
  | app₁ _ ih => exact .app ih (refl _)
  | app₂ _ ih => exact .app (refl _) ih
  | pair₁ _ ih => exact .pair ih (refl _)
  | pair₂ _ ih => exact .pair (refl _) ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | stamp₁ _ ih => exact .stamp ih (refl _) (refl _)
  | stamp₂ _ ih => exact .stamp (refl _) ih (refl _)
  | stamp₃ _ ih => exact .stamp (refl _) (refl _) ih
  | gate₁ _ ih => exact .gate ih (refl _)
  | gate₂ _ ih => exact .gate (refl _) ih
  | node₁ _ ih => exact .node ih (refl _) (refl _)
  | node₂ _ ih => exact .node (refl _) ih (refl _)
  | node₃ _ ih => exact .node (refl _) (refl _) ih
  | cons₁ _ ih => exact .cons ih (refl _)
  | cons₂ _ ih => exact .cons (refl _) ih

theorem to_steps {t t' : Exp} (h : PStep t t') : Steps t t' := by
  induction h with
  | var | const | event | nil => exact .refl
  | fam _ ih => exact Steps.lift (Exp.fam _) Step.fam ih
  | origin _ _ _ ih₁ ih₂ ih₃ =>
    exact Steps.lift₃ Exp.origin Step.origin₁ Step.origin₂ Step.origin₃ ih₁ ih₂ ih₃
  | stamped _ ih => exact Steps.lift (Exp.stamped _) Step.stamped ih
  | pi _ _ ih₁ ih₂ => exact Steps.lift₂ (Exp.pi _ _) Step.pi₁ Step.pi₂ ih₁ ih₂
  | sigma _ _ ih₁ ih₂ => exact Steps.lift₂ (Exp.sigma _) Step.sigma₁ Step.sigma₂ ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact Steps.lift₂ (Exp.lam _ _) Step.lam₁ Step.lam₂ ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact Steps.lift₂ Exp.app Step.app₁ Step.app₂ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact Steps.lift₂ Exp.pair Step.pair₁ Step.pair₂ ih₁ ih₂
  | fst _ ih => exact Steps.lift Exp.fst Step.fst ih
  | snd _ ih => exact Steps.lift Exp.snd Step.snd ih
  | stamp _ _ _ ih₁ ih₂ ih₃ =>
    exact Steps.lift₃ Exp.stamp Step.stamp₁ Step.stamp₂ Step.stamp₃ ih₁ ih₂ ih₃
  | gate _ _ ih₁ ih₂ => exact Steps.lift₂ (Exp.gate _) Step.gate₁ Step.gate₂ ih₁ ih₂
  | node _ _ _ ih₁ ih₂ ih₃ =>
    exact Steps.lift₃ (Exp.node _ _) Step.node₁ Step.node₂ Step.node₃ ih₁ ih₂ ih₃
  | cons _ _ ih₁ ih₂ => exact Steps.lift₂ Exp.cons Step.cons₁ Step.cons₂ ih₁ ih₂
  | @beta q σ A t t' u u' _ _ ih₁ ih₂ =>
    have h₁ : Steps (Exp.app (Exp.lam q σ A t) u) (Exp.app (Exp.lam q σ A t') u') :=
      Steps.lift₂ Exp.app Step.app₁ Step.app₂ (Steps.lift (Exp.lam q σ A) Step.lam₂ ih₁) ih₂
    exact h₁.tail .beta
  | fstPair _ ih => exact (Steps.single .fstPair).trans ih
  | sndPair _ ih => exact (Steps.single .sndPair).trans ih
  | record _ _ _ ih₁ ih₂ ih₃ =>
    exact (Steps.single .record).trans
      (Steps.lift₃ (Exp.node _ 0) Step.node₁ Step.node₂ Step.node₃ ih₁ ih₂ ih₃)

theorem ren {t t' : Exp} (h : PStep t t') (ξ : ℕ → ℕ) : PStep (t.ren ξ) (t'.ren ξ) := by
  induction h generalizing ξ with
  | var i => exact .var _
  | const => exact .const _ _
  | event => exact .event
  | nil => exact .nil
  | fam _ ih => exact .fam (ih ξ)
  | origin _ _ _ ih₁ ih₂ ih₃ => exact .origin (ih₁ ξ) (ih₂ ξ) (ih₃ ξ)
  | stamped _ ih => exact .stamped (ih ξ)
  | pi _ _ ih₁ ih₂ => exact .pi (ih₁ ξ) (ih₂ _)
  | sigma _ _ ih₁ ih₂ => exact .sigma (ih₁ ξ) (ih₂ _)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ ξ) (ih₂ _)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ξ) (ih₂ ξ)
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ ξ) (ih₂ ξ)
  | fst _ ih => exact .fst (ih ξ)
  | snd _ ih => exact .snd (ih ξ)
  | stamp _ _ _ ih₁ ih₂ ih₃ => exact .stamp (ih₁ ξ) (ih₂ ξ) (ih₃ ξ)
  | gate _ _ ih₁ ih₂ => exact .gate (ih₁ ξ) (ih₂ ξ)
  | node _ _ _ ih₁ ih₂ ih₃ => exact .node (ih₁ ξ) (ih₂ ξ) (ih₃ ξ)
  | cons _ _ ih₁ ih₂ => exact .cons (ih₁ ξ) (ih₂ ξ)
  | beta _ _ ih₁ ih₂ => rw [Exp.ren_inst]; exact .beta (ih₁ _) (ih₂ ξ)
  | fstPair _ ih => exact .fstPair (ih ξ)
  | sndPair _ ih => exact .sndPair (ih ξ)
  | record _ _ _ ih₁ ih₂ ih₃ => exact .record (ih₁ ξ) (ih₂ ξ) (ih₃ ξ)

theorem up {σ τ : ℕ → Exp} (h : ∀ i, PStep (σ i) (τ i)) : ∀ i, PStep (Exp.up σ i) (Exp.up τ i)
  | 0 => .var 0
  | i + 1 => (h i).ren _

/-- Parallel reduction is stable under parallel substitution. -/
theorem subst {t t' : Exp} (h : PStep t t') {σ τ : ℕ → Exp} (hσ : ∀ i, PStep (σ i) (τ i)) :
    PStep (t.subst σ) (t'.subst τ) := by
  induction h generalizing σ τ with
  | var i => exact hσ i
  | const => exact .const _ _
  | event => exact .event
  | nil => exact .nil
  | fam _ ih => exact .fam (ih hσ)
  | origin _ _ _ ih₁ ih₂ ih₃ => exact .origin (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)
  | stamped _ ih => exact .stamped (ih hσ)
  | pi _ _ ih₁ ih₂ => exact .pi (ih₁ hσ) (ih₂ (up hσ))
  | sigma _ _ ih₁ ih₂ => exact .sigma (ih₁ hσ) (ih₂ (up hσ))
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ hσ) (ih₂ (up hσ))
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hσ) (ih₂ hσ)
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ hσ) (ih₂ hσ)
  | fst _ ih => exact .fst (ih hσ)
  | snd _ ih => exact .snd (ih hσ)
  | stamp _ _ _ ih₁ ih₂ ih₃ => exact .stamp (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)
  | gate _ _ ih₁ ih₂ => exact .gate (ih₁ hσ) (ih₂ hσ)
  | node _ _ _ ih₁ ih₂ ih₃ => exact .node (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)
  | cons _ _ ih₁ ih₂ => exact .cons (ih₁ hσ) (ih₂ hσ)
  | beta _ _ ih₁ ih₂ =>
    rw [Exp.subst_inst]; exact .beta (ih₁ (up hσ)) (ih₂ hσ)
  | fstPair _ ih => exact .fstPair (ih hσ)
  | sndPair _ ih => exact .sndPair (ih hσ)
  | record _ _ _ ih₁ ih₂ ih₃ => exact .record (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)

theorem inst {t t' u u' : Exp} (ht : PStep t t') (hu : PStep u u') :
    PStep (t.inst u) (t'.inst u') :=
  subst ht fun i => by
    cases i with
    | zero => exact hu
    | succ i => exact .var i

end PStep

/-- The complete development: every redex present in the expression is
contracted. -/
def cd : Exp → Exp
  | .app (.lam _ _ _ t) u => (cd t).inst (cd u)
  | .fst (.pair t _) => cd t
  | .snd (.pair _ u) => cd u
  | .gate g ds (.stamp t e _) => .node g 0 (cd ds) (cd t) (cd e)
  | .var i => .var i
  | .const i k => .const i k
  | .fam a args => .fam a (cd args)
  | .event => .event
  | .origin A e t => .origin (cd A) (cd e) (cd t)
  | .stamped σ A => .stamped σ (cd A)
  | .pi q σ A B => .pi q σ (cd A) (cd B)
  | .sigma ρ A B => .sigma ρ (cd A) (cd B)
  | .lam q σ A t => .lam q σ (cd A) (cd t)
  | .app t u => .app (cd t) (cd u)
  | .pair t u => .pair (cd t) (cd u)
  | .fst t => .fst (cd t)
  | .snd t => .snd (cd t)
  | .stamp t e o => .stamp (cd t) (cd e) (cd o)
  | .gate g ds s => .gate g (cd ds) (cd s)
  | .node g ℓ ds t e => .node g ℓ (cd ds) (cd t) (cd e)
  | .nil => .nil
  | .cons t ts => .cons (cd t) (cd ts)

namespace PStep

/-- The triangle property: a parallel reduct reduces in parallel to the
complete development. -/
theorem triangle {t u : Exp} (h : PStep t u) : PStep u (cd t) := by
  induction h with
  | var i => exact .var i
  | const => exact .const _ _
  | event => exact .event
  | nil => exact .nil
  | fam _ ih => exact .fam ih
  | origin _ _ _ ih₁ ih₂ ih₃ => exact .origin ih₁ ih₂ ih₃
  | stamped _ ih => exact .stamped ih
  | pi _ _ ih₁ ih₂ => exact .pi ih₁ ih₂
  | sigma _ _ ih₁ ih₂ => exact .sigma ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | @app t t' u u' ht _ ih₁ ih₂ =>
    cases ht with
    | lam _ hb =>
      simp only [cd] at ih₁ ⊢
      cases ih₁ with
      | lam _ hb' => exact .beta hb' ih₂
    | _ => simpa [cd] using PStep.app ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | @fst t t' ht ih =>
    cases ht with
    | pair _ _ =>
      simp only [cd] at ih ⊢
      cases ih with
      | pair h₁ _ => exact .fstPair h₁
    | _ => simpa [cd] using PStep.fst ih
  | @snd t t' ht ih =>
    cases ht with
    | pair _ _ =>
      simp only [cd] at ih ⊢
      cases ih with
      | pair _ h₂ => exact .sndPair h₂
    | _ => simpa [cd] using PStep.snd ih
  | stamp _ _ _ ih₁ ih₂ ih₃ => exact .stamp ih₁ ih₂ ih₃
  | @gate g ds ds' s s' _ hs ih₁ ih₂ =>
    cases hs with
    | stamp _ _ _ =>
      simp only [cd] at ih₂ ⊢
      cases ih₂ with
      | stamp h₁ h₂ _ => exact .record ih₁ h₁ h₂
    | _ => simpa [cd] using PStep.gate ih₁ ih₂
  | node _ _ _ ih₁ ih₂ ih₃ => exact .node ih₁ ih₂ ih₃
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | beta _ _ ih₁ ih₂ => exact inst ih₁ ih₂
  | fstPair _ ih => exact ih
  | sndPair _ ih => exact ih
  | record _ _ _ ih₁ ih₂ ih₃ => exact .node ih₁ ih₂ ih₃

/-- The diamond property of parallel reduction. -/
theorem diamond {t u v : Exp} (hu : PStep t u) (hv : PStep t v) :
    ∃ w, PStep u w ∧ PStep v w :=
  ⟨cd t, hu.triangle, hv.triangle⟩

end PStep

namespace Steps

open Relation

/-- Reduction sequences are sequences of parallel steps. -/
theorem to_pSteps {t t' : Exp} (h : Steps t t') : ReflTransGen PStep t t' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (PStep.of_step hs)

theorem of_pSteps {t t' : Exp} (h : ReflTransGen PStep t t') : Steps t t' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans hs.to_steps

/-- The strip lemma for parallel reduction. -/
theorem strip {t u v : Exp} (hu : PStep t u) (hv : ReflTransGen PStep t v) :
    ∃ w, ReflTransGen PStep u w ∧ PStep v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, .refl, hu⟩
  | tail _ hs ih =>
    obtain ⟨w, huw, hvw⟩ := ih hu
    obtain ⟨w', hw, hs'⟩ := hvw.diamond hs
    exact ⟨w', huw.tail hw, hs'⟩

/-- Theorem 8.13 (`thm:confluence`): reduction is confluent. -/
theorem confluent {t u v : Exp} (hu : Steps t u) (hv : Steps t v) :
    ∃ w, Steps u w ∧ Steps v w := by
  have key : ∀ {t u v}, ReflTransGen PStep t u → ReflTransGen PStep t v →
      ∃ w, ReflTransGen PStep u w ∧ ReflTransGen PStep v w := by
    intro t u v hu hv
    induction hu generalizing v with
    | refl => exact ⟨v, hv, .refl⟩
    | tail _ hs ih =>
      obtain ⟨w, hw₁, hw₂⟩ := ih hv
      obtain ⟨w', hw', hs'⟩ := strip hs hw₁
      exact ⟨w', hw', hw₂.tail hs'⟩
  obtain ⟨w, h₁, h₂⟩ := key hu.to_pSteps hv.to_pSteps
  exact ⟨w, of_pSteps h₁, of_pSteps h₂⟩

/-- Lemma 8.12 (`lem:local-confluence`): one-step peaks are joinable. -/
theorem local_confluent {t u v : Exp} (hu : Step t u) (hv : Step t v) :
    ∃ w, Steps u w ∧ Steps v w :=
  confluent (single hu) (single hv)

end Steps

namespace Conv

open Relation

/-- Church–Rosser: convertible expressions have a common reduct. -/
theorem joinable {t u : Exp} (h : Conv t u) : ∃ w, Steps t w ∧ Steps u w := by
  induction h with
  | rel _ _ h => exact ⟨_, Steps.single h, .refl⟩
  | refl t => exact ⟨t, .refl, .refl⟩
  | symm _ _ _ ih =>
    obtain ⟨w, h₁, h₂⟩ := ih
    exact ⟨w, h₂, h₁⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨w₁, h₁, h₂⟩ := ih₁
    obtain ⟨w₂, h₃, h₄⟩ := ih₂
    obtain ⟨w, h₅, h₆⟩ := Steps.confluent h₂ h₃
    exact ⟨w, h₁.trans h₅, h₄.trans h₆⟩

theorem iff_joinable {t u : Exp} : Conv t u ↔ ∃ w, Steps t w ∧ Steps u w :=
  ⟨joinable, fun ⟨_, h₁, h₂⟩ => (of_steps h₁).trans (of_steps h₂).symm⟩

end Conv

end Artform.Roles.Calculus
