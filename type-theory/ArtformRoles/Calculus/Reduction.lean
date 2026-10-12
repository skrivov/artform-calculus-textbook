import ArtformRoles.Calculus.Syntax
import Mathlib.Logic.Relation

/-!
# Reduction and conversion

Section 7.1 and Appendix B of the paper. `Step` is one-step reduction on raw
expressions: the four primitive redexes (β, the two projections, and the record
step `gate_g(d⃗; stamp(t, e, o)) ⟶ node_g(d⃗; t, e)`) and their compatible
closure under every type and term former, including binders, type indices,
lambda annotations, gate parameters and retained node fields. The record step
writes the label `0`; labels are chosen only by the labelled reduction of
`ArtformRoles.Calculus.Records`.

`Steps` is the reflexive–transitive closure and `Conv` the equivalence closure.
The paper's typed definitional equality relates well-typed expressions only;
the calculus here uses `Conv` in the conversion rule together with an accepted
formation derivation of the target type, and every typed equality is a `Conv`.

`Step.subst` and `Steps.subst_arg` are Lemma 8.8 (residuals of one step).
-/

namespace Artform.Roles.Calculus

open Exp

/-- One-step reduction: the primitive redexes and their compatible closure. -/
inductive Step : Exp → Exp → Prop
  | beta {q σ A t u} : Step (.app (.lam q σ A t) u) (t.inst u)
  | fstPair {t u} : Step (.fst (.pair t u)) t
  | sndPair {t u} : Step (.snd (.pair t u)) u
  | record {g ds t e o} : Step (.gate g ds (.stamp t e o)) (.node g 0 ds t e)
  | fam {a args args'} : Step args args' → Step (.fam a args) (.fam a args')
  | origin₁ {A A' e t} : Step A A' → Step (.origin A e t) (.origin A' e t)
  | origin₂ {A e e' t} : Step e e' → Step (.origin A e t) (.origin A e' t)
  | origin₃ {A e t t'} : Step t t' → Step (.origin A e t) (.origin A e t')
  | stamped {σ A A'} : Step A A' → Step (.stamped σ A) (.stamped σ A')
  | pi₁ {q σ A A' B} : Step A A' → Step (.pi q σ A B) (.pi q σ A' B)
  | pi₂ {q σ A B B'} : Step B B' → Step (.pi q σ A B) (.pi q σ A B')
  | sigma₁ {ρ A A' B} : Step A A' → Step (.sigma ρ A B) (.sigma ρ A' B)
  | sigma₂ {ρ A B B'} : Step B B' → Step (.sigma ρ A B) (.sigma ρ A B')
  | lam₁ {q σ A A' t} : Step A A' → Step (.lam q σ A t) (.lam q σ A' t)
  | lam₂ {q σ A t t'} : Step t t' → Step (.lam q σ A t) (.lam q σ A t')
  | app₁ {t t' u} : Step t t' → Step (.app t u) (.app t' u)
  | app₂ {t u u'} : Step u u' → Step (.app t u) (.app t u')
  | pair₁ {t t' u} : Step t t' → Step (.pair t u) (.pair t' u)
  | pair₂ {t u u'} : Step u u' → Step (.pair t u) (.pair t u')
  | fst {t t'} : Step t t' → Step (.fst t) (.fst t')
  | snd {t t'} : Step t t' → Step (.snd t) (.snd t')
  | stamp₁ {t t' e o} : Step t t' → Step (.stamp t e o) (.stamp t' e o)
  | stamp₂ {t e e' o} : Step e e' → Step (.stamp t e o) (.stamp t e' o)
  | stamp₃ {t e o o'} : Step o o' → Step (.stamp t e o) (.stamp t e o')
  | gate₁ {g ds ds' s} : Step ds ds' → Step (.gate g ds s) (.gate g ds' s)
  | gate₂ {g ds s s'} : Step s s' → Step (.gate g ds s) (.gate g ds s')
  | node₁ {g ℓ ds ds' t e} : Step ds ds' → Step (.node g ℓ ds t e) (.node g ℓ ds' t e)
  | node₂ {g ℓ ds t t' e} : Step t t' → Step (.node g ℓ ds t e) (.node g ℓ ds t' e)
  | node₃ {g ℓ ds t e e'} : Step e e' → Step (.node g ℓ ds t e) (.node g ℓ ds t e')
  | cons₁ {t t' ts} : Step t t' → Step (.cons t ts) (.cons t' ts)
  | cons₂ {t ts ts'} : Step ts ts' → Step (.cons t ts) (.cons t ts')

/-- Reduction in any number of steps. -/
abbrev Steps : Exp → Exp → Prop := Relation.ReflTransGen Step

/-- Conversion: the equivalence closure of reduction. -/
abbrev Conv : Exp → Exp → Prop := Relation.EqvGen Step

/-- A normal expression has no reduct. -/
def Normal (t : Exp) : Prop := ∀ t', ¬Step t t'

namespace Step

theorem ren {t t' : Exp} (h : Step t t') (ξ : ℕ → ℕ) : Step (t.ren ξ) (t'.ren ξ) := by
  induction h generalizing ξ with
  | beta => rw [Exp.ren_inst]; exact .beta
  | fstPair => exact .fstPair
  | sndPair => exact .sndPair
  | record => exact .record
  | fam _ ih => exact .fam (ih ξ)
  | origin₁ _ ih => exact .origin₁ (ih ξ)
  | origin₂ _ ih => exact .origin₂ (ih ξ)
  | origin₃ _ ih => exact .origin₃ (ih ξ)
  | stamped _ ih => exact .stamped (ih ξ)
  | pi₁ _ ih => exact .pi₁ (ih ξ)
  | pi₂ _ ih => exact .pi₂ (ih _)
  | sigma₁ _ ih => exact .sigma₁ (ih ξ)
  | sigma₂ _ ih => exact .sigma₂ (ih _)
  | lam₁ _ ih => exact .lam₁ (ih ξ)
  | lam₂ _ ih => exact .lam₂ (ih _)
  | app₁ _ ih => exact .app₁ (ih ξ)
  | app₂ _ ih => exact .app₂ (ih ξ)
  | pair₁ _ ih => exact .pair₁ (ih ξ)
  | pair₂ _ ih => exact .pair₂ (ih ξ)
  | fst _ ih => exact .fst (ih ξ)
  | snd _ ih => exact .snd (ih ξ)
  | stamp₁ _ ih => exact .stamp₁ (ih ξ)
  | stamp₂ _ ih => exact .stamp₂ (ih ξ)
  | stamp₃ _ ih => exact .stamp₃ (ih ξ)
  | gate₁ _ ih => exact .gate₁ (ih ξ)
  | gate₂ _ ih => exact .gate₂ (ih ξ)
  | node₁ _ ih => exact .node₁ (ih ξ)
  | node₂ _ ih => exact .node₂ (ih ξ)
  | node₃ _ ih => exact .node₃ (ih ξ)
  | cons₁ _ ih => exact .cons₁ (ih ξ)
  | cons₂ _ ih => exact .cons₂ (ih ξ)

/-- Lemma 8.8, first part: a step survives substitution. -/
theorem subst {t t' : Exp} (h : Step t t') (σ : ℕ → Exp) : Step (t.subst σ) (t'.subst σ) := by
  induction h generalizing σ with
  | beta => rw [Exp.subst_inst]; exact .beta
  | fstPair => exact .fstPair
  | sndPair => exact .sndPair
  | record => exact .record
  | fam _ ih => exact .fam (ih σ)
  | origin₁ _ ih => exact .origin₁ (ih σ)
  | origin₂ _ ih => exact .origin₂ (ih σ)
  | origin₃ _ ih => exact .origin₃ (ih σ)
  | stamped _ ih => exact .stamped (ih σ)
  | pi₁ _ ih => exact .pi₁ (ih σ)
  | pi₂ _ ih => exact .pi₂ (ih _)
  | sigma₁ _ ih => exact .sigma₁ (ih σ)
  | sigma₂ _ ih => exact .sigma₂ (ih _)
  | lam₁ _ ih => exact .lam₁ (ih σ)
  | lam₂ _ ih => exact .lam₂ (ih _)
  | app₁ _ ih => exact .app₁ (ih σ)
  | app₂ _ ih => exact .app₂ (ih σ)
  | pair₁ _ ih => exact .pair₁ (ih σ)
  | pair₂ _ ih => exact .pair₂ (ih σ)
  | fst _ ih => exact .fst (ih σ)
  | snd _ ih => exact .snd (ih σ)
  | stamp₁ _ ih => exact .stamp₁ (ih σ)
  | stamp₂ _ ih => exact .stamp₂ (ih σ)
  | stamp₃ _ ih => exact .stamp₃ (ih σ)
  | gate₁ _ ih => exact .gate₁ (ih σ)
  | gate₂ _ ih => exact .gate₂ (ih σ)
  | node₁ _ ih => exact .node₁ (ih σ)
  | node₂ _ ih => exact .node₂ (ih σ)
  | node₃ _ ih => exact .node₃ (ih σ)
  | cons₁ _ ih => exact .cons₁ (ih σ)
  | cons₂ _ ih => exact .cons₂ (ih σ)

end Step

namespace Steps

open Relation

theorem single {t t' : Exp} (h : Step t t') : Steps t t' := ReflTransGen.single h

theorem lift (f : Exp → Exp) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {t t' : Exp}
    (h : Steps t t') : Steps (f t) (f t') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hf hs)

theorem ren {t t' : Exp} (h : Steps t t') (ξ : ℕ → ℕ) : Steps (t.ren ξ) (t'.ren ξ) :=
  lift (Exp.ren ξ) (fun h => h.ren ξ) h

theorem subst {t t' : Exp} (h : Steps t t') (σ : ℕ → Exp) : Steps (t.subst σ) (t'.subst σ) :=
  lift (Exp.subst σ) (fun h => h.subst σ) h

/-- Two reductions in the two arguments of a binary former. -/
theorem lift₂ (f : Exp → Exp → Exp) (hf₁ : ∀ {a a' b}, Step a a' → Step (f a b) (f a' b))
    (hf₂ : ∀ {a b b'}, Step b b' → Step (f a b) (f a b')) {a a' b b' : Exp}
    (ha : Steps a a') (hb : Steps b b') : Steps (f a b) (f a' b') :=
  (lift (f · b) hf₁ ha).trans (lift (f a' ·) hf₂ hb)

/-- Three reductions in the three arguments of a ternary former. -/
theorem lift₃ (f : Exp → Exp → Exp → Exp)
    (hf₁ : ∀ {a a' b c}, Step a a' → Step (f a b c) (f a' b c))
    (hf₂ : ∀ {a b b' c}, Step b b' → Step (f a b c) (f a b' c))
    (hf₃ : ∀ {a b c c'}, Step c c' → Step (f a b c) (f a b c'))
    {a a' b b' c c' : Exp} (ha : Steps a a') (hb : Steps b b') (hc : Steps c c') :
    Steps (f a b c) (f a' b' c') :=
  ((lift (f · b c) hf₁ ha).trans (lift (f a' · c) hf₂ hb)).trans (lift (f a' b' ·) hf₃ hc)

theorem up {σ τ : ℕ → Exp} (h : ∀ i, Steps (σ i) (τ i)) : ∀ i, Steps (Exp.up σ i) (Exp.up τ i)
  | 0 => .refl
  | i + 1 => (h i).ren _

/-- Lemma 8.8, second part: reducing the substituted terms reduces the result. -/
theorem subst_arg {σ τ : ℕ → Exp} (h : ∀ i, Steps (σ i) (τ i)) (t : Exp) :
    Steps (t.subst σ) (t.subst τ) := by
  induction t generalizing σ τ with
  | var i => exact h i
  | const => exact .refl
  | fam a args ih => exact lift (fam a) Step.fam (ih h)
  | event => exact .refl
  | origin A e t ihA ihe iht =>
    exact lift₃ origin Step.origin₁ Step.origin₂ Step.origin₃ (ihA h) (ihe h) (iht h)
  | stamped ρ A ih => exact lift (stamped ρ) Step.stamped (ih h)
  | pi q ρ A B ihA ihB => exact lift₂ (pi q ρ) Step.pi₁ Step.pi₂ (ihA h) (ihB (up h))
  | sigma ρ A B ihA ihB => exact lift₂ (sigma ρ) Step.sigma₁ Step.sigma₂ (ihA h) (ihB (up h))
  | lam q ρ A t ihA iht => exact lift₂ (lam q ρ) Step.lam₁ Step.lam₂ (ihA h) (iht (up h))
  | app t u iht ihu => exact lift₂ app Step.app₁ Step.app₂ (iht h) (ihu h)
  | pair t u iht ihu => exact lift₂ pair Step.pair₁ Step.pair₂ (iht h) (ihu h)
  | fst t ih => exact lift fst Step.fst (ih h)
  | snd t ih => exact lift snd Step.snd (ih h)
  | stamp t e o iht ihe iho =>
    exact lift₃ stamp Step.stamp₁ Step.stamp₂ Step.stamp₃ (iht h) (ihe h) (iho h)
  | gate g ds s ihd ihs => exact lift₂ (gate g) Step.gate₁ Step.gate₂ (ihd h) (ihs h)
  | node g ℓ ds t e ihd iht ihe =>
    exact lift₃ (node g ℓ) Step.node₁ Step.node₂ Step.node₃ (ihd h) (iht h) (ihe h)
  | nil => exact .refl
  | cons t ts iht ihts => exact lift₂ cons Step.cons₁ Step.cons₂ (iht h) (ihts h)

/-- Lemma 8.8 for one variable: reducing the argument of an instantiation. -/
theorem inst_arg {u u' : Exp} (h : Steps u u') (t : Exp) : Steps (t.inst u) (t.inst u') :=
  subst_arg (fun i => by cases i with | zero => exact h | succ i => exact .refl) t

end Steps

namespace Conv

open Relation

theorem of_steps {t t' : Exp} (h : Steps t t') : Conv t t' := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ hs ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hs)

theorem of_step {t t' : Exp} (h : Step t t') : Conv t t' := EqvGen.rel _ _ h

theorem refl (t : Exp) : Conv t t := EqvGen.refl t

theorem symm {t t' : Exp} (h : Conv t t') : Conv t' t := EqvGen.symm _ _ h

theorem trans {t t' t'' : Exp} (h : Conv t t') (h' : Conv t' t'') : Conv t t'' :=
  EqvGen.trans _ _ _ h h'

theorem lift (f : Exp → Exp) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {t t' : Exp}
    (h : Conv t t') : Conv (f t) (f t') := by
  induction h with
  | rel _ _ h => exact of_step (hf h)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem subst {t t' : Exp} (h : Conv t t') (σ : ℕ → Exp) : Conv (t.subst σ) (t'.subst σ) :=
  lift (Exp.subst σ) (fun h => h.subst σ) h

theorem ren {t t' : Exp} (h : Conv t t') (ξ : ℕ → ℕ) : Conv (t.ren ξ) (t'.ren ξ) :=
  lift (Exp.ren ξ) (fun h => h.ren ξ) h

end Conv

end Artform.Roles.Calculus
