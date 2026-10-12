import ArtformRoles.Calculus.Confluence

/-!
# Injectivity of the formers under conversion

No reduction rule changes the head of a type former, of a lambda, a pair, a
stamp or a node: they reduce only inside. With confluence this gives the
injectivity of the formers under conversion (type-head injectivity, used in the
proofs of Theorem 8.14 and Lemma 10.1 of the paper), and distinct heads are
never convertible.
-/

namespace Artform.Roles.Calculus

open Exp Relation

namespace Steps

theorem fam_inv {a args X} (h : Steps (.fam a args) X) :
    ∃ args', X = .fam a args' ∧ Steps args args' := by
  induction h with
  | refl => exact ⟨_, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨args', rfl, h'⟩ := ih
    cases hs with
    | fam h₁ => exact ⟨_, rfl, h'.tail h₁⟩

theorem event_inv {X} (h : Steps .event X) : X = .event := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem origin_inv {A e t X} (h : Steps (.origin A e t) X) :
    ∃ A' e' t', X = .origin A' e' t' ∧ Steps A A' ∧ Steps e e' ∧ Steps t t' := by
  induction h with
  | refl => exact ⟨_, _, _, rfl, .refl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', e', t', rfl, h₁, h₂, h₃⟩ := ih
    cases hs with
    | origin₁ h => exact ⟨_, _, _, rfl, h₁.tail h, h₂, h₃⟩
    | origin₂ h => exact ⟨_, _, _, rfl, h₁, h₂.tail h, h₃⟩
    | origin₃ h => exact ⟨_, _, _, rfl, h₁, h₂, h₃.tail h⟩

theorem stamped_inv {σ A X} (h : Steps (.stamped σ A) X) :
    ∃ A', X = .stamped σ A' ∧ Steps A A' := by
  induction h with
  | refl => exact ⟨_, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', rfl, h'⟩ := ih
    cases hs with
    | stamped h₁ => exact ⟨_, rfl, h'.tail h₁⟩

theorem pi_inv {q σ A B X} (h : Steps (.pi q σ A B) X) :
    ∃ A' B', X = .pi q σ A' B' ∧ Steps A A' ∧ Steps B B' := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', B', rfl, h₁, h₂⟩ := ih
    cases hs with
    | pi₁ h => exact ⟨_, _, rfl, h₁.tail h, h₂⟩
    | pi₂ h => exact ⟨_, _, rfl, h₁, h₂.tail h⟩

theorem sigma_inv {ρ A B X} (h : Steps (.sigma ρ A B) X) :
    ∃ A' B', X = .sigma ρ A' B' ∧ Steps A A' ∧ Steps B B' := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', B', rfl, h₁, h₂⟩ := ih
    cases hs with
    | sigma₁ h => exact ⟨_, _, rfl, h₁.tail h, h₂⟩
    | sigma₂ h => exact ⟨_, _, rfl, h₁, h₂.tail h⟩

theorem lam_inv {q σ A t X} (h : Steps (.lam q σ A t) X) :
    ∃ A' t', X = .lam q σ A' t' ∧ Steps A A' ∧ Steps t t' := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', t', rfl, h₁, h₂⟩ := ih
    cases hs with
    | lam₁ h => exact ⟨_, _, rfl, h₁.tail h, h₂⟩
    | lam₂ h => exact ⟨_, _, rfl, h₁, h₂.tail h⟩

theorem pair_inv {t u X} (h : Steps (.pair t u) X) :
    ∃ t' u', X = .pair t' u' ∧ Steps t t' ∧ Steps u u' := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', u', rfl, h₁, h₂⟩ := ih
    cases hs with
    | pair₁ h => exact ⟨_, _, rfl, h₁.tail h, h₂⟩
    | pair₂ h => exact ⟨_, _, rfl, h₁, h₂.tail h⟩

theorem stamp_inv {t e o X} (h : Steps (.stamp t e o) X) :
    ∃ t' e' o', X = .stamp t' e' o' ∧ Steps t t' ∧ Steps e e' ∧ Steps o o' := by
  induction h with
  | refl => exact ⟨_, _, _, rfl, .refl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', e', o', rfl, h₁, h₂, h₃⟩ := ih
    cases hs with
    | stamp₁ h => exact ⟨_, _, _, rfl, h₁.tail h, h₂, h₃⟩
    | stamp₂ h => exact ⟨_, _, _, rfl, h₁, h₂.tail h, h₃⟩
    | stamp₃ h => exact ⟨_, _, _, rfl, h₁, h₂, h₃.tail h⟩

theorem node_inv {g ℓ ds t e X} (h : Steps (.node g ℓ ds t e) X) :
    ∃ ds' t' e', X = .node g ℓ ds' t' e' ∧ Steps ds ds' ∧ Steps t t' ∧ Steps e e' := by
  induction h with
  | refl => exact ⟨_, _, _, rfl, .refl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨ds', t', e', rfl, h₁, h₂, h₃⟩ := ih
    cases hs with
    | node₁ h => exact ⟨_, _, _, rfl, h₁.tail h, h₂, h₃⟩
    | node₂ h => exact ⟨_, _, _, rfl, h₁, h₂.tail h, h₃⟩
    | node₃ h => exact ⟨_, _, _, rfl, h₁, h₂, h₃.tail h⟩

theorem var_inv {i X} (h : Steps (.var i) X) : X = .var i := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem const_inv {i k X} (h : Steps (.const i k) X) : X = .const i k := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem nil_inv {X} (h : Steps .nil X) : X = .nil := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

theorem cons_inv {t ts X} (h : Steps (.cons t ts) X) :
    ∃ t' ts', X = .cons t' ts' ∧ Steps t t' ∧ Steps ts ts' := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', ts', rfl, h₁, h₂⟩ := ih
    cases hs with
    | cons₁ h => exact ⟨_, _, rfl, h₁.tail h, h₂⟩
    | cons₂ h => exact ⟨_, _, rfl, h₁, h₂.tail h⟩

end Steps

namespace Conv

theorem of_joined {t u w : Exp} (h₁ : Steps t w) (h₂ : Steps u w) : Conv t u :=
  (of_steps h₁).trans (of_steps h₂).symm

theorem fam_inj {a a' args args'} (h : Conv (.fam a args) (.fam a' args')) :
    a = a' ∧ Conv args args' := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨x, rfl, hx⟩ := Steps.fam_inv h₁
  obtain ⟨y, hy, hy'⟩ := Steps.fam_inv h₂
  cases hy
  exact ⟨rfl, of_joined hx hy'⟩

theorem origin_inj {A e t A' e' t'} (h : Conv (.origin A e t) (.origin A' e' t')) :
    Conv A A' ∧ Conv e e' ∧ Conv t t' := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨_, _, _, rfl, hA, he, ht⟩ := Steps.origin_inv h₁
  obtain ⟨_, _, _, hy, hA', he', ht'⟩ := Steps.origin_inv h₂
  cases hy
  exact ⟨of_joined hA hA', of_joined he he', of_joined ht ht'⟩

theorem stamped_inj {σ σ' A A'} (h : Conv (.stamped σ A) (.stamped σ' A')) :
    σ = σ' ∧ Conv A A' := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨_, rfl, hA⟩ := Steps.stamped_inv h₁
  obtain ⟨_, hy, hA'⟩ := Steps.stamped_inv h₂
  cases hy
  exact ⟨rfl, of_joined hA hA'⟩

theorem pi_inj {q q' σ σ' A A' B B'} (h : Conv (.pi q σ A B) (.pi q' σ' A' B')) :
    q = q' ∧ σ = σ' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨_, _, rfl, hA, hB⟩ := Steps.pi_inv h₁
  obtain ⟨_, _, hy, hA', hB'⟩ := Steps.pi_inv h₂
  cases hy
  exact ⟨rfl, rfl, of_joined hA hA', of_joined hB hB'⟩

theorem sigma_inj {ρ ρ' A A' B B'} (h : Conv (.sigma ρ A B) (.sigma ρ' A' B')) :
    ρ = ρ' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨_, _, rfl, hA, hB⟩ := Steps.sigma_inv h₁
  obtain ⟨_, _, hy, hA', hB'⟩ := Steps.sigma_inv h₂
  cases hy
  exact ⟨rfl, of_joined hA hA', of_joined hB hB'⟩

/-- The head of a type former, of a lambda, pair, stamp, node or atom: what no
reduction changes. -/
def headTag : Exp → ℕ
  | .fam a _ => 2 * a + 100
  | .event => 1
  | .origin .. => 2
  | .stamped .. => 3
  | .pi .. => 4
  | .sigma .. => 5
  | .lam .. => 6
  | .pair .. => 7
  | .stamp .. => 8
  | .node .. => 9
  | _ => 0

/-- Expressions headed by a former that never reduces at the head. -/
def Rigid : Exp → Prop
  | .fam .. | .event | .origin .. | .stamped .. | .pi .. | .sigma .. => True
  | .lam .. | .pair .. | .stamp .. | .node .. => True
  | _ => False

theorem Steps.headTag_eq {t u : Exp} (ht : Rigid t) (h : Steps t u) :
    headTag u = headTag t ∧ Rigid u := by
  cases t with
  | fam a args => obtain ⟨_, rfl, _⟩ := Steps.fam_inv h; exact ⟨rfl, trivial⟩
  | event => rw [Steps.event_inv h]; exact ⟨rfl, trivial⟩
  | origin => obtain ⟨_, _, _, rfl, _⟩ := Steps.origin_inv h; exact ⟨rfl, trivial⟩
  | stamped => obtain ⟨_, rfl, _⟩ := Steps.stamped_inv h; exact ⟨rfl, trivial⟩
  | pi => obtain ⟨_, _, rfl, _⟩ := Steps.pi_inv h; exact ⟨rfl, trivial⟩
  | sigma => obtain ⟨_, _, rfl, _⟩ := Steps.sigma_inv h; exact ⟨rfl, trivial⟩
  | lam => obtain ⟨_, _, rfl, _⟩ := Steps.lam_inv h; exact ⟨rfl, trivial⟩
  | pair => obtain ⟨_, _, rfl, _⟩ := Steps.pair_inv h; exact ⟨rfl, trivial⟩
  | stamp => obtain ⟨_, _, _, rfl, _⟩ := Steps.stamp_inv h; exact ⟨rfl, trivial⟩
  | node => obtain ⟨_, _, _, rfl, _⟩ := Steps.node_inv h; exact ⟨rfl, trivial⟩
  | _ => exact absurd ht id

/-- Convertible rigid expressions have the same head. -/
theorem headTag_eq {t u : Exp} (ht : Rigid t) (hu : Rigid u) (h : Conv t u) :
    headTag t = headTag u := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  rw [← (Steps.headTag_eq ht h₁).1, ← (Steps.headTag_eq hu h₂).1]

end Conv

end Artform.Roles.Calculus
