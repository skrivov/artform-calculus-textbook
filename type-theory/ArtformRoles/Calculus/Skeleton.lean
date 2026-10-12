import ArtformRoles.Calculus.Preservation

/-!
# Skeletons

The simple skeleton of a type (§8.4 of the paper) erases its term indices,
roles and grades and keeps its computational shape:
`τ ::= ι_a | ι_E | ι_O | Sτ | τ ⇒ τ | τ × τ`. The graded skeleton keeps the
roles and grades of the formers as well.

* `Exp.TyShape`: every type position is filled by a type former, as in every
  well-formed type (`Deriv.tyShape`).
* Lemma 8.6 (skeleton invariance): reduction, conversion and substitution keep
  the skeleton of a type (`gskel_step`, `gskel_conv`, `gskel_subst`, and the
  same for `skel`).
-/

namespace Artform.Roles.Calculus

open Exp

/-- Simple skeletons (§8.4). -/
inductive Skel
  | base (a : ℕ)
  | ev
  | org
  | stmp (τ : Skel)
  | arr (τ υ : Skel)
  | prod (τ υ : Skel)
  | junk
  deriving DecidableEq, Repr

/-- Skeletons that keep the roles and grades of the formers. -/
inductive GSkel
  | base (a : ℕ)
  | ev
  | org
  | stmp (σ : Role) (τ : GSkel)
  | arr (q : Grade) (σ : Role) (τ υ : GSkel)
  | prod (ρ : Role) (τ υ : GSkel)
  | junk
  deriving DecidableEq, Repr

/-- Forget the roles and grades of a graded skeleton. -/
def GSkel.erase : GSkel → Skel
  | .base a => .base a
  | .ev => .ev
  | .org => .org
  | .stmp _ τ => .stmp τ.erase
  | .arr _ _ τ υ => .arr τ.erase υ.erase
  | .prod _ τ υ => .prod τ.erase υ.erase
  | .junk => .junk

/-- The graded skeleton of a type. -/
def gskel : Exp → GSkel
  | .fam a _ => .base a
  | .event => .ev
  | .origin .. => .org
  | .stamped σ A => .stmp σ (gskel A)
  | .pi q σ A B => .arr q σ (gskel A) (gskel B)
  | .sigma ρ A B => .prod ρ (gskel A) (gskel B)
  | _ => .junk

/-- The simple skeleton `⌊A⌋` of a type. -/
def skel (A : Exp) : Skel := (gskel A).erase

/-- Every type position of `A` holds a type former. -/
def Exp.TyShape : Exp → Prop
  | .fam .. => True
  | .event => True
  | .origin .. => True
  | .stamped _ A => TyShape A
  | .pi _ _ A B => TyShape A ∧ TyShape B
  | .sigma _ A B => TyShape A ∧ TyShape B
  | _ => False

/-- A well-formed type has the shape of a type. -/
theorem Deriv.tyShape {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    match j with
    | .ty _ _ A _ => A.TyShape
    | _ => True := by
  induction d with
  | tyFam | tyEvent | tyOrigin => trivial
  | tyStamped _ _ _ _ ih => exact ih
  | tyPi _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | tySigma _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | _ => trivial

theorem Deriv.tyShape_ty {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp} {α : Eff}
    (d : Deriv S acc (.ty Γ ρ A α)) : A.TyShape := d.tyShape

/-- Lemma 8.6, substitution: substituting in indices keeps the skeleton. -/
theorem gskel_subst {A : Exp} (h : A.TyShape) (σ : ℕ → Exp) :
    gskel (A.subst σ) = gskel A ∧ (A.subst σ).TyShape := by
  induction A generalizing σ with
  | fam => exact ⟨rfl, trivial⟩
  | event => exact ⟨rfl, trivial⟩
  | origin => exact ⟨rfl, trivial⟩
  | stamped ρ A ih =>
    obtain ⟨h₁, h₂⟩ := ih h σ
    exact ⟨by simp [gskel, Exp.subst, h₁], h₂⟩
  | pi q ρ A B ihA ihB =>
    obtain ⟨h₁, h₂⟩ := ihA h.1 σ
    obtain ⟨h₃, h₄⟩ := ihB h.2 (up σ)
    exact ⟨by simp [gskel, Exp.subst, h₁, h₃], h₂, h₄⟩
  | sigma ρ A B ihA ihB =>
    obtain ⟨h₁, h₂⟩ := ihA h.1 σ
    obtain ⟨h₃, h₄⟩ := ihB h.2 (up σ)
    exact ⟨by simp [gskel, Exp.subst, h₁, h₃], h₂, h₄⟩
  | _ => exact absurd h id

/-- Lemma 8.6, reduction: a step keeps the skeleton of a type. -/
theorem gskel_step {A A' : Exp} (h : Step A A') (hA : A.TyShape) :
    gskel A' = gskel A ∧ A'.TyShape := by
  induction h with
  | fam => exact ⟨rfl, trivial⟩
  | origin₁ | origin₂ | origin₃ => exact ⟨rfl, trivial⟩
  | stamped _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA
    exact ⟨by simp [gskel, h₁], h₂⟩
  | pi₁ _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA.1
    exact ⟨by simp [gskel, h₁], h₂, hA.2⟩
  | pi₂ _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA.2
    exact ⟨by simp [gskel, h₁], hA.1, h₂⟩
  | sigma₁ _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA.1
    exact ⟨by simp [gskel, h₁], h₂, hA.2⟩
  | sigma₂ _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA.2
    exact ⟨by simp [gskel, h₁], hA.1, h₂⟩
  | _ => exact absurd hA id

theorem gskel_steps {A A' : Exp} (h : Steps A A') (hA : A.TyShape) :
    gskel A' = gskel A ∧ A'.TyShape := by
  induction h with
  | refl => exact ⟨rfl, hA⟩
  | tail _ hs ih =>
    obtain ⟨h₁, h₂⟩ := ih
    obtain ⟨h₃, h₄⟩ := gskel_step hs h₂
    exact ⟨h₃.trans h₁, h₄⟩

/-- Lemma 8.6, conversion: convertible types have the same skeleton. -/
theorem gskel_conv {A B : Exp} (h : Conv A B) (hA : A.TyShape) (hB : B.TyShape) :
    gskel A = gskel B := by
  obtain ⟨W, h₁, h₂⟩ := h.joinable
  rw [← (gskel_steps h₁ hA).1, ← (gskel_steps h₂ hB).1]

theorem skel_subst {A : Exp} (h : A.TyShape) (σ : ℕ → Exp) : skel (A.subst σ) = skel A := by
  simp [skel, (gskel_subst h σ).1]

theorem skel_step {A A' : Exp} (h : Step A A') (hA : A.TyShape) : skel A' = skel A := by
  simp [skel, (gskel_step h hA).1]

theorem skel_conv {A B : Exp} (h : Conv A B) (hA : A.TyShape) (hB : B.TyShape) :
    skel A = skel B := by
  simp [skel, gskel_conv h hA hB]

/-- The skeleton of an instantiated type. -/
theorem gskel_instType {B : Exp} (h : B.TyShape) (ds : Exp) (Δ : Tel) :
    gskel (instType ds Δ B) = gskel B ∧ (instType ds Δ B).TyShape := by
  obtain ⟨σ, hσ⟩ := instType_eq_subst ds Δ
  rw [hσ]; exact gskel_subst h σ

end Artform.Roles.Calculus
