import ArtformRoles.Calculus.CheckerComplete

/-!
# Forms and construction history

Part II of the paper, *The book in the calculus* (`sec:artforms`): the book's
forms in the calculus (`sec:forms-calculus`), and a computable test for normal
forms that every example uses.

* `Exp.redexFree`: a computable check for normal forms (`Exp.redexFree_normal`).
* `Book.artforms`: the families `FinCode` and `Hist` of the Artforms signature,
  and the type `Form = Σ(A :_F FinCode). Hist(A)` of a carrier with its
  construction history.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## A computable test for normal forms -/

/-- No redex occurs in the expression. -/
def Exp.redexFree : Exp → Bool
  | var _ | const _ _ | event | nil => true
  | fam _ args => args.redexFree
  | origin A e t => A.redexFree && e.redexFree && t.redexFree
  | stamped _ A => A.redexFree
  | pi _ _ A B => A.redexFree && B.redexFree
  | sigma _ A B => A.redexFree && B.redexFree
  | lam _ _ A t => A.redexFree && t.redexFree
  | app t u =>
    (match t with
      | lam .. => false
      | _ => true) && t.redexFree && u.redexFree
  | pair t u => t.redexFree && u.redexFree
  | fst t =>
    (match t with
      | pair .. => false
      | _ => true) && t.redexFree
  | snd t =>
    (match t with
      | pair .. => false
      | _ => true) && t.redexFree
  | stamp t e o => t.redexFree && e.redexFree && o.redexFree
  | gate _ ds s =>
    (match s with
      | stamp .. => false
      | _ => true) && ds.redexFree && s.redexFree
  | node _ _ ds t e => ds.redexFree && t.redexFree && e.redexFree
  | cons t ts => t.redexFree && ts.redexFree

/-- An expression without a redex is normal. -/
theorem Exp.redexFree_normal {t : Exp} (h : t.redexFree = true) : Normal t := by
  intro t' hs
  induction hs with
  | beta => simp [Exp.redexFree] at h
  | fstPair => simp [Exp.redexFree] at h
  | sndPair => simp [Exp.redexFree] at h
  | record => simp [Exp.redexFree] at h
  | fam _ ih => exact ih h
  | origin₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | origin₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | origin₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | stamped _ ih => exact ih h
  | pi₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | pi₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | sigma₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | sigma₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | lam₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | lam₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | app₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | app₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | pair₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | pair₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | fst _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | snd _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | stamp₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | stamp₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | stamp₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | gate₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | gate₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | node₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | node₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | node₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | cons₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | cons₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2


/-! ## Forms and construction history -/

namespace Book

/-- `FinCode`, at declaration `0`. -/
abbrev finCode : Exp := .fam 0 .nil
/-- `Hist(A)`, at declaration `1`. -/
abbrev hist (A : Exp) : Exp := .fam 1 (.cons A .nil)
/-- `Form = Σ(A :_F FinCode). Hist(A)`: a carrier with its construction history. -/
abbrev form : Exp := .sigma .form finCode (hist (.var 0))

/-- The two families of the Artforms signature: `FinCode` and `Hist`. -/
def artforms : Sig := [.family [] .form, .family [(.form, finCode)] .form]

/-- `⊢_F FinCode type`. -/
def dFinCode {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form)) {Γ : Ctx} :
    Deriv S true (.ty Γ .form finCode (Eff.unit (.decl 0 0) ⊓ ⊤)) :=
  .mkTyFam hS h0 .mkSpineNil

/-- `⊢_F Hist(A) type`, for a term `A` of `FinCode`. -/
def dHist {S : Sig} (hS : SigWF S) (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    {Γ : Ctx} {A : Exp} {α : Eff} (dA : Deriv S true (.tm Γ .form A finCode α)) :
    Deriv S true (.ty Γ .form (hist A) (Eff.unit (.decl 1 0) ⊓ (α ⊓ ⊤))) :=
  .mkTyFam hS h1 (.mkSpineCons dA .mkSpineNil)

/-- `⊢_F Form type`. -/
def dForm {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form)) {Γ : Ctx} :
    Deriv S true (.ty Γ .form form ((Eff.unit (.decl 0 0) ⊓ ⊤) ⊓
      (Eff.unit (.decl 1 0) ⊓ (Eff.unit (.var 0) ⊓ ⊤)).unbind)) :=
  .mkTySigma (dFinCode hS h0) (dHist hS h1 (.mkVar (A := finCode) rfl (dFinCode hS h0)))

theorem artforms_wf : SigWF artforms := by
  have h₀ : SigWF [.family [] .form] := .family (S := []) .nil ⟨.mkTelNil⟩ (fun _ h => by cases h)
  refine .family (S := [.family [] .form]) h₀ ⟨.mkTelCons (dFinCode h₀ rfl) .mkTelNil⟩ ?_
  intro p hp
  rw [List.mem_singleton.mp hp]
  rfl


end Book

end Artform.Roles.Calculus
