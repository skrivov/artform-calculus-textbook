import ArtformRoles.Calculus.CheckerComplete
import ArtformRoles.Calculus.Modules

/-!
# Checking signatures, contexts and module classes

Steps (1) and (7) of the reference procedure of Appendix C (`app:checker`),
and the signature and context parts of `thm:decidability`.

* The side conditions of the signature rules are decidable: grade-freeness,
  public terms, ordinary result heads, witness data and old expressions.
* `checkTel`, `checkCtx`, `checkEntry`, `checkSig` check telescopes, contexts,
  one signature entry and a whole signature; every answer carries its proof.
  On the bidirectional fragment they are complete (`checkTel_complete`,
  `checkCtx_complete`, `checkSig_complete`), so signature and context formation
  are decidable there (`decSigWF`, `decCtxWF`).
* The module classes of §10 are decidable (`RenderingOnly`, `FreshWitnessFamily`,
  `EvidenceInhabitant`), and `moduleEvents` computes the qualified event
  namespace of a module (`mem_moduleEvents`).
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Decidable side conditions -/

/-- Grade-freeness is decidable. -/
def Exp.decGradefree : (t : Exp) → Decidable t.gradefree
  | .var _ | .const _ _ | .event | .nil => isTrue trivial
  | .fam _ args => decGradefree args
  | .origin A e t =>
    @instDecidableAnd _ _ (decGradefree A) (@instDecidableAnd _ _ (decGradefree e) (decGradefree t))
  | .stamped _ A => decGradefree A
  | .pi q _ A B =>
    @instDecidableAnd _ _ (decEq q .free)
      (@instDecidableAnd _ _ (decGradefree A) (decGradefree B))
  | .sigma _ A B | .lam _ _ A B | .app A B | .pair A B | .gate _ A B | .cons A B =>
    @instDecidableAnd _ _ (decGradefree A) (decGradefree B)
  | .fst t | .snd t => decGradefree t
  | .stamp t e o | .node _ _ t e o =>
    @instDecidableAnd _ _ (decGradefree t) (@instDecidableAnd _ _ (decGradefree e) (decGradefree o))

instance : DecidablePred Exp.gradefree := Exp.decGradefree

/-- Publicity is decidable. -/
def Exp.decIsPublic : (t : Exp) → Decidable t.IsPublic
  | .var _ | .const _ _ | .event | .nil => isTrue trivial
  | .fam _ args => decIsPublic args
  | .origin A e t | .stamp A e t =>
    @instDecidableAnd _ _ (decIsPublic A) (@instDecidableAnd _ _ (decIsPublic e) (decIsPublic t))
  | .stamped _ A | .fst A | .snd A => decIsPublic A
  | .pi _ _ A B | .sigma _ A B | .lam _ _ A B | .app A B | .pair A B | .gate _ A B
  | .cons A B => @instDecidableAnd _ _ (decIsPublic A) (decIsPublic B)
  | .node .. => isFalse id

instance : DecidablePred Exp.IsPublic := Exp.decIsPublic

/-- Being old over a base of `N` entries is decidable. -/
def Exp.decOld (N : ℕ) : (t : Exp) → Decidable (t.Old N)
  | .var _ | .event | .nil => isTrue trivial
  | .const i _ => Nat.decLt i N
  | .fam a args => @instDecidableAnd _ _ (Nat.decLt a N) (decOld N args)
  | .origin A e t | .stamp A e t =>
    @instDecidableAnd _ _ (decOld N A) (@instDecidableAnd _ _ (decOld N e) (decOld N t))
  | .stamped _ A | .fst A | .snd A => decOld N A
  | .pi _ _ A B | .sigma _ A B | .lam _ _ A B | .app A B | .pair A B | .cons A B =>
    @instDecidableAnd _ _ (decOld N A) (decOld N B)
  | .gate g ds s =>
    @instDecidableAnd _ _ (Nat.decLt g N) (@instDecidableAnd _ _ (decOld N ds) (decOld N s))
  | .node g _ ds t e =>
    @instDecidableAnd _ _ (Nat.decLt g N)
      (@instDecidableAnd _ _ (decOld N ds) (@instDecidableAnd _ _ (decOld N t) (decOld N e)))

instance (N : ℕ) : DecidablePred (Exp.Old N) := Exp.decOld N

/-- Whether the result head of a type is a declared family. -/
def ordinaryHeadB (S : Sig) (A : Exp) : Bool :=
  match A.resultHead with
  | .fam a _ => (S.family? a).isSome
  | _ => false

theorem ordinaryHeadB_iff {S : Sig} {A : Exp} : ordinaryHeadB S A = true ↔ OrdinaryHead S A := by
  unfold ordinaryHeadB OrdinaryHead
  generalize A.resultHead = X
  cases X <;> simp

instance (S : Sig) (A : Exp) : Decidable (OrdinaryHead S A) :=
  decidable_of_iff _ ordinaryHeadB_iff

/-- Whether a type is witness data. -/
def wdataB (S : Sig) : Exp → Bool
  | .fam a _ =>
    match S.family? a with
    | some (_, .witness) => true
    | _ => false
  | .sigma .witness A B => wdataB S A && wdataB S B
  | _ => false

theorem wdataB_iff {S : Sig} : ∀ {A : Exp}, wdataB S A = true ↔ WData S A := by
  intro A
  induction A with
  | fam a args =>
    constructor
    · intro h
      simp only [wdataB] at h
      split at h
      · exact .fam (by assumption)
      · cases h
    · intro h
      cases h with
      | fam hf => simp [wdataB, hf]
  | sigma ρ A B ihA ihB =>
    constructor
    · intro h
      cases ρ <;> simp only [wdataB, Bool.and_eq_true, reduceCtorEq] at h
      exact .sigma (ihA.1 h.1) (ihB.1 h.2)
    · intro h
      cases h with
      | sigma hA hB => simp [wdataB, ihA.2 hA, ihB.2 hB]
  | _ =>
    constructor
    · intro h
      simp [wdataB] at h
    · intro h
      cases h

instance (S : Sig) (A : Exp) : Decidable (WData S A) := decidable_of_iff _ wdataB_iff

/-! ## Telescopes and contexts -/

/-- A formed telescope extends a well-formed context. -/
theorem Deriv.tel_ctxWF {S : Sig} {Γ : Ctx} {Δ : Tel} {δ : Eff}
    (d : Deriv S true (.tel Γ Δ δ)) (hΓ : CtxWF S Γ) : CtxWF S (Δ.reverse ++ Γ) := by
  generalize hj : Judg.tel Γ Δ δ = j at d
  induction d generalizing Γ Δ δ with
  | telNil _ =>
    cases hj
    exact hΓ
  | telCons dA _ _ _ ihΔ =>
    cases hj
    have := ihΔ (.cons hΓ ⟨dA⟩) rfl
    simpa using this
  | _ => cases hj

section Check

variable {S : Sig} (hS : SigWF S)

/-- Check a telescope: each entry's type is formed, with the role it declares,
in the context of the earlier entries. -/
def checkTel (Γ : Ctx) (hΓ : CtxWF S Γ) : (Δ : Tel) →
    Option {δ : Eff // Derivable S true (.tel Γ Δ δ)}
  | [] => some ⟨⊤, ⟨Deriv.mkTelNil⟩⟩
  | (ρ, A) :: Δ =>
    match inferTy hS Γ hΓ A with
    | none => none
    | some ⟨(ρ', α), hA⟩ =>
      if h : ρ' = ρ then
        match checkTel ((ρ, A) :: Γ) (.cons hΓ (h ▸ hA)) Δ with
        | none => none
        | some ⟨δ, hΔ⟩ =>
          some ⟨α ⊓ δ.unbind, let ⟨dA⟩ := hA; let ⟨dΔ⟩ := hΔ; ⟨Deriv.mkTelCons (h ▸ dA) dΔ⟩⟩
      else none

/-- Check a context: each type is formed, with its declared role, in the context
of the later entries. -/
def checkCtx : (Γ : Ctx) → Option (PLift (CtxWF S Γ))
  | [] => some ⟨.nil hS⟩
  | (ρ, A) :: Γ =>
    match checkCtx Γ with
    | none => none
    | some ⟨hΓ⟩ =>
      match inferTy hS Γ hΓ A with
      | none => none
      | some ⟨(ρ', _), hA⟩ => if h : ρ' = ρ then some ⟨.cons hΓ (h ▸ hA)⟩ else none

end Check

/-! ## Signature entries -/

/-- The premises of the signature rule for an entry. -/
def EntryOK (S : Sig) : Entry → Prop
  | .family Δ ρ => (∃ δ, Derivable S true (.tel [] Δ δ)) ∧ ∀ p ∈ Δ, demand p.1 ρ = .free
  | .prim ρ A => (∃ α, Derivable S true (.ty [] ρ A α)) ∧ A.gradefree ∧ OrdinaryHead S A
  | .cert σ A => (∃ α, Derivable S true (.ty [] σ A α)) ∧ σ ≠ .rendering ∧ A.gradefree ∧
      OrdinaryHead S A
  | .attest A t => (∃ θ, Derivable S true (.tm [] .witness t A θ)) ∧ t.IsPublic ∧
      A.gradefree ∧ WData S A
  | .gate Δ σ A ρ B => (∃ δ, Derivable S true (.tel [] Δ δ)) ∧
      (∃ α, Derivable S true (.ty Δ.reverse σ A α)) ∧
      (∃ β, Derivable S true (.ty Δ.reverse ρ B β)) ∧ (ρ = .form ∨ ρ = .presentation) ∧
      σ ≠ .rendering ∧ (∀ p ∈ Δ, demand p.1 ρ = .free) ∧ demand σ ρ ≤ .gated ∧
      B.gradefree ∧ (∀ p ∈ Δ, p.2.gradefree) ∧ A.gradefree

/-- A well-formed signature ends with an entry whose rule premises hold. -/
theorem SigWF.inv_last {S : Sig} {e : Entry} (h : SigWF (S ++ [e])) : SigWF S ∧ EntryOK S e := by
  generalize hT : S ++ [e] = T at h
  cases h with
  | nil => simp at hT
  | family hS hΔ hd =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, and_true] at he
    subst he
    exact ⟨hS, ⟨_, hΔ⟩, hd⟩
  | prim hS hA hgf hhead =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, and_true] at he
    subst he
    exact ⟨hS, ⟨_, hA⟩, hgf, hhead⟩
  | cert hS hA hσ hgf hhead =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, and_true] at he
    subst he
    exact ⟨hS, ⟨_, hA⟩, hσ, hgf, hhead⟩
  | attest hS ht hpub hgf hw =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, and_true] at he
    subst he
    exact ⟨hS, ⟨_, ht⟩, hpub, hgf, hw⟩
  | gate hS hΔ hA hB hρ hσ hd hσρ hBg hΔg hAg =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, and_true] at he
    subst he
    exact ⟨hS, ⟨_, hΔ⟩, ⟨_, hA⟩, ⟨_, hB⟩, hρ, hσ, hd, hσρ, hBg, hΔg, hAg⟩

/-- The signature rules, read forward. -/
theorem SigWF.snoc {S : Sig} {e : Entry} (hS : SigWF S) (h : EntryOK S e) : SigWF (S ++ [e]) := by
  cases e with
  | family Δ ρ => obtain ⟨⟨_, hΔ⟩, hd⟩ := h; exact .family hS hΔ hd
  | prim ρ A => obtain ⟨⟨_, hA⟩, hgf, hhead⟩ := h; exact .prim hS hA hgf hhead
  | cert σ A => obtain ⟨⟨_, hA⟩, hσ, hgf, hhead⟩ := h; exact .cert hS hA hσ hgf hhead
  | attest A t => obtain ⟨⟨_, ht⟩, hpub, hgf, hw⟩ := h; exact .attest hS ht hpub hgf hw
  | gate Δ σ A ρ B =>
    obtain ⟨⟨_, hΔ⟩, ⟨_, hA⟩, ⟨_, hB⟩, hρ, hσ, hd, hσρ, hBg, hΔg, hAg⟩ := h
    exact .gate hS hΔ hA hB hρ hσ hd hσρ hBg hΔg hAg

section CheckSig

variable {S : Sig} (hS : SigWF S)

/-- Check one entry over a well-formed signature. -/
def checkEntry : (e : Entry) → Option (PLift (SigWF (S ++ [e])))
  | .family Δ ρ =>
    match checkTel hS [] (.nil hS) Δ with
    | none => none
    | some ⟨_, hΔ⟩ =>
      if h : ∀ p ∈ Δ, demand p.1 ρ = .free then some ⟨hS.snoc ⟨⟨_, hΔ⟩, h⟩⟩ else none
  | .prim ρ A =>
    match inferTy hS [] (.nil hS) A with
    | none => none
    | some ⟨(ρ', α), hA⟩ =>
      if h : ρ' = ρ ∧ A.gradefree ∧ OrdinaryHead S A then
        some ⟨hS.snoc ⟨⟨α, h.1 ▸ hA⟩, h.2.1, h.2.2⟩⟩
      else none
  | .cert σ A =>
    match inferTy hS [] (.nil hS) A with
    | none => none
    | some ⟨(σ', α), hA⟩ =>
      if h : σ' = σ ∧ σ ≠ .rendering ∧ A.gradefree ∧ OrdinaryHead S A then
        some ⟨hS.snoc ⟨⟨α, h.1 ▸ hA⟩, h.2.1, h.2.2.1, h.2.2.2⟩⟩
      else none
  | .attest A t =>
    match inferTy hS [] (.nil hS) A with
    | none => none
    | some ⟨(ρ', α), hA⟩ =>
      if hW : ρ' = .witness then
        match check hS [] (.nil hS) t .witness A ⟨α, hW ▸ hA⟩ with
        | none => none
        | some ⟨θ, ht⟩ =>
          if h : t.IsPublic ∧ A.gradefree ∧ WData S A then
            some ⟨hS.snoc ⟨⟨θ, ht⟩, h.1, h.2.1, h.2.2⟩⟩
          else none
      else none
  | .gate Δ σ A ρ B =>
    match checkTel hS [] (.nil hS) Δ with
    | none => none
    | some ⟨δ, hΔ⟩ =>
      have hΓ : CtxWF S Δ.reverse := by
        obtain ⟨d⟩ := hΔ
        simpa using d.tel_ctxWF (.nil hS)
      match inferTy hS Δ.reverse hΓ A, inferTy hS Δ.reverse hΓ B with
      | some ⟨(σ', α), hA⟩, some ⟨(ρ', β), hB⟩ =>
        if h : σ' = σ ∧ ρ' = ρ ∧ (ρ = .form ∨ ρ = .presentation) ∧ σ ≠ .rendering ∧
            (∀ p ∈ Δ, demand p.1 ρ = .free) ∧ demand σ ρ ≤ .gated ∧ B.gradefree ∧
            (∀ p ∈ Δ, p.2.gradefree) ∧ A.gradefree then
          some ⟨hS.snoc ⟨⟨δ, hΔ⟩, ⟨α, h.1 ▸ hA⟩, ⟨β, h.2.1 ▸ hB⟩, h.2.2.1, h.2.2.2.1,
            h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
            h.2.2.2.2.2.2.2.2⟩⟩
        else none
      | _, _ => none

end CheckSig

/-- Check a signature given last entry first. -/
def checkSigRev : (R : List Entry) → Option (PLift (SigWF R.reverse))
  | [] => some ⟨.nil⟩
  | e :: R =>
    match checkSigRev R with
    | none => none
    | some ⟨hR⟩ =>
      match checkEntry hR e with
      | none => none
      | some ⟨h⟩ => some ⟨by rw [List.reverse_cons]; exact h⟩

/-- Step (1) of the reference procedure: check an ordered signature entry by
entry. -/
def checkSig (S : Sig) : Option (PLift (SigWF S)) :=
  match checkSigRev S.reverse with
  | none => none
  | some ⟨h⟩ => some ⟨by rw [List.reverse_reverse] at h; exact h⟩

/-! ## Completeness on the fragment -/

/-- An entry whose declared types are in the fragment, and whose attested term
is checkable. -/
def Entry.InFragment : Entry → Prop
  | .family Δ _ => ∀ p ∈ Δ, p.2.TyFr
  | .prim _ A | .cert _ A => A.TyFr
  | .attest A t => A.TyFr ∧ t.Chk
  | .gate Δ _ A _ B => (∀ p ∈ Δ, p.2.TyFr) ∧ A.TyFr ∧ B.TyFr

section Complete

variable {S : Sig} (hS : SigWF S)

theorem checkTel_complete : ∀ (Δ : Tel) {Γ : Ctx} (hΓ : CtxWF S Γ) {δ : Eff},
    (∀ p ∈ Δ, p.2.TyFr) → Derivable S true (.tel Γ Δ δ) → (checkTel hS Γ hΓ Δ).isSome
  | [], _, _, _, _, _ => rfl
  | (ρ, A) :: Δ, Γ, hΓ, δ, hfr, ⟨d⟩ => by
    cases d with
    | telCons dA dΔ _ =>
      obtain ⟨rA, hrA⟩ := (complete hS A).1 hΓ (hfr (ρ, A) (by simp)) ⟨dA⟩
      have hrole := rA.role ⟨dA⟩
      obtain ⟨⟨ρ', α⟩, hA'⟩ := rA
      simp only at hrole
      subst hrole
      have hΔ := checkTel_complete Δ (CtxWF.cons hΓ hA') (fun p hp => hfr p (by simp [hp])) ⟨dΔ⟩
      obtain ⟨⟨δ', hΔ'⟩, hrΔ⟩ := Option.isSome_iff_exists.mp hΔ
      simp only [checkTel, hrA, ↓reduceDIte, hrΔ, Option.isSome_some]

theorem checkCtx_complete : ∀ (Γ : Ctx), CtxWF S Γ → (∀ p ∈ Γ, p.2.TyFr) →
    (checkCtx hS Γ).isSome
  | [], _, _ => rfl
  | (ρ, A) :: Γ, hΓ, hfr => by
    cases hΓ with
    | cons hΓ' hA =>
      obtain ⟨⟨hΓ''⟩, hr⟩ := Option.isSome_iff_exists.mp
        (checkCtx_complete Γ hΓ' (fun p hp => hfr p (by simp [hp])))
      obtain ⟨rA, hrA⟩ := (complete hS A).1 hΓ'' (hfr (ρ, A) (by simp)) hA
      have hrole := rA.role hA
      obtain ⟨⟨ρ', α⟩, hA'⟩ := rA
      simp only at hrole
      subst hrole
      simp only [checkCtx, hr, hrA, ↓reduceDIte, Option.isSome_some]

theorem checkEntry_complete {e : Entry} (h : EntryOK S e) (hfr : e.InFragment) :
    (checkEntry hS e).isSome := by
  cases e with
  | family Δ ρ =>
    obtain ⟨⟨δ, hΔ⟩, hd⟩ := h
    obtain ⟨⟨δ', hΔ'⟩, hr⟩ := Option.isSome_iff_exists.mp
      (checkTel_complete hS Δ (.nil hS) hfr hΔ)
    simp only [checkEntry, hr]
    split
    · rfl
    · next hneg => exact absurd hd hneg
  | prim ρ A =>
    obtain ⟨⟨α, hA⟩, hgf, hhead⟩ := h
    obtain ⟨rA, hrA⟩ := (complete hS A).1 (.nil hS) hfr hA
    have hrole := rA.role hA
    obtain ⟨⟨ρ', α'⟩, hA'⟩ := rA
    simp only at hrole
    subst hrole
    simp only [checkEntry, hrA]
    split
    · rfl
    · next hneg => exact absurd (by simp_all) hneg
  | cert σ A =>
    obtain ⟨⟨α, hA⟩, hσ, hgf, hhead⟩ := h
    obtain ⟨rA, hrA⟩ := (complete hS A).1 (.nil hS) hfr hA
    have hrole := rA.role hA
    obtain ⟨⟨σ', α'⟩, hA'⟩ := rA
    simp only at hrole
    subst hrole
    simp only [checkEntry, hrA]
    split
    · rfl
    · next hneg => exact absurd (by simp_all) hneg
  | attest A t =>
    obtain ⟨⟨θ, ht⟩, hpub, hgf, hw⟩ := h
    obtain ⟨γ, hA⟩ := Derivable.ty_of_tm ht
    obtain ⟨rA, hrA⟩ := (complete hS A).1 (.nil hS) hfr.1 hA
    have hrole := rA.role hA
    obtain ⟨⟨ρ', α'⟩, hA'⟩ := rA
    simp only at hrole
    subst hrole
    obtain ⟨⟨θ', ht'⟩, hrt⟩ := (complete hS t).2.2.1 (.nil hS) ⟨α', hA'⟩ hfr.2 ht
    simp only [checkEntry, hrA, ↓reduceDIte, hrt]
    split
    · rfl
    · next hneg => exact absurd ⟨hpub, hgf, hw⟩ hneg
  | gate Δ σ A ρ B =>
    obtain ⟨⟨δ, hΔ⟩, ⟨α, hA⟩, ⟨β, hB⟩, hρ, hσ, hd, hσρ, hBg, hΔg, hAg⟩ := h
    obtain ⟨⟨δ', hΔ'⟩, hrΔ⟩ := Option.isSome_iff_exists.mp
      (checkTel_complete hS Δ (.nil hS) hfr.1 hΔ)
    have hΓ : CtxWF S Δ.reverse := by
      obtain ⟨d⟩ := hΔ'
      simpa using d.tel_ctxWF (.nil hS)
    obtain ⟨rA, hrA⟩ := (complete hS A).1 hΓ hfr.2.1 hA
    obtain ⟨rB, hrB⟩ := (complete hS B).1 hΓ hfr.2.2 hB
    have hσ' := rA.role hA
    have hρ' := rB.role hB
    obtain ⟨⟨σ', α'⟩, hA'⟩ := rA
    obtain ⟨⟨ρ', β'⟩, hB'⟩ := rB
    simp only at hσ' hρ'
    subst hσ' hρ'
    simp only [checkEntry, hrΔ, hrA, hrB]
    split
    · rfl
    · next hneg => exact absurd ⟨trivial, trivial, hρ, hσ, hd, hσρ, hBg, hΔg, hAg⟩ hneg

end Complete

theorem checkSigRev_complete : ∀ (R : List Entry), SigWF R.reverse →
    (∀ e ∈ R, e.InFragment) → (checkSigRev R).isSome
  | [], _, _ => rfl
  | e :: R, h, hfr => by
    rw [List.reverse_cons] at h
    obtain ⟨hR, he⟩ := h.inv_last
    obtain ⟨⟨hR'⟩, hr⟩ := Option.isSome_iff_exists.mp
      (checkSigRev_complete R hR (fun e' he' => hfr e' (by simp [he'])))
    obtain ⟨⟨he'⟩, hre⟩ := Option.isSome_iff_exists.mp
      (checkEntry_complete hR' he (hfr e (by simp)))
    simp only [checkSigRev, hr, hre, Option.isSome_some]

/-- Signature checking succeeds on every well-formed signature of the fragment. -/
theorem checkSig_complete {S : Sig} (hS : SigWF S) (hfr : ∀ e ∈ S, e.InFragment) :
    (checkSig S).isSome := by
  obtain ⟨⟨h⟩, hr⟩ := Option.isSome_iff_exists.mp
    (checkSigRev_complete S.reverse (by rw [List.reverse_reverse]; exact hS)
      (fun e he => hfr e (by simpa using he)))
  simp only [checkSig, hr, Option.isSome_some]

/-- `thm:decidability`, signatures: whether a signature of the fragment is well
formed is decidable. -/
def decSigWF (S : Sig) (hfr : ∀ e ∈ S, e.InFragment) : Decidable (SigWF S) :=
  match h : checkSig S with
  | some ⟨hS⟩ => isTrue hS
  | none => isFalse fun hS => by
      have := checkSig_complete hS hfr
      rw [h] at this
      cases this

/-- `thm:decidability`, contexts: over a well-formed signature, whether a
context of the fragment is well formed is decidable. -/
def decCtxWF {S : Sig} (hS : SigWF S) (Γ : Ctx) (hfr : ∀ p ∈ Γ, p.2.TyFr) :
    Decidable (CtxWF S Γ) :=
  match h : checkCtx hS Γ with
  | some ⟨hΓ⟩ => isTrue hΓ
  | none => isFalse fun hΓ => by
      have := checkCtx_complete hS Γ hΓ hfr
      rw [h] at this
      cases this

/-! ## Module classes and event namespaces (step 7) -/

/-- Whether an entry may occur in a rendering-only module. -/
def Entry.renderingOnlyB : Entry → Bool
  | .family _ ρ | .prim ρ _ => ρ == .rendering
  | _ => false

theorem Entry.renderingOnlyB_iff (e : Entry) : e.renderingOnlyB = true ↔
    (∃ Δ, e = .family Δ .rendering) ∨ (∃ A, e = .prim .rendering A) := by
  cases e <;> simp [Entry.renderingOnlyB]

instance (M : Sig) : Decidable (RenderingOnly M) :=
  decidable_of_iff (∀ e ∈ M, e.renderingOnlyB = true) (by
    simp only [RenderingOnly, Entry.renderingOnlyB_iff])

/-- Whether an entry may occur in a fresh-witness-family module over a base of
`N` entries. -/
def Entry.freshWitnessB (N : ℕ) : Entry → Bool
  | .family _ ρ => ρ == .witness
  | .prim _ A =>
    match A.resultHead with
    | .fam a _ => decide (N ≤ a)
    | _ => false
  | _ => false

theorem Entry.freshWitnessB_iff (N : ℕ) (e : Entry) : e.freshWitnessB N = true ↔
    (∃ Δ, e = .family Δ .witness) ∨
      (∃ ρ A a args, e = .prim ρ A ∧ A.resultHead = .fam a args ∧ N ≤ a) := by
  cases e with
  | prim ρ A =>
    simp only [Entry.freshWitnessB, reduceCtorEq, exists_const, false_or, Entry.prim.injEq]
    constructor
    · intro h
      split at h
      · exact ⟨ρ, A, _, _, ⟨rfl, rfl⟩, by assumption, by simpa using h⟩
      · cases h
    · rintro ⟨ρ', A', a, args, ⟨rfl, rfl⟩, h₁, h₂⟩
      rw [h₁]
      simpa using h₂
  | _ => simp [Entry.freshWitnessB]

instance (N : ℕ) (M : Sig) : Decidable (FreshWitnessFamily N M) :=
  decidable_of_iff (∀ e ∈ M, e.freshWitnessB N = true) (by
    simp only [FreshWitnessFamily, Entry.freshWitnessB_iff])

/-- Whether an entry may occur in an evidence-inhabitant module over a base of
`N` entries. -/
def Entry.evidenceB (N : ℕ) : Entry → Bool
  | .cert σ A => σ == .witness && decide (A.Old N)
  | .attest A t => decide (A.Old N) && decide (t.Old N)
  | _ => false

theorem Entry.evidenceB_iff (N : ℕ) (e : Entry) : e.evidenceB N = true ↔
    (∃ A, e = .cert .witness A ∧ A.Old N) ∨ (∃ A t, e = .attest A t ∧ A.Old N ∧ t.Old N) := by
  cases e <;> simp [Entry.evidenceB]

instance (N : ℕ) (M : Sig) : Decidable (EvidenceInhabitant N M) :=
  decidable_of_iff (M ≠ [] ∧ ∀ e ∈ M, e.evidenceB N = true) (by
    simp only [EvidenceInhabitant, Entry.evidenceB_iff])

/-- The qualified event namespace of the module `M` over `S`: the event
constant of each of its certificates and attestations. -/
def moduleEvents (S M : Sig) : List Exp :=
  (List.range M.length).filterMap fun j =>
    match M[j]? with
    | some (Entry.cert _ _) => some (.const (S.length + j) 1)
    | some (Entry.attest _ _) => some (.const (S.length + j) 0)
    | _ => none

theorem mem_moduleEvents {S M : Sig} {e : Exp} : e ∈ moduleEvents S M ↔ ModuleEvent S M e := by
  unfold moduleEvents ModuleEvent
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩
    refine ⟨S.length + j, by omega, ?_⟩
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    split at h
    · rename_i σ A hM
      exact .inl ⟨σ, A, hM, (Option.some.inj h).symm⟩
    · rename_i A t hM
      exact .inr ⟨A, t, hM, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨i, hi, h⟩
    have key : ∀ x, (S ++ M)[i]? = some x →
        i - S.length < M.length ∧ M[i - S.length]? = some x := by
      intro x hx
      rw [List.getElem?_append_right hi] at hx
      exact ⟨(List.getElem?_eq_some_iff.mp hx).1, hx⟩
    refine ⟨i - S.length, ?_⟩
    rcases h with ⟨σ, A, hM, rfl⟩ | ⟨A, t, hM, rfl⟩
    · obtain ⟨hl, hM'⟩ := key _ hM
      refine ⟨hl, ?_⟩
      rw [hM']
      simp only [Option.some.injEq]
      congr 1
      omega
    · obtain ⟨hl, hM'⟩ := key _ hM
      refine ⟨hl, ?_⟩
      rw [hM']
      simp only [Option.some.injEq]
      congr 1
      omega

end Artform.Roles.Calculus
