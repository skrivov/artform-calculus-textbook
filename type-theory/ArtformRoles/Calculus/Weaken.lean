import ArtformRoles.Calculus.Rename

/-!
# Weakening, validity of accepted derivations, raw derivations

* `Deriv.valid_tm`, `Deriv.valid_ty`: the effect of an accepted conclusion is
  policy valid (rule Accept).
* `Deriv.toRaw`: an accepted derivation is a raw one.
* `Deriv.weaken_ty`, `Deriv.weaken_tm`: weakening by one variable extends the
  effect by `∞` at the new variable (§8.2: "Weakening is the special case that
  extends an effect by `∞`").
* `CtxWF.var_formed`: in a well-formed context, the type of each variable is
  well formed.
-/

namespace Artform.Roles.Calculus

open Exp

/-- The effect of an accepted conclusion is valid. -/
theorem Deriv.valid {S : Sig} {j : Judg} (d : Deriv S true j) :
    match j with
    | .ty Γ ρ _ ε => Valid S Γ ρ ε
    | .tm Γ ρ _ _ ε => Valid S Γ ρ ε
    | _ => True := by
  induction d with
  | tyFam _ _ _ hv => exact hv rfl
  | tyEvent hε => subst hε; exact fun _ _ _ => le_top
  | tyOrigin _ _ _ _ hv => exact hv rfl
  | tyStamped _ _ _ hv => exact hv rfl
  | tyPi _ _ _ _ hv => exact hv rfl
  | tySigma _ _ _ hv => exact hv rfl
  | var _ _ _ _ hv => exact hv rfl
  | const _ _ _ hv => exact hv rfl
  | lam _ _ _ _ _ hv => exact hv rfl
  | app _ _ _ _ _ hv => exact hv rfl
  | pair _ _ _ _ hv => exact hv rfl
  | fst _ _ hv => exact hv rfl
  | snd _ _ _ hv => exact hv rfl
  | stamp _ _ _ _ _ hv => exact hv rfl
  | gate _ _ _ _ _ _ hv => exact hv rfl
  | node _ _ _ _ _ _ _ hv => exact hv rfl
  | conv _ _ _ ih _ => exact ih
  | spineNil | spineCons | telNil | telCons => trivial

theorem Deriv.valid_tm {S : Sig} {Γ : Ctx} {ρ : Role} {t A : Exp} {ε : Eff}
    (d : Deriv S true (.tm Γ ρ t A ε)) : Valid S Γ ρ ε := d.valid

theorem Deriv.valid_ty {S : Sig} {Γ : Ctx} {ρ : Role} {A : Exp} {ε : Eff}
    (d : Deriv S true (.ty Γ ρ A ε)) : Valid S Γ ρ ε := d.valid

/-- An accepted derivation is a raw derivation. -/
noncomputable def Deriv.toRaw {S : Sig} {j : Judg} (d : Deriv S true j) : Deriv S false j := by
  induction d with
  | tyFam hS _ hε _ ih => exact .tyFam hS ih hε (by simp)
  | tyEvent hε => exact .tyEvent hε
  | tyOrigin _ _ _ hε _ ihA ihe iht => exact .tyOrigin ihA ihe iht hε (by simp)
  | tyStamped _ hσ hε _ ih => exact .tyStamped ih hσ hε (by simp)
  | tyPi _ _ hq hε _ ihA ihB => exact .tyPi ihA ihB hq hε (by simp)
  | tySigma _ _ hε _ ihA ihB => exact .tySigma ihA ihB hε (by simp)
  | var hΓ hC _ hε _ ih => exact .var hΓ hC ih hε (by simp)
  | const hc _ hε _ ih => exact .const hc ih hε (by simp)
  | lam _ _ hq _ hε _ ihA iht ihC => exact .lam ihA iht hq ihC hε (by simp)
  | app _ _ hC _ hε _ ihf ihu ihC => exact .app ihf ihu hC ihC hε (by simp)
  | pair _ _ _ hε _ iht ihu ihC => exact .pair iht ihu ihC hε (by simp)
  | fst _ _ _ ihp ihA => exact .fst ihp ihA (by simp)
  | snd _ hC _ _ ihp ihC => exact .snd ihp hC ihC (by simp)
  | stamp _ _ _ _ hε _ iht ihe iho ihC => exact .stamp iht ihe iho ihC hε (by simp)
  | gate hg _ _ hC _ hε _ ihds ihs ihC => exact .gate hg ihds ihs hC ihC hε (by simp)
  | node hg _ _ _ hC _ hε _ ihds iht ihe ihC => exact .node hg ihds iht ihe hC ihC hε (by simp)
  | conv _ hAB _ iht ihB => exact .conv iht hAB ihB
  | spineNil hε => exact .spineNil hε
  | spineCons _ _ hε iht ihts => exact .spineCons iht ihts hε
  | telNil hε => exact .telNil hε
  | telCons _ _ hε ihA ihΔ => exact .telCons ihA ihΔ hε

theorem ite_pos_eq {P : Prop} [Decidable P] (h : P) (a b : Grade) :
    (if P then a else b) = a := by simp [h]

theorem ite_neg_eq {P : Prop} [Decidable P] (h : ¬P) (a b : Grade) :
    (if P then a else b) = b := by simp [h]

/-- The matrix action of the renaming `i ↦ i + c` on a variable or a
declaration. -/
theorem Eff.actVars_unit_add (n c : ℕ) (ε : Eff) (z : Atom) :
    Eff.actVars n (fun j => Eff.unit (.var (j + c))) ε z =
      match z with
      | .var k => if c ≤ k ∧ k < n + c then ε (.var (k - c)) else ⊤
      | .decl _ _ => ⊤ := by
  induction n generalizing c ε with
  | zero =>
    cases z with
    | var k => exact (ite_neg_eq (by omega) _ _).symm
    | decl => rfl
  | succ n ih =>
    have hM : (fun j => (fun j => Eff.unit (.var (j + c))) (j + 1)) =
        fun j => Eff.unit (.var (j + (c + 1))) := by
      funext j; simp only [show j + 1 + c = j + (c + 1) by omega]
    simp only [Eff.actVars, Pi.inf_apply, Eff.scale_apply]
    rw [hM, ih]
    cases z with
    | var k =>
      simp only [Eff.unbind_var, Nat.zero_add]
      rcases lt_trichotomy k c with hk | rfl | hk
      · rw [Eff.unit_ne (by simp; omega), ite_neg_eq (by omega), ite_neg_eq (by omega)]
        simp
      · rw [Eff.unit_self, ite_neg_eq (by omega), ite_pos_eq (by omega)]
        simp
      · rw [Eff.unit_ne (by simp; omega)]
        simp only [le_top, sup_of_le_right, top_inf_eq]
        by_cases h : k < n + (c + 1)
        · rw [ite_pos_eq (by omega), ite_pos_eq (by omega)]
          congr 2; omega
        · rw [ite_neg_eq (by omega), ite_neg_eq (by omega)]
    | decl a k =>
      rw [Eff.unit_ne (by simp)]
      simp

/-- Renaming by `i ↦ i + 1` extends an effect by `∞` at the new variable. -/
theorem Eff.act_succ {m n : ℕ} {ε : Eff} (hε : ε.Scoped m n) :
    Eff.act n (fun j => Eff.unit (.var (j + 1))) ε = Eff.bind ε := by
  funext z
  simp only [Eff.act, Pi.inf_apply, Eff.actVars_unit_add]
  cases z with
  | var k =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Eff.declPart_var, top_inf_eq, Eff.bind_var_succ]
      split_ifs with h
      · rfl
      · rw [hε.1 k (by omega)]
  | decl a k => simp

/-- The identity matrix action keeps the variables below `n`. -/
theorem Eff.act_id {m n : ℕ} {ε : Eff} (hε : ε.Scoped m n) :
    Eff.act n (fun j => Eff.unit (.var j)) ε = ε := by
  funext z
  have h := Eff.actVars_unit_add n 0 ε z
  simp only [Nat.add_zero] at h
  simp only [Eff.act, Pi.inf_apply, h]
  cases z with
  | var k =>
    simp only [Eff.declPart_var, top_inf_eq, Nat.sub_zero]
    split_ifs with hk
    · rfl
    · rw [hε.1 k (by omega)]
  | decl a k => simp

/-- Weakening a formation judgment by one variable. -/
theorem Deriv.weaken_ty {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp}
    {ε : Eff} (d : Deriv S acc (.ty Γ ρ A ε)) (p : Role × Exp) :
    Derivable S acc (.ty (p :: Γ) ρ A.shift ε.bind) := by
  obtain ⟨d'⟩ := d.rename hS (RenOK.succ Γ p)
  simp only [Judg.substJ] at d'
  rw [Eff.act_succ d.scoped.2, ← ren_eq_subst] at d'
  exact ⟨d'⟩

/-- Weakening a typing judgment by one variable. -/
theorem Deriv.weaken_tm {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {ρ : Role}
    {t A : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ t A ε)) (p : Role × Exp) :
    Derivable S acc (.tm (p :: Γ) ρ t.shift A.shift ε.bind) := by
  obtain ⟨d'⟩ := d.rename hS (RenOK.succ Γ p)
  simp only [Judg.substJ] at d'
  rw [Eff.act_succ d.scoped.2.2, ← ren_eq_subst, ← ren_eq_subst] at d'
  exact ⟨d'⟩

/-- In a well-formed context, the type of every variable is well formed. -/
theorem CtxWF.var_formed {S : Sig} {Γ : Ctx} (hΓ : CtxWF S Γ) :
    ∀ {i : ℕ} {ρ : Role} {A : Exp}, Γ[i]? = some (ρ, A) →
      ∃ α, Derivable S true (.ty Γ ρ (A.ren (· + (i + 1))) α) := by
  induction hΓ with
  | nil => intro i ρ A h; simp at h
  | @cons Γ ρ' A' α' hΓ hA ih =>
    have hS : SigWF S := by
      clear ih hA; induction hΓ with
      | nil h => exact h
      | cons _ _ ih => exact ih
    intro i ρ A h
    obtain ⟨dA⟩ := hA
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨d'⟩ := dA.weaken_ty hS (ρ', A')
      refine ⟨α'.bind, ⟨?_⟩⟩
      have e : A'.ren (· + (0 + 1)) = A'.shift := by congr 1
      rw [e]; exact d'
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨α, ⟨d⟩⟩ := ih h
      obtain ⟨d'⟩ := d.weaken_ty hS (ρ', A')
      refine ⟨α.bind, ⟨?_⟩⟩
      have e : A.ren (· + (i + 1 + 1)) = (A.ren (· + (i + 1))).shift := by
        rw [shift, ren_ren]; congr 1
      rw [e]; exact d'

theorem CtxWF.sigWF {S : Sig} {Γ : Ctx} (hΓ : CtxWF S Γ) : SigWF S := by
  induction hΓ with
  | nil h => exact h
  | cons _ _ ih => exact ih

end Artform.Roles.Calculus
