import ArtformRoles.Calculus.Weaken

/-!
# Substitution

Lemma 8.3 (exact single substitution) and Theorem 8.4 (policy-preserving
substitution) of the paper.

* `SubstOK S acc σ M Γ Δ`: `σ` maps every variable of `Γ` to a term over `Δ` of
  the substituted type, `var i` to a term of effect `M i`.
* `Deriv.subst`: a derivation survives the substitution, and its effect becomes
  the matrix action `M ⋆ ε` (simultaneous substitution has effect `M_θ ⋆ ε`).
  For accepted derivations the result is accepted again: the policy is path
  closed (Theorem 8.4). For raw derivations it is the exact effect of
  Lemma 8.3.
* `Deriv.inst_tm`, `Deriv.inst_ty`: the single substitution `J[u/x]` has effect
  `ε⟨x := η⟩ = (ε ∖ x) ⊕ (ε(x) ⊗ η)`, equation (2) of the paper.
-/

namespace Artform.Roles.Calculus

open Exp

/-- A substitution of `Γ` into `Δ`: the term put for `var i` has the
substituted type of `var i`, at its role, with effect `M i`. -/
def SubstOK (S : Sig) (acc : Bool) (σ : ℕ → Exp) (M : ℕ → Eff) (Γ Δ : Ctx) : Prop :=
  ∀ i ρ A, Γ[i]? = some (ρ, A) →
    Derivable S acc (.tm Δ ρ (σ i) ((A.ren (· + (i + 1))).subst σ) (M i))

theorem SubstOK.valid {S : Sig} {acc : Bool} {σ : ℕ → Exp} {M : ℕ → Eff} {Γ Δ : Ctx}
    (h : SubstOK S acc σ M Γ Δ) (hacc : acc = true) :
    ∀ i r, roleOf S Γ (.var i) = some r → Valid S Δ r (M i) := by
  subst hacc
  intro i r hr
  simp only [roleOf, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', A⟩, hi, rfl⟩ := hr
  obtain ⟨d⟩ := h i r' A hi
  exact d.valid_tm

theorem SubstOK.up {S : Sig} (hS : SigWF S) {acc : Bool} {σ : ℕ → Exp} {M : ℕ → Eff}
    {Γ Δ : Ctx} (h : SubstOK S acc σ M Γ Δ) {ρ : Role} {A : Exp} {α : Eff}
    (dA : Deriv S acc (.ty Δ ρ (A.subst σ) α)) :
    SubstOK S acc (Exp.up σ) (Eff.upM M) ((ρ, A) :: Γ) ((ρ, A.subst σ) :: Δ) := by
  intro i ρ' A' hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨dA'⟩ := dA.weaken_ty hS (ρ, A.subst σ)
    have e : (A.ren (· + (0 + 1))).subst (Exp.up σ) = (A.subst σ).ren (· + (0 + 1)) := by
      rw [subst_ren, ren_subst]; rfl
    have e' : (A.subst σ).ren (· + (0 + 1)) = (A.subst σ).shift := by congr 1
    refine ⟨.var rfl (by rw [e]) (by rw [e, e']; exact dA') rfl
      (fun _ => valid_unit_var (by simp [roleOf]))⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    obtain ⟨d⟩ := h i ρ' A' hi
    obtain ⟨d'⟩ := d.weaken_tm hS (ρ, A.subst σ)
    have e : (A'.ren (· + (i + 1 + 1))).subst (Exp.up σ) =
        ((A'.ren (· + (i + 1))).subst σ).shift := by
      rw [shift, ren_subst, subst_ren, subst_ren]
      refine subst_ext (fun j => ?_) A'
      simp only [Function.comp_apply]
      rw [show j + (i + 1 + 1) = j + (i + 1) + 1 by omega]
      rfl
    rw [e]
    exact ⟨d'⟩

/-- Theorem 8.4: a derivation survives a substitution, and its effect becomes the
matrix action of the substitution; accepted derivations stay accepted, because
the policy is path closed. -/
theorem Deriv.subst {S : Sig} (hS : SigWF S) {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    ∀ {Δ : Ctx} {σ : ℕ → Exp} {M : ℕ → Eff}, SubstOK S acc σ M j.ctx Δ →
      Derivable S acc (j.substJ σ Δ M) := by
  induction d with
  | @tyFam Γ a args Δt ρ δ ε hS' dargs hε hv ih =>
    intro Δ σ M hσ
    obtain ⟨d'⟩ := ih hσ
    simp only [Judg.substJ, Tel.subst_closed (hS.family_closed hS')] at d'
    subst hε
    exact ⟨.tyFam hS' d' (by rw [Eff.act_inf, Eff.act_unit_decl])
      (fun h => (hv h).act (hσ.valid h))⟩
  | tyEvent hε =>
    intro Δ σ M hσ
    subst hε
    exact ⟨.tyEvent (Eff.act_top _ _)⟩
  | @tyOrigin Γ σr A e t α η θ ε dA de dt hε hv ihA ihe iht =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    obtain ⟨de'⟩ := ihe hσ
    obtain ⟨dt'⟩ := iht hσ
    simp only [Judg.substJ, Exp.subst] at dA' de' dt' ⊢
    subst hε
    exact ⟨.tyOrigin dA' de' dt' (by rw [Eff.act_inf, Eff.act_inf])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @tyStamped Γ σr A α ε dA hσr hε hv ihA =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ, Exp.subst] at dA' ⊢
    subst hε
    exact ⟨.tyStamped dA' hσr rfl (fun h => (hv h).act (hσ.valid h))⟩
  | @tyPi Γ q σr ρ A B α β ε dA dB hq hε hv ihA ihB =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ] at dA'
    obtain ⟨dB'⟩ := ihB (hσ.up hS dA')
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dB' ⊢
    subst hε
    exact ⟨.tyPi dA' dB' hq (by rw [Eff.act_inf, Eff.act_scale, Eff.unbind_act_upM])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @tySigma Γ ρ A B α β ε dA dB hε hv ihA ihB =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ] at dA'
    obtain ⟨dB'⟩ := ihB (hσ.up hS dA')
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dB' ⊢
    subst hε
    exact ⟨.tySigma dA' dB' (by rw [Eff.act_inf, Eff.unbind_act_upM])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @var Γ i ρ A C γ ε hΓ hC dC hε hv ih =>
    intro Δ σ M hσ
    obtain ⟨d'⟩ := hσ i ρ A hΓ
    simp only [Judg.substJ, Exp.subst]
    subst hε hC
    rw [Eff.act_unit_var (lt_of_getElem? hΓ)]
    exact ⟨d'⟩
  | @const Γ i k ρ A γ ε hc dA hε hv ih =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ih hσ
    have hA := Exp.subst_closed (σ := σ) (hS.const_closed hc)
    simp only [Judg.substJ, hA] at dA' ⊢
    subst hε
    exact ⟨.const hc dA' (Eff.act_unit_decl _ _ _ _) (fun h => (hv h).act (hσ.valid h))⟩
  | @lam Γ q σr ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ] at dA'
    obtain ⟨dt'⟩ := iht (hσ.up hS dA')
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dt' dC' ⊢
    subst hε
    exact ⟨.lam dA' dt' (by rw [Eff.act_upM_var_zero]; exact hq) dC'
      (by rw [Eff.unbind_act_upM]) (fun h => (hv h).act (hσ.valid h))⟩
  | @app Γ q σr ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro Δ σ M hσ
    obtain ⟨df'⟩ := ihf hσ
    obtain ⟨du'⟩ := ihu hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at df' du' dC' ⊢
    subst hε hC
    exact ⟨.app df' du' (subst_inst _ _ _) dC' (by rw [Eff.act_inf, Eff.act_scale])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @pair Γ ρ A B t u θ η γ ε dt du dC hε hv iht ihu ihC =>
    intro Δ σ M hσ
    obtain ⟨dt'⟩ := iht hσ
    obtain ⟨du'⟩ := ihu hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at dt' du' dC' ⊢
    rw [subst_inst] at du'
    subst hε
    exact ⟨.pair dt' du' dC' (by rw [Eff.act_inf]) (fun h => (hv h).act (hσ.valid h))⟩
  | @fst Γ ρ A B p π γ dp dA hv ihp ihA =>
    intro Δ σ M hσ
    obtain ⟨dp'⟩ := ihp hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ, Exp.subst] at dp' dA' ⊢
    exact ⟨.fst dp' dA' (fun h => (hv h).act (hσ.valid h))⟩
  | @snd Γ ρ A B C p π γ dp hC dC hv ihp ihC =>
    intro Δ σ M hσ
    obtain ⟨dp'⟩ := ihp hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at dp' dC' ⊢
    subst hC
    exact ⟨.snd dp' (subst_inst _ _ _) dC' (fun h => (hv h).act (hσ.valid h))⟩
  | @stamp Γ σr A t e o θ η ω γ ε dt de dorg dC hε hv iht ihe iho ihC =>
    intro Δ σ M hσ
    obtain ⟨dt'⟩ := iht hσ
    obtain ⟨de'⟩ := ihe hσ
    obtain ⟨dorg'⟩ := iho hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at dt' de' dorg' dC' ⊢
    subst hε
    exact ⟨.stamp dt' de' dorg' dC' (by rw [Eff.act_inf, Eff.act_inf])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @gate Γ g ds s Δt σg A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro Δ σ M hσ
    obtain ⟨hΔt, hAb, hBb⟩ := hS.gate_closed hg
    have hl := dds.isList
    obtain ⟨dds'⟩ := ihds hσ
    obtain ⟨dst'⟩ := ihst hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at dds' dst' dC' ⊢
    rw [Tel.subst_closed hΔt] at dds'
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hAb] at dst'
    subst hε hC
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hBb] at dC' ⊢
    exact ⟨.gate hg dds' dst' rfl dC'
      (by rw [Eff.act_inf, Eff.act_inf, Eff.act_unit_decl, Eff.act_scale])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @node Γ g ℓ ds t e Δt σg A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro Δ σ M hσ
    obtain ⟨hΔt, hAb, hBb⟩ := hS.gate_closed hg
    have hl := dds.isList
    obtain ⟨dds'⟩ := ihds hσ
    obtain ⟨dt'⟩ := iht hσ
    obtain ⟨de'⟩ := ihe hσ
    obtain ⟨dC'⟩ := ihC hσ
    simp only [Judg.substJ, Exp.subst] at dds' dt' de' dC' ⊢
    rw [Tel.subst_closed hΔt] at dds'
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hAb] at dt'
    subst hε hC
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hBb] at dC' ⊢
    exact ⟨.node hg dds' dt' de' rfl dC'
      (by rw [Eff.act_inf, Eff.act_inf, Eff.act_unit_decl, Eff.act_scale, Eff.act_inf])
      (fun h => (hv h).act (hσ.valid h))⟩
  | @conv Γ ρ t A B θ γ dt hAB dB iht ihB =>
    intro Δ σ M hσ
    obtain ⟨dt'⟩ := iht hσ
    obtain ⟨dB'⟩ := ihB hσ
    simp only [Judg.substJ] at dt' dB' ⊢
    exact ⟨.conv dt' (hAB.subst _) dB'⟩
  | spineNil hε =>
    intro Δ σ M hσ
    subst hε
    exact ⟨.spineNil (Eff.act_top _ _)⟩
  | @spineCons Γ ρ t ts A Δt ε₁ ε₂ ε dt dts hε iht ihts =>
    intro Δ σ M hσ
    obtain ⟨dt'⟩ := iht hσ
    obtain ⟨dts'⟩ := ihts hσ
    simp only [Judg.substJ, Exp.subst, Tel.subst_cons] at dt' dts' ⊢
    rw [Tel.subst_inst] at dts'
    subst hε
    exact ⟨.spineCons dt' dts' (by rw [Eff.act_inf])⟩
  | telNil hε =>
    intro Δ σ M hσ
    subst hε
    exact ⟨.telNil (Eff.act_top _ _)⟩
  | @telCons Γ ρ A Δt α δ ε dA dΔ hε ihA ihΔ =>
    intro Δ σ M hσ
    obtain ⟨dA'⟩ := ihA hσ
    simp only [Judg.substJ] at dA'
    obtain ⟨dΔ'⟩ := ihΔ (hσ.up hS dA')
    simp only [Judg.substJ, List.length_cons, Tel.subst_cons] at dΔ' ⊢
    subst hε
    exact ⟨.telCons dA' dΔ' (by rw [Eff.act_inf, Eff.unbind_act_upM])⟩

/-! ## Single substitution -/

/-- The effects of the single substitution `[u/x]`: `x` is replaced by a term
of effect `η`, and the other variables move down by one. -/
def Eff.instM (η : Eff) : ℕ → Eff
  | 0 => η
  | i + 1 => Eff.unit (.var i)

/-- Equation (2) of the paper: `ε⟨x := η⟩ = (ε ∖ x) ⊕ (ε(x) ⊗ η)`. -/
def Eff.instEff (ε η : Eff) : Eff := ε.unbind ⊓ Eff.scale (ε (.var 0)) η

theorem Eff.declPart_unbind_eq {ε : Eff} : Eff.declPart ε = Eff.declPart ε.unbind := by
  funext z; cases z <;> rfl

theorem Eff.act_instM {m n : ℕ} {ε : Eff} (hε : ε.Scoped m (n + 1)) (η : Eff) :
    Eff.act (n + 1) (Eff.instM η) ε = Eff.instEff ε η := by
  have h₁ : (fun i => Eff.instM η (i + 1)) = fun i => Eff.unit (.var i) := rfl
  have h₂ : Eff.act n (fun i => Eff.unit (.var i)) ε.unbind = ε.unbind := Eff.act_id hε.unbind
  simp only [Eff.act] at h₂ ⊢
  simp only [Eff.actVars, h₁]
  rw [Eff.declPart_unbind_eq, ← inf_assoc, inf_comm (Eff.declPart _), inf_assoc, h₂,
    Eff.instEff, inf_comm]
  rfl

/-- The single substitution `[u/x]` is a substitution of `x : A, Γ` into `Γ`, in a
well-formed context. -/
theorem SubstOK.inst1 {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {A u : Exp} {η : Eff}
    (hΓ : CtxWF S Γ) (du : Deriv S acc (.tm Γ ρ u A η)) :
    SubstOK S acc (Exp.inst1 u) (Eff.instM η) ((ρ, A) :: Γ) Γ := by
  intro i ρ' A' hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    have e : (A.ren (· + (0 + 1))).subst (Exp.inst1 u) = A := inst_shift A u
    rw [e]
    exact ⟨du⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    have e : (A'.ren (· + (i + 1 + 1))).subst (Exp.inst1 u) = A'.ren (· + (i + 1)) := by
      rw [subst_ren, ren_eq_subst]
      refine subst_ext (fun j => ?_) A'
      simp only [Function.comp_apply]
      rw [show j + (i + 1 + 1) = (j + (i + 1)) + 1 by omega]
      rfl
    rw [e]
    obtain ⟨α, ⟨dC⟩⟩ := hΓ.var_formed hi
    have hv : Valid S Γ ρ' (Eff.unit (.var i)) := valid_unit_var (by simp [roleOf, hi])
    cases acc with
    | true => exact ⟨.var hi rfl dC rfl (fun _ => hv)⟩
    | false => exact ⟨.var hi rfl dC.toRaw rfl (fun _ => hv)⟩

/-- Lemma 8.3 for a term: `J[u/x]` has effect `ε⟨x := η⟩`. -/
theorem Deriv.inst_tm {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {σr ρ : Role}
    {A t B u : Exp} {ε η : Eff} (hΓ : CtxWF S Γ) (d : Deriv S acc (.tm ((σr, A) :: Γ) ρ t B ε))
    (du : Deriv S acc (.tm Γ σr u A η)) :
    Derivable S acc (.tm Γ ρ (t.inst u) (B.inst u) (Eff.instEff ε η)) := by
  obtain ⟨d'⟩ := d.subst hS (SubstOK.inst1 hΓ du)
  simp only [Judg.substJ, List.length_cons] at d'
  rw [Eff.act_instM d.scoped.2.2] at d'
  exact ⟨d'⟩

/-- Lemma 8.3 for a type: `A[u/x]` has effect `ε⟨x := η⟩`. -/
theorem Deriv.inst_ty {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {σr ρ : Role}
    {A B u : Exp} {ε η : Eff} (hΓ : CtxWF S Γ) (d : Deriv S acc (.ty ((σr, A) :: Γ) ρ B ε))
    (du : Deriv S acc (.tm Γ σr u A η)) :
    Derivable S acc (.ty Γ ρ (B.inst u) (Eff.instEff ε η)) := by
  obtain ⟨d'⟩ := d.subst hS (SubstOK.inst1 hΓ du)
  simp only [Judg.substJ, List.length_cons] at d'
  rw [Eff.act_instM d.scoped.2] at d'
  exact ⟨d'⟩

end Artform.Roles.Calculus
