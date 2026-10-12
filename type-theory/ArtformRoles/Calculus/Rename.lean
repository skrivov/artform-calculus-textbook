import ArtformRoles.Calculus.SigFacts

/-!
# Renaming

A derivation survives a renaming of its variables into a context that gives
them the same roles and types (`Deriv.rename`). Its effect becomes the matrix
action of the renaming (§8.2 of the paper): the variable `i` is replaced by
`var (ξ i)`, of effect `𝟙_{ξ i}`. Weakening, the special case that adds a
variable, extends the effect by `∞` at the new variable (`Deriv.weaken`).

Policy validity is preserved because the matrix action of a substitution whose
terms are policy valid at the roles of the variables they replace is valid when
the policy is path closed (`Valid.act`); this is also the core of Theorem 8.4.
-/

namespace Artform.Roles.Calculus

open Exp

/-- The context of a judgment. -/
def Judg.ctx : Judg → Ctx
  | .ty Γ .. => Γ
  | .tm Γ .. => Γ
  | .spine Γ .. => Γ
  | .tel Γ .. => Γ

/-- A judgment after a substitution `σ` from its context into `Δ`, the term put
for `var i` having effect `M i`: the matrix action `M ⋆ ε` on its effect. -/
def Judg.substJ (σ : ℕ → Exp) (Δ : Ctx) (M : ℕ → Eff) : Judg → Judg
  | .ty Γ ρ A ε => .ty Δ ρ (A.subst σ) (Eff.act Γ.length M ε)
  | .tm Γ ρ t A ε => .tm Δ ρ (t.subst σ) (A.subst σ) (Eff.act Γ.length M ε)
  | .spine Γ ts Δ' ε => .spine Δ (ts.subst σ) (Tel.subst σ Δ') (Eff.act Γ.length M ε)
  | .tel Γ Δ' ε => .tel Δ (Tel.subst σ Δ') (Eff.act Γ.length M ε)

/-- A renaming of `Γ` into `Δ`: every variable keeps its role and its type. -/
def RenOK (ξ : ℕ → ℕ) (Γ Δ : Ctx) : Prop :=
  ∀ i ρ A, Γ[i]? = some (ρ, A) → ∃ A', Δ[ξ i]? = some (ρ, A') ∧
    A'.ren (· + (ξ i + 1)) = (A.ren (· + (i + 1))).subst (var ∘ ξ)

theorem RenOK.up {ξ : ℕ → ℕ} {Γ Δ : Ctx} (h : RenOK ξ Γ Δ) (ρ : Role) (A : Exp) :
    RenOK (upRen ξ) ((ρ, A) :: Γ) ((ρ, A.subst (var ∘ ξ)) :: Δ) := by
  intro i ρ' A' hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    refine ⟨A.subst (var ∘ ξ), rfl, ?_⟩
    rw [ren_subst, subst_ren]
    rfl
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    obtain ⟨A'', h₁, h₂⟩ := h i ρ' A' hi
    refine ⟨A'', by simpa [upRen] using h₁, ?_⟩
    have e₁ : A''.ren (· + (upRen ξ (i + 1) + 1)) = (A''.ren (· + (ξ i + 1))).ren (· + 1) := by
      rw [ren_ren]; congr 1
    rw [e₁, h₂, ren_subst, subst_ren, subst_ren]
    refine subst_ext (fun j => ?_) A'
    simp [ren, upRen]

theorem RenOK.succ (Γ : Ctx) (p : Role × Exp) : RenOK Nat.succ Γ (p :: Γ) := by
  intro i ρ A hi
  refine ⟨A, by simpa using hi, ?_⟩
  rw [ren_eq_subst, ren_eq_subst, subst_subst]
  refine subst_ext (fun j => ?_) A
  simp [subst]
  omega

theorem le_actVars {c : Grade} {z : Atom} :
    ∀ (n : ℕ) (M : ℕ → Eff) (ε : Eff), (∀ i < n, c ≤ ε (.var i) ⊔ M i z) →
      c ≤ Eff.actVars n M ε z
  | 0, _, _, _ => le_top
  | n + 1, M, ε, h =>
    le_inf (h 0 (by omega)) (le_actVars n _ _ fun i hi => h (i + 1) (by omega))

/-- The matrix action of a substitution whose terms are valid at the roles of
the variables they replace is valid, because the policy is path closed. -/
theorem Valid.act {S : Sig} {Γ Δ : Ctx} {ρ : Role} {ε : Eff} {M : ℕ → Eff}
    (hv : Valid S Γ ρ ε)
    (hM : ∀ i r, roleOf S Γ (.var i) = some r → Valid S Δ r (M i)) :
    Valid S Δ ρ (Eff.act Γ.length M ε) := by
  intro z r hz
  refine le_inf ?_ (le_actVars _ _ _ fun i hi => ?_)
  · cases z with
    | var j => exact le_top
    | decl a k => exact hv (.decl a k) r hz
  · obtain ⟨⟨rᵢ, Aᵢ⟩, hi'⟩ : ∃ p, Γ[i]? = some p := ⟨Γ[i], List.getElem?_eq_getElem hi⟩
    have h₁ := hv (.var i) rᵢ (by simp [roleOf, hi'])
    have h₂ := hM i rᵢ (by simp [roleOf, hi']) z r hz
    calc demand r ρ ≤ demand r rᵢ ⊔ demand rᵢ ρ := demand_pathClosed r rᵢ ρ
      _ ≤ M i z ⊔ ε (.var i) := sup_le_sup h₂ h₁
      _ = ε (.var i) ⊔ M i z := sup_comm _ _

/-- A variable's unit effect is valid at its own role. -/
theorem valid_unit_var {S : Sig} {Δ : Ctx} {j : ℕ} {r : Role}
    (h : roleOf S Δ (.var j) = some r) : Valid S Δ r (Eff.unit (.var j)) := by
  intro z r' hz
  by_cases hzj : z = .var j
  · subst hzj
    rw [h] at hz
    cases hz
    rw [demand_self, Eff.unit_self]
    exact le_rfl
  · rw [Eff.unit_ne hzj]; exact le_top

theorem RenOK.valid {S : Sig} {ξ : ℕ → ℕ} {Γ Δ : Ctx} (h : RenOK ξ Γ Δ) :
    ∀ i r, roleOf S Γ (.var i) = some r → Valid S Δ r (Eff.unit (.var (ξ i))) := by
  intro i r hr
  simp only [roleOf, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', A⟩, hi, rfl⟩ := hr
  obtain ⟨A', hA', -⟩ := h i r' A hi
  exact valid_unit_var (by simp [roleOf, hA'])

/-- An argument list checked against a telescope has its length. -/
theorem Deriv.spine_isList {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    match j with
    | .spine _ ts Δ _ => ts.IsList Δ.length
    | _ => True := by
  induction d with
  | spineNil => trivial
  | spineCons _ _ _ _ ih => simpa [Exp.IsList] using ih
  | _ => trivial

theorem Deriv.isList {S : Sig} {acc : Bool} {Γ : Ctx} {ts : Exp} {Δ : Tel} {ε : Eff}
    (d : Deriv S acc (.spine Γ ts Δ ε)) : ts.IsList Δ.length := d.spine_isList

/-- Renaming (§8.2): a derivation survives a renaming of its variables into a
context that keeps their roles and types, and its effect becomes the matrix
action of the renaming. -/
theorem Deriv.rename {S : Sig} (hS : SigWF S) {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    ∀ {Δ : Ctx} {ξ : ℕ → ℕ}, RenOK ξ j.ctx Δ →
      Derivable S acc (j.substJ (Exp.var ∘ ξ) Δ (fun i => Eff.unit (.var (ξ i)))) := by
  induction d with
  | @tyFam Γ a args Δt ρ δ ε hS' dargs hε hv ih =>
    intro Δ ξ hξ
    obtain ⟨d'⟩ := ih hξ
    simp only [Judg.substJ, Tel.subst_closed (hS.family_closed hS')] at d'
    subst hε
    exact ⟨.tyFam hS' d' (by rw [Eff.act_inf, Eff.act_unit_decl])
      (fun h => (hv h).act hξ.valid)⟩
  | tyEvent hε =>
    intro Δ ξ hξ
    subst hε
    exact ⟨.tyEvent (Eff.act_top _ _)⟩
  | @tyOrigin Γ σr A e t α η θ ε dA de dt hε hv ihA ihe iht =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    obtain ⟨de'⟩ := ihe hξ
    obtain ⟨dt'⟩ := iht hξ
    simp only [Judg.substJ, Exp.subst] at dA' de' dt' ⊢
    subst hε
    exact ⟨.tyOrigin dA' de' dt' (by rw [Eff.act_inf, Eff.act_inf])
      (fun h => (hv h).act hξ.valid)⟩
  | @tyStamped Γ σr A α ε dA hσ hε hv ihA =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    simp only [Judg.substJ, Exp.subst] at dA' ⊢
    subst hε
    exact ⟨.tyStamped dA' hσ rfl (fun h => (hv h).act hξ.valid)⟩
  | @tyPi Γ q σr ρ A B α β ε dA dB hq hε hv ihA ihB =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    obtain ⟨dB'⟩ := ihB (hξ.up σr A)
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dA' dB' ⊢
    rw [← Eff.upM_unit] at dB'
    rw [upRen_var]
    subst hε
    exact ⟨.tyPi dA' dB' hq (by rw [Eff.act_inf, Eff.act_scale, Eff.unbind_act_upM])
      (fun h => (hv h).act hξ.valid)⟩
  | @tySigma Γ ρ A B α β ε dA dB hε hv ihA ihB =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    obtain ⟨dB'⟩ := ihB (hξ.up ρ A)
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dA' dB' ⊢
    rw [← Eff.upM_unit] at dB'
    rw [upRen_var]
    subst hε
    exact ⟨.tySigma dA' dB' (by rw [Eff.act_inf, Eff.unbind_act_upM])
      (fun h => (hv h).act hξ.valid)⟩
  | @var Γ i ρ A C γ ε hΓ hC dC hε hv ih =>
    intro Δ ξ hξ
    obtain ⟨dC'⟩ := ih hξ
    obtain ⟨A', hA', hAeq⟩ := hξ i ρ A hΓ
    simp only [Judg.substJ] at dC' ⊢
    subst hε hC
    exact ⟨.var hA' hAeq.symm dC' (Eff.act_unit_var (lt_of_getElem? hΓ) _)
      (fun h => (hv h).act hξ.valid)⟩
  | @const Γ i k ρ A γ ε hc dA hε hv ih =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ih hξ
    have hA := Exp.subst_closed (σ := Exp.var ∘ ξ) (hS.const_closed hc)
    simp only [Judg.substJ, hA] at dA' ⊢
    subst hε
    exact ⟨.const hc dA' (Eff.act_unit_decl _ _ _ _) (fun h => (hv h).act hξ.valid)⟩
  | @lam Γ q σr ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    obtain ⟨dt'⟩ := iht (hξ.up σr A)
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst, List.length_cons] at dA' dt' dC' ⊢
    rw [← Eff.upM_unit] at dt'
    rw [upRen_var] at dC' ⊢
    subst hε
    exact ⟨.lam dA' dt' (by rw [Eff.act_upM_var_zero]; exact hq) dC'
      (by rw [Eff.unbind_act_upM]) (fun h => (hv h).act hξ.valid)⟩
  | @app Γ q σr ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro Δ ξ hξ
    obtain ⟨df'⟩ := ihf hξ
    obtain ⟨du'⟩ := ihu hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at df' du' dC' ⊢
    subst hε hC
    exact ⟨.app df' du' (subst_inst _ _ _) dC' (by rw [Eff.act_inf, Eff.act_scale])
      (fun h => (hv h).act hξ.valid)⟩
  | @pair Γ ρ A B t u θ η γ ε dt du dC hε hv iht ihu ihC =>
    intro Δ ξ hξ
    obtain ⟨dt'⟩ := iht hξ
    obtain ⟨du'⟩ := ihu hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at dt' du' dC' ⊢
    rw [subst_inst] at du'
    subst hε
    exact ⟨.pair dt' du' dC' (by rw [Eff.act_inf]) (fun h => (hv h).act hξ.valid)⟩
  | @fst Γ ρ A B p π γ dp dA hv ihp ihA =>
    intro Δ ξ hξ
    obtain ⟨dp'⟩ := ihp hξ
    obtain ⟨dA'⟩ := ihA hξ
    simp only [Judg.substJ, Exp.subst] at dp' dA' ⊢
    exact ⟨.fst dp' dA' (fun h => (hv h).act hξ.valid)⟩
  | @snd Γ ρ A B C p π γ dp hC dC hv ihp ihC =>
    intro Δ ξ hξ
    obtain ⟨dp'⟩ := ihp hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at dp' dC' ⊢
    subst hC
    exact ⟨.snd dp' (subst_inst _ _ _) dC' (fun h => (hv h).act hξ.valid)⟩
  | @stamp Γ σr A t e o θ η ω γ ε dt de dorg dC hε hv iht ihe iho ihC =>
    intro Δ ξ hξ
    obtain ⟨dt'⟩ := iht hξ
    obtain ⟨de'⟩ := ihe hξ
    obtain ⟨dorg'⟩ := iho hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at dt' de' dorg' dC' ⊢
    subst hε
    exact ⟨.stamp dt' de' dorg' dC' (by rw [Eff.act_inf, Eff.act_inf])
      (fun h => (hv h).act hξ.valid)⟩
  | @gate Γ g ds s Δt σg A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro Δ ξ hξ
    obtain ⟨hΔt, hAb, hBb⟩ := hS.gate_closed hg
    have hl := dds.isList
    obtain ⟨dds'⟩ := ihds hξ
    obtain ⟨dst'⟩ := ihst hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at dds' dst' dC' ⊢
    rw [Tel.subst_closed hΔt] at dds'
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hAb] at dst'
    subst hε hC
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hBb] at dC' ⊢
    exact ⟨.gate hg dds' dst' rfl dC'
      (by rw [Eff.act_inf, Eff.act_inf, Eff.act_unit_decl, Eff.act_scale])
      (fun h => (hv h).act hξ.valid)⟩
  | @node Γ g ℓ ds t e Δt σg A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro Δ ξ hξ
    obtain ⟨hΔt, hAb, hBb⟩ := hS.gate_closed hg
    have hl := dds.isList
    obtain ⟨dds'⟩ := ihds hξ
    obtain ⟨dt'⟩ := iht hξ
    obtain ⟨de'⟩ := ihe hξ
    obtain ⟨dC'⟩ := ihC hξ
    simp only [Judg.substJ, Exp.subst] at dds' dt' de' dC' ⊢
    rw [Tel.subst_closed hΔt] at dds'
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hAb] at dt'
    subst hε hC
    rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hBb] at dC' ⊢
    exact ⟨.node hg dds' dt' de' rfl dC'
      (by rw [Eff.act_inf, Eff.act_inf, Eff.act_unit_decl, Eff.act_scale, Eff.act_inf])
      (fun h => (hv h).act hξ.valid)⟩
  | @conv Γ ρ t A B θ γ dt hAB dB iht ihB =>
    intro Δ ξ hξ
    obtain ⟨dt'⟩ := iht hξ
    obtain ⟨dB'⟩ := ihB hξ
    simp only [Judg.substJ] at dt' dB' ⊢
    exact ⟨.conv dt' (hAB.subst _) dB'⟩
  | spineNil hε =>
    intro Δ ξ hξ
    subst hε
    exact ⟨.spineNil (Eff.act_top _ _)⟩
  | @spineCons Γ ρ t ts A Δt ε₁ ε₂ ε dt dts hε iht ihts =>
    intro Δ ξ hξ
    obtain ⟨dt'⟩ := iht hξ
    obtain ⟨dts'⟩ := ihts hξ
    simp only [Judg.substJ, Exp.subst, Tel.subst_cons] at dt' dts' ⊢
    rw [Tel.subst_inst] at dts'
    subst hε
    exact ⟨.spineCons dt' dts' (by rw [Eff.act_inf])⟩
  | telNil hε =>
    intro Δ ξ hξ
    subst hε
    exact ⟨.telNil (Eff.act_top _ _)⟩
  | @telCons Γ ρ A Δt α δ ε dA dΔ hε ihA ihΔ =>
    intro Δ ξ hξ
    obtain ⟨dA'⟩ := ihA hξ
    obtain ⟨dΔ'⟩ := ihΔ (hξ.up ρ A)
    simp only [Judg.substJ, List.length_cons, Tel.subst_cons] at dA' dΔ' ⊢
    rw [← Eff.upM_unit] at dΔ'
    rw [upRen_var]
    subst hε
    exact ⟨.telCons dA' dΔ' (by rw [Eff.act_inf, Eff.unbind_act_upM])⟩

end Artform.Roles.Calculus
