import ArtformRoles.Calculus.Subst

/-!
# Inversion and context conversion

* `Deriv.tm_ty`: the displayed type of a term judgment is well formed.
* `Deriv.inv_lam`, `Deriv.inv_pair`, `Deriv.inv_stamp`: inversion of the
  introduction rules through any chain of conversions.
* `Deriv.ctx_conv_tm`, `Deriv.ctx_conv_ty`, `Deriv.ctx_conv_tel`: a judgment
  over `x : A, Γ` holds over `x : A', Γ` when `A` and `A'` are convertible and
  both well formed, with the same effect.
-/

namespace Artform.Roles.Calculus

open Exp

/-- The displayed type of a term judgment is well formed. -/
theorem Deriv.tm_ty {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t A : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ t A ε)) : ∃ γ, Derivable S acc (.ty Γ ρ A γ) := by
  cases d with
  | var _ hC dC => exact ⟨_, ⟨dC⟩⟩
  | const _ dA => exact ⟨_, ⟨dA⟩⟩
  | lam _ _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | app _ _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | pair _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | fst _ dA => exact ⟨_, ⟨dA⟩⟩
  | snd _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | stamp _ _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | gate _ _ _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | node _ _ _ _ _ dC => exact ⟨_, ⟨dC⟩⟩
  | conv _ _ dB => exact ⟨_, ⟨dB⟩⟩

theorem Deriv.inv_lam {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {q : Grade} {A t C : Exp}
    {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.lam q σ A t) C ε)) :
    ∃ B θ, Conv (.pi q σ A B) C ∧ q ≤ θ (.var 0) ∧ ε = θ.unbind ∧
      (∃ α, Derivable S acc (.ty Γ σ A α)) ∧ Derivable S acc (.tm ((σ, A) :: Γ) ρ t B θ) ∧
      (∃ γ, Derivable S acc (.ty Γ ρ (.pi q σ A B) γ)) := by
  generalize hj : Judg.tm Γ ρ (.lam q σ A t) C ε = j at d
  induction d generalizing C with
  | lam dA dt hq dC hε _ =>
    cases hj
    exact ⟨_, _, Conv.refl _, hq, hε, ⟨_, ⟨dA⟩⟩, ⟨dt⟩, ⟨_, ⟨dC⟩⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨B, θ, hc, hq, hε, hA, ht, hpi⟩ := iht rfl
    exact ⟨B, θ, hc.trans hAB, hq, hε, hA, ht, hpi⟩
  | _ => cases hj

theorem Deriv.inv_pair {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t u C : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ (.pair t u) C ε)) :
    ∃ A B θ η, Conv (.sigma ρ A B) C ∧ ε = θ ⊓ η ∧ Derivable S acc (.tm Γ ρ t A θ) ∧
      Derivable S acc (.tm Γ ρ u (B.inst t) η) ∧
      (∃ γ, Derivable S acc (.ty Γ ρ (.sigma ρ A B) γ)) := by
  generalize hj : Judg.tm Γ ρ (.pair t u) C ε = j at d
  induction d generalizing C with
  | pair dt du dC hε _ =>
    cases hj
    exact ⟨_, _, _, _, Conv.refl _, hε, ⟨dt⟩, ⟨du⟩, ⟨_, ⟨dC⟩⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨A, B, θ, η, hc, hε, ht, hu, hs⟩ := iht rfl
    exact ⟨A, B, θ, η, hc.trans hAB, hε, ht, hu, hs⟩
  | _ => cases hj

theorem Deriv.inv_stamp {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t e o C : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ (.stamp t e o) C ε)) :
    ∃ σ A θ η ω, ρ = .witness ∧ Conv (.stamped σ A) C ∧ ε = θ ⊓ η ⊓ ω ∧
      Derivable S acc (.tm Γ σ t A θ) ∧ Derivable S acc (.tm Γ .witness e .event η) ∧
      Derivable S acc (.tm Γ .witness o (.origin A e t) ω) ∧
      (∃ γ, Derivable S acc (.ty Γ .witness (.stamped σ A) γ)) := by
  generalize hj : Judg.tm Γ ρ (.stamp t e o) C ε = j at d
  induction d generalizing C with
  | stamp dt de dorg dC hε _ =>
    cases hj
    exact ⟨_, _, _, _, _, rfl, Conv.refl _, hε, ⟨dt⟩, ⟨de⟩, ⟨dorg⟩, ⟨_, ⟨dC⟩⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨σ, A, θ, η, ω, hρ, hc, hε, ht, he, ho, hs⟩ := iht rfl
    exact ⟨σ, A, θ, η, ω, hρ, hc.trans hAB, hε, ht, he, ho, hs⟩
  | _ => cases hj

/-! ## Context conversion -/

/-- The identity substitution of `x : A, Γ` into `x : A', Γ`, for convertible,
well-formed `A` and `A'`. -/
theorem SubstOK.convCtx {S : Sig} (hS : SigWF S) {Γ : Ctx} {σ : Role} {A A' : Exp}
    {α α' : Eff} (hΓ : CtxWF S Γ) (dA : Deriv S true (.ty Γ σ A α))
    (dA' : Deriv S true (.ty Γ σ A' α')) (hAA' : Conv A A') :
    SubstOK S true Exp.var (fun i => Eff.unit (.var i)) ((σ, A) :: Γ) ((σ, A') :: Γ) := by
  intro i ρ B hi
  rw [subst_var]
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨wA'⟩ := dA'.weaken_ty hS (σ, A')
    obtain ⟨wA⟩ := dA.weaken_ty hS (σ, A')
    have e : ∀ X : Exp, X.ren (· + (0 + 1)) = X.shift := fun X => by congr 1
    have hv : Valid S ((σ, A') :: Γ) σ (Eff.unit (.var 0)) := valid_unit_var (by simp [roleOf])
    rw [e]
    exact ⟨.conv (.var rfl (e A') wA' rfl (fun _ => hv)) (hAA'.symm.ren _) wA⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    have hΓ' : CtxWF S ((σ, A') :: Γ) := .cons hΓ ⟨dA'⟩
    obtain ⟨γ, ⟨dC⟩⟩ := hΓ'.var_formed (i := i + 1) (by simpa using hi)
    exact ⟨.var (by simpa using hi) rfl dC rfl (fun _ => valid_unit_var (by simp [roleOf, hi]))⟩

theorem Deriv.ctx_conv_tm {S : Sig} (hS : SigWF S) {Γ : Ctx} {σ ρ : Role} {A A' t B : Exp}
    {α α' ε : Eff} (d : Deriv S true (.tm ((σ, A) :: Γ) ρ t B ε)) (hΓ : CtxWF S Γ)
    (dA : Deriv S true (.ty Γ σ A α)) (dA' : Deriv S true (.ty Γ σ A' α')) (hAA' : Conv A A') :
    Derivable S true (.tm ((σ, A') :: Γ) ρ t B ε) := by
  obtain ⟨d'⟩ := d.subst hS (SubstOK.convCtx hS hΓ dA dA' hAA')
  simp only [Judg.substJ, subst_var] at d'
  rw [Eff.act_id d.scoped.2.2] at d'
  exact ⟨d'⟩

theorem Deriv.ctx_conv_ty {S : Sig} (hS : SigWF S) {Γ : Ctx} {σ ρ : Role} {A A' B : Exp}
    {α α' ε : Eff} (d : Deriv S true (.ty ((σ, A) :: Γ) ρ B ε)) (hΓ : CtxWF S Γ)
    (dA : Deriv S true (.ty Γ σ A α)) (dA' : Deriv S true (.ty Γ σ A' α')) (hAA' : Conv A A') :
    Derivable S true (.ty ((σ, A') :: Γ) ρ B ε) := by
  obtain ⟨d'⟩ := d.subst hS (SubstOK.convCtx hS hΓ dA dA' hAA')
  simp only [Judg.substJ, subst_var] at d'
  rw [Eff.act_id d.scoped.2] at d'
  exact ⟨d'⟩

theorem Deriv.ctx_conv_tel {S : Sig} (hS : SigWF S) {Γ : Ctx} {σ : Role} {A A' : Exp}
    {Δ : Tel} {α α' ε : Eff} (d : Deriv S true (.tel ((σ, A) :: Γ) Δ ε)) (hΓ : CtxWF S Γ)
    (dA : Deriv S true (.ty Γ σ A α)) (dA' : Deriv S true (.ty Γ σ A' α')) (hAA' : Conv A A') :
    Derivable S true (.tel ((σ, A') :: Γ) Δ ε) := by
  obtain ⟨d'⟩ := d.subst hS (SubstOK.convCtx hS hΓ dA dA' hAA')
  simp only [Judg.substJ, Tel.subst_var] at d'
  rw [Eff.act_id d.scoped.2] at d'
  exact ⟨d'⟩

end Artform.Roles.Calculus
