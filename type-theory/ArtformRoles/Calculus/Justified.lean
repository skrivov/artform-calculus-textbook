import ArtformRoles.Calculus.Records

/-!
# Justified records

The record step `gate_g(d⃗; stamp(t, e, o)) ⟶ node_g(d⃗; t, e)` drops the origin
`o`. The node keeps a justification all the same: in the context of the binders
above it there is an origin `o : Origin_{A[d⃗]}(e, t)` for its payload and
event. This invariant carries the argument of Lemma 10.1 (iv) of the paper
("apply the composite substitution to the creating stamp, including its
then-discarded origin field").

* `NodeJust`, `Justified`: every private node of an expression is justified,
  and every binder annotation is formed, in the context of the binders above.
* `Justified.ren`, `Justified.subst`: renaming and well-typed substitution keep
  the invariant.
* `Deriv.justified_step`: reduction of a well-typed expression keeps it.
* `Deriv.justified_of_public`: a well-typed public expression is justified,
  and so is every reduct of a well-typed public term (`Deriv.justified_steps`).
-/

namespace Artform.Roles.Calculus

open Exp

/-- A node of the gate `g` with parameters `ds`, payload `p` and event `e` is
justified in `Γ`: some origin `o : Origin_{A[ds]}(e, p)` exists there. -/
def NodeJust (S : Sig) (Γ : Ctx) (g : ℕ) (ds p e : Exp) : Prop :=
  ∃ Δ σ A ρ B, S.gate? g = some (Δ, σ, A, ρ, B) ∧ ds.IsList Δ.length ∧
    ∃ o ω, Derivable S true (.tm Γ .witness o (.origin (instType ds Δ A) e p) ω)

/-- Every private node is justified, and every binder annotation formed, in the
context of the binders above it. -/
def Justified (S : Sig) : Ctx → Exp → Prop
  | _, .var _ | _, .const _ _ | _, .event | _, .nil => True
  | Γ, .fam _ args => Justified S Γ args
  | Γ, .origin A e t => Justified S Γ A ∧ Justified S Γ e ∧ Justified S Γ t
  | Γ, .stamped _ A => Justified S Γ A
  | Γ, .pi _ σ A B =>
    (∃ α, Derivable S true (.ty Γ σ A α)) ∧ Justified S Γ A ∧ Justified S ((σ, A) :: Γ) B
  | Γ, .sigma ρ A B =>
    (∃ α, Derivable S true (.ty Γ ρ A α)) ∧ Justified S Γ A ∧ Justified S ((ρ, A) :: Γ) B
  | Γ, .lam _ σ A t =>
    (∃ α, Derivable S true (.ty Γ σ A α)) ∧ Justified S Γ A ∧ Justified S ((σ, A) :: Γ) t
  | Γ, .app t u => Justified S Γ t ∧ Justified S Γ u
  | Γ, .pair t u => Justified S Γ t ∧ Justified S Γ u
  | Γ, .cons t u => Justified S Γ t ∧ Justified S Γ u
  | Γ, .fst t => Justified S Γ t
  | Γ, .snd t => Justified S Γ t
  | Γ, .stamp t e o => Justified S Γ t ∧ Justified S Γ e ∧ Justified S Γ o
  | Γ, .gate _ ds s => Justified S Γ ds ∧ Justified S Γ s
  | Γ, .node g _ ds p e =>
    NodeJust S Γ g ds p e ∧ Justified S Γ ds ∧ Justified S Γ p ∧ Justified S Γ e

theorem Exp.IsList.subst {ds : Exp} {n : ℕ} (h : ds.IsList n) (σ : ℕ → Exp) :
    (ds.subst σ).IsList n := by
  induction ds generalizing n with
  | nil => cases n <;> simp_all [Exp.IsList, Exp.subst]
  | cons t ts _ ih =>
    cases n with
    | zero => simp [Exp.IsList] at h
    | succ n => exact ih h
  | _ => cases n <;> simp_all [Exp.IsList]

/-- The origin type of a justified node after a substitution. -/
theorem origin_instType_subst {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B : Exp} (hg : S.gate? g = some (Δ, σ, A, ρ, B)) {ds : Exp} (hl : ds.IsList Δ.length)
    (e p : Exp) (τ : ℕ → Exp) :
    (Exp.origin (instType ds Δ A) e p).subst τ =
      .origin (instType (ds.subst τ) Δ A) (e.subst τ) (p.subst τ) := by
  obtain ⟨hΔt, hAb, -⟩ := hS.gate_closed hg
  simp only [Exp.subst]
  rw [instType_subst _ hl, Tel.subst_closed hΔt, subst_upN_below hAb]

/-! ## Renaming and substitution -/

theorem Justified.ren {S : Sig} (hS : SigWF S) :
    ∀ (t : Exp) {Γ Δ : Ctx} {ξ : ℕ → ℕ}, Justified S Γ t → RenOK ξ Γ Δ →
      Justified S Δ (t.ren ξ) := by
  intro t
  induction t with
  | var | const | event | nil => intros; trivial
  | fam a args ih => intro Γ Δ ξ h hξ; exact ih h hξ
  | origin A e t ihA ihe iht =>
    intro Γ Δ ξ h hξ; exact ⟨ihA h.1 hξ, ihe h.2.1 hξ, iht h.2.2 hξ⟩
  | stamped σ A ih => intro Γ Δ ξ h hξ; exact ih h hξ
  | pi q σ A B ihA ihB =>
    intro Γ Δ ξ h hξ
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, hB⟩ := h
    obtain ⟨dA'⟩ := dA.rename hS hξ
    simp only [Judg.substJ, ← Exp.ren_eq_subst] at dA'
    have hξ' := hξ.up σ A
    rw [← Exp.ren_eq_subst] at hξ'
    exact ⟨⟨_, ⟨dA'⟩⟩, ihA hA hξ, ihB hB hξ'⟩
  | sigma ρ A B ihA ihB =>
    intro Γ Δ ξ h hξ
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, hB⟩ := h
    obtain ⟨dA'⟩ := dA.rename hS hξ
    simp only [Judg.substJ, ← Exp.ren_eq_subst] at dA'
    have hξ' := hξ.up ρ A
    rw [← Exp.ren_eq_subst] at hξ'
    exact ⟨⟨_, ⟨dA'⟩⟩, ihA hA hξ, ihB hB hξ'⟩
  | lam q σ A t ihA iht =>
    intro Γ Δ ξ h hξ
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, ht⟩ := h
    obtain ⟨dA'⟩ := dA.rename hS hξ
    simp only [Judg.substJ, ← Exp.ren_eq_subst] at dA'
    have hξ' := hξ.up σ A
    rw [← Exp.ren_eq_subst] at hξ'
    exact ⟨⟨_, ⟨dA'⟩⟩, ihA hA hξ, iht ht hξ'⟩
  | app t u iht ihu => intro Γ Δ ξ h hξ; exact ⟨iht h.1 hξ, ihu h.2 hξ⟩
  | pair t u iht ihu => intro Γ Δ ξ h hξ; exact ⟨iht h.1 hξ, ihu h.2 hξ⟩
  | cons t u iht ihu => intro Γ Δ ξ h hξ; exact ⟨iht h.1 hξ, ihu h.2 hξ⟩
  | fst t ih => intro Γ Δ ξ h hξ; exact ih h hξ
  | snd t ih => intro Γ Δ ξ h hξ; exact ih h hξ
  | stamp t e o iht ihe iho =>
    intro Γ Δ ξ h hξ; exact ⟨iht h.1 hξ, ihe h.2.1 hξ, iho h.2.2 hξ⟩
  | gate g ds s ihds ihs => intro Γ Δ ξ h hξ; exact ⟨ihds h.1 hξ, ihs h.2 hξ⟩
  | node g ℓ ds p e ihds ihp ihe =>
    intro Γ Δ ξ h hξ
    obtain ⟨⟨Δg, σ, A, ρ, B, hg, hl, o, ω, ⟨dO⟩⟩, hds, hp, he⟩ := h
    obtain ⟨dO'⟩ := dO.rename hS hξ
    simp only [Judg.substJ] at dO'
    rw [origin_instType_subst hS hg hl] at dO'
    simp only [← Exp.ren_eq_subst] at dO'
    refine ⟨⟨Δg, σ, A, ρ, B, hg, ?_, _, _, ⟨dO'⟩⟩, ihds hds hξ, ihp hp hξ, ihe he hξ⟩
    rw [Exp.ren_eq_subst]; exact hl.subst _

theorem Justified.weaken {S : Sig} (hS : SigWF S) {Γ : Ctx} {t : Exp}
    (h : Justified S Γ t) (p : Role × Exp) : Justified S (p :: Γ) (t.ren Nat.succ) :=
  Justified.ren hS t h (RenOK.succ Γ p)

theorem Justified.subst {S : Sig} (hS : SigWF S) :
    ∀ (t : Exp) {Γ Δ : Ctx} {σ : ℕ → Exp} {M : ℕ → Eff}, Justified S Γ t →
      SubstOK S true σ M Γ Δ → (∀ i, Justified S Δ (σ i)) → Justified S Δ (t.subst σ) := by
  intro t
  induction t with
  | var i => intro Γ Δ σ M _ _ hσ'; exact hσ' i
  | const | event | nil => intros; trivial
  | fam a args ih => intro Γ Δ σ M h hσ hσ'; exact ih h hσ hσ'
  | origin A e t ihA ihe iht =>
    intro Γ Δ σ M h hσ hσ'; exact ⟨ihA h.1 hσ hσ', ihe h.2.1 hσ hσ', iht h.2.2 hσ hσ'⟩
  | stamped σ A ih => intro Γ Δ τ M h hσ hσ'; exact ih h hσ hσ'
  | pi q σ' A B ihA ihB =>
    intro Γ Δ σ M h hσ hσ'
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, hB⟩ := h
    obtain ⟨dA'⟩ := dA.subst hS hσ
    simp only [Judg.substJ] at dA'
    refine ⟨⟨_, ⟨dA'⟩⟩, ihA hA hσ hσ', ihB hB (hσ.up hS dA') fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ j => exact (hσ' j).weaken hS _
  | sigma ρ A B ihA ihB =>
    intro Γ Δ σ M h hσ hσ'
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, hB⟩ := h
    obtain ⟨dA'⟩ := dA.subst hS hσ
    simp only [Judg.substJ] at dA'
    refine ⟨⟨_, ⟨dA'⟩⟩, ihA hA hσ hσ', ihB hB (hσ.up hS dA') fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ j => exact (hσ' j).weaken hS _
  | lam q σ' A t ihA iht =>
    intro Γ Δ σ M h hσ hσ'
    obtain ⟨⟨α, ⟨dA⟩⟩, hA, ht⟩ := h
    obtain ⟨dA'⟩ := dA.subst hS hσ
    simp only [Judg.substJ] at dA'
    refine ⟨⟨_, ⟨dA'⟩⟩, ihA hA hσ hσ', iht ht (hσ.up hS dA') fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ j => exact (hσ' j).weaken hS _
  | app t u iht ihu => intro Γ Δ σ M h hσ hσ'; exact ⟨iht h.1 hσ hσ', ihu h.2 hσ hσ'⟩
  | pair t u iht ihu => intro Γ Δ σ M h hσ hσ'; exact ⟨iht h.1 hσ hσ', ihu h.2 hσ hσ'⟩
  | cons t u iht ihu => intro Γ Δ σ M h hσ hσ'; exact ⟨iht h.1 hσ hσ', ihu h.2 hσ hσ'⟩
  | fst t ih => intro Γ Δ σ M h hσ hσ'; exact ih h hσ hσ'
  | snd t ih => intro Γ Δ σ M h hσ hσ'; exact ih h hσ hσ'
  | stamp t e o iht ihe iho =>
    intro Γ Δ σ M h hσ hσ'; exact ⟨iht h.1 hσ hσ', ihe h.2.1 hσ hσ', iho h.2.2 hσ hσ'⟩
  | gate g ds s ihds ihs => intro Γ Δ σ M h hσ hσ'; exact ⟨ihds h.1 hσ hσ', ihs h.2 hσ hσ'⟩
  | node g ℓ ds p e ihds ihp ihe =>
    intro Γ Δ σ M h hσ hσ'
    obtain ⟨⟨Δg, σg, A, ρ, B, hg, hl, o, ω, ⟨dO⟩⟩, hds, hp, he⟩ := h
    obtain ⟨dO'⟩ := dO.subst hS hσ
    simp only [Judg.substJ] at dO'
    rw [origin_instType_subst hS hg hl] at dO'
    exact ⟨⟨Δg, σg, A, ρ, B, hg, hl.subst _, _, _, ⟨dO'⟩⟩, ihds hds hσ hσ', ihp hp hσ hσ',
      ihe he hσ hσ'⟩

/-- Converting the type of the nearest variable keeps the invariant. -/
theorem Justified.convCtx {S : Sig} (hS : SigWF S) {Γ : Ctx} {σ : Role} {A A' t : Exp}
    {α α' : Eff} (hΓ : CtxWF S Γ) (dA : Deriv S true (.ty Γ σ A α))
    (dA' : Deriv S true (.ty Γ σ A' α')) (hAA' : Conv A A')
    (h : Justified S ((σ, A) :: Γ) t) : Justified S ((σ, A') :: Γ) t := by
  have := Justified.subst hS t h (SubstOK.convCtx hS hΓ dA dA' hAA') (fun _ => trivial)
  rwa [Exp.subst_var] at this


/-! ## Reduction keeps the invariant -/

/-- Reduction keeps the invariant: a reduct of a well-typed justified expression
is justified. -/
theorem Deriv.justified_step {S : Sig} (hS : SigWF S) {j : Judg} (d : Deriv S true j) :
    match j with
    | .ty Γ _ A _ => CtxWF S Γ → Justified S Γ A → ∀ {A'}, Step A A' → Justified S Γ A'
    | .tm Γ _ t _ _ => CtxWF S Γ → Justified S Γ t → ∀ {t'}, Step t t' → Justified S Γ t'
    | .spine Γ ts _ _ =>
        CtxWF S Γ → Justified S Γ ts → ∀ {ts'}, Step ts ts' → Justified S Γ ts'
    | .tel _ _ _ => True := by
  induction d with
  | tyFam _ _ _ _ ih =>
    intro hΓ hJ A' hstep
    cases hstep with
    | fam h => have := ih hΓ hJ h; exact this
  | tyEvent => intro hΓ _ A' hstep; cases hstep
  | tyOrigin _ _ _ _ _ ihA ihe iht =>
    intro hΓ hJ X hstep
    obtain ⟨hA, he, ht⟩ := hJ
    cases hstep with
    | origin₁ h => exact ⟨ihA hΓ hA h, he, ht⟩
    | origin₂ h => exact ⟨hA, ihe hΓ he h, ht⟩
    | origin₃ h => exact ⟨hA, he, iht hΓ ht h⟩
  | tyStamped _ _ _ _ ih =>
    intro hΓ hJ X hstep
    cases hstep with
    | stamped h => have := ih hΓ hJ h; exact this
  | @tyPi Γ q σ ρ A B α β ε dA dB hq hε hv ihA ihB =>
    intro hΓ hJ X hstep
    obtain ⟨-, hA, hB⟩ := hJ
    cases hstep with
    | pi₁ h =>
      obtain ⟨α', -, ⟨dA'⟩⟩ := dA.subject_reduction_ty hS hΓ h
      exact ⟨⟨_, ⟨dA'⟩⟩, ihA hΓ hA h, hB.convCtx hS hΓ dA dA' (Conv.of_step h)⟩
    | pi₂ h => exact ⟨⟨_, ⟨dA⟩⟩, hA, ihB (.cons hΓ ⟨dA⟩) hB h⟩
  | @tySigma Γ ρ A B α β ε dA dB hε hv ihA ihB =>
    intro hΓ hJ X hstep
    obtain ⟨-, hA, hB⟩ := hJ
    cases hstep with
    | sigma₁ h =>
      obtain ⟨α', -, ⟨dA'⟩⟩ := dA.subject_reduction_ty hS hΓ h
      exact ⟨⟨_, ⟨dA'⟩⟩, ihA hΓ hA h, hB.convCtx hS hΓ dA dA' (Conv.of_step h)⟩
    | sigma₂ h => exact ⟨⟨_, ⟨dA⟩⟩, hA, ihB (.cons hΓ ⟨dA⟩) hB h⟩
  | var => intro hΓ _ t' hstep; cases hstep
  | const => intro hΓ _ t' hstep; cases hstep
  | @lam Γ q σ ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro hΓ hJ X hstep
    obtain ⟨-, hA, ht⟩ := hJ
    cases hstep with
    | lam₁ h =>
      obtain ⟨α', -, ⟨dA'⟩⟩ := dA.subject_reduction_ty hS hΓ h
      exact ⟨⟨_, ⟨dA'⟩⟩, ihA hΓ hA h, ht.convCtx hS hΓ dA dA' (Conv.of_step h)⟩
    | lam₂ h => exact ⟨⟨_, ⟨dA⟩⟩, hA, iht (.cons hΓ ⟨dA⟩) ht h⟩
  | @app Γ q σ ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro hΓ hJ X hstep
    obtain ⟨hf, hu⟩ := hJ
    cases hstep with
    | @beta q' σ' A' b _ =>
      obtain ⟨⟨αA', ⟨dA'₀⟩⟩, -, hb⟩ := hf
      obtain ⟨B', θ, hc, -, -, ⟨α', ⟨dA'⟩⟩, -, -⟩ := df.inv_lam
      obtain ⟨rfl, rfl, hAA, -⟩ := Conv.pi_inj hc
      have du' : Deriv S true (.tm Γ σ' u A' η) := .conv du hAA.symm dA'
      refine Justified.subst hS b hb (SubstOK.inst1 hΓ du') fun i => ?_
      cases i with
      | zero => exact hu
      | succ => trivial
    | app₁ h => exact ⟨ihf hΓ hf h, hu⟩
    | app₂ h => exact ⟨hf, ihu hΓ hu h⟩
  | pair _ _ _ _ _ iht ihu _ =>
    intro hΓ hJ X hstep
    obtain ⟨ht, hu⟩ := hJ
    cases hstep with
    | pair₁ h => exact ⟨iht hΓ ht h, hu⟩
    | pair₂ h => exact ⟨ht, ihu hΓ hu h⟩
  | fst _ _ _ ihp _ =>
    intro hΓ hJ X hstep
    cases hstep with
    | fstPair => exact hJ.1
    | fst h => have := ihp hΓ hJ h; exact this
  | snd _ _ _ _ ihp _ =>
    intro hΓ hJ X hstep
    cases hstep with
    | sndPair => exact hJ.2
    | snd h => have := ihp hΓ hJ h; exact this
  | stamp _ _ _ _ _ _ iht ihe iho _ =>
    intro hΓ hJ X hstep
    obtain ⟨ht, he, ho⟩ := hJ
    cases hstep with
    | stamp₁ h => exact ⟨iht hΓ ht h, he, ho⟩
    | stamp₂ h => exact ⟨ht, ihe hΓ he h, ho⟩
    | stamp₃ h => exact ⟨ht, he, iho hΓ ho h⟩
  | @gate Γ g ds s Δt σg A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro hΓ hJ X hstep
    obtain ⟨hds, hs⟩ := hJ
    cases hstep with
    | @record _ _ t e o =>
      obtain ⟨ht, he, ho⟩ := hs
      obtain ⟨hσg, -⟩ := hS.gate_cond hg
      obtain ⟨σ', A', θ, η', ω, -, hc, -, ⟨dt⟩, ⟨de⟩, ⟨dorg⟩, -⟩ := dst.inv_stamp
      obtain ⟨rfl, hAA⟩ := Conv.stamped_inj hc
      obtain ⟨γs, ⟨dS⟩⟩ := dst.tm_ty
      obtain ⟨-, -, αX, ⟨dX⟩⟩ := dS.inv_tyStamped
      have dt' : Deriv S true (.tm Γ σ' t (instType ds Δt A) θ) := .conv dt hAA dX
      have dF : Deriv S true (.ty Γ .witness (.origin (instType ds Δt A) e t) (αX ⊓ η' ⊓ θ)) :=
        .tyOrigin dX de dt' rfl (fun _ => ((dX.valid_ty.toWitness hσg).inf de.valid_tm).inf
          (dt'.valid_tm.toWitness hσg))
      have hco : Conv (.origin A' e t) (.origin (instType ds Δt A) e t) :=
        Conv.lift (fun X => Exp.origin X e t) Step.origin₁ hAA
      exact ⟨⟨Δt, σ', A, ρ, B, hg, dds.isList, o, _, ⟨.conv dorg hco dF⟩⟩, hds, ht, he⟩
    | gate₁ h => exact ⟨ihds hΓ hds h, hs⟩
    | gate₂ h => exact ⟨hds, ihst hΓ hs h⟩
  | @node Γ g ℓ ds t e Δt σg A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro hΓ hJ X hstep
    obtain ⟨⟨Δ', σ', A', ρ', B', hg', hl, o, ω, ⟨dO⟩⟩, hds, ht, he⟩ := hJ
    rw [hg] at hg'
    cases hg'
    obtain ⟨hσg, -⟩ := hS.gate_cond hg
    obtain ⟨⟨δt, ⟨dtel⟩⟩, ⟨δA, ⟨dtelA⟩⟩, -⟩ := hS.gate_tel hg Γ
    obtain ⟨γX, ⟨dX⟩⟩ := dt.tm_ty
    cases hstep with
    | @node₁ _ _ _ ds' _ _ h =>
      obtain ⟨δ', -, ⟨dds'⟩⟩ := dds.sr hS hΓ ⟨_, ⟨dtel⟩⟩ h
      obtain ⟨αX', ⟨dX'⟩⟩ := dds'.instType_formed hS hΓ dtelA
      have hcA : Conv (instType ds Δt A) (instType ds' Δt A) :=
        Conv.of_steps (instType_step_args h hl Δt A)
      have dt' : Deriv S true (.tm Γ σg t (instType ds' Δt A) θ) := .conv dt hcA dX'
      have dF : Deriv S true (.ty Γ .witness (.origin (instType ds' Δt A) e t)
          (αX' ⊓ η ⊓ θ)) :=
        .tyOrigin dX' de dt' rfl (fun _ => ((dX'.valid_ty.toWitness hσg).inf de.valid_tm).inf
          (dt'.valid_tm.toWitness hσg))
      have hco : Conv (.origin (instType ds Δt A) e t) (.origin (instType ds' Δt A) e t) :=
        Conv.lift (fun X => Exp.origin X e t) Step.origin₁ hcA
      exact ⟨⟨Δt, σg, A, ρ, B, hg, dds'.isList, o, _, ⟨.conv dO hco dF⟩⟩, ihds hΓ hds h,
        ht, he⟩
    | @node₂ _ _ _ _ t' _ h =>
      obtain ⟨θ', -, ⟨dt'⟩⟩ := dt.subject_reduction hS hΓ h
      have dF : Deriv S true (.ty Γ .witness (.origin (instType ds Δt A) e t') (γX ⊓ η ⊓ θ')) :=
        .tyOrigin dX de dt' rfl (fun _ => ((dX.valid_ty.toWitness hσg).inf de.valid_tm).inf
          (dt'.valid_tm.toWitness hσg))
      have hco : Conv (.origin (instType ds Δt A) e t) (.origin (instType ds Δt A) e t') :=
        Conv.of_step (Step.origin₃ h)
      exact ⟨⟨Δt, σg, A, ρ, B, hg, hl, o, _, ⟨.conv dO hco dF⟩⟩, hds, iht hΓ ht h, he⟩
    | @node₃ _ _ _ _ _ e' h =>
      obtain ⟨η', -, ⟨de'⟩⟩ := de.subject_reduction hS hΓ h
      have dF : Deriv S true (.ty Γ .witness (.origin (instType ds Δt A) e' t) (γX ⊓ η' ⊓ θ)) :=
        .tyOrigin dX de' dt rfl (fun _ => ((dX.valid_ty.toWitness hσg).inf de'.valid_tm).inf
          (dt.valid_tm.toWitness hσg))
      have hco : Conv (.origin (instType ds Δt A) e t) (.origin (instType ds Δt A) e' t) :=
        Conv.of_step (Step.origin₂ h)
      exact ⟨⟨Δt, σg, A, ρ, B, hg, hl, o, _, ⟨.conv dO hco dF⟩⟩, hds, ht, ihe hΓ he h⟩
  | conv _ _ _ iht _ =>
    intro hΓ hJ X hstep
    exact iht hΓ hJ hstep
  | spineNil => intro hΓ _ ts' hstep; cases hstep
  | spineCons _ _ _ iht ihts =>
    intro hΓ hJ ts' hstep
    obtain ⟨ht, hts⟩ := hJ
    cases hstep with
    | cons₁ h => exact ⟨iht hΓ ht h, hts⟩
    | cons₂ h => exact ⟨ht, ihts hΓ hts h⟩
  | telNil => trivial
  | telCons => trivial


/-- Reduction keeps the invariant, in any number of steps. -/
theorem Deriv.justified_steps {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {t A : Exp}
    {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) (hJ : Justified S Γ t)
    {t' : Exp} (h : Steps t t') : Justified S Γ t' := by
  induction h with
  | refl => exact hJ
  | @tail u v hs hst ih =>
    obtain ⟨ε', -, ⟨du⟩⟩ := d.subject_reduction_steps hS hΓ hs
    exact du.justified_step hS hΓ ih hst

/-! ## Public expressions are justified -/

/-- A well-typed public expression is justified: it has no private node, and its
binder annotations are formed. -/
theorem Deriv.justified_of_public {S : Sig} {j : Judg} (d : Deriv S true j) :
    match j with
    | .ty Γ _ A _ => A.IsPublic → Justified S Γ A
    | .tm Γ _ t _ _ => t.IsPublic → Justified S Γ t
    | .spine Γ ts _ _ => ts.IsPublic → Justified S Γ ts
    | .tel _ _ _ => True := by
  induction d with
  | tyFam _ _ _ _ ih => intro h; exact ih h
  | tyEvent => intro _; trivial
  | tyOrigin _ _ _ _ _ ihA ihe iht => intro h; exact ⟨ihA h.1, ihe h.2.1, iht h.2.2⟩
  | tyStamped _ _ _ _ ih => intro h; exact ih h
  | tyPi dA _ _ _ _ ihA ihB => intro h; exact ⟨⟨_, ⟨dA⟩⟩, ihA h.1, ihB h.2⟩
  | tySigma dA _ _ _ ihA ihB => intro h; exact ⟨⟨_, ⟨dA⟩⟩, ihA h.1, ihB h.2⟩
  | var => intro _; trivial
  | const => intro _; trivial
  | lam dA _ _ _ _ _ ihA iht _ => intro h; exact ⟨⟨_, ⟨dA⟩⟩, ihA h.1, iht h.2⟩
  | app _ _ _ _ _ _ ihf ihu _ => intro h; exact ⟨ihf h.1, ihu h.2⟩
  | pair _ _ _ _ _ iht ihu _ => intro h; exact ⟨iht h.1, ihu h.2⟩
  | fst _ _ _ ihp _ => intro h; exact ihp h
  | snd _ _ _ _ ihp _ => intro h; exact ihp h
  | stamp _ _ _ _ _ _ iht ihe iho _ => intro h; exact ⟨iht h.1, ihe h.2.1, iho h.2.2⟩
  | gate _ _ _ _ _ _ _ ihds ihs _ => intro h; exact ⟨ihds h.1, ihs h.2⟩
  | node => intro h; exact h.elim
  | conv _ _ _ iht _ => intro h; exact iht h
  | spineNil => intro _; trivial
  | spineCons _ _ _ iht ihts => intro h; exact ⟨iht h.1, ihts h.2⟩
  | telNil => trivial
  | telCons => trivial

/-- Every reduct of a well-typed public term is justified. -/
theorem Deriv.justified_of_reduct {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {t A : Exp}
    {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) (hpub : t.IsPublic)
    {t' : Exp} (h : Steps t t') : Justified S Γ t' :=
  d.justified_steps hS hΓ (d.justified_of_public hpub) h

end Artform.Roles.Calculus
