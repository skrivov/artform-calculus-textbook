import ArtformRoles.Calculus.SigWeaken
import ArtformRoles.Calculus.Injectivity

/-!
# Subject reduction with effect improvement

Theorem 8.5 of the paper: if `Σ; Γ ⊢_ρ t : A ▷ ε` and `t ⟶ t'`, then
`Σ; Γ ⊢_ρ t' : A ▷ ε'` for some `ε ≤ ε'`; consequently policy validity is
preserved, and the analogous result holds for reduction in types
(`Deriv.subject_reduction`, `Deriv.subject_reduction_ty`, and the multi-step
versions). Contexts and the signature are presupposed well formed.

Moving up means that a dependency becomes more mediated or disappears: the
β-step may raise `q ⊗ η` to `θ(x) ⊗ η`, a projection discards a component, and
the record step discards the origin proof.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Inversion of formation rules -/

theorem Deriv.inv_tyPi {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {q : Grade} {A B : Exp}
    {ε : Eff} (d : Deriv S acc (.ty Γ ρ (.pi q σ A B) ε)) :
    (∃ α, Derivable S acc (.ty Γ σ A α)) ∧ (∃ β, Derivable S acc (.ty ((σ, A) :: Γ) ρ B β)) := by
  cases d with
  | tyPi dA dB => exact ⟨⟨_, ⟨dA⟩⟩, ⟨_, ⟨dB⟩⟩⟩

theorem Deriv.inv_tySigma {S : Sig} {acc : Bool} {Γ : Ctx} {ρ ρ' : Role} {A B : Exp} {ε : Eff}
    (d : Deriv S acc (.ty Γ ρ (.sigma ρ' A B) ε)) :
    ρ' = ρ ∧ (∃ α, Derivable S acc (.ty Γ ρ A α)) ∧
      (∃ β, Derivable S acc (.ty ((ρ, A) :: Γ) ρ B β)) := by
  cases d with
  | tySigma dA dB => exact ⟨rfl, ⟨_, ⟨dA⟩⟩, ⟨_, ⟨dB⟩⟩⟩

theorem Deriv.inv_tyStamped {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {A : Exp} {ε : Eff}
    (d : Deriv S acc (.ty Γ ρ (.stamped σ A) ε)) :
    ρ = .witness ∧ σ ≠ .rendering ∧ ∃ α, Derivable S acc (.ty Γ σ A α) := by
  cases d with
  | tyStamped dA hσ => exact ⟨rfl, hσ, ⟨_, ⟨dA⟩⟩⟩

theorem Valid.inf {S : Sig} {Γ : Ctx} {ρ : Role} {ε η : Eff} (h₁ : Valid S Γ ρ ε)
    (h₂ : Valid S Γ ρ η) : Valid S Γ ρ (ε ⊓ η) :=
  fun z r hz => le_inf (h₁ z r hz) (h₂ z r hz)

/-- Witness data may depend on whatever a non-rendering datum may depend on. -/
theorem Valid.toWitness {S : Sig} {Γ : Ctx} {σ : Role} {ε : Eff} (hσ : σ ≠ .rendering)
    (hv : Valid S Γ σ ε) : Valid S Γ .witness ε := by
  intro z r hz
  refine le_trans ?_ (hv z r hz)
  cases r <;> cases σ <;> first | exact absurd rfl hσ | decide

/-- The side conditions of a declared gate. -/
theorem SigWF.gate_cond {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) :
    σ ≠ .rendering ∧ (ρ = .form ∨ ρ = .presentation) ∧ (∀ p ∈ Δ, demand p.1 ρ = .free) ∧
      demand σ ρ ≤ .gated ∧ B.gradefree := by
  induction hS with
  | nil => simp [Sig.gate?] at h
  | gate _ _ _ _ hρ hσ hΔ hσρ hB _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, hp⟩
    · exact ih h
    · cases he; cases hp; exact ⟨hσ, hρ, hΔ, hσρ, hB⟩
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
    · exact ih h
    · cases he

/-- The interface of a declared gate is grade-free: its parameter types and its
payload type, as well as its result type. -/
theorem SigWF.gate_gradefree {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B : Exp} (h : S.gate? g = some (Δ, σ, A, ρ, B)) :
    (∀ p ∈ Δ, p.2.gradefree) ∧ A.gradefree := by
  induction hS with
  | nil => simp [Sig.gate?] at h
  | gate _ _ _ _ _ _ _ _ _ hΔ hA ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, hp⟩
    · exact ih h
    · cases he; cases hp; exact ⟨hΔ, hA⟩
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
    · exact ih h
    · cases he

/-! ## Subject reduction -/

/-- Subject reduction for every judgment form: formation, typing and argument
lists (whose telescope is formed in the context). -/
theorem Deriv.sr {S : Sig} (hS : SigWF S) {j : Judg} (d : Deriv S true j) :
    match j with
    | .ty Γ ρ A α => CtxWF S Γ → ∀ {A'}, Step A A' →
        ∃ α', α ≤ α' ∧ Derivable S true (.ty Γ ρ A' α')
    | .tm Γ ρ t A ε => CtxWF S Γ → ∀ {t'}, Step t t' →
        ∃ ε', ε ≤ ε' ∧ Derivable S true (.tm Γ ρ t' A ε')
    | .spine Γ ts Δ ε => CtxWF S Γ → (∃ δ, Derivable S true (.tel Γ Δ δ)) → ∀ {ts'},
        Step ts ts' → ∃ ε', ε ≤ ε' ∧ Derivable S true (.spine Γ ts' Δ ε')
    | .tel _ _ _ => True := by
  induction d with
  | @tyFam Γ a args Δt ρ δ ε hS' dargs hε hv ih =>
    intro hΓ A' hstep
    cases hstep with
    | fam hargs =>
      obtain ⟨δ', hle, ⟨dargs'⟩⟩ := ih hΓ (hS.family_tel hS' Γ) hargs
      subst hε
      have hle' : Eff.unit (.decl a 0) ⊓ δ ≤ Eff.unit (.decl a 0) ⊓ δ' := inf_le_inf le_rfl hle
      exact ⟨_, hle', ⟨.tyFam hS' dargs' rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | tyEvent hε =>
    intro hΓ A' hstep
    cases hstep
  | @tyOrigin Γ σ A e t α η θ ε dA de dt hε hv ihA ihe iht =>
    intro hΓ X hstep
    subst hε
    cases hstep with
    | origin₁ hA =>
      obtain ⟨α', hle, ⟨dA'⟩⟩ := ihA hΓ hA
      have hle' : α ⊓ η ⊓ θ ≤ α' ⊓ η ⊓ θ := inf_le_inf (inf_le_inf hle le_rfl) le_rfl
      exact ⟨_, hle', ⟨.tyOrigin dA' de (.conv dt (Conv.of_step hA) dA') rfl
        (fun _ => (hv rfl).mono hle')⟩⟩
    | origin₂ he =>
      obtain ⟨η', hle, ⟨de'⟩⟩ := ihe hΓ he
      have hle' : α ⊓ η ⊓ θ ≤ α ⊓ η' ⊓ θ := inf_le_inf (inf_le_inf le_rfl hle) le_rfl
      exact ⟨_, hle', ⟨.tyOrigin dA de' dt rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | origin₃ ht =>
      obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht hΓ ht
      have hle' : α ⊓ η ⊓ θ ≤ α ⊓ η ⊓ θ' := inf_le_inf le_rfl hle
      exact ⟨_, hle', ⟨.tyOrigin dA de dt' rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | @tyStamped Γ σ A α ε dA hσ hε hv ihA =>
    intro hΓ X hstep
    subst hε
    cases hstep with
    | stamped hA =>
      obtain ⟨α', hle, ⟨dA'⟩⟩ := ihA hΓ hA
      exact ⟨_, hle, ⟨.tyStamped dA' hσ rfl (fun _ => (hv rfl).mono hle)⟩⟩
  | @tyPi Γ q σ ρ A B α β ε dA dB hq hε hv ihA ihB =>
    intro hΓ X hstep
    subst hε
    cases hstep with
    | pi₁ hA =>
      obtain ⟨α', hle, ⟨dA'⟩⟩ := ihA hΓ hA
      obtain ⟨dB'⟩ := dB.ctx_conv_ty hS hΓ dA dA' (Conv.of_step hA)
      have hle' : Eff.scale q α ⊓ β.unbind ≤ Eff.scale q α' ⊓ β.unbind :=
        inf_le_inf (Eff.scale_mono le_rfl hle) le_rfl
      exact ⟨_, hle', ⟨.tyPi dA' dB' hq rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | pi₂ hB =>
      obtain ⟨β', hle, ⟨dB'⟩⟩ := ihB (.cons hΓ ⟨dA⟩) hB
      have hle' : Eff.scale q α ⊓ β.unbind ≤ Eff.scale q α ⊓ β'.unbind :=
        inf_le_inf le_rfl (Eff.unbind_mono hle)
      exact ⟨_, hle', ⟨.tyPi dA dB' hq rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | @tySigma Γ ρ A B α β ε dA dB hε hv ihA ihB =>
    intro hΓ X hstep
    subst hε
    cases hstep with
    | sigma₁ hA =>
      obtain ⟨α', hle, ⟨dA'⟩⟩ := ihA hΓ hA
      obtain ⟨dB'⟩ := dB.ctx_conv_ty hS hΓ dA dA' (Conv.of_step hA)
      have hle' : α ⊓ β.unbind ≤ α' ⊓ β.unbind := inf_le_inf hle le_rfl
      exact ⟨_, hle', ⟨.tySigma dA' dB' rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | sigma₂ hB =>
      obtain ⟨β', hle, ⟨dB'⟩⟩ := ihB (.cons hΓ ⟨dA⟩) hB
      have hle' : α ⊓ β.unbind ≤ α ⊓ β'.unbind := inf_le_inf le_rfl (Eff.unbind_mono hle)
      exact ⟨_, hle', ⟨.tySigma dA dB' rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | var =>
    intro hΓ t' hstep
    cases hstep
  | const =>
    intro hΓ t' hstep
    cases hstep
  | @lam Γ q σ ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro hΓ X hstep
    subst hε
    cases hstep with
    | lam₁ hA =>
      obtain ⟨α', -, ⟨dA'⟩⟩ := ihA hΓ hA
      obtain ⟨dt'⟩ := dt.ctx_conv_tm hS hΓ dA dA' (Conv.of_step hA)
      obtain ⟨γ', -, ⟨dC'⟩⟩ := ihC hΓ (Step.pi₁ hA)
      exact ⟨_, le_rfl, ⟨.conv (.lam dA' dt' hq dC' rfl hv) (Conv.of_step (Step.pi₁ hA)).symm dC⟩⟩
    | lam₂ ht =>
      obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht (.cons hΓ ⟨dA⟩) ht
      exact ⟨_, Eff.unbind_mono hle, ⟨.lam dA dt' (le_trans hq (hle _)) dC rfl
        (fun _ => (hv rfl).mono (Eff.unbind_mono hle))⟩⟩
  | @app Γ q σ ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro hΓ X hstep
    subst hε hC
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    obtain ⟨⟨αA, ⟨dA⟩⟩, ⟨βB, ⟨dB⟩⟩⟩ := dpi.inv_tyPi
    cases hstep with
    | @beta q' σ' A' b _ =>
      obtain ⟨B', θ, hc, hq', hφ, ⟨α', ⟨dA'⟩⟩, ⟨db⟩, -⟩ := df.inv_lam
      obtain ⟨rfl, rfl, hAA, hBB⟩ := Conv.pi_inj hc
      obtain ⟨db'⟩ := db.ctx_conv_tm hS hΓ dA' dA hAA
      obtain ⟨d'⟩ := (Deriv.conv db' hBB dB).inst_tm hS hΓ du
      subst hφ
      refine ⟨_, ?_, ⟨d'⟩⟩
      exact inf_le_inf le_rfl (Eff.scale_mono hq' le_rfl)
    | app₁ hf =>
      obtain ⟨φ', hle, ⟨df'⟩⟩ := ihf hΓ hf
      have hle' : φ ⊓ Eff.scale q η ≤ φ' ⊓ Eff.scale q η := inf_le_inf hle le_rfl
      exact ⟨_, hle', ⟨.app df' du rfl dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | app₂ hu =>
      obtain ⟨η', hle, ⟨du'⟩⟩ := ihu hΓ hu
      obtain ⟨dBu⟩ := dB.inst_ty hS hΓ du'
      have hle' : φ ⊓ Eff.scale q η ≤ φ ⊓ Eff.scale q η' :=
        inf_le_inf le_rfl (Eff.scale_mono le_rfl hle)
      have hc : Conv (B.inst u) (B.inst _) := Conv.of_steps (Steps.inst_arg (.single hu) B)
      exact ⟨_, hle', ⟨.conv (.app df du' rfl dBu rfl (fun _ => (hv rfl).mono hle')) hc.symm dC⟩⟩
  | @pair Γ ρ A B t u θ η γ ε dt du dC hε hv iht ihu ihC =>
    intro hΓ X hstep
    subst hε
    obtain ⟨-, ⟨αA, ⟨dA⟩⟩, ⟨βB, ⟨dB⟩⟩⟩ := dC.inv_tySigma
    cases hstep with
    | pair₁ ht =>
      obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht hΓ ht
      obtain ⟨dBt⟩ := dB.inst_ty hS hΓ dt'
      have hc : Conv (B.inst t) (B.inst _) := Conv.of_steps (Steps.inst_arg (.single ht) B)
      have hle' : θ ⊓ η ≤ θ' ⊓ η := inf_le_inf hle le_rfl
      exact ⟨_, hle', ⟨.pair dt' (.conv du hc dBt) dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | pair₂ hu =>
      obtain ⟨η', hle, ⟨du'⟩⟩ := ihu hΓ hu
      have hle' : θ ⊓ η ≤ θ ⊓ η' := inf_le_inf le_rfl hle
      exact ⟨_, hle', ⟨.pair dt du' dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | @fst Γ ρ A B p π γ dp dA hv ihp ihA =>
    intro hΓ X hstep
    cases hstep with
    | fstPair =>
      obtain ⟨A', B', θ, η, hc, hπ, ⟨dt⟩, -, -⟩ := dp.inv_pair
      obtain ⟨-, hAA, -⟩ := Conv.sigma_inj hc
      subst hπ
      exact ⟨_, inf_le_left, ⟨.conv dt hAA dA⟩⟩
    | fst hp =>
      obtain ⟨π', hle, ⟨dp'⟩⟩ := ihp hΓ hp
      exact ⟨_, hle, ⟨.fst dp' dA (fun _ => (hv rfl).mono hle)⟩⟩
  | @snd Γ ρ A B C p π γ dp hC dC hv ihp ihC =>
    intro hΓ X hstep
    subst hC
    cases hstep with
    | @sndPair t u =>
      obtain ⟨A', B', θ, η, hc, hπ, -, ⟨du⟩, -⟩ := dp.inv_pair
      obtain ⟨-, -, hBB⟩ := Conv.sigma_inj hc
      subst hπ
      have h₁ : Conv (B'.inst t) (B.inst t) := hBB.subst _
      refine ⟨_, inf_le_right, ⟨.conv du (h₁.trans ?_) dC⟩⟩
      exact (Conv.of_steps (Steps.inst_arg (.single .fstPair) B)).symm
    | snd hp =>
      obtain ⟨π', hle, ⟨dp'⟩⟩ := ihp hΓ hp
      obtain ⟨γs, ⟨ds⟩⟩ := dp.tm_ty
      obtain ⟨-, ⟨αA, ⟨dA⟩⟩, ⟨βB, ⟨dB⟩⟩⟩ := ds.inv_tySigma
      have dfst : Deriv S true (.tm Γ ρ (.fst _) A π') := .fst dp' dA (fun _ => (hv rfl).mono hle)
      obtain ⟨dBf⟩ := dB.inst_ty hS hΓ dfst
      have hc : Conv (B.inst (.fst p)) (B.inst (.fst _)) :=
        Conv.of_steps (Steps.inst_arg (.single (.fst hp)) B)
      exact ⟨_, hle, ⟨.conv (.snd dp' rfl dBf (fun _ => (hv rfl).mono hle)) hc.symm dC⟩⟩
  | @stamp Γ σ A t e o θ η ω γ ε dt de dorg dC hε hv iht ihe iho ihC =>
    intro hΓ X hstep
    subst hε
    obtain ⟨-, hσ, αA, ⟨dA⟩⟩ := dC.inv_tyStamped
    cases hstep with
    | stamp₁ ht =>
      obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht hΓ ht
      have dO : Deriv S true (.ty Γ .witness (.origin A e _) (αA ⊓ η ⊓ θ')) :=
        .tyOrigin dA de dt' rfl (fun _ => (((dA.valid_ty.toWitness hσ).inf
          de.valid_tm)).inf (dt'.valid_tm.toWitness hσ))
      have hc : Conv (.origin A e t) (.origin A e _) := Conv.of_step (.origin₃ ht)
      have hle' : θ ⊓ η ⊓ ω ≤ θ' ⊓ η ⊓ ω := inf_le_inf (inf_le_inf hle le_rfl) le_rfl
      exact ⟨_, hle', ⟨.stamp dt' de (.conv dorg hc dO) dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | stamp₂ he =>
      obtain ⟨η', hle, ⟨de'⟩⟩ := ihe hΓ he
      have dO : Deriv S true (.ty Γ .witness (.origin A _ t) (αA ⊓ η' ⊓ θ)) :=
        .tyOrigin dA de' dt rfl (fun _ => (((dA.valid_ty.toWitness hσ).inf
          de'.valid_tm)).inf (dt.valid_tm.toWitness hσ))
      have hc : Conv (.origin A e t) (.origin A _ t) := Conv.of_step (.origin₂ he)
      have hle' : θ ⊓ η ⊓ ω ≤ θ ⊓ η' ⊓ ω := inf_le_inf (inf_le_inf le_rfl hle) le_rfl
      exact ⟨_, hle', ⟨.stamp dt de' (.conv dorg hc dO) dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | stamp₃ ho =>
      obtain ⟨ω', hle, ⟨dorg'⟩⟩ := iho hΓ ho
      have hle' : θ ⊓ η ⊓ ω ≤ θ ⊓ η ⊓ ω' := inf_le_inf le_rfl hle
      exact ⟨_, hle', ⟨.stamp dt de dorg' dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | @gate Γ g ds s Δt σg A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro hΓ X hstep
    subst hε hC
    obtain ⟨hσg, -⟩ := hS.gate_cond hg
    obtain ⟨⟨δt, ⟨dtel⟩⟩, ⟨δA, ⟨dtelA⟩⟩, ⟨δB, ⟨dtelB⟩⟩⟩ := hS.gate_tel hg Γ
    cases hstep with
    | @record _ _ t e o =>
      obtain ⟨σ', A', θ, η', ω, -, hc, hη, ⟨dt⟩, ⟨de⟩, -, -⟩ := dst.inv_stamp
      obtain ⟨rfl, hAA⟩ := Conv.stamped_inj hc
      obtain ⟨γs, ⟨dS⟩⟩ := dst.tm_ty
      obtain ⟨-, -, αX, ⟨dX⟩⟩ := dS.inv_tyStamped
      subst hη
      have hle : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η' ⊓ ω) ≤
          Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η') :=
        inf_le_inf le_rfl (Eff.scale_mono le_rfl inf_le_left)
      exact ⟨_, hle, ⟨.node hg dds (.conv dt hAA dX) de rfl dC rfl
        (fun _ => (hv rfl).mono hle)⟩⟩
    | gate₁ hds =>
      obtain ⟨δ', hle, ⟨dds'⟩⟩ := ihds hΓ ⟨_, ⟨dtel⟩⟩ hds
      obtain ⟨αX, ⟨dX⟩⟩ := dds'.instType_formed hS hΓ dtelA
      obtain ⟨βY, ⟨dY⟩⟩ := dds'.instType_formed hS hΓ dtelB
      have hl := dds.isList
      have hcA : Conv (.stamped σg (instType ds Δt A)) (.stamped σg (instType _ Δt A)) :=
        Conv.of_steps (Steps.lift (Exp.stamped σg) Step.stamped (instType_step_args hds hl Δt A))
      have hcB : Conv (instType ds Δt B) (instType _ Δt B) :=
        Conv.of_steps (instType_step_args hds hl Δt B)
      have dSt : Deriv S true (.ty Γ .witness (.stamped σg (instType _ Δt A)) αX) :=
        .tyStamped dX hσg rfl (fun _ => dX.valid_ty.toWitness hσg)
      have hle' : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η ≤
          Eff.unit (.decl g 0) ⊓ δ' ⊓ Eff.scale .gated η :=
        inf_le_inf (inf_le_inf le_rfl hle) le_rfl
      exact ⟨_, hle', ⟨.conv (.gate hg dds' (.conv dst hcA dSt) rfl dY rfl
        (fun _ => (hv rfl).mono hle')) hcB.symm dC⟩⟩
    | gate₂ hs =>
      obtain ⟨η', hle, ⟨dst'⟩⟩ := ihst hΓ hs
      have hle' : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η ≤
          Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η' :=
        inf_le_inf le_rfl (Eff.scale_mono le_rfl hle)
      exact ⟨_, hle', ⟨.gate hg dds dst' rfl dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | @node Γ g ℓ ds t e Δt σg A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro hΓ X hstep
    subst hε hC
    obtain ⟨⟨δt, ⟨dtel⟩⟩, ⟨δA, ⟨dtelA⟩⟩, ⟨δB, ⟨dtelB⟩⟩⟩ := hS.gate_tel hg Γ
    cases hstep with
    | node₁ hds =>
      obtain ⟨δ', hle, ⟨dds'⟩⟩ := ihds hΓ ⟨_, ⟨dtel⟩⟩ hds
      obtain ⟨αX, ⟨dX⟩⟩ := dds'.instType_formed hS hΓ dtelA
      obtain ⟨βY, ⟨dY⟩⟩ := dds'.instType_formed hS hΓ dtelB
      have hl := dds.isList
      have hcA : Conv (instType ds Δt A) (instType _ Δt A) :=
        Conv.of_steps (instType_step_args hds hl Δt A)
      have hcB : Conv (instType ds Δt B) (instType _ Δt B) :=
        Conv.of_steps (instType_step_args hds hl Δt B)
      have hle' : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η) ≤
          Eff.unit (.decl g 0) ⊓ δ' ⊓ Eff.scale .gated (θ ⊓ η) :=
        inf_le_inf (inf_le_inf le_rfl hle) le_rfl
      exact ⟨_, hle', ⟨.conv (.node hg dds' (.conv dt hcA dX) de rfl dY rfl
        (fun _ => (hv rfl).mono hle')) hcB.symm dC⟩⟩
    | node₂ ht =>
      obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht hΓ ht
      have hle' : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η) ≤
          Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ' ⊓ η) :=
        inf_le_inf le_rfl (Eff.scale_mono le_rfl (inf_le_inf hle le_rfl))
      exact ⟨_, hle', ⟨.node hg dds dt' de rfl dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
    | node₃ he =>
      obtain ⟨η', hle, ⟨de'⟩⟩ := ihe hΓ he
      have hle' : Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η) ≤
          Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η') :=
        inf_le_inf le_rfl (Eff.scale_mono le_rfl (inf_le_inf le_rfl hle))
      exact ⟨_, hle', ⟨.node hg dds dt de' rfl dC rfl (fun _ => (hv rfl).mono hle')⟩⟩
  | conv dt hAB dB iht ihB =>
    intro hΓ X hstep
    obtain ⟨θ', hle, ⟨dt'⟩⟩ := iht hΓ hstep
    exact ⟨_, hle, ⟨.conv dt' hAB dB⟩⟩
  | spineNil hε =>
    intro hΓ _ ts' hstep
    cases hstep
  | @spineCons Γ ρ t ts A Δ' ε₁ ε₂ ε dt dts hε iht ihts =>
    intro hΓ htel ts' hstep
    subst hε
    obtain ⟨δ, ⟨dtel⟩⟩ := htel
    cases dtel with
    | telCons dA drest =>
      cases hstep with
      | cons₁ ht =>
        obtain ⟨ε₁', hle, ⟨dt'⟩⟩ := iht hΓ ht
        obtain ⟨drest'⟩ := drest.subst hS (SubstOK.inst1 hΓ dt')
        simp only [Judg.substJ] at drest'
        obtain ⟨dts'⟩ := dts.spine_conv hS hΓ (TelConv.inst_steps (.single ht) Δ') drest'
        exact ⟨_, inf_le_inf hle le_rfl, ⟨.spineCons dt' dts' rfl⟩⟩
      | cons₂ hts =>
        obtain ⟨drest'⟩ := drest.subst hS (SubstOK.inst1 hΓ dt)
        simp only [Judg.substJ] at drest'
        obtain ⟨ε₂', hle, ⟨dts'⟩⟩ := ihts hΓ ⟨_, ⟨drest'⟩⟩ hts
        exact ⟨_, inf_le_inf le_rfl hle, ⟨.spineCons dt dts' rfl⟩⟩
  | telNil => trivial
  | telCons => trivial

/-- Theorem 8.5 (subject reduction with effect improvement). -/
theorem Deriv.subject_reduction {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {t A : Exp}
    {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) {t' : Exp} (h : Step t t') :
    ∃ ε', ε ≤ ε' ∧ Derivable S true (.tm Γ ρ t' A ε') :=
  d.sr hS hΓ h

/-- Theorem 8.5 for reduction in types. -/
theorem Deriv.subject_reduction_ty {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {A : Exp}
    {α : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.ty Γ ρ A α)) {A' : Exp} (h : Step A A') :
    ∃ α', α ≤ α' ∧ Derivable S true (.ty Γ ρ A' α') :=
  d.sr hS hΓ h

/-- Subject reduction along a reduction sequence. -/
theorem Deriv.subject_reduction_steps {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role}
    {t A : Exp} {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) {t' : Exp}
    (h : Steps t t') : ∃ ε', ε ≤ ε' ∧ Derivable S true (.tm Γ ρ t' A ε') := by
  induction h with
  | refl => exact ⟨ε, le_rfl, ⟨d⟩⟩
  | tail _ hs ih =>
    obtain ⟨ε₁, hle₁, ⟨d₁⟩⟩ := ih
    obtain ⟨ε₂, hle₂, hd₂⟩ := d₁.subject_reduction hS hΓ hs
    exact ⟨ε₂, le_trans hle₁ hle₂, hd₂⟩

/-- Subject reduction along a reduction sequence of types. -/
theorem Deriv.subject_reduction_ty_steps {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role}
    {A : Exp} {α : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.ty Γ ρ A α)) {A' : Exp}
    (h : Steps A A') : ∃ α', α ≤ α' ∧ Derivable S true (.ty Γ ρ A' α') := by
  induction h with
  | refl => exact ⟨α, le_rfl, ⟨d⟩⟩
  | tail _ hs ih =>
    obtain ⟨α₁, hle₁, ⟨d₁⟩⟩ := ih
    obtain ⟨α₂, hle₂, hd₂⟩ := d₁.subject_reduction_ty hS hΓ hs
    exact ⟨α₂, le_trans hle₁ hle₂, hd₂⟩

/-- Policy validity is preserved by reduction: the reduct's effect is valid. -/
theorem Deriv.valid_of_steps {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {t A : Exp}
    {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) {t' : Exp}
    (h : Steps t t') : ∃ ε', ε ≤ ε' ∧ Valid S Γ ρ ε' := by
  obtain ⟨ε', hle, ⟨d'⟩⟩ := d.subject_reduction_steps hS hΓ h
  exact ⟨ε', hle, d'.valid_tm⟩

end Artform.Roles.Calculus
