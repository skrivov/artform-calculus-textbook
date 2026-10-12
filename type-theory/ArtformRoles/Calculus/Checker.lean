import ArtformRoles.Calculus.Accept
import ArtformRoles.Calculus.Normalize

/-!
# A certified bidirectional checker

Appendix C (`app:checker`) and the checking part of the decidability theorem
(`thm:decidability`). Over a well-formed signature and in a well-formed context:

* `inferTy` synthesizes the role and effect of a type;
* `infer` synthesizes the role, a type and the effect of a term built from
  variables, constants, annotated abstractions, applications, projections,
  stamps, gates and nodes;
* `check` checks a term against a role and a formed type: pairs against a
  dependent sum, abstractions against a function type, stamps against a stamped
  type, and every other term by synthesis followed by a conversion test
  (`decConv`, by normal forms);
* `checkSpine` checks an argument list against a formed telescope.

Every answer carries its derivation (a certificate), so the checker is sound by
construction; it is a total function, by recursion on the size of the
expression, so it terminates on every input. Its completeness is proved in
`CheckerComplete.lean` for the bidirectional fragment.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Rules at the level of derivability -/

/-- A closed type formed in the empty context is formed in every context. -/
theorem Deriv.ty_weaken_closed {S : Sig} (hS : SigWF S) {ρ : Role} {A : Exp} {α : Eff}
    (d : Deriv S true (.ty [] ρ A α)) (hA : Closed A) (Γ : Ctx) :
    ∃ α', Derivable S true (.ty Γ ρ A α') := by
  obtain ⟨dt⟩ := (Deriv.mkTelCons d .mkTelNil).tel_weaken_closed hS ⟨hA, trivial⟩ Γ
  cases dt with
  | telCons dA _ _ => exact ⟨_, ⟨dA⟩⟩

/-- The declared type of a constant is formed in every context. -/
theorem SigWF.const_formed {S : Sig} (hS : SigWF S) {i k : ℕ} {ρ : Role} {A : Exp}
    (h : S.const? i k = some (ρ, A)) (Γ : Ctx) : ∃ γ, Derivable S true (.ty Γ ρ A γ) := by
  suffices key : ∃ γ, Derivable S true (.ty [] ρ A γ) by
    obtain ⟨γ, ⟨d⟩⟩ := key
    exact d.ty_weaken_closed hS (hS.const_closed h) Γ
  clear Γ
  induction hS generalizing i k ρ A with
  | nil => simp [Sig.const?] at h
  | family _ _ _ ih | gate _ _ _ _ _ _ _ _ _ _ _ ih =>
    rcases Sig.const?_snoc h with h | ⟨-, ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩⟩
    · obtain ⟨γ, hd⟩ := ih h
      exact ⟨γ, hd.weakenSig _⟩
    all_goals cases he
  | @prim S' ρ' A' α' _ dA _ _ ih =>
    rcases Sig.const?_snoc h with h | ⟨-, ⟨_, _, he, -, hp⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩⟩
    · obtain ⟨γ, hd⟩ := ih h
      exact ⟨γ, hd.weakenSig _⟩
    · cases he; cases hp
      exact ⟨α', dA.weakenSig _⟩
    all_goals cases he
  | @cert S' σ' A' α' _ dA hσ _ _ ih =>
    rcases Sig.const?_snoc h with h | ⟨rfl, ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩ | ⟨_, _, he, _⟩⟩
    · obtain ⟨γ, hd⟩ := ih h
      exact ⟨γ, hd.weakenSig _⟩
    · cases he
    · cases he
      obtain ⟨dA'⟩ := dA.weakenSig [Entry.cert σ' A']
      rcases hk with ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨-, hp⟩ <;> cases hp
      · exact ⟨_, ⟨dA'⟩⟩
      · exact ⟨_, ⟨Deriv.mkTyEvent⟩⟩
      · have h1 : (S' ++ [Entry.cert σ' A']).const? S'.length 1 = some (.witness, .event) := by
          simp [Sig.const?]
        have h0 : (S' ++ [Entry.cert σ' A']).const? S'.length 0 = some (σ', A') := by
          simp [Sig.const?]
        exact ⟨_, ⟨Deriv.mkTyOrigin hσ dA' (Deriv.mkConst h1 .mkTyEvent) (Deriv.mkConst h0 dA')⟩⟩
    · cases he
  | @attest S' A' t' θ' _ dt _ _ _ ih =>
    rcases Sig.const?_snoc h with h | ⟨rfl, ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩⟩
    · obtain ⟨γ, hd⟩ := ih h
      exact ⟨γ, hd.weakenSig _⟩
    · cases he
    · cases he
    · cases he
      obtain ⟨dt'⟩ := dt.weakenSig [Entry.attest A' t']
      obtain ⟨_, ⟨dA'⟩⟩ := dt'.tm_ty
      rcases hk with ⟨-, hp⟩ | ⟨-, hp⟩ <;> cases hp
      · exact ⟨_, ⟨Deriv.mkTyEvent⟩⟩
      · have h0 : (S' ++ [Entry.attest A' t']).const? S'.length 0 = some (.witness, .event) := by
          simp [Sig.const?]
        exact ⟨_, ⟨Deriv.mkTyOrigin (by decide) dA' (Deriv.mkConst h0 .mkTyEvent) dt'⟩⟩

namespace Derivable

variable {S : Sig} {Γ : Ctx}

theorem conv {ρ : Role} {t A B : Exp} {θ : Eff} (ht : Derivable S true (.tm Γ ρ t A θ))
    (h : Conv A B) (hB : ∃ γ, Derivable S true (.ty Γ ρ B γ)) :
    Derivable S true (.tm Γ ρ t B θ) := by
  obtain ⟨d⟩ := ht
  obtain ⟨_, ⟨dB⟩⟩ := hB
  exact ⟨.conv d h dB⟩

theorem ty_of_tm {ρ : Role} {t A : Exp} {θ : Eff} (ht : Derivable S true (.tm Γ ρ t A θ)) :
    ∃ γ, Derivable S true (.ty Γ ρ A γ) := by
  obtain ⟨d⟩ := ht
  exact d.tm_ty

theorem sn_ty {ρ : Role} {A : Exp} (hA : ∃ γ, Derivable S true (.ty Γ ρ A γ)) : SN A := by
  obtain ⟨_, ⟨d⟩⟩ := hA
  exact d.sn_ty

theorem pi_dom {ρ σ : Role} {q : Grade} {A B : Exp}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ (.pi q σ A B) γ)) :
    ∃ α, Derivable S true (.ty Γ σ A α) := by
  obtain ⟨_, ⟨d⟩⟩ := hC
  exact d.inv_tyPi.1

theorem sigma_fst {ρ ρ' : Role} {A B : Exp}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ (.sigma ρ' A B) γ)) :
    ∃ α, Derivable S true (.ty Γ ρ A α) := by
  obtain ⟨_, ⟨d⟩⟩ := hC
  exact d.inv_tySigma.2.1

theorem stamped_inner {ρ σ : Role} {A : Exp}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ (.stamped σ A) γ)) :
    ρ = .witness ∧ σ ≠ .rendering ∧ ∃ α, Derivable S true (.ty Γ σ A α) := by
  obtain ⟨_, ⟨d⟩⟩ := hC
  exact d.inv_tyStamped

/-- Instantiating the codomain of a formed dependent sum. -/
theorem sigma_snd (hS : SigWF S) (hΓ : CtxWF S Γ) {ρ ρ' : Role} {A B t : Exp} {θ : Eff}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ (.sigma ρ' A B) γ))
    (ht : Derivable S true (.tm Γ ρ t A θ)) :
    ∃ γ, Derivable S true (.ty Γ ρ (B.inst t) γ) := by
  obtain ⟨_, ⟨d⟩⟩ := hC
  obtain ⟨rfl, -, β, ⟨dB⟩⟩ := d.inv_tySigma
  obtain ⟨dt⟩ := ht
  exact ⟨_, Deriv.inst_ty hS hΓ dB dt⟩

theorem app (hS : SigWF S) (hΓ : CtxWF S Γ) {q : Grade} {σ ρ : Role} {A B f u : Exp}
    {φ η : Eff} (df : Derivable S true (.tm Γ ρ f (.pi q σ A B) φ))
    (du : Derivable S true (.tm Γ σ u A η)) :
    Derivable S true (.tm Γ ρ (.app f u) (B.inst u) (φ ⊓ Eff.scale q η)) := by
  obtain ⟨df⟩ := df
  obtain ⟨du⟩ := du
  obtain ⟨_, ⟨dpi⟩⟩ := df.tm_ty
  obtain ⟨-, _, ⟨dB⟩⟩ := dpi.inv_tyPi
  obtain ⟨dC⟩ := Deriv.inst_ty hS hΓ dB du
  exact ⟨Deriv.mkApp df du dC⟩

theorem fst {ρ : Role} {A B p : Exp} {π : Eff}
    (hp : Derivable S true (.tm Γ ρ p (.sigma ρ A B) π)) :
    Derivable S true (.tm Γ ρ (.fst p) A π) := by
  obtain ⟨d⟩ := hp
  obtain ⟨_, ⟨ds⟩⟩ := d.tm_ty
  obtain ⟨-, ⟨_, ⟨dA⟩⟩, -⟩ := ds.inv_tySigma
  exact ⟨Deriv.mkFst d dA⟩

theorem snd (hS : SigWF S) (hΓ : CtxWF S Γ) {ρ : Role} {A B p : Exp} {π : Eff}
    (hp : Derivable S true (.tm Γ ρ p (.sigma ρ A B) π)) :
    Derivable S true (.tm Γ ρ (.snd p) (B.inst (.fst p)) π) := by
  obtain ⟨dfst⟩ := fst hp
  obtain ⟨d⟩ := hp
  obtain ⟨_, ⟨ds⟩⟩ := d.tm_ty
  obtain ⟨-, -, ⟨_, ⟨dB⟩⟩⟩ := ds.inv_tySigma
  obtain ⟨dC⟩ := Deriv.inst_ty hS hΓ dB dfst
  exact ⟨Deriv.mkSnd d dC⟩

theorem lam {q : Grade} {σ ρ : Role} {A B t : Exp} {α θ : Eff}
    (hA : Derivable S true (.ty Γ σ A α)) (ht : Derivable S true (.tm ((σ, A) :: Γ) ρ t B θ))
    (hq : q ≤ θ (.var 0)) (hq' : demand σ ρ ≤ q) :
    Derivable S true (.tm Γ ρ (.lam q σ A t) (.pi q σ A B) θ.unbind) := by
  obtain ⟨dA⟩ := hA
  obtain ⟨dt⟩ := ht
  obtain ⟨_, ⟨dB⟩⟩ := dt.tm_ty
  exact ⟨Deriv.mkLam dA dt hq (Deriv.mkTyPi dA dB hq')⟩

/-- The codomain of a formed function type, over a convertible domain. -/
theorem pi_cod (hS : SigWF S) (hΓ : CtxWF S Γ) {q : Grade} {σ ρ : Role} {A A' B : Exp}
    {α : Eff} (hC : ∃ γ, Derivable S true (.ty Γ ρ (.pi q σ A' B) γ))
    (hA : Derivable S true (.ty Γ σ A α)) (hAA' : Conv A A') :
    ∃ β, Derivable S true (.ty ((σ, A) :: Γ) ρ B β) := by
  obtain ⟨_, ⟨d⟩⟩ := hC
  obtain ⟨⟨_, ⟨dA'⟩⟩, ⟨_, ⟨dB⟩⟩⟩ := d.inv_tyPi
  obtain ⟨dA⟩ := hA
  exact ⟨_, Deriv.ctx_conv_ty hS dB hΓ dA' dA hAA'.symm⟩

/-- An abstraction checked against a function type with a convertible domain. -/
theorem lam_check {q : Grade} {σ ρ : Role} {A A' B t : Exp}
    {α θ : Eff} (hC : ∃ γ, Derivable S true (.ty Γ ρ (.pi q σ A' B) γ))
    (hA : Derivable S true (.ty Γ σ A α)) (hAA' : Conv A A')
    (ht : Derivable S true (.tm ((σ, A) :: Γ) ρ t B θ)) (hq : q ≤ θ (.var 0)) :
    Derivable S true (.tm Γ ρ (.lam q σ A t) (.pi q σ A' B) θ.unbind) := by
  have hq' : demand σ ρ ≤ q := by
    obtain ⟨_, ⟨d⟩⟩ := hC
    exact d.tyPi_demand
  have hl := lam hA ht hq hq'
  exact conv hl (Conv.lift (fun X => Exp.pi q σ X B) (fun h => Step.pi₁ h) hAA') hC

theorem pair {ρ : Role} {A B t u : Exp} {θ η : Eff}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ (.sigma ρ A B) γ))
    (ht : Derivable S true (.tm Γ ρ t A θ)) (hu : Derivable S true (.tm Γ ρ u (B.inst t) η)) :
    Derivable S true (.tm Γ ρ (.pair t u) (.sigma ρ A B) (θ ⊓ η)) := by
  obtain ⟨_, ⟨dC⟩⟩ := hC
  obtain ⟨dt⟩ := ht
  obtain ⟨du⟩ := hu
  exact ⟨Deriv.mkPair dt du dC⟩

theorem origin_formed {σ : Role} {A e t : Exp} {θ η : Eff} (hσ : σ ≠ .rendering)
    (hA : ∃ α, Derivable S true (.ty Γ σ A α)) (he : Derivable S true (.tm Γ .witness e .event η))
    (ht : Derivable S true (.tm Γ σ t A θ)) :
    ∃ γ, Derivable S true (.ty Γ .witness (.origin A e t) γ) := by
  obtain ⟨_, ⟨dA⟩⟩ := hA
  obtain ⟨de⟩ := he
  obtain ⟨dt⟩ := ht
  exact ⟨_, ⟨Deriv.mkTyOrigin hσ dA de dt⟩⟩

theorem stamp {σ : Role} {A t e o : Exp} {θ η ω : Eff} (hσ : σ ≠ .rendering)
    (hA : ∃ α, Derivable S true (.ty Γ σ A α)) (ht : Derivable S true (.tm Γ σ t A θ))
    (he : Derivable S true (.tm Γ .witness e .event η))
    (ho : Derivable S true (.tm Γ .witness o (.origin A e t) ω)) :
    Derivable S true (.tm Γ .witness (.stamp t e o) (.stamped σ A) (θ ⊓ η ⊓ ω)) := by
  obtain ⟨_, ⟨dA⟩⟩ := hA
  obtain ⟨dt⟩ := ht
  obtain ⟨de⟩ := he
  obtain ⟨dorg⟩ := ho
  exact ⟨Deriv.mkStamp dt de dorg (Deriv.mkTyStamped dA hσ)⟩

theorem event_formed : ∃ γ, Derivable S true (.ty Γ .witness .event γ) :=
  ⟨_, ⟨Deriv.mkTyEvent⟩⟩

/-- The payload type of a gate, instantiated by checked arguments, is formed. -/
theorem gate_payload (hS : SigWF S) (hΓ : CtxWF S Γ) {g : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B ds : Exp} {δ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : Derivable S true (.spine Γ ds Δ δ)) :
    ∃ α, Derivable S true (.ty Γ σ (instType ds Δ A) α) := by
  obtain ⟨dds⟩ := hds
  obtain ⟨-, ⟨_, ⟨dΔA⟩⟩, -⟩ := hS.gate_tel hg Γ
  exact dds.instType_formed hS hΓ dΔA

/-- The credential type of a gate, instantiated by checked arguments, is formed. -/
theorem gate_cred (hS : SigWF S) (hΓ : CtxWF S Γ) {g : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B ds : Exp} {δ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : Derivable S true (.spine Γ ds Δ δ)) :
    ∃ γ, Derivable S true (.ty Γ .witness (.stamped σ (instType ds Δ A)) γ) := by
  obtain ⟨_, ⟨dA⟩⟩ := gate_payload hS hΓ hg hds
  exact ⟨_, ⟨Deriv.mkTyStamped dA (hS.gate_cond hg).1⟩⟩

theorem gate (hS : SigWF S) (hΓ : CtxWF S Γ) {g : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B ds s : Exp} {δ η : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : Derivable S true (.spine Γ ds Δ δ))
    (hs : Derivable S true (.tm Γ .witness s (.stamped σ (instType ds Δ A)) η)) :
    Derivable S true (.tm Γ ρ (.gate g ds s) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η)) := by
  obtain ⟨dds⟩ := hds
  obtain ⟨dst⟩ := hs
  obtain ⟨-, -, ⟨_, ⟨dΔB⟩⟩⟩ := hS.gate_tel hg Γ
  obtain ⟨_, ⟨dB⟩⟩ := dds.instType_formed hS hΓ dΔB
  exact ⟨Deriv.mkGate hS hg dds dst dB⟩

theorem node (hS : SigWF S) (hΓ : CtxWF S Γ) {g ℓ : ℕ} {Δ : Tel} {σ ρ : Role}
    {A B ds t e : Exp} {δ θ η : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : Derivable S true (.spine Γ ds Δ δ))
    (ht : Derivable S true (.tm Γ σ t (instType ds Δ A) θ))
    (he : Derivable S true (.tm Γ .witness e .event η)) :
    Derivable S true (.tm Γ ρ (.node g ℓ ds t e) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η))) := by
  obtain ⟨dds⟩ := hds
  obtain ⟨dt⟩ := ht
  obtain ⟨de⟩ := he
  obtain ⟨-, -, ⟨_, ⟨dΔB⟩⟩⟩ := hS.gate_tel hg Γ
  obtain ⟨_, ⟨dB⟩⟩ := dds.instType_formed hS hΓ dΔB
  exact ⟨Deriv.mkNode hS hg dds dt de dB⟩

theorem tel_head {ρ : Role} {A : Exp} {Δ : Tel}
    (hΔ : ∃ δ, Derivable S true (.tel Γ ((ρ, A) :: Δ) δ)) :
    ∃ α, Derivable S true (.ty Γ ρ A α) := by
  obtain ⟨_, ⟨d⟩⟩ := hΔ
  cases d with
  | telCons dA _ _ => exact ⟨_, ⟨dA⟩⟩

/-- Instantiating the first entry of a formed telescope. -/
theorem tel_inst (hS : SigWF S) (hΓ : CtxWF S Γ) {ρ : Role} {A t : Exp} {Δ : Tel} {θ : Eff}
    (hΔ : ∃ δ, Derivable S true (.tel Γ ((ρ, A) :: Δ) δ))
    (ht : Derivable S true (.tm Γ ρ t A θ)) :
    ∃ δ, Derivable S true (.tel Γ (Tel.inst t Δ) δ) := by
  obtain ⟨_, ⟨d⟩⟩ := hΔ
  obtain ⟨dt⟩ := ht
  cases d with
  | telCons _ dΔ _ =>
    obtain ⟨d'⟩ := dΔ.subst hS (SubstOK.inst1 hΓ dt)
    exact ⟨_, ⟨d'⟩⟩

theorem spineCons {ρ : Role} {t ts A : Exp} {Δ : Tel} {ε₁ ε₂ : Eff}
    (ht : Derivable S true (.tm Γ ρ t A ε₁))
    (hts : Derivable S true (.spine Γ ts (Tel.inst t Δ) ε₂)) :
    Derivable S true (.spine Γ (.cons t ts) ((ρ, A) :: Δ) (ε₁ ⊓ ε₂)) := by
  obtain ⟨dt⟩ := ht
  obtain ⟨dts⟩ := hts
  exact ⟨Deriv.mkSpineCons dt dts⟩

end Derivable

/-! ## The checker -/

/-- A type with its role and effect, and a derivation. -/
abbrev TyCert (S : Sig) (Γ : Ctx) (A : Exp) : Type :=
  {p : Role × Eff // Derivable S true (.ty Γ p.1 A p.2)}

/-- A term with its role, a type and its effect, and a derivation. -/
abbrev TmCert (S : Sig) (Γ : Ctx) (t : Exp) : Type :=
  {p : Role × Exp × Eff // Derivable S true (.tm Γ p.1 t p.2.1 p.2.2)}

/-- A term checked against a role and a type, with its effect and a derivation. -/
abbrev ChkCert (S : Sig) (Γ : Ctx) (t : Exp) (ρ : Role) (C : Exp) : Type :=
  {ε : Eff // Derivable S true (.tm Γ ρ t C ε)}

/-- An argument list checked against a telescope, with its effect and a derivation. -/
abbrev SpCert (S : Sig) (Γ : Ctx) (ds : Exp) (Δ : Tel) : Type :=
  {δ : Eff // Derivable S true (.spine Γ ds Δ δ)}

section Checker

variable {S : Sig} (hS : SigWF S)

mutual

/-- Synthesize the role and the effect of a type. -/
def inferTy (Γ : Ctx) (hΓ : CtxWF S Γ) (T : Exp) : Option (TyCert S Γ T) :=
  match T with
  | .fam a args =>
    match ha : S.family? a with
    | none => none
    | some (Δ, ρ) =>
      match checkSpine Γ hΓ args Δ (hS.family_tel ha Γ) with
      | none => none
      | some ⟨δ, hd⟩ =>
        some ⟨(ρ, Eff.unit (.decl a 0) ⊓ δ), let ⟨d⟩ := hd; ⟨Deriv.mkTyFam hS ha d⟩⟩
  | .event => some ⟨(.witness, ⊤), ⟨Deriv.mkTyEvent⟩⟩
  | .origin A e t =>
    match inferTy Γ hΓ A with
    | none => none
    | some ⟨(σ, α), hA⟩ =>
      if hσ : σ = .rendering then none else
      match check Γ hΓ e .witness .event Derivable.event_formed with
      | none => none
      | some ⟨η, he⟩ =>
        match check Γ hΓ t σ A ⟨α, hA⟩ with
        | none => none
        | some ⟨θ, ht⟩ =>
          some ⟨(.witness, α ⊓ η ⊓ θ),
            let ⟨dA⟩ := hA; let ⟨de⟩ := he; let ⟨dt⟩ := ht; ⟨Deriv.mkTyOrigin hσ dA de dt⟩⟩
  | .stamped σ A =>
    match inferTy Γ hΓ A with
    | none => none
    | some ⟨(σ', α), hA⟩ =>
      if h : σ' = σ ∧ σ ≠ .rendering then
        some ⟨(.witness, α), let ⟨dA⟩ := hA; ⟨Deriv.mkTyStamped (h.1 ▸ dA) h.2⟩⟩
      else none
  | .pi q σ A B =>
    match inferTy Γ hΓ A with
    | none => none
    | some ⟨(σ', α), hA⟩ =>
      if hσ : σ' = σ then
        match inferTy ((σ, A) :: Γ) (.cons hΓ (hσ ▸ hA)) B with
        | none => none
        | some ⟨(ρ, β), hB⟩ =>
          if hq : demand σ ρ ≤ q then
            some ⟨(ρ, Eff.scale q α ⊓ β.unbind),
              let ⟨dA⟩ := hA; let ⟨dB⟩ := hB; ⟨Deriv.mkTyPi (hσ ▸ dA) dB hq⟩⟩
          else none
      else none
  | .sigma ρ A B =>
    match inferTy Γ hΓ A with
    | none => none
    | some ⟨(ρ', α), hA⟩ =>
      if hρ : ρ' = ρ then
        match inferTy ((ρ, A) :: Γ) (.cons hΓ (hρ ▸ hA)) B with
        | none => none
        | some ⟨(ρ'', β), hB⟩ =>
          if hρ' : ρ'' = ρ then
            some ⟨(ρ, α ⊓ β.unbind),
              let ⟨dA⟩ := hA; let ⟨dB⟩ := hB; ⟨Deriv.mkTySigma (hρ ▸ dA) (hρ' ▸ dB)⟩⟩
          else none
      else none
  | _ => none
termination_by (sizeOf T, 0)

/-- Synthesize the role, a type and the effect of a term. -/
def infer (Γ : Ctx) (hΓ : CtxWF S Γ) (t : Exp) : Option (TmCert S Γ t) :=
  match t with
  | .var i =>
    match hi : Γ[i]? with
    | none => none
    | some (ρ, A) =>
      some ⟨(ρ, A.ren (· + (i + 1)), Eff.unit (.var i)),
        let ⟨_, ⟨dC⟩⟩ := hΓ.var_formed hi; ⟨Deriv.mkVar hi dC⟩⟩
  | .const i k =>
    match hc : S.const? i k with
    | none => none
    | some (ρ, A) =>
      some ⟨(ρ, A, Eff.unit (.decl i k)),
        let ⟨_, ⟨dA⟩⟩ := hS.const_formed hc Γ; ⟨Deriv.mkConst hc dA⟩⟩
  | .lam q σ A b =>
    match inferTy Γ hΓ A with
    | none => none
    | some ⟨(σ', α), hA⟩ =>
      if hσ : σ' = σ then
        match infer ((σ, A) :: Γ) (.cons hΓ (hσ ▸ hA)) b with
        | none => none
        | some ⟨(ρ, B, θ), hb⟩ =>
          if hq : q ≤ θ (.var 0) ∧ demand σ ρ ≤ q then
            some ⟨(ρ, .pi q σ A B, θ.unbind), Derivable.lam (hσ ▸ hA) hb hq.1 hq.2⟩
          else none
      else none
  | .app f u =>
    match infer Γ hΓ f with
    | some ⟨(ρ, .pi q σ A B, φ), hf⟩ =>
      match check Γ hΓ u σ A (Derivable.pi_dom (Derivable.ty_of_tm hf)) with
      | none => none
      | some ⟨η, hu⟩ => some ⟨(ρ, B.inst u, φ ⊓ Eff.scale q η), Derivable.app hS hΓ hf hu⟩
    | _ => none
  | .fst p =>
    match infer Γ hΓ p with
    | some ⟨(ρ, .sigma ρ' A B, π), hp⟩ =>
      if h : ρ' = ρ then some ⟨(ρ, A, π), Derivable.fst (h ▸ hp)⟩ else none
    | _ => none
  | .snd p =>
    match infer Γ hΓ p with
    | some ⟨(ρ, .sigma ρ' A B, π), hp⟩ =>
      if h : ρ' = ρ then some ⟨(ρ, B.inst (.fst p), π), Derivable.snd hS hΓ (h ▸ hp)⟩
      else none
    | _ => none
  | .stamp a e o =>
    match infer Γ hΓ a with
    | none => none
    | some ⟨(σ, A, θ), ha⟩ =>
      if hσ : σ = .rendering then none else
      match check Γ hΓ e .witness .event Derivable.event_formed with
      | none => none
      | some ⟨η, he⟩ =>
        match check Γ hΓ o .witness (.origin A e a)
            (Derivable.origin_formed hσ (Derivable.ty_of_tm ha) he ha) with
        | none => none
        | some ⟨ω, ho⟩ =>
          some ⟨(.witness, .stamped σ A, θ ⊓ η ⊓ ω),
            Derivable.stamp hσ (Derivable.ty_of_tm ha) ha he ho⟩
  | .gate g ds s =>
    match hg : S.gate? g with
    | none => none
    | some (Δ, σ, A, ρ, B) =>
      match checkSpine Γ hΓ ds Δ (hS.gate_tel hg Γ).1 with
      | none => none
      | some ⟨δ, hds⟩ =>
        match check Γ hΓ s .witness (.stamped σ (instType ds Δ A))
            (Derivable.gate_cred hS hΓ hg hds) with
        | none => none
        | some ⟨η, hs⟩ =>
          some ⟨(ρ, instType ds Δ B, Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η),
            Derivable.gate hS hΓ hg hds hs⟩
  | .node g ℓ ds a e =>
    match hg : S.gate? g with
    | none => none
    | some (Δ, σ, A, ρ, B) =>
      match checkSpine Γ hΓ ds Δ (hS.gate_tel hg Γ).1 with
      | none => none
      | some ⟨δ, hds⟩ =>
        match check Γ hΓ a σ (instType ds Δ A) (Derivable.gate_payload hS hΓ hg hds) with
        | none => none
        | some ⟨θ, ha⟩ =>
          match check Γ hΓ e .witness .event Derivable.event_formed with
          | none => none
          | some ⟨η, he⟩ =>
            some ⟨(ρ, instType ds Δ B, Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η)),
              Derivable.node (ℓ := ℓ) hS hΓ hg hds ha he⟩
  | _ => none
termination_by (sizeOf t, 0)

/-- Check a term against a role and a formed type. -/
def check (Γ : Ctx) (hΓ : CtxWF S Γ) (t : Exp) (ρ : Role) (C : Exp)
    (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ)) : Option (ChkCert S Γ t ρ C) :=
  match t, C, hC with
  | .pair a b, .sigma ρ' A B, hC =>
    if h : ρ' = ρ then
      match ρ', h, hC with
      | _, rfl, hC =>
        match check Γ hΓ a ρ A (Derivable.sigma_fst hC) with
        | none => none
        | some ⟨θ, ha⟩ =>
          match check Γ hΓ b ρ (B.inst a) (Derivable.sigma_snd hS hΓ hC ha) with
          | none => none
          | some ⟨η, hb⟩ => some ⟨θ ⊓ η, Derivable.pair hC ha hb⟩
    else none
  | .lam q σ A b, .pi q' σ' A' B', hC =>
    if h : q' = q ∧ σ' = σ then
      match inferTy Γ hΓ A with
      | none => none
      | some ⟨(σ'', α), hA⟩ =>
        if hσ : σ'' = σ then
          match decConv (Derivable.sn_ty ⟨α, hσ ▸ hA⟩)
              (Derivable.sn_ty (Derivable.pi_dom hC)) with
          | isFalse _ => none
          | isTrue hconv =>
            match check ((σ, A) :: Γ) (.cons hΓ (hσ ▸ hA)) b ρ B'
                (by obtain ⟨rfl, rfl⟩ := h; exact Derivable.pi_cod hS hΓ hC (hσ ▸ hA) hconv) with
            | none => none
            | some ⟨θ, hb⟩ =>
              if hq : q ≤ θ (.var 0) then
                some ⟨θ.unbind, by
                  obtain ⟨rfl, rfl⟩ := h
                  exact Derivable.lam_check hC (hσ ▸ hA) hconv hb hq⟩
              else none
        else none
    else none
  | .stamp a e o, .stamped σ A, hC =>
    if hσ : σ = .rendering then none else
    if hρ : ρ = .witness then
      match ρ, hρ, hC with
      | _, rfl, hC =>
        match check Γ hΓ a σ A (Derivable.stamped_inner hC).2.2 with
        | none => none
        | some ⟨θ, ha⟩ =>
          match check Γ hΓ e .witness .event Derivable.event_formed with
          | none => none
          | some ⟨η, he⟩ =>
            match check Γ hΓ o .witness (.origin A e a)
                (Derivable.origin_formed hσ (Derivable.stamped_inner hC).2.2 he ha) with
            | none => none
            | some ⟨ω, ho⟩ =>
              some ⟨θ ⊓ η ⊓ ω, Derivable.stamp hσ (Derivable.stamped_inner hC).2.2 ha he ho⟩
    else none
  | t, C, hC =>
    match infer Γ hΓ t with
    | none => none
    | some ⟨(ρ', T, ε), ht⟩ =>
      if hρ : ρ' = ρ then
        match decConv (Derivable.sn_ty (Derivable.ty_of_tm ht)) (Derivable.sn_ty hC) with
        | isFalse _ => none
        | isTrue hconv => some ⟨ε, Derivable.conv (hρ ▸ ht) hconv hC⟩
      else none
termination_by (sizeOf t, 1)

/-- Check an argument list against a formed telescope. -/
def checkSpine (Γ : Ctx) (hΓ : CtxWF S Γ) (ds : Exp) (Δ : Tel)
    (hΔ : ∃ δ, Derivable S true (.tel Γ Δ δ)) : Option (SpCert S Γ ds Δ) :=
  match ds, Δ, hΔ with
  | .nil, [], _ => some ⟨⊤, ⟨Deriv.mkSpineNil⟩⟩
  | .cons a rest, (ρ, A) :: Δ, hΔ =>
    match check Γ hΓ a ρ A (Derivable.tel_head hΔ) with
    | none => none
    | some ⟨ε₁, ha⟩ =>
      match checkSpine Γ hΓ rest (Tel.inst a Δ) (Derivable.tel_inst hS hΓ hΔ ha) with
      | none => none
      | some ⟨ε₂, hrest⟩ => some ⟨ε₁ ⊓ ε₂, Derivable.spineCons ha hrest⟩
  | _, _, _ => none
termination_by (sizeOf ds, 0)

end

/-- Type checking: a term against a role and a type, in a well-formed context.
The type is formed first; the term is then checked against it. -/
def typeCheck (Γ : Ctx) (hΓ : CtxWF S Γ) (t : Exp) (ρ : Role) (C : Exp) :
    Option (ChkCert S Γ t ρ C) :=
  match inferTy hS Γ hΓ C with
  | none => none
  | some ⟨(ρ', γ), hC⟩ => if h : ρ' = ρ then check hS Γ hΓ t ρ C ⟨γ, h ▸ hC⟩ else none

end Checker

end Artform.Roles.Calculus
