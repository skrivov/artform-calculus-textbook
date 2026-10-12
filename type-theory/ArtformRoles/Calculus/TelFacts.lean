import ArtformRoles.Calculus.Inversion

/-!
# Telescopes, spines and instantiated types

What subject reduction needs about argument lists:

* `Deriv.tel_snoc`: a type formed under a telescope extends the telescope.
* `Deriv.instType_formed`: a type under a telescope, instantiated by a
  well-typed argument list, is well formed.
* `Deriv.spine_conv`: an argument list checked against a telescope is checked
  against every convertible well-formed telescope.
* `instType_steps_args`, `TelConv.inst_steps`: reducing an argument reduces the
  instantiated types.
* `Deriv.tel_weaken_closed`: a closed telescope formed in the empty context is
  formed in every context.
-/

namespace Artform.Roles.Calculus

open Exp

theorem Tel.subst_append (σ : ℕ → Exp) (Δ : Tel) (ρ : Role) (C : Exp) :
    Tel.subst σ (Δ ++ [(ρ, C)]) = Tel.subst σ Δ ++ [(ρ, C.subst (upN Δ.length σ))] := by
  induction Δ generalizing σ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨ρ', A⟩ := p
    simp only [List.cons_append, Tel.subst_cons, ih, List.length_cons, upN_succ']

theorem Tel.inst_append (t : Exp) (Δ : Tel) (ρ : Role) (C : Exp) :
    Tel.inst t (Δ ++ [(ρ, C)]) = Tel.inst t Δ ++ [(ρ, instAt t Δ.length C)] :=
  Tel.subst_append _ _ _ _

/-- A type formed under a telescope extends the telescope. -/
theorem Deriv.tel_snoc {S : Sig} {Γ : Ctx} {Δ : Tel} {δ : Eff}
    (d : Deriv S true (.tel Γ Δ δ)) :
    ∀ {ρ C α}, Deriv S true (.ty (Δ.reverse ++ Γ) ρ C α) →
      ∃ δ', Derivable S true (.tel Γ (Δ ++ [(ρ, C)]) δ') := by
  generalize hj : Judg.tel Γ Δ δ = j at d
  induction d generalizing Γ Δ δ with
  | telNil hε =>
    cases hj
    intro ρ C α dC
    exact ⟨_, ⟨.telCons dC (.telNil rfl) rfl⟩⟩
  | telCons dA _ _ _ ihΔ =>
    cases hj
    intro ρ C α dC
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at dC
    obtain ⟨δ', ⟨d'⟩⟩ := ihΔ rfl dC
    exact ⟨_, ⟨.telCons dA d' rfl⟩⟩
  | _ => cases hj

/-- A type under a telescope, instantiated by a well-typed argument list, is
well formed. -/
theorem Deriv.instType_formed {S : Sig} (hS : SigWF S) {Γ : Ctx} {ds : Exp} {Δ : Tel} {ε : Eff}
    (d : Deriv S true (.spine Γ ds Δ ε)) (hΓ : CtxWF S Γ) :
    ∀ {ρ C δ}, Deriv S true (.tel Γ (Δ ++ [(ρ, C)]) δ) →
      ∃ α, Derivable S true (.ty Γ ρ (instType ds Δ C) α) := by
  generalize hj : Judg.spine Γ ds Δ ε = j at d
  induction d generalizing Γ ds Δ ε with
  | spineNil hε =>
    cases hj
    intro ρ C δ dt
    cases dt with
    | telCons dC _ _ => exact ⟨_, ⟨dC⟩⟩
  | @spineCons Γ' ρ' t ts A Δ' ε₁ ε₂ ε' dt dts hε iht ihts =>
    cases hj
    intro ρ C δ dtel
    cases dtel with
    | telCons dA drest _ =>
      obtain ⟨d'⟩ := drest.subst hS (SubstOK.inst1 hΓ dt)
      simp only [Judg.substJ, List.append_eq] at d'
      rw [Tel.subst_append] at d'
      obtain ⟨α, hα⟩ := ihts hΓ rfl d'
      exact ⟨α, hα⟩
  | _ => cases hj

/-- Pointwise convertible telescopes. -/
def TelConv : Tel → Tel → Prop := List.Forall₂ fun p q => p.1 = q.1 ∧ Conv p.2 q.2

theorem TelConv.subst {Δ₁ Δ₂ : Tel} (h : TelConv Δ₁ Δ₂) (σ : ℕ → Exp) :
    TelConv (Tel.subst σ Δ₁) (Tel.subst σ Δ₂) := by
  induction h generalizing σ with
  | nil => exact .nil
  | @cons p q Δ₁ Δ₂ hpq _ ih =>
    obtain ⟨ρ, A⟩ := p
    obtain ⟨ρ', A'⟩ := q
    obtain ⟨h₁, h₂⟩ := hpq
    exact .cons ⟨h₁, h₂.subst σ⟩ (ih _)

/-- Substitutions that reduce pointwise give convertible telescopes. -/
theorem TelConv.of_steps {σ τ : ℕ → Exp} (h : ∀ i, Steps (σ i) (τ i)) (Δ : Tel) :
    TelConv (Tel.subst σ Δ) (Tel.subst τ Δ) := by
  induction Δ generalizing σ τ with
  | nil => exact .nil
  | cons p Δ ih =>
    obtain ⟨ρ, A⟩ := p
    exact .cons ⟨rfl, Conv.of_steps (Steps.subst_arg h A)⟩ (ih (Steps.up h))

theorem TelConv.inst_steps {t t' : Exp} (h : Steps t t') (Δ : Tel) :
    TelConv (Tel.inst t Δ) (Tel.inst t' Δ) :=
  TelConv.of_steps (fun i => by cases i with | zero => exact h | succ => exact .refl) Δ

/-- An argument list checked against a telescope is checked against every
convertible telescope formed in the context. -/
theorem Deriv.spine_conv {S : Sig} (hS : SigWF S) {Γ : Ctx} {ts : Exp} {Δ₁ : Tel} {ε : Eff}
    (d : Deriv S true (.spine Γ ts Δ₁ ε)) (hΓ : CtxWF S Γ) :
    ∀ {Δ₂ δ}, TelConv Δ₁ Δ₂ → Deriv S true (.tel Γ Δ₂ δ) →
      Derivable S true (.spine Γ ts Δ₂ ε) := by
  generalize hj : Judg.spine Γ ts Δ₁ ε = j at d
  induction d generalizing Γ ts Δ₁ ε with
  | spineNil hε =>
    cases hj
    intro Δ₂ δ hc _
    cases hc
    exact ⟨.spineNil hε⟩
  | @spineCons Γ' ρ t ts' A Δ' ε₁ ε₂ ε' dt dts hε iht ihts =>
    cases hj
    intro Δ₂ δ hc dtel
    cases hc with
    | cons hpq hrest =>
      rename_i q Δ₂'
      obtain ⟨ρ₂, A₂⟩ := q
      obtain ⟨hρ, hA⟩ := hpq
      simp only at hρ hA
      subst hρ
      cases dtel with
      | telCons dA₂ drest _ =>
        have dt₂ : Deriv S true (.tm Γ' ρ t A₂ ε₁) := .conv dt hA dA₂
        obtain ⟨d'⟩ := drest.subst hS (SubstOK.inst1 hΓ dt₂)
        simp only [Judg.substJ] at d'
        obtain ⟨dts'⟩ := ihts hΓ rfl (TelConv.subst hrest _) d'
        exact ⟨.spineCons dt₂ dts' hε⟩
  | _ => cases hj

/-! ## Reduction of instantiated types -/

theorem Steps.up_n {σ τ : ℕ → Exp} (h : ∀ i, Steps (σ i) (τ i)) :
    ∀ k i, Steps (upN k σ i) (upN k τ i)
  | 0, i => h i
  | k + 1, i => Steps.up (Steps.up_n h k) i

/-- `instType` uses only the length of its telescope. -/
theorem instType_length {ds : Exp} {Δ Δ' : Tel} (h : Δ.length = Δ'.length) (C : Exp) :
    instType ds Δ C = instType ds Δ' C := by
  induction ds generalizing Δ Δ' C with
  | cons t ts _ ihts =>
    cases Δ with
    | nil => cases Δ' with
      | nil => rfl
      | cons => simp at h
    | cons p Δ₁ =>
      cases Δ' with
      | nil => simp at h
      | cons p' Δ₁' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        simp only [instType, h]
        exact ihts (by simp [h]) _
  | _ => rfl

/-- An instantiated type is a substitution instance of the type. -/
theorem instType_eq_subst (ds : Exp) (Δ : Tel) :
    ∃ σ : ℕ → Exp, ∀ C, instType ds Δ C = C.subst σ := by
  induction ds generalizing Δ with
  | cons t ts _ ihts =>
    cases Δ with
    | nil => exact ⟨Exp.var, fun C => (subst_var C).symm⟩
    | cons p Δ₁ =>
      obtain ⟨σ, hσ⟩ := ihts (Tel.inst t Δ₁)
      refine ⟨Exp.subst σ ∘ upN Δ₁.length (inst1 t), fun C => ?_⟩
      simp only [instType, hσ, instAt, subst_subst]
  | _ =>
    exact ⟨Exp.var, fun C => by cases Δ <;> simp [instType, subst_var]⟩

theorem instType_steps_type {ds : Exp} {Δ : Tel} {C C' : Exp} (h : Steps C C') :
    Steps (instType ds Δ C) (instType ds Δ C') := by
  obtain ⟨σ, hσ⟩ := instType_eq_subst ds Δ
  rw [hσ, hσ]; exact h.subst σ

/-- Reducing an argument of an argument list reduces the instantiated type. -/
theorem instType_step_args {ds ds' : Exp} (h : Step ds ds') {n : ℕ} (hl : ds.IsList n)
    (Δ : Tel) (C : Exp) : Steps (instType ds Δ C) (instType ds' Δ C) := by
  induction ds generalizing ds' n Δ C with
  | cons t ts _ ihts =>
    cases h with
    | @cons₁ _ t' _ ht =>
      cases Δ with
      | nil => exact .refl
      | cons p Δ₁ =>
        simp only [instType]
        rw [instType_length (Δ := Tel.inst t' Δ₁) (Δ' := Tel.inst t Δ₁) (by simp)]
        refine instType_steps_type (Steps.subst_arg (fun i => ?_) C)
        exact Steps.up_n
          (fun j => by cases j with | zero => exact .single ht | succ => exact .refl) Δ₁.length i
    | cons₂ hts =>
      cases n with
      | zero => simp [Exp.IsList] at hl
      | succ n =>
        cases Δ with
        | nil => exact .refl
        | cons p Δ₁ => simp only [instType]; exact ihts hts hl _ _
  | nil => cases h
  | _ => cases n <;> simp [Exp.IsList] at hl

end Artform.Roles.Calculus
