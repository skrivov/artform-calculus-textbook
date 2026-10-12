import ArtformRoles.Calculus.CheckerComplete
import ArtformRoles.Calculus.Modules

/-!
# Strengthening, and inhabitation under a rendering-only module

§10 of the paper: the inhabitation sentence of Theorem 10.5.

* `checker_strengthen`: on a subject that is old over `S`, every answer of the
  checker over `S ++ M` is an answer of the checker over `S`, with the same role,
  type and effect. The checker reads the signature only at the declarations its
  subject names, and its conversion test does not read the signature. This holds
  for every suffix `M`.
* `Derivable.strengthen`: an old term of the bidirectional fragment that is typed
  over `S ++ M` at a type formed over `S` is typed over `S`, with the same
  effect. `Derivable.strengthen_ty` is the same for an old type of the fragment.
  Every well-typed normal term lies in the fragment (`normal_fragment`).
* `rendering_inhabitation` (Theorem 10.5, "it cannot change inhabitation"): let
  `M` be rendering-only over `S`, and let `A` be a closed grade-free type of the
  base at a role other than rendering. The normal form of every closed term of
  `A` over `S ++ M` is a closed term of `A` over `S`; so `A` has a closed term
  over `S ++ M` exactly when it has one over `S`.
-/

namespace Artform.Roles.Calculus

open Exp

/-- A context formed over a signature is formed over every well-formed
extension. -/
theorem CtxWF.weakenSig {S M : Sig} (hSM : SigWF (S ++ M)) {Γ : Ctx} (hΓ : CtxWF S Γ) :
    CtxWF (S ++ M) Γ := by
  induction hΓ with
  | nil => exact .nil hSM
  | cons _ hA ih => exact .cons ih (hA.weakenSig M)

section Strengthen

variable {S M : Sig} (hS : SigWF S) (hSM : SigWF (S ++ M))

/-- The generic clause of `check`, by synthesis, a role test and a conversion
test, carries an answer over `S ++ M` to the same answer over `S` when synthesis
does. -/
theorem check_strengthen_generic {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
    {t : Exp} {ρ : Role} {C : Exp} (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ))
    (hC' : ∃ γ, Derivable (S ++ M) true (.ty Γ ρ C γ))
    (hp : ∀ a b ρ' A B, t = .pair a b → C = .sigma ρ' A B → False)
    (hl : ∀ q σ A b q' σ' A' B', t = .lam q σ A b → C = .pi q' σ' A' B' → False)
    (hs : ∀ a e o σ A, t = .stamp a e o → C = .stamped σ A → False)
    (hinf : ∀ {r' : TmCert (S ++ M) Γ t}, infer hSM Γ hΓ' t = some r' →
      ∃ r, infer hS Γ hΓ t = some r ∧ r.1 = r'.1)
    {r' : ChkCert (S ++ M) Γ t ρ C} (h : check hSM Γ hΓ' t ρ C hC' = some r') :
    ∃ r, check hS Γ hΓ t ρ C hC = some r ∧ r.1 = r'.1 := by
  rw [check.eq_4 hSM Γ hΓ' t ρ C hC' (fun a b ρ' A B _ h₁ h₂ _ => hp a b ρ' A B h₁ h₂)
    (fun q σ A b q' σ' A' B' _ h₁ h₂ _ => hl q σ A b q' σ' A' B' h₁ h₂)
    (fun a e o σ A _ h₁ h₂ _ => hs a e o σ A h₁ h₂)] at h
  split at h
  · cases h
  · rename_i ρ₁ T ε _ heq
    split at h
    · rename_i hρ
      split at h
      · cases h
      · rename_i hconv _
        cases h
        obtain ⟨⟨⟨ρ₀, T₀, ε₀⟩, hd⟩, hr, hr1⟩ := hinf heq
        simp only [Prod.mk.injEq] at hr1
        obtain ⟨rfl, rfl, rfl⟩ := hr1
        subst hρ
        rw [check.eq_4 hS Γ hΓ t _ C hC (fun a b ρ' A B _ h₁ h₂ _ => hp a b ρ' A B h₁ h₂)
          (fun q σ A b q' σ' A' B' _ h₁ h₂ _ => hl q σ A b q' σ' A' B' h₁ h₂)
          (fun a e o σ A _ h₁ h₂ _ => hs a e o σ A h₁ h₂)]
        simp only [hr, ↓reduceDIte]
        split
        · contradiction
        · exact ⟨_, rfl, rfl⟩
    · cases h

/-- `check_strengthen_generic` for a term that is not an introduction form. -/
theorem check_strengthen_notIntro {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
    {t : Exp} (hni : t.NotIntro) {ρ : Role} {C : Exp} (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ))
    (hC' : ∃ γ, Derivable (S ++ M) true (.ty Γ ρ C γ))
    (hinf : ∀ {r' : TmCert (S ++ M) Γ t}, infer hSM Γ hΓ' t = some r' →
      ∃ r, infer hS Γ hΓ t = some r ∧ r.1 = r'.1)
    {r' : ChkCert (S ++ M) Γ t ρ C} (h : check hSM Γ hΓ' t ρ C hC' = some r') :
    ∃ r, check hS Γ hΓ t ρ C hC = some r ∧ r.1 = r'.1 :=
  check_strengthen_generic hS hSM hΓ hΓ' hC hC' (fun a b _ _ _ h₁ _ => hni.1 a b h₁)
    (fun q σ A b _ _ _ _ h₁ _ => hni.2.2 q σ A b h₁) (fun a e o _ _ h₁ _ => hni.2.1 a e o h₁)
    hinf h

/-- **Strengthening for the checker.** On a subject that is old over `S`, every
answer of the checker over `S ++ M` (type synthesis, term synthesis, checking and
argument lists) is an answer of the checker over `S` with the same role, type and
effect. -/
theorem checker_strengthen (t : Exp) (ht : t.Old S.length) :
    (∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ) {r' : TyCert (S ++ M) Γ t},
      inferTy hSM Γ hΓ' t = some r' → ∃ r, inferTy hS Γ hΓ t = some r ∧ r.1 = r'.1) ∧
    (∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ) {r' : TmCert (S ++ M) Γ t},
      infer hSM Γ hΓ' t = some r' → ∃ r, infer hS Γ hΓ t = some r ∧ r.1 = r'.1) ∧
    (∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ) {ρ : Role} {C : Exp}
      (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ))
      (hC' : ∃ γ, Derivable (S ++ M) true (.ty Γ ρ C γ)) {r' : ChkCert (S ++ M) Γ t ρ C},
      check hSM Γ hΓ' t ρ C hC' = some r' → ∃ r, check hS Γ hΓ t ρ C hC = some r ∧ r.1 = r'.1) ∧
    (∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ) {Δ : Tel}
      (hΔ : ∃ δ, Derivable S true (.tel Γ Δ δ))
      (hΔ' : ∃ δ, Derivable (S ++ M) true (.tel Γ Δ δ)) {r' : SpCert (S ++ M) Γ t Δ},
      checkSpine hSM Γ hΓ' t Δ hΔ' = some r' →
        ∃ r, checkSpine hS Γ hΓ t Δ hΔ = some r ∧ r.1 = r'.1) := by
  induction t with
  | var i =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.var i)}, infer hSM Γ hΓ' (.var i) = some r' →
          ∃ r, infer hS Γ hΓ (.var i) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i ρ A hc
        cases h
        rw [infer]
        split
        · rename_i hc'; rw [hc] at hc'; cases hc'
        · rename_i ρ' A' hc'
          rw [hc] at hc'
          cases hc'
          exact ⟨_, rfl, rfl⟩
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | const i k =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.const i k)}, infer hSM Γ hΓ' (.const i k) = some r' →
          ∃ r, infer hS Γ hΓ (.const i k) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i ρ A hc
        cases h
        rw [Sig.const?_append_lt ht] at hc
        rw [infer]
        split
        · rename_i hc'; rw [hc] at hc'; cases hc'
        · rename_i ρ' A' hc'
          rw [hc] at hc'
          cases hc'
          exact ⟨_, rfl, rfl⟩
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | fam a args ih =>
    refine ⟨fun {Γ} hΓ hΓ' {r'} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · rw [inferTy] at h
      split at h
      · cases h
      · rename_i Δ ρ hfam
        split at h
        · cases h
        · rename_i δ _ hdeq
          cases h
          rw [Sig.family?_append_lt ht.1] at hfam
          obtain ⟨⟨δ₀, hd⟩, hr, hr1⟩ := (ih ht.2).2.2.2 hΓ hΓ' (hS.family_tel hfam Γ) _ hdeq
          simp only at hr1
          subst hr1
          rw [inferTy]
          split
          · rename_i h'; rw [hfam] at h'; cases h'
          · rename_i Δ' ρ' h'
            have e : (Δ', ρ') = (Δ, ρ) := Option.some.inj (h'.symm.trans hfam)
            cases e
            rw [hr]
            exact ⟨_, rfl, rfl⟩
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | event =>
    refine ⟨fun {_} hΓ hΓ' {_} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · simp only [inferTy] at h
      cases h
      simp only [inferTy]
      exact ⟨_, rfl, rfl⟩
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | origin A e u ihA ihe ihu =>
    refine ⟨fun {_} hΓ hΓ' {_} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · rw [inferTy] at h
      split at h
      · cases h
      · rename_i σ α _ hAeq
        split at h
        · cases h
        · rename_i hσ
          split at h
          · cases h
          · rename_i η _ heeq
            split at h
            · cases h
            · rename_i θ _ hueq
              cases h
              obtain ⟨⟨⟨σ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ihA ht.1).1 hΓ hΓ' hAeq
              simp only [Prod.mk.injEq] at hrA1
              obtain ⟨rfl, rfl⟩ := hrA1
              obtain ⟨⟨η₀, he⟩, hre, hre1⟩ :=
                (ihe ht.2.1).2.2.1 hΓ hΓ' Derivable.event_formed _ heeq
              simp only at hre1
              subst hre1
              obtain ⟨⟨θ₀, hu⟩, hru, hru1⟩ := (ihu ht.2.2).2.2.1 hΓ hΓ' ⟨α₀, hA⟩ _ hueq
              simp only at hru1
              subst hru1
              simp only [inferTy, hrA, hσ, ↓reduceDIte, hre, hru]
              exact ⟨_, rfl, rfl⟩
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | stamped σ A ih =>
    refine ⟨fun {_} hΓ hΓ' {_} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · rw [inferTy] at h
      split at h
      · cases h
      · rename_i σ' α _ hAeq
        split at h
        · rename_i hc
          cases h
          obtain ⟨⟨⟨σ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ih ht).1 hΓ hΓ' hAeq
          simp only [Prod.mk.injEq] at hrA1
          obtain ⟨rfl, rfl⟩ := hrA1
          simp only [inferTy, hrA, dite_eq_left hc]
          exact ⟨_, rfl, rfl⟩
        · cases h
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | pi q σ A B ihA ihB =>
    refine ⟨fun {Γ} hΓ hΓ' {r'} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · rw [inferTy] at h
      split at h
      · cases h
      · rename_i σ' α _ hAeq
        split at h
        · rename_i hσ
          subst hσ
          split at h
          · cases h
          · rename_i ρ β _ hBeq
            split at h
            · rename_i hq
              cases h
              obtain ⟨⟨⟨σ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ihA ht.1).1 hΓ hΓ' hAeq
              simp only [Prod.mk.injEq] at hrA1
              obtain ⟨rfl, rfl⟩ := hrA1
              obtain ⟨⟨⟨ρ₀, β₀⟩, hB⟩, hrB, hrB1⟩ :=
                (ihB ht.2).1 (Γ := (σ₀, A) :: Γ) (.cons hΓ hA) _ hBeq
              simp only [Prod.mk.injEq] at hrB1
              obtain ⟨rfl, rfl⟩ := hrB1
              simp only [inferTy, hrA, ↓reduceDIte, hrB, hq]
              exact ⟨_, rfl, rfl⟩
            · cases h
        · cases h
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | sigma ρ A B ihA ihB =>
    refine ⟨fun {Γ} hΓ hΓ' {r'} h => ?_, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    · rw [inferTy] at h
      split at h
      · cases h
      · rename_i ρ' α _ hAeq
        split at h
        · rename_i hρ
          subst hρ
          split at h
          · cases h
          · rename_i ρ'' β _ hBeq
            split at h
            · rename_i hρ'
              subst hρ'
              cases h
              obtain ⟨⟨⟨ρ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ihA ht.1).1 hΓ hΓ' hAeq
              simp only [Prod.mk.injEq] at hrA1
              obtain ⟨rfl, rfl⟩ := hrA1
              obtain ⟨⟨⟨ρ₁, β₀⟩, hB⟩, hrB, hrB1⟩ :=
                (ihB ht.2).1 (Γ := (ρ₀, A) :: Γ) (.cons hΓ hA) _ hBeq
              simp only [Prod.mk.injEq] at hrB1
              obtain ⟨rfl, rfl⟩ := hrB1
              simp only [inferTy, hrA, ↓reduceDIte, hrB]
              exact ⟨_, rfl, rfl⟩
            · cases h
        · cases h
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
  | lam q σ A b ihA ihb =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.lam q σ A b)}, infer hSM Γ hΓ' (.lam q σ A b) = some r' →
          ∃ r, infer hS Γ hΓ (.lam q σ A b) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i σ' α _ hAeq
        split at h
        · rename_i hσ
          subst hσ
          split at h
          · cases h
          · rename_i ρ B θ _ hbeq
            split at h
            · rename_i hq
              cases h
              obtain ⟨⟨⟨σ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ihA ht.1).1 hΓ hΓ' hAeq
              simp only [Prod.mk.injEq] at hrA1
              obtain ⟨rfl, rfl⟩ := hrA1
              obtain ⟨⟨⟨ρ₀, B₀, θ₀⟩, hb⟩, hrb, hrb1⟩ :=
                (ihb ht.2).2.1 (Γ := (σ₀, A) :: Γ) (.cons hΓ hA) _ hbeq
              simp only [Prod.mk.injEq] at hrb1
              obtain ⟨rfl, rfl, rfl⟩ := hrb1
              simp only [infer, hrA, ↓reduceDIte, hrb, hq]
              exact ⟨_, rfl, rfl⟩
            · cases h
        · cases h
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {Γ} hΓ hΓ' {ρ C} hC hC' {r'} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    by_cases hpi : ∃ q' σ' A' B', C = .pi q' σ' A' B'
    · obtain ⟨q', σ', A', B', rfl⟩ := hpi
      rw [check.eq_2] at h
      split at h
      · rename_i hqσ
        obtain ⟨rfl, rfl⟩ := hqσ
        split at h
        · cases h
        · rename_i σ'' α _ hAeq
          split at h
          · rename_i hσ
            subst hσ
            split at h
            · cases h
            · rename_i hconv _
              split at h
              · cases h
              · rename_i θ _ hbeq
                split at h
                · rename_i hq
                  cases h
                  obtain ⟨⟨⟨σ₀, α₀⟩, hA⟩, hrA, hrA1⟩ := (ihA ht.1).1 hΓ hΓ' hAeq
                  simp only [Prod.mk.injEq] at hrA1
                  obtain ⟨rfl, rfl⟩ := hrA1
                  obtain ⟨⟨θ₀, hb⟩, hrb, hrb1⟩ :=
                    (ihb ht.2).2.2.1 (Γ := (σ₀, A) :: Γ) (.cons hΓ hA) _
                      (Derivable.pi_cod hS hΓ hC hA hconv) _ hbeq
                  simp only at hrb1
                  subst hrb1
                  rw [check.eq_2, dite_eq_left ⟨rfl, rfl⟩, hrA]
                  simp only [↓reduceDIte]
                  split
                  · contradiction
                  · rw [hrb]
                    simp only [dite_eq_left hq]
                    exact ⟨_, rfl, rfl⟩
                · cases h
          · cases h
      · cases h
    · exact check_strengthen_generic hS hSM hΓ hΓ' hC hC' (fun _ _ _ _ _ h₁ _ => by cases h₁)
        (fun _ _ _ _ q' σ' A' B' _ h₂ => hpi ⟨q', σ', A', B', h₂⟩)
        (fun _ _ _ _ _ h₁ _ => by cases h₁) (inf hΓ hΓ') h
  | app f u ihf ihu =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.app f u)}, infer hSM Γ hΓ' (.app f u) = some r' →
          ∃ r, infer hS Γ hΓ (.app f u) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · rename_i ρ q σ A B φ _ hfeq
        split at h
        · cases h
        · rename_i η _ hueq
          cases h
          obtain ⟨⟨⟨ρ₀, T₀, φ₀⟩, hf⟩, hrf, hrf1⟩ := (ihf ht.1).2.1 hΓ hΓ' hfeq
          simp only [Prod.mk.injEq] at hrf1
          obtain ⟨rfl, rfl, rfl⟩ := hrf1
          obtain ⟨⟨η₀, hu⟩, hru, hru1⟩ :=
            (ihu ht.2).2.2.1 hΓ hΓ' (Derivable.pi_dom (Derivable.ty_of_tm hf)) _ hueq
          simp only at hru1
          subst hru1
          simp only [infer, hrf, hru]
          exact ⟨_, rfl, rfl⟩
      · cases h
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | pair a b iha ihb =>
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {Γ} hΓ hΓ' {ρ C} hC hC' {r'} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    by_cases hsig : ∃ ρ' A B, C = .sigma ρ' A B
    · obtain ⟨ρ', A, B, rfl⟩ := hsig
      rw [check.eq_1] at h
      split at h
      · rename_i hρ
        subst hρ
        simp only at h
        split at h
        · cases h
        · rename_i θ _ haeq
          split at h
          · cases h
          · rename_i η _ hbeq
            cases h
            obtain ⟨⟨θ₀, ha⟩, hra, hra1⟩ := (iha ht.1).2.2.1 hΓ hΓ' (Derivable.sigma_fst hC) _ haeq
            simp only at hra1
            subst hra1
            obtain ⟨⟨η₀, hb⟩, hrb, hrb1⟩ :=
              (ihb ht.2).2.2.1 hΓ hΓ' (Derivable.sigma_snd hS hΓ hC ha) _ hbeq
            simp only at hrb1
            subst hrb1
            simp only [check, ↓reduceDIte, hra, hrb]
            exact ⟨_, rfl, rfl⟩
      · cases h
    · exact check_strengthen_generic hS hSM hΓ hΓ' hC hC'
        (fun _ _ ρ' A B _ h₂ => hsig ⟨ρ', A, B, h₂⟩) (fun _ _ _ _ _ _ _ _ h₁ _ => by cases h₁)
        (fun _ _ _ _ _ h₁ _ => by cases h₁) (fun h => by simp [infer] at h) h
  | fst p ih =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.fst p)}, infer hSM Γ hΓ' (.fst p) = some r' →
          ∃ r, infer hS Γ hΓ (.fst p) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · rename_i ρ ρ' A B π _ hpeq
        split at h
        · rename_i hρ
          cases h
          obtain ⟨⟨⟨ρ₀, T₀, π₀⟩, hp⟩, hrp, hrp1⟩ := (ih ht).2.1 hΓ hΓ' hpeq
          simp only [Prod.mk.injEq] at hrp1
          obtain ⟨rfl, rfl, rfl⟩ := hrp1
          simp only [infer, hrp, hρ, ↓reduceDIte]
          exact ⟨_, rfl, rfl⟩
        · cases h
      · cases h
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | snd p ih =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.snd p)}, infer hSM Γ hΓ' (.snd p) = some r' →
          ∃ r, infer hS Γ hΓ (.snd p) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · rename_i ρ ρ' A B π _ hpeq
        split at h
        · rename_i hρ
          cases h
          obtain ⟨⟨⟨ρ₀, T₀, π₀⟩, hp⟩, hrp, hrp1⟩ := (ih ht).2.1 hΓ hΓ' hpeq
          simp only [Prod.mk.injEq] at hrp1
          obtain ⟨rfl, rfl, rfl⟩ := hrp1
          simp only [infer, hrp, hρ, ↓reduceDIte]
          exact ⟨_, rfl, rfl⟩
        · cases h
      · cases h
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | stamp a e o iha ihe iho =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.stamp a e o)}, infer hSM Γ hΓ' (.stamp a e o) = some r' →
          ∃ r, infer hS Γ hΓ (.stamp a e o) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i σ A θ _ haeq
        split at h
        · cases h
        · rename_i hσ
          split at h
          · cases h
          · rename_i η _ heeq
            split at h
            · cases h
            · rename_i ω _ hoeq
              cases h
              obtain ⟨⟨⟨σ₀, A₀, θ₀⟩, ha⟩, hra, hra1⟩ := (iha ht.1).2.1 hΓ hΓ' haeq
              simp only [Prod.mk.injEq] at hra1
              obtain ⟨rfl, rfl, rfl⟩ := hra1
              obtain ⟨⟨η₀, he⟩, hre, hre1⟩ :=
                (ihe ht.2.1).2.2.1 hΓ hΓ' Derivable.event_formed _ heeq
              simp only at hre1
              subst hre1
              obtain ⟨⟨ω₀, ho⟩, hro, hro1⟩ := (iho ht.2.2).2.2.1 hΓ hΓ'
                (Derivable.origin_formed hσ (Derivable.ty_of_tm ha) he ha) _ hoeq
              simp only at hro1
              subst hro1
              simp only [infer, hra, hσ, ↓reduceDIte, hre, hro]
              exact ⟨_, rfl, rfl⟩
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {Γ} hΓ hΓ' {ρ C} hC hC' {r'} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    by_cases hst : ∃ σ A, C = .stamped σ A
    · obtain ⟨σ, A, rfl⟩ := hst
      rw [check.eq_3] at h
      split at h
      · cases h
      · rename_i hσ
        split at h
        · rename_i hρ
          subst hρ
          simp only at h
          split at h
          · cases h
          · rename_i θ _ haeq
            split at h
            · cases h
            · rename_i η _ heeq
              split at h
              · cases h
              · rename_i ω _ hoeq
                cases h
                obtain ⟨⟨θ₀, ha⟩, hra, hra1⟩ :=
                  (iha ht.1).2.2.1 hΓ hΓ' (Derivable.stamped_inner hC).2.2 _ haeq
                simp only at hra1
                subst hra1
                obtain ⟨⟨η₀, he⟩, hre, hre1⟩ :=
                  (ihe ht.2.1).2.2.1 hΓ hΓ' Derivable.event_formed _ heeq
                simp only at hre1
                subst hre1
                obtain ⟨⟨ω₀, ho⟩, hro, hro1⟩ := (iho ht.2.2).2.2.1 hΓ hΓ'
                  (Derivable.origin_formed hσ (Derivable.stamped_inner hC).2.2 he ha) _ hoeq
                simp only at hro1
                subst hro1
                simp only [check, hσ, ↓reduceDIte, hra, hre, hro]
                exact ⟨_, rfl, rfl⟩
        · cases h
    · exact check_strengthen_generic hS hSM hΓ hΓ' hC hC' (fun _ _ _ _ _ h₁ _ => by cases h₁)
        (fun _ _ _ _ _ _ _ _ h₁ _ => by cases h₁)
        (fun _ _ _ σ A _ h₂ => hst ⟨σ, A, h₂⟩) (inf hΓ hΓ') h
  | gate g ds s ihds ihs =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.gate g ds s)}, infer hSM Γ hΓ' (.gate g ds s) = some r' →
          ∃ r, infer hS Γ hΓ (.gate g ds s) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i Δ σ A ρ B hg
        split at h
        · cases h
        · rename_i δ _ hdseq
          split at h
          · cases h
          · rename_i η _ hseq
            cases h
            rw [Sig.gate?_append_lt ht.1] at hg
            obtain ⟨⟨δ₀, hds⟩, hrds, hrds1⟩ :=
              (ihds ht.2.1).2.2.2 hΓ hΓ' (hS.gate_tel hg Γ).1 _ hdseq
            simp only at hrds1
            subst hrds1
            obtain ⟨⟨η₀, hs⟩, hrs, hrs1⟩ :=
              (ihs ht.2.2).2.2.1 hΓ hΓ' (Derivable.gate_cred hS hΓ hg hds) _ hseq
            simp only at hrs1
            subst hrs1
            rw [infer]
            split
            · rename_i h'; rw [hg] at h'; cases h'
            · rename_i Δ' σ' A' ρ' B' h'
              have e : (Δ', σ', A', ρ', B') = (Δ, σ, A, ρ, B) :=
                Option.some.inj (h'.symm.trans hg)
              cases e
              rw [hrds]
              simp only [hrs]
              exact ⟨_, rfl, rfl⟩
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | node g ℓ ds a e ihds iha ihe =>
    have inf : ∀ {Γ : Ctx} (hΓ : CtxWF S Γ) (hΓ' : CtxWF (S ++ M) Γ)
        {r' : TmCert (S ++ M) Γ (.node g ℓ ds a e)},
          infer hSM Γ hΓ' (.node g ℓ ds a e) = some r' →
            ∃ r, infer hS Γ hΓ (.node g ℓ ds a e) = some r ∧ r.1 = r'.1 := by
      intro Γ hΓ hΓ' r' h
      rw [infer] at h
      split at h
      · cases h
      · rename_i Δ σ A ρ B hg
        split at h
        · cases h
        · rename_i δ _ hdseq
          split at h
          · cases h
          · rename_i θ _ haeq
            split at h
            · cases h
            · rename_i η _ heeq
              cases h
              rw [Sig.gate?_append_lt ht.1] at hg
              obtain ⟨⟨δ₀, hds⟩, hrds, hrds1⟩ :=
                (ihds ht.2.1).2.2.2 hΓ hΓ' (hS.gate_tel hg Γ).1 _ hdseq
              simp only at hrds1
              subst hrds1
              obtain ⟨⟨θ₀, ha⟩, hra, hra1⟩ :=
                (iha ht.2.2.1).2.2.1 hΓ hΓ' (Derivable.gate_payload hS hΓ hg hds) _ haeq
              simp only at hra1
              subst hra1
              obtain ⟨⟨η₀, he⟩, hre, hre1⟩ :=
                (ihe ht.2.2.2).2.2.1 hΓ hΓ' Derivable.event_formed _ heeq
              simp only at hre1
              subst hre1
              rw [infer]
              split
              · rename_i h'; rw [hg] at h'; cases h'
              · rename_i Δ' σ' A' ρ' B' h'
                have e : (Δ', σ', A', ρ', B') = (Δ, σ, A, ρ, B) :=
                  Option.some.inj (h'.symm.trans hg)
                cases e
                rw [hrds]
                simp only [hra, hre]
                exact ⟨_, rfl, rfl⟩
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, inf,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_,
      fun {_} _ _ {_} _ _ {_} h => by simp [checkSpine] at h⟩
    exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
      (inf hΓ hΓ') h
  | nil =>
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_, fun {Γ} hΓ hΓ' {Δ} hΔ hΔ' {r'} h => ?_⟩
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
    · cases Δ with
      | nil =>
        simp only [checkSpine] at h
        cases h
        simp only [checkSpine]
        exact ⟨_, rfl, rfl⟩
      | cons p Δ => simp [checkSpine] at h
  | cons a rest iha ihrest =>
    refine ⟨fun {_} _ _ {_} h => by simp [inferTy] at h, fun {_} _ _ {_} h => by simp [infer] at h,
      fun {_} hΓ hΓ' {_ _} hC hC' {_} h => ?_, fun {Γ} hΓ hΓ' {Δ} hΔ hΔ' {r'} h => ?_⟩
    · exact check_strengthen_notIntro hS hSM hΓ hΓ' (by simp [Exp.NotIntro]) hC hC'
        (fun h => by simp [infer] at h) h
    · cases Δ with
      | nil => simp [checkSpine] at h
      | cons p Δ =>
        obtain ⟨ρ, A⟩ := p
        rw [checkSpine] at h
        split at h
        · cases h
        · rename_i ε₁ _ haeq
          split at h
          · cases h
          · rename_i ε₂ _ hresteq
            cases h
            obtain ⟨⟨ε₁₀, ha⟩, hra, hra1⟩ :=
              (iha ht.1).2.2.1 hΓ hΓ' (Derivable.tel_head hΔ) _ haeq
            simp only at hra1
            subst hra1
            obtain ⟨⟨ε₂₀, hrest⟩, hrr, hrr1⟩ :=
              (ihrest ht.2).2.2.2 hΓ hΓ' (Derivable.tel_inst hS hΓ hΔ ha) _ hresteq
            simp only at hrr1
            subst hrr1
            simp only [checkSpine, hra, hrr]
            exact ⟨_, rfl, rfl⟩

end Strengthen

/-- **Strengthening.** An old term of the bidirectional fragment, typed over
`S ++ M` at a type formed over `S`, in a context formed over `S`, is typed over `S`
with the same role, type and effect. -/
theorem Derivable.strengthen {S M : Sig} (hSM : SigWF (S ++ M)) {Γ : Ctx} (hΓ : CtxWF S Γ)
    {ρ : Role} {t C : Exp} {ε : Eff} (ht : t.Old S.length) (hchk : t.Chk)
    (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ))
    (d : Derivable (S ++ M) true (.tm Γ ρ t C ε)) : Derivable S true (.tm Γ ρ t C ε) := by
  have hΓ' := hΓ.weakenSig hSM
  obtain ⟨γ, hCγ⟩ := hC
  obtain ⟨r', hr'⟩ := (complete hSM t).2.2.1 hΓ' ⟨γ, hCγ.weakenSig M⟩ hchk d
  obtain ⟨r, hr, hr1⟩ :=
    (checker_strengthen hSM.prefix hSM t ht).2.2.1 hΓ hΓ' ⟨γ, hCγ⟩ _ hr'
  have he : r'.1 = ε := r'.eff d
  have := r.2
  rwa [hr1, he] at this

/-- **Strengthening for types.** An old type of the bidirectional fragment that is
formed over `S ++ M`, in a context formed over `S`, is formed over `S` at the same
role. -/
theorem Derivable.strengthen_ty {S M : Sig} (hSM : SigWF (S ++ M)) {Γ : Ctx} (hΓ : CtxWF S Γ)
    {ρ : Role} {A : Exp} {α : Eff} (hA : A.Old S.length) (hfr : A.TyFr)
    (d : Derivable (S ++ M) true (.ty Γ ρ A α)) : ∃ α', Derivable S true (.ty Γ ρ A α') := by
  have hΓ' := hΓ.weakenSig hSM
  obtain ⟨r', hr'⟩ := (complete hSM A).1 hΓ' hfr d
  obtain ⟨r, hr, hr1⟩ := (checker_strengthen hSM.prefix hSM A hA).1 hΓ hΓ' hr'
  have hρ : r'.1.1 = ρ := r'.role d
  obtain ⟨⟨ρ₀, α₀⟩, hd⟩ := r
  simp only at hr1
  rw [hr1, hρ] at hd
  exact ⟨_, hd⟩

/-- **Theorem 10.5** (rendering noninterference, `thm:rendering`): a
rendering-only module cannot change inhabitation. Let `M` be rendering-only over
`S`, and let `A` be a closed grade-free type formed over `S` at a role other
than rendering. The normal form of every closed term of `A` over `S ++ M` is a
closed term of `A` over `S`; hence `A` has a closed term over `S ++ M` exactly
when it has one over `S`. -/
theorem rendering_inhabitation {S M : Sig} (hSM : SigWF (S ++ M)) (hM : RenderingOnly M)
    {ρ : Role} (hρ : ρ ≠ .rendering) {A : Exp} {α : Eff} (hA : Derivable S true (.ty [] ρ A α))
    (hgf : A.gradefree) :
    (∀ {t : Exp} {ε : Eff}, Derivable (S ++ M) true (.tm [] ρ t A ε) →
      ∃ n ε', Steps t n ∧ Normal n ∧ Derivable S true (.tm [] ρ n A ε')) ∧
    ((∃ t ε, Derivable (S ++ M) true (.tm [] ρ t A ε)) ↔
      ∃ t ε, Derivable S true (.tm [] ρ t A ε)) := by
  have hAold : A.Old S.length := hA.some.subject_old
  have key : ∀ {t : Exp} {ε : Eff}, Derivable (S ++ M) true (.tm [] ρ t A ε) →
      ∃ n ε', Steps t n ∧ Normal n ∧ Derivable S true (.tm [] ρ n A ε') := by
    rintro t ε ⟨dt⟩
    obtain ⟨⟨n, ε', hs, hn, hold, hdn⟩, -⟩ := rendering_noninterference hSM hM hρ hAold hgf dt
    exact ⟨n, ε', hs, hn, hdn.strengthen hSM (.nil hSM.prefix) hold
      ((normal_fragment n).2.1 hn hdn) ⟨α, hA⟩⟩
  refine ⟨key, ⟨fun ⟨t, ε, d⟩ => ?_, fun ⟨t, ε, d⟩ => ⟨t, ε, d.weakenSig M⟩⟩⟩
  obtain ⟨n, ε', -, -, hd⟩ := key d
  exact ⟨n, ε', hd⟩

end Artform.Roles.Calculus
