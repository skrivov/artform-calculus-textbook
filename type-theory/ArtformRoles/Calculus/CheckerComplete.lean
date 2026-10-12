import ArtformRoles.Calculus.Checker

/-!
# Completeness of the checker on the bidirectional fragment

Appendix C (`app:checker`), declarative adequacy of the reference procedure.

* `Exp.Syn`, `Exp.Chk`, `Exp.TyFr`, `Exp.SpFr`: the bidirectional fragment.
  Variables, constants, applications, projections, gates and nodes are
  synthesized; abstractions and stamps are synthesized when their bodies are;
  pairs are only checked, against a dependent sum. Types and argument lists
  check their terms.
* `complete`: over a well-formed signature and in a well-formed context, the
  checker succeeds on every derivable judgment whose subject is in the
  fragment, and a synthesized type is convertible to every type of the term.
* `typeCheck_complete`, `decTyping`, `decFormed`: type checking and type
  formation are decidable on the fragment.
* `normal_fragment`: every well-typed normal term, well-formed normal type and
  well-typed normal argument list lies in the fragment, so the checker is
  complete on normal judgments (`typeCheck_complete_normal`).

Outside the fragment the procedure of Appendix C is incomplete: a pair has no
principal type, so a pair in a synthesis position, such as the argument of a
projection, is rejected although the judgment may be derivable
(`infer_fst_pair`). Proposition C.1 of the paper holds for the fragment.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## The bidirectional fragment -/

mutual

/-- Terms whose type the checker synthesizes. -/
def Exp.Syn : Exp → Prop
  | .var _ | .const _ _ => True
  | .lam _ _ A b => A.TyFr ∧ b.Syn
  | .app f u => f.Syn ∧ u.Chk
  | .fst p | .snd p => p.Syn
  | .stamp a e o => a.Syn ∧ e.Chk ∧ o.Chk
  | .gate _ ds s => ds.SpFr ∧ s.Chk
  | .node _ _ ds a e => ds.SpFr ∧ a.Chk ∧ e.Chk
  | _ => False

/-- Terms the checker checks against a type. -/
def Exp.Chk : Exp → Prop
  | .var _ | .const _ _ => True
  | .lam _ _ A b => A.TyFr ∧ b.Chk
  | .app f u => f.Syn ∧ u.Chk
  | .pair a b => a.Chk ∧ b.Chk
  | .fst p | .snd p => p.Syn
  | .stamp a e o => a.Chk ∧ e.Chk ∧ o.Chk
  | .gate _ ds s => ds.SpFr ∧ s.Chk
  | .node _ _ ds a e => ds.SpFr ∧ a.Chk ∧ e.Chk
  | _ => False

/-- Types whose terms are checkable. -/
def Exp.TyFr : Exp → Prop
  | .fam _ args => args.SpFr
  | .event => True
  | .origin A e t => A.TyFr ∧ e.Chk ∧ t.Chk
  | .stamped _ A => A.TyFr
  | .pi _ _ A B => A.TyFr ∧ B.TyFr
  | .sigma _ A B => A.TyFr ∧ B.TyFr
  | _ => False

/-- Argument lists of checkable terms. -/
def Exp.SpFr : Exp → Prop
  | .nil => True
  | .cons t ts => t.Chk ∧ ts.SpFr
  | _ => False

end

/-! ## Shapes of convertible types -/

theorem Exp.TyShape.rigid {A : Exp} (h : A.TyShape) : Conv.Rigid A := by
  cases A <;> simp_all [Exp.TyShape, Conv.Rigid]

theorem conv_pi_shape {T : Exp} (hT : T.TyShape) {q : Grade} {σ : Role} {A B : Exp}
    (h : Conv T (.pi q σ A B)) : ∃ A' B', T = .pi q σ A' B' := by
  have ht := Conv.headTag_eq hT.rigid (by simp [Conv.Rigid]) h
  cases T <;> simp only [Conv.headTag, reduceCtorEq] at ht <;> try omega
  obtain ⟨rfl, rfl, -, -⟩ := Conv.pi_inj h
  exact ⟨_, _, rfl⟩

theorem conv_sigma_shape {T : Exp} (hT : T.TyShape) {ρ : Role} {A B : Exp}
    (h : Conv T (.sigma ρ A B)) : ∃ A' B', T = .sigma ρ A' B' := by
  have ht := Conv.headTag_eq hT.rigid (by simp [Conv.Rigid]) h
  cases T <;> simp only [Conv.headTag, reduceCtorEq] at ht <;> try omega
  obtain ⟨rfl, -, -⟩ := Conv.sigma_inj h
  exact ⟨_, _, rfl⟩

theorem conv_stamped_shape {T : Exp} (hT : T.TyShape) {σ : Role} {A : Exp}
    (h : Conv T (.stamped σ A)) : ∃ A', T = .stamped σ A' := by
  have ht := Conv.headTag_eq hT.rigid (by simp [Conv.Rigid]) h
  cases T <;> simp only [Conv.headTag, reduceCtorEq] at ht <;> try omega
  obtain ⟨rfl, -⟩ := Conv.stamped_inj h
  exact ⟨_, rfl⟩

/-! ## Origins over rendering types are never accepted -/

/-- A type formed at the rendering role has grade `0` at a rendering family. -/
theorem Deriv.rendering_head {S : Sig} {acc : Bool} {Γ : Ctx} {A : Exp} {α : Eff}
    (d : Deriv S acc (.ty Γ .rendering A α)) :
    ∃ a Δ, S.family? a = some (Δ, .rendering) ∧ α (.decl a 0) = .free := by
  generalize hj : Judg.ty Γ .rendering A α = j at d
  induction d generalizing Γ A α with
  | tyFam h _ hε _ _ =>
    cases hj
    exact ⟨_, _, h, by rw [hε]; simp [Eff.unit, ← Grade.bot_eq]⟩
  | tyPi _ _ _ hε _ _ ihB =>
    cases hj
    obtain ⟨a, Δ, ha, hz⟩ := ihB rfl
    exact ⟨a, Δ, ha, by rw [hε]; simp [hz, ← Grade.bot_eq]⟩
  | tySigma _ _ hε _ ihA _ =>
    cases hj
    obtain ⟨a, Δ, ha, hz⟩ := ihA rfl
    exact ⟨a, Δ, ha, by rw [hε]; simp [hz, ← Grade.bot_eq]⟩
  | _ => cases hj

/-- An accepted origin type has a non-rendering payload type. -/
theorem Deriv.origin_nonrendering {S : Sig} {Γ : Ctx} {σ : Role} {A : Exp} {α ε : Eff}
    (dA : Deriv S true (.ty Γ σ A α)) (hle : ε ≤ α) (hv : Valid S Γ .witness ε) :
    σ ≠ .rendering := by
  rintro rfl
  obtain ⟨a, Δ, ha, hz⟩ := dA.rendering_head
  have h := hv (.decl a 0) .rendering (by simp [roleOf, Sig.declRole_family ha])
  have := (hle (.decl a 0)).trans_eq hz
  have := h.trans this
  exact absurd this (by decide)

/-! ## Roles and effects of the checker's answers -/

section Answers

variable {S : Sig} {Γ : Ctx}

theorem TyCert.role {A : Exp} (r : TyCert S Γ A) {ρ : Role} {α : Eff}
    (d : Derivable S true (.ty Γ ρ A α)) : r.1.1 = ρ := by
  obtain ⟨d₁⟩ := r.2
  obtain ⟨d⟩ := d
  exact d₁.role_unique d

theorem TmCert.role {t : Exp} (r : TmCert S Γ t) {ρ : Role} {C : Exp} {ε : Eff}
    (d : Derivable S true (.tm Γ ρ t C ε)) : r.1.1 = ρ := by
  obtain ⟨d₁⟩ := r.2
  obtain ⟨d⟩ := d
  exact (Deriv.gskel_unique t d₁ d).2

theorem TmCert.eff {t : Exp} (r : TmCert S Γ t) {ρ : Role} {C : Exp} {ε : Eff}
    (d : Derivable S true (.tm Γ ρ t C ε)) : r.1.2.2 = ε := by
  obtain ⟨d₁⟩ := r.2
  obtain ⟨d⟩ := d
  exact Deriv.effect_unique d₁ d

theorem ChkCert.eff {t : Exp} {ρ : Role} {C : Exp} (r : ChkCert S Γ t ρ C) {ρ' : Role}
    {C' : Exp} {ε : Eff} (d : Derivable S true (.tm Γ ρ' t C' ε)) : r.1 = ε := by
  obtain ⟨d₁⟩ := r.2
  obtain ⟨d⟩ := d
  exact Deriv.effect_unique d₁ d

end Answers

/-! ## Evaluating the checker -/

section Eval

variable {S : Sig} (hS : SigWF S) {Γ : Ctx} (hΓ : CtxWF S Γ)

/-- A term that is not a pair, an abstraction or a stamp is checked by synthesis
and a conversion test. -/
theorem check_by_infer {t : Exp} {ρ : Role} {C : Exp} {hC : ∃ γ, Derivable S true (.ty Γ ρ C γ)}
    (ht : ∀ a b, t ≠ .pair a b) (hl : ∀ q σ A b, t ≠ .lam q σ A b)
    (hs : ∀ a e o, t ≠ .stamp a e o) {r : TmCert S Γ t} (hr : infer hS Γ hΓ t = some r)
    (hρ : r.1.1 = ρ) (hconv : Conv r.1.2.1 C) :
    ∃ r', check hS Γ hΓ t ρ C hC = some r' := by
  rw [check]
  · split
    · rename_i h
      rw [hr] at h
      cases h
    · rename_i σ' A' θ' ha h
      rw [hr] at h
      cases h
      simp only at hρ hconv
      split
      · split
        · rename_i hn _
          exact absurd hconv hn
        · exact ⟨_, rfl⟩
      · contradiction
  · intro a b _ _ _ _ h _ _
    exact ht a b h
  · intro q σ A b _ _ _ _ _ h _ _
    exact hl q σ A b h
  · intro a e o _ _ _ h _ _
    exact hs a e o h


theorem inferTy_fam {a : ℕ} {args : Exp} {Δ : Tel} {ρ : Role} (ha : S.family? a = some (Δ, ρ))
    (hsp : ∀ hΔ, ∃ r, checkSpine hS Γ hΓ args Δ hΔ = some r) :
    ∃ r, inferTy hS Γ hΓ (.fam a args) = some r := by
  rw [inferTy]
  split
  · rename_i h
    rw [ha] at h
    cases h
  · rename_i Δ' ρ' h
    have e : (Δ', ρ') = (Δ, ρ) := Option.some.inj (h.symm.trans ha)
    cases e
    obtain ⟨r, hr⟩ := hsp (hS.family_tel h Γ)
    rw [hr]
    exact ⟨_, rfl⟩

theorem inferTy_origin {A e t : Exp} {r : TyCert S Γ A} (hA : inferTy hS Γ hΓ A = some r)
    (hσ : r.1.1 ≠ .rendering)
    (he : ∀ hC, ∃ r', check hS Γ hΓ e .witness .event hC = some r')
    (ht : ∀ hC, ∃ r', check hS Γ hΓ t r.1.1 A hC = some r') :
    ∃ r', inferTy hS Γ hΓ (.origin A e t) = some r' := by
  obtain ⟨⟨σ, α⟩, hA'⟩ := r
  simp only at hσ ht
  obtain ⟨⟨η, he'⟩, h₁⟩ := he Derivable.event_formed
  obtain ⟨⟨θ, ht'⟩, h₂⟩ := ht ⟨α, hA'⟩
  simp only [inferTy, hA, hσ, ↓reduceDIte, h₁, h₂]
  exact ⟨_, rfl⟩

theorem inferTy_event : ∃ r, inferTy hS Γ hΓ .event = some r := by
  simp only [inferTy]
  exact ⟨_, rfl⟩

theorem inferTy_stamped {σ : Role} {A : Exp} {r : TyCert S Γ A} (hA : inferTy hS Γ hΓ A = some r)
    (hr : r.1.1 = σ) (hσ : σ ≠ .rendering) :
    ∃ r', inferTy hS Γ hΓ (.stamped σ A) = some r' := by
  obtain ⟨⟨σ', α⟩, hA'⟩ := r
  simp only at hr
  subst hr
  simp only [inferTy, hA, hσ, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem inferTy_pi {q : Grade} {σ : Role} {A B : Exp} {r : TyCert S Γ A}
    (hA : inferTy hS Γ hΓ A = some r) (hr : r.1.1 = σ) {hΓ' : CtxWF S ((σ, A) :: Γ)}
    {rB : TyCert S ((σ, A) :: Γ) B} (hB : inferTy hS _ hΓ' B = some rB)
    (hq : demand σ rB.1.1 ≤ q) :
    ∃ r', inferTy hS Γ hΓ (.pi q σ A B) = some r' := by
  obtain ⟨⟨σ', α⟩, hA'⟩ := r
  obtain ⟨⟨ρ, β⟩, hB'⟩ := rB
  simp only at hr hq
  subst hr
  simp only [inferTy, hA, ↓reduceDIte, hB, hq]
  exact ⟨_, rfl⟩

theorem inferTy_sigma {ρ : Role} {A B : Exp} {r : TyCert S Γ A}
    (hA : inferTy hS Γ hΓ A = some r) (hr : r.1.1 = ρ) {hΓ' : CtxWF S ((ρ, A) :: Γ)}
    {rB : TyCert S ((ρ, A) :: Γ) B} (hB : inferTy hS _ hΓ' B = some rB) (hrB : rB.1.1 = ρ) :
    ∃ r', inferTy hS Γ hΓ (.sigma ρ A B) = some r' := by
  obtain ⟨⟨ρ', α⟩, hA'⟩ := r
  obtain ⟨⟨ρ'', β⟩, hB'⟩ := rB
  simp only at hr hrB
  subst hr hrB
  simp only [inferTy, hA, ↓reduceDIte, hB]
  exact ⟨_, rfl⟩

theorem infer_var {i : ℕ} {ρ : Role} {A : Exp} (hi : Γ[i]? = some (ρ, A)) :
    ∃ r, infer hS Γ hΓ (.var i) = some r ∧ r.1.2.1 = A.ren (· + (i + 1)) := by
  rw [infer]
  split
  · rename_i h
    rw [hi] at h
    cases h
  · rename_i ρ' A' h
    have e : (ρ', A') = (ρ, A) := Option.some.inj (h.symm.trans hi)
    cases e
    exact ⟨_, rfl, rfl⟩

theorem infer_const {i k : ℕ} {ρ : Role} {A : Exp} (hc : S.const? i k = some (ρ, A)) :
    ∃ r, infer hS Γ hΓ (.const i k) = some r ∧ r.1.2.1 = A := by
  rw [infer]
  split
  · rename_i h
    rw [hc] at h
    cases h
  · rename_i ρ' A' h
    have e : (ρ', A') = (ρ, A) := Option.some.inj (h.symm.trans hc)
    cases e
    exact ⟨_, rfl, rfl⟩

theorem infer_lam {q : Grade} {σ : Role} {A b : Exp} {rA : TyCert S Γ A}
    (hA : inferTy hS Γ hΓ A = some rA) (hσ : rA.1.1 = σ) {hΓ' : CtxWF S ((σ, A) :: Γ)}
    {rb : TmCert S ((σ, A) :: Γ) b} (hb : infer hS _ hΓ' b = some rb)
    (hq : q ≤ rb.1.2.2 (.var 0)) (hq' : demand σ rb.1.1 ≤ q) :
    ∃ r, infer hS Γ hΓ (.lam q σ A b) = some r ∧ r.1.2.1 = .pi q σ A rb.1.2.1 := by
  obtain ⟨⟨σ', α⟩, hA'⟩ := rA
  obtain ⟨⟨ρ, B, θ⟩, hb'⟩ := rb
  simp only at hσ hq hq' ⊢
  subst hσ
  simp only [infer, hA, ↓reduceDIte, hb, hq, hq', and_self]
  exact ⟨_, rfl, rfl⟩

theorem infer_app {f u : Exp} {rf : TmCert S Γ f} (hf : infer hS Γ hΓ f = some rf)
    {q : Grade} {σ : Role} {A B : Exp} (hT : rf.1.2.1 = .pi q σ A B)
    {hC : ∃ α, Derivable S true (.ty Γ σ A α)} {ru : ChkCert S Γ u σ A}
    (hu : check hS Γ hΓ u σ A hC = some ru) :
    ∃ r, infer hS Γ hΓ (.app f u) = some r ∧ r.1.2.1 = B.inst u := by
  obtain ⟨⟨ρ, T, φ⟩, hf'⟩ := rf
  simp only at hT
  subst hT
  simp only [infer, hf, hu]
  exact ⟨_, rfl, rfl⟩

theorem infer_fst {p : Exp} {rp : TmCert S Γ p} (hp : infer hS Γ hΓ p = some rp)
    {A B : Exp} (hT : rp.1.2.1 = .sigma rp.1.1 A B) :
    ∃ r, infer hS Γ hΓ (.fst p) = some r ∧ r.1.2.1 = A := by
  obtain ⟨⟨ρ, T, π⟩, hp'⟩ := rp
  simp only at hT
  subst hT
  simp only [infer, hp, ↓reduceDIte]
  exact ⟨_, rfl, rfl⟩

theorem infer_snd {p : Exp} {rp : TmCert S Γ p} (hp : infer hS Γ hΓ p = some rp)
    {A B : Exp} (hT : rp.1.2.1 = .sigma rp.1.1 A B) :
    ∃ r, infer hS Γ hΓ (.snd p) = some r ∧ r.1.2.1 = B.inst (.fst p) := by
  obtain ⟨⟨ρ, T, π⟩, hp'⟩ := rp
  simp only at hT
  subst hT
  simp only [infer, hp, ↓reduceDIte]
  exact ⟨_, rfl, rfl⟩

theorem infer_stamp {a e o : Exp} {ra : TmCert S Γ a} (ha : infer hS Γ hΓ a = some ra)
    (hσ : ra.1.1 ≠ .rendering)
    (he : ∀ hC, ∃ r, check hS Γ hΓ e .witness .event hC = some r)
    (ho : ∀ hC, ∃ r, check hS Γ hΓ o .witness (.origin ra.1.2.1 e a) hC = some r) :
    ∃ r, infer hS Γ hΓ (.stamp a e o) = some r ∧ r.1.2.1 = .stamped ra.1.1 ra.1.2.1 := by
  obtain ⟨⟨σ, A, θ⟩, ha'⟩ := ra
  simp only at hσ ho ⊢
  obtain ⟨⟨η, he'⟩, h₁⟩ := he Derivable.event_formed
  obtain ⟨⟨ω, ho'⟩, h₂⟩ := ho (Derivable.origin_formed hσ (Derivable.ty_of_tm ha') he' ha')
  simp only [infer, ha, hσ, ↓reduceDIte, h₁, h₂]
  exact ⟨_, rfl, rfl⟩

theorem infer_gate {g : ℕ} {ds s : Exp} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : ∀ hΔ, ∃ r, checkSpine hS Γ hΓ ds Δ hΔ = some r)
    (hs : ∀ hC, ∃ r, check hS Γ hΓ s .witness (.stamped σ (instType ds Δ A)) hC = some r) :
    ∃ r, infer hS Γ hΓ (.gate g ds s) = some r ∧ r.1.2.1 = instType ds Δ B := by
  rw [infer]
  split
  · rename_i h
    rw [hg] at h
    cases h
  · rename_i Δ' σ' A' ρ' B' h
    have e : (Δ', σ', A', ρ', B') = (Δ, σ, A, ρ, B) := Option.some.inj (h.symm.trans hg)
    cases e
    obtain ⟨⟨δ, hds'⟩, h₁⟩ := hds (hS.gate_tel h Γ).1
    obtain ⟨⟨η, hs'⟩, h₂⟩ := hs (Derivable.gate_cred hS hΓ h hds')
    simp only [h₁, h₂]
    exact ⟨_, rfl, rfl⟩

theorem infer_node {g ℓ : ℕ} {ds a e : Exp} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hds : ∀ hΔ, ∃ r, checkSpine hS Γ hΓ ds Δ hΔ = some r)
    (ha : ∀ hC, ∃ r, check hS Γ hΓ a σ (instType ds Δ A) hC = some r)
    (he : ∀ hC, ∃ r, check hS Γ hΓ e .witness .event hC = some r) :
    ∃ r, infer hS Γ hΓ (.node g ℓ ds a e) = some r ∧ r.1.2.1 = instType ds Δ B := by
  rw [infer]
  split
  · rename_i h
    rw [hg] at h
    cases h
  · rename_i Δ' σ' A' ρ' B' h
    have e' : (Δ', σ', A', ρ', B') = (Δ, σ, A, ρ, B) := Option.some.inj (h.symm.trans hg)
    cases e'
    obtain ⟨⟨δ, hds'⟩, h₁⟩ := hds (hS.gate_tel h Γ).1
    obtain ⟨⟨θ, ha'⟩, h₂⟩ := ha (Derivable.gate_payload hS hΓ h hds')
    obtain ⟨⟨η, he'⟩, h₃⟩ := he Derivable.event_formed
    simp only [h₁, h₂, h₃]
    exact ⟨_, rfl, rfl⟩

theorem check_pair {a b : Exp} {ρ : Role} {A B : Exp}
    {hC : ∃ γ, Derivable S true (.ty Γ ρ (.sigma ρ A B) γ)}
    (ha : ∀ hA, ∃ r, check hS Γ hΓ a ρ A hA = some r)
    (hb : ∀ hB, ∃ r, check hS Γ hΓ b ρ (B.inst a) hB = some r) :
    ∃ r, check hS Γ hΓ (.pair a b) ρ (.sigma ρ A B) hC = some r := by
  obtain ⟨⟨θ, ha'⟩, h₁⟩ := ha (Derivable.sigma_fst hC)
  obtain ⟨⟨η, hb'⟩, h₂⟩ := hb (Derivable.sigma_snd hS hΓ hC ha')
  simp only [check, ↓reduceDIte, h₁, h₂]
  exact ⟨_, rfl⟩

theorem check_lam {q : Grade} {σ ρ : Role} {A b A' B' : Exp}
    {hC : ∃ γ, Derivable S true (.ty Γ ρ (.pi q σ A' B') γ)} {rA : TyCert S Γ A}
    (hA : inferTy hS Γ hΓ A = some rA) (hσ : rA.1.1 = σ) (hconv : Conv A A')
    (hb : ∀ hΓ' hB, ∃ r, check hS ((σ, A) :: Γ) hΓ' b ρ B' hB = some r ∧ q ≤ r.1 (.var 0)) :
    ∃ r, check hS Γ hΓ (.lam q σ A b) ρ (.pi q σ A' B') hC = some r := by
  obtain ⟨⟨σ', α⟩, hA'⟩ := rA
  simp only at hσ
  subst hσ
  rw [check]
  rw [dite_eq_left ⟨rfl, rfl⟩, hA]
  simp only [↓reduceDIte]
  split
  · rename_i hn _
    exact absurd hconv hn
  · obtain ⟨⟨θ, hb'⟩, h₁, hq⟩ := hb _ _
    rw [h₁]
    simp only at hq ⊢
    rw [dite_eq_left hq]
    exact ⟨_, rfl⟩

theorem check_stamp {a e o : Exp} {σ : Role} {A : Exp}
    {hC : ∃ γ, Derivable S true (.ty Γ .witness (.stamped σ A) γ)}
    (ha : ∀ hA, ∃ r, check hS Γ hΓ a σ A hA = some r)
    (he : ∀ hC, ∃ r, check hS Γ hΓ e .witness .event hC = some r)
    (ho : ∀ hC, ∃ r, check hS Γ hΓ o .witness (.origin A e a) hC = some r) :
    ∃ r, check hS Γ hΓ (.stamp a e o) .witness (.stamped σ A) hC = some r := by
  have hσ := (Derivable.stamped_inner hC).2.1
  obtain ⟨⟨θ, ha'⟩, h₁⟩ := ha (Derivable.stamped_inner hC).2.2
  obtain ⟨⟨η, he'⟩, h₂⟩ := he Derivable.event_formed
  obtain ⟨⟨ω, ho'⟩, h₃⟩ := ho (Derivable.origin_formed hσ (Derivable.stamped_inner hC).2.2 he' ha')
  simp only [check, hσ, ↓reduceDIte, h₁, h₂, h₃]
  exact ⟨_, rfl⟩

theorem checkSpine_nil {hΔ : ∃ δ, Derivable S true (.tel Γ [] δ)} :
    ∃ r, checkSpine hS Γ hΓ .nil [] hΔ = some r := by
  simp only [checkSpine]
  exact ⟨_, rfl⟩

theorem checkSpine_cons {a rest : Exp} {ρ : Role} {A : Exp} {Δ : Tel}
    {hΔ : ∃ δ, Derivable S true (.tel Γ ((ρ, A) :: Δ) δ)}
    (ha : ∀ hA, ∃ r, check hS Γ hΓ a ρ A hA = some r)
    (hrest : ∀ hΔ', ∃ r, checkSpine hS Γ hΓ rest (Tel.inst a Δ) hΔ' = some r) :
    ∃ r, checkSpine hS Γ hΓ (.cons a rest) ((ρ, A) :: Δ) hΔ = some r := by
  obtain ⟨⟨ε₁, ha'⟩, h₁⟩ := ha (Derivable.tel_head hΔ)
  obtain ⟨⟨ε₂, hrest'⟩, h₂⟩ := hrest (Derivable.tel_inst hS hΓ hΔ ha')
  simp only [checkSpine, h₁, h₂]
  exact ⟨_, rfl⟩

end Eval

/-! ## Normal forms lie in the fragment -/

/-- A term that synthesizes is not an introduction form of a pair, a stamp or an
abstraction. -/
def Exp.NotIntro (t : Exp) : Prop :=
  (∀ a b, t ≠ .pair a b) ∧ (∀ a e o, t ≠ .stamp a e o) ∧ (∀ q σ A b, t ≠ .lam q σ A b)

/-- Every well-formed normal type, every well-typed normal term and every
well-typed normal argument list lies in the bidirectional fragment; a normal
term that is not an introduction form synthesizes. -/
theorem normal_fragment {S : Sig} (t : Exp) :
    (∀ {Γ : Ctx} {ρ : Role} {α : Eff}, Normal t → Derivable S true (.ty Γ ρ t α) → t.TyFr) ∧
    (∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal t →
      Derivable S true (.tm Γ ρ t C ε) → t.Chk) ∧
    (∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal t → t.NotIntro →
      Derivable S true (.tm Γ ρ t C ε) → t.Syn) ∧
    (∀ {Γ : Ctx} {Δ : Tel} {δ : Eff}, Normal t →
      Derivable S true (.spine Γ t Δ δ) → t.SpFr) := by
  induction t with
  | var i =>
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun _ _ => trivial, fun _ _ _ => trivial,
      fun _ ⟨d⟩ => (by cases d)⟩
  | const i k =>
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun _ _ => trivial, fun _ _ _ => trivial,
      fun _ ⟨d⟩ => (by cases d)⟩
  | fam a args ih =>
    refine ⟨fun hn ⟨d⟩ => ?_, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
    cases d with
    | tyFam _ dargs _ _ => exact ih.2.2.2 (Normal.of_step_lift (fun h => Step.fam h) hn) ⟨dargs⟩
  | event =>
    exact ⟨fun _ _ => trivial, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
  | origin A e t ihA ihe iht =>
    refine ⟨fun hn ⟨d⟩ => ?_, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
    cases d with
    | tyOrigin dA de dt _ _ =>
      exact ⟨ihA.1 (Normal.of_step_lift (fun h => Step.origin₁ h) hn) ⟨dA⟩,
        ihe.2.1 (Normal.of_step_lift (fun h => Step.origin₂ h) hn) ⟨de⟩,
        iht.2.1 (Normal.of_step_lift (fun h => Step.origin₃ h) hn) ⟨dt⟩⟩
  | stamped σ A ih =>
    refine ⟨fun hn ⟨d⟩ => ?_, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
    cases d with
    | tyStamped dA _ _ _ => exact ih.1 (Normal.of_step_lift (fun h => Step.stamped h) hn) ⟨dA⟩
  | pi q σ A B ihA ihB =>
    refine ⟨fun hn ⟨d⟩ => ?_, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
    cases d with
    | tyPi dA dB _ _ _ =>
      exact ⟨ihA.1 (Normal.of_step_lift (fun h => Step.pi₁ h) hn) ⟨dA⟩,
        ihB.1 (Normal.of_step_lift (fun h => Step.pi₂ h) hn) ⟨dB⟩⟩
  | sigma ρ A B ihA ihB =>
    refine ⟨fun hn ⟨d⟩ => ?_, fun _ ⟨d⟩ => d.isTermHead.elim, fun _ _ ⟨d⟩ => d.isTermHead.elim,
      fun _ ⟨d⟩ => (by cases d)⟩
    cases d with
    | tySigma dA dB _ _ =>
      exact ⟨ihA.1 (Normal.of_step_lift (fun h => Step.sigma₁ h) hn) ⟨dA⟩,
        ihB.1 (Normal.of_step_lift (fun h => Step.sigma₂ h) hn) ⟨dB⟩⟩
  | lam q σ A b ihA ihb =>
    refine ⟨fun _ ⟨d⟩ => (by cases d), fun hn ⟨d⟩ => ?_, fun _ hi _ => absurd rfl (hi.2.2 _ _ _ _),
      fun _ ⟨d⟩ => (by cases d)⟩
    obtain ⟨_, _, _, _, _, ⟨_, hA⟩, hb, _⟩ := d.inv_lam
    exact ⟨ihA.1 hn.lam.1 hA, ihb.2.1 hn.lam.2 hb⟩
  | app f u ihf ihu =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal (.app f u) →
        Derivable S true (.tm Γ ρ (.app f u) C ε) → (Exp.app f u).Syn := by
      intro Γ ρ C ε hn ⟨d⟩
      obtain ⟨_, _, _, _, _, _, _, _, ⟨df⟩, hu, _⟩ := d.inv_app
      obtain ⟨hf, hu', hlam⟩ := hn.app
      refine ⟨ihf.2.2.1 hf ⟨fun a b he => ?_, fun a e o he => ?_, hlam⟩ ⟨df⟩, ihu.2.1 hu' hu⟩
      · subst he
        exact df.not_pair_of_pi
      · subst he
        exact df.not_stamp_of_pi
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun hn d => syn hn d, fun hn _ d => syn hn d,
      fun _ ⟨d⟩ => (by cases d)⟩
  | pair a b iha ihb =>
    refine ⟨fun _ ⟨d⟩ => (by cases d), fun hn ⟨d⟩ => ?_, fun _ hi _ => absurd rfl (hi.1 _ _),
      fun _ ⟨d⟩ => (by cases d)⟩
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := d.inv_pair
    exact ⟨iha.2.1 hn.pair.1 ha, ihb.2.1 hn.pair.2 hb⟩
  | fst p ih =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal (.fst p) →
        Derivable S true (.tm Γ ρ (.fst p) C ε) → (Exp.fst p).Syn := by
      intro Γ ρ C ε hn ⟨d⟩
      obtain ⟨_, _, _, ⟨dp⟩, _⟩ := d.inv_fst
      obtain ⟨hp, hpair⟩ := hn.fst
      refine ih.2.2.1 hp ⟨hpair, fun a e o he => ?_, fun q σ A b he => ?_⟩ ⟨dp⟩
      · subst he
        exact dp.not_stamp_of_sigma
      · subst he
        exact dp.not_lam_of_sigma
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun hn d => syn hn d, fun hn _ d => syn hn d,
      fun _ ⟨d⟩ => (by cases d)⟩
  | snd p ih =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal (.snd p) →
        Derivable S true (.tm Γ ρ (.snd p) C ε) → (Exp.snd p).Syn := by
      intro Γ ρ C ε hn ⟨d⟩
      obtain ⟨_, _, _, ⟨dp⟩, _⟩ := d.inv_snd
      obtain ⟨hp, hpair⟩ := hn.snd
      refine ih.2.2.1 hp ⟨hpair, fun a e o he => ?_, fun q σ A b he => ?_⟩ ⟨dp⟩
      · subst he
        exact dp.not_stamp_of_sigma
      · subst he
        exact dp.not_lam_of_sigma
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun hn d => syn hn d, fun hn _ d => syn hn d,
      fun _ ⟨d⟩ => (by cases d)⟩
  | stamp a e o iha ihe iho =>
    refine ⟨fun _ ⟨d⟩ => (by cases d), fun hn ⟨d⟩ => ?_, fun _ hi _ => absurd rfl (hi.2.1 _ _ _),
      fun _ ⟨d⟩ => (by cases d)⟩
    obtain ⟨_, _, _, _, _, _, _, _, ha, he, ho, _⟩ := d.inv_stamp
    obtain ⟨n₁, n₂, n₃⟩ := hn.stamp
    exact ⟨iha.2.1 n₁ ha, ihe.2.1 n₂ he, iho.2.1 n₃ ho⟩
  | gate g ds s ihds ihs =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal (.gate g ds s) →
        Derivable S true (.tm Γ ρ (.gate g ds s) C ε) → (Exp.gate g ds s).Syn := by
      intro Γ ρ C ε hn ⟨d⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, hds, hs, _⟩ := d.inv_gate
      exact ⟨ihds.2.2.2 hn.gate.1 hds, ihs.2.1 hn.gate.2.1 hs⟩
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun hn d => syn hn d, fun hn _ d => syn hn d,
      fun _ ⟨d⟩ => (by cases d)⟩
  | node g ℓ ds a e ihds iha ihe =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Normal (.node g ℓ ds a e) →
        Derivable S true (.tm Γ ρ (.node g ℓ ds a e) C ε) → (Exp.node g ℓ ds a e).Syn := by
      intro Γ ρ C ε hn ⟨d⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hds, ha, he, _⟩ := d.inv_node
      obtain ⟨n₁, n₂, n₃⟩ := hn.node
      exact ⟨ihds.2.2.2 n₁ hds, iha.2.1 n₂ ha, ihe.2.1 n₃ he⟩
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun hn d => syn hn d, fun hn _ d => syn hn d,
      fun _ ⟨d⟩ => (by cases d)⟩
  | nil =>
    exact ⟨fun _ ⟨d⟩ => (by cases d), fun _ ⟨d⟩ => d.isTermHead.elim,
      fun _ _ ⟨d⟩ => d.isTermHead.elim, fun _ _ => trivial⟩
  | cons a rest iha ihrest =>
    refine ⟨fun _ ⟨d⟩ => (by cases d), fun _ ⟨d⟩ => d.isTermHead.elim,
      fun _ _ ⟨d⟩ => d.isTermHead.elim, fun hn ⟨d⟩ => ?_⟩
    cases d with
    | spineCons da drest _ =>
      exact ⟨iha.2.1 hn.cons.1 ⟨da⟩, ihrest.2.2.2 hn.cons.2 ⟨drest⟩⟩

/-! ## Completeness -/

section Complete

variable {S : Sig} (hS : SigWF S)

/-- Checking a term that is neither a pair, an abstraction nor a stamp reduces to
synthesis. -/
theorem check_of_syn {Γ : Ctx} {hΓ : CtxWF S Γ} {t : Exp} {ρ : Role} {C : Exp} {ε : Eff}
    {hC : ∃ γ, Derivable S true (.ty Γ ρ C γ)}
    (ht : ∀ a b, t ≠ .pair a b) (hl : ∀ q σ A b, t ≠ .lam q σ A b)
    (hs : ∀ a e o, t ≠ .stamp a e o)
    (hsyn : ∃ r, infer hS Γ hΓ t = some r ∧ Conv r.1.2.1 C)
    (d : Derivable S true (.tm Γ ρ t C ε)) :
    ∃ r, check hS Γ hΓ t ρ C hC = some r := by
  obtain ⟨r, hr, hconv⟩ := hsyn
  exact check_by_infer hS hΓ ht hl hs hr (r.role d) hconv

/-- The type of a checked or synthesized term is a well-formed type, hence of the
shape of a type. -/
theorem TmCert.tyShape {Γ : Ctx} {t : Exp} (r : TmCert S Γ t) : r.1.2.1.TyShape :=
  Exp.TyShape.of_ex (Derivable.ty_of_tm r.2)

/-- **Proposition C.1** (`app:checker`, declarative adequacy of the reference
procedure), on the bidirectional fragment. Over a well-formed signature and in a
well-formed context: `inferTy` succeeds on every formed type of the fragment;
`infer` succeeds on every typable term it synthesizes, with a type convertible to
every type of the term; `check` succeeds on every derivable judgment of a
checkable term; `checkSpine` on every derivable argument list. The answers are
derivations, so the procedure accepts exactly the derivable judgments of the
fragment. -/
theorem complete (t : Exp) :
    (∀ {Γ : Ctx} {ρ : Role} {α : Eff} (hΓ : CtxWF S Γ), t.TyFr →
      Derivable S true (.ty Γ ρ t α) → ∃ r, inferTy hS Γ hΓ t = some r) ∧
    (∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ), t.Syn →
      Derivable S true (.tm Γ ρ t C ε) → ∃ r, infer hS Γ hΓ t = some r ∧ Conv r.1.2.1 C) ∧
    (∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ)
      (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ)), t.Chk →
      Derivable S true (.tm Γ ρ t C ε) → ∃ r, check hS Γ hΓ t ρ C hC = some r) ∧
    (∀ {Γ : Ctx} {Δ : Tel} {δ : Eff} (hΓ : CtxWF S Γ)
      (hΔ : ∃ δ, Derivable S true (.tel Γ Δ δ)), t.SpFr →
      Derivable S true (.spine Γ t Δ δ) → ∃ r, checkSpine hS Γ hΓ t Δ hΔ = some r) := by
  induction t with
  | var i =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ), (Exp.var i).Syn →
        Derivable S true (.tm Γ ρ (.var i) C ε) →
          ∃ r, infer hS Γ hΓ (.var i) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ _ ⟨d⟩
      obtain ⟨A₀, hi, hconv, -, -⟩ := d.inv_var
      obtain ⟨r, hr, hT⟩ := infer_var hS hΓ hi
      exact ⟨r, hr, hT ▸ hconv⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ trivial d) d
  | const i k =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ),
        (Exp.const i k).Syn → Derivable S true (.tm Γ ρ (.const i k) C ε) →
          ∃ r, infer hS Γ hΓ (.const i k) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ _ ⟨d⟩
      obtain ⟨A₀, hc, hconv, -, -⟩ := d.inv_const
      obtain ⟨r, hr, hT⟩ := infer_const hS hΓ hc
      exact ⟨r, hr, hT ▸ hconv⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ trivial d) d
  | fam a args ihargs =>
    refine ⟨fun hΓ h ⟨d⟩ => ?_, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    cases d with
    | tyFam ha dargs _ _ =>
      exact inferTy_fam hS hΓ ha (fun hΔ => ihargs.2.2.2 hΓ hΔ h ⟨dargs⟩)
  | event =>
    exact ⟨fun hΓ _ _ => inferTy_event hS hΓ, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
  | origin A e t ihA ihe iht =>
    refine ⟨fun hΓ h ⟨d⟩ => ?_, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    simp only [Exp.TyFr] at h
    cases d with
    | tyOrigin dA de dt hε hv =>
      have hσ := dA.origin_nonrendering (hε ▸ inf_le_left.trans inf_le_left) (hv rfl)
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h.1 ⟨dA⟩
      have hrole := rA.role ⟨dA⟩
      obtain ⟨⟨σ', α'⟩, hA'⟩ := rA
      simp only at hrole
      subst hrole
      exact inferTy_origin hS hΓ hrA hσ (fun hC => ihe.2.2.1 hΓ hC h.2.1 ⟨de⟩)
        (fun hC => iht.2.2.1 hΓ hC h.2.2 ⟨dt⟩)
  | stamped σ A ihA =>
    refine ⟨fun hΓ h ⟨d⟩ => ?_, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    simp only [Exp.TyFr] at h
    cases d with
    | tyStamped dA hσ _ _ =>
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h ⟨dA⟩
      exact inferTy_stamped hS hΓ hrA (rA.role ⟨dA⟩) hσ
  | pi q σ A B ihA ihB =>
    refine ⟨fun hΓ h ⟨d⟩ => ?_, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    simp only [Exp.TyFr] at h
    cases d with
    | tyPi dA dB hq _ _ =>
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h.1 ⟨dA⟩
      have hΓ' := CtxWF.cons hΓ ⟨dA⟩
      obtain ⟨rB, hrB⟩ := ihB.1 hΓ' h.2 ⟨dB⟩
      exact inferTy_pi hS hΓ hrA (rA.role ⟨dA⟩) hrB (by rw [rB.role ⟨dB⟩]; exact hq)
  | sigma ρ A B ihA ihB =>
    refine ⟨fun hΓ h ⟨d⟩ => ?_, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    simp only [Exp.TyFr] at h
    cases d with
    | tySigma dA dB _ _ =>
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h.1 ⟨dA⟩
      have hΓ' := CtxWF.cons hΓ ⟨dA⟩
      obtain ⟨rB, hrB⟩ := ihB.1 hΓ' h.2 ⟨dB⟩
      exact inferTy_sigma hS hΓ hrA (rA.role ⟨dA⟩) hrB (rB.role ⟨dB⟩)
  | lam q σ A b ihA ihb =>
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, fun hΓ h ⟨d⟩ => ?_, fun hΓ hC h ⟨d⟩ => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    · simp only [Exp.Syn] at h
      obtain ⟨B, θ, hc, hq, -, ⟨α, hA⟩, hb, ⟨γ, ⟨dpi⟩⟩⟩ := d.inv_lam
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h.1 hA
      have hΓ' := CtxWF.cons hΓ hA
      obtain ⟨rb, hrb, hconv⟩ := ihb.2.1 hΓ' h.2 hb
      obtain ⟨r, hr, hT⟩ := infer_lam (q := q) hS hΓ hrA (rA.role hA) hrb
        (by rw [rb.eff hb]; exact hq) (by rw [rb.role hb]; exact dpi.tyPi_demand)
      exact ⟨r, hr, hT ▸ (Conv.lift (fun X => Exp.pi q σ A X) (fun h => Step.pi₂ h) hconv).trans hc⟩
    · simp only [Exp.Chk] at h
      obtain ⟨B, θ, hc, hq, -, ⟨α, hA⟩, hb, -⟩ := d.inv_lam
      obtain ⟨A', B', rfl⟩ := conv_pi_shape (Exp.TyShape.of_ex hC) hc.symm
      obtain ⟨-, -, hAA', hBB'⟩ := Conv.pi_inj hc
      obtain ⟨rA, hrA⟩ := ihA.1 hΓ h.1 hA
      refine check_lam hS hΓ hrA (rA.role hA) hAA' (fun hΓ' hB => ?_)
      obtain ⟨r, hr⟩ := ihb.2.2.1 hΓ' hB h.2 (Derivable.conv hb hBB' hB)
      exact ⟨r, hr, by rw [r.eff hb]; exact hq⟩
  | app f u ihf ihu =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ), (Exp.app f u).Syn →
        Derivable S true (.tm Γ ρ (.app f u) C ε) →
          ∃ r, infer hS Γ hΓ (.app f u) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ h ⟨d⟩
      simp only [Exp.Syn] at h
      obtain ⟨q, σ, A, B, φ, η, hc, -, hf, hu, -⟩ := d.inv_app
      obtain ⟨rf, hrf, hconv⟩ := ihf.2.1 hΓ h.1 hf
      obtain ⟨A', B', hT⟩ := conv_pi_shape rf.tyShape hconv
      rw [hT] at hconv
      obtain ⟨-, -, hAA', hBB'⟩ := Conv.pi_inj hconv
      have hA' : ∃ α, Derivable S true (.ty Γ σ A' α) := by
        have := Derivable.ty_of_tm rf.2
        rw [hT] at this
        exact Derivable.pi_dom this
      obtain ⟨ru, hru⟩ := ihu.2.2.1 hΓ hA' h.2 (Derivable.conv hu hAA'.symm hA')
      obtain ⟨r, hr, hT'⟩ := infer_app hS hΓ hrf hT hru
      exact ⟨r, hr, hT' ▸ (Conv.subst hBB' (inst1 u)).trans hc⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ h d) d
  | pair a b iha ihb =>
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, fun _ h _ => by simp [Exp.Syn] at h,
      fun hΓ hC h ⟨d⟩ => ?_, fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    simp only [Exp.Chk] at h
    obtain ⟨A, B, θ, η, hc, -, ha, hb, -⟩ := d.inv_pair
    obtain ⟨A', B', rfl⟩ := conv_sigma_shape (Exp.TyShape.of_ex hC) hc.symm
    obtain ⟨-, hAA', hBB'⟩ := Conv.sigma_inj hc
    exact check_pair hS hΓ (fun hA => iha.2.2.1 hΓ hA h.1 (Derivable.conv ha hAA' hA))
      (fun hB => ihb.2.2.1 hΓ hB h.2 (Derivable.conv hb (Conv.subst hBB' (inst1 a)) hB))
  | fst p ih =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ), (Exp.fst p).Syn →
        Derivable S true (.tm Γ ρ (.fst p) C ε) →
          ∃ r, infer hS Γ hΓ (.fst p) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ h ⟨d⟩
      simp only [Exp.Syn] at h
      obtain ⟨A, B, hc, hp, -⟩ := d.inv_fst
      obtain ⟨rp, hrp, hconv⟩ := ih.2.1 hΓ h hp
      obtain ⟨A', B', hT⟩ := conv_sigma_shape rp.tyShape hconv
      rw [hT] at hconv
      obtain ⟨-, hAA', -⟩ := Conv.sigma_inj hconv
      obtain ⟨r, hr, hT'⟩ := infer_fst hS hΓ hrp (by rw [hT, rp.role hp])
      exact ⟨r, hr, hT' ▸ hAA'.trans hc⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ h d) d
  | snd p ih =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ), (Exp.snd p).Syn →
        Derivable S true (.tm Γ ρ (.snd p) C ε) →
          ∃ r, infer hS Γ hΓ (.snd p) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ h ⟨d⟩
      simp only [Exp.Syn] at h
      obtain ⟨A, B, hc, hp, -⟩ := d.inv_snd
      obtain ⟨rp, hrp, hconv⟩ := ih.2.1 hΓ h hp
      obtain ⟨A', B', hT⟩ := conv_sigma_shape rp.tyShape hconv
      rw [hT] at hconv
      obtain ⟨-, -, hBB'⟩ := Conv.sigma_inj hconv
      obtain ⟨r, hr, hT'⟩ := infer_snd hS hΓ hrp (by rw [hT, rp.role hp])
      exact ⟨r, hr, hT' ▸ (Conv.subst hBB' (inst1 (.fst p))).trans hc⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ h d) d
  | stamp a e o iha ihe iho =>
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, fun hΓ h ⟨d⟩ => ?_, fun hΓ hC h ⟨d⟩ => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    · simp only [Exp.Syn] at h
      obtain ⟨σ, A, θ, η, ω, -, hc, -, ha, he, ho, hs⟩ := d.inv_stamp
      have hσ := (Derivable.stamped_inner hs).2.1
      obtain ⟨ra, hra, hconv⟩ := iha.2.1 hΓ h.1 ha
      have hrole := ra.role ha
      obtain ⟨⟨σ', A', θ'⟩, ha'⟩ := ra
      simp only at hrole hconv
      subst hrole
      obtain ⟨r, hr, hT⟩ := infer_stamp hS hΓ hra hσ (fun hC => ihe.2.2.1 hΓ hC h.2.1 he)
        (fun hC => iho.2.2.1 hΓ hC h.2.2 (Derivable.conv ho
          (Conv.lift (fun X => Exp.origin X e a) (fun h => Step.origin₁ h) hconv.symm) hC))
      exact ⟨r, hr, hT ▸ (Conv.lift (fun X => Exp.stamped σ' X) (fun h => Step.stamped h)
        hconv).trans hc⟩
    · simp only [Exp.Chk] at h
      obtain ⟨σ, A, θ, η, ω, rfl, hc, -, ha, he, ho, -⟩ := d.inv_stamp
      obtain ⟨A', rfl⟩ := conv_stamped_shape (Exp.TyShape.of_ex hC) hc.symm
      obtain ⟨-, hAA'⟩ := Conv.stamped_inj hc
      exact check_stamp hS hΓ (fun hA => iha.2.2.1 hΓ hA h.1 (Derivable.conv ha hAA' hA))
        (fun hC => ihe.2.2.1 hΓ hC h.2.1 he)
        (fun hC => iho.2.2.1 hΓ hC h.2.2 (Derivable.conv ho
          (Conv.lift (fun X => Exp.origin X e a) (fun h => Step.origin₁ h) hAA') hC))
  | gate g ds s ihds ihs =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ),
        (Exp.gate g ds s).Syn → Derivable S true (.tm Γ ρ (.gate g ds s) C ε) →
          ∃ r, infer hS Γ hΓ (.gate g ds s) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ h ⟨d⟩
      simp only [Exp.Syn] at h
      obtain ⟨Δ, σ, A, B, δ, η, hg, hc, -, hds, hs, -⟩ := d.inv_gate
      obtain ⟨r, hr, hT⟩ := infer_gate hS hΓ hg (fun hΔ => ihds.2.2.2 hΓ hΔ h.1 hds)
        (fun hC => ihs.2.2.1 hΓ hC h.2 hs)
      exact ⟨r, hr, hT ▸ hc⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ h d) d
  | node g ℓ ds a e ihds iha ihe =>
    have syn : ∀ {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} (hΓ : CtxWF S Γ),
        (Exp.node g ℓ ds a e).Syn → Derivable S true (.tm Γ ρ (.node g ℓ ds a e) C ε) →
          ∃ r, infer hS Γ hΓ (.node g ℓ ds a e) = some r ∧ Conv r.1.2.1 C := by
      intro Γ ρ C ε hΓ h ⟨d⟩
      simp only [Exp.Syn] at h
      obtain ⟨Δ, σ, A, B, δ, θ, η, hg, hc, -, hds, ha, he, -⟩ := d.inv_node
      obtain ⟨r, hr, hT⟩ := infer_node hS hΓ hg (fun hΔ => ihds.2.2.2 hΓ hΔ h.1 hds)
        (fun hC => iha.2.2.1 hΓ hC h.2.1 ha) (fun hC => ihe.2.2.1 hΓ hC h.2.2 he)
      exact ⟨r, hr, hT ▸ hc⟩
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, syn, fun hΓ hC h d => ?_,
      fun _ _ h _ => by simp [Exp.SpFr] at h⟩
    exact check_of_syn hS (by simp) (by simp) (by simp) (syn hΓ h d) d
  | nil =>
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun hΓ hΔ _ ⟨d⟩ => ?_⟩
    cases d with
    | spineNil _ => exact checkSpine_nil hS hΓ
  | cons a rest iha ihrest =>
    refine ⟨fun _ h _ => by simp [Exp.TyFr] at h, fun _ h _ => by simp [Exp.Syn] at h,
      fun _ _ h _ => by simp [Exp.Chk] at h, fun hΓ hΔ h ⟨d⟩ => ?_⟩
    simp only [Exp.SpFr] at h
    cases d with
    | spineCons da drest _ =>
      exact checkSpine_cons hS hΓ (fun hA => iha.2.2.1 hΓ hA h.1 ⟨da⟩)
        (fun hΔ' => ihrest.2.2.2 hΓ hΔ' h.2 ⟨drest⟩)

/-- Type checking succeeds on every derivable judgment of the fragment. -/
theorem typeCheck_complete {Γ : Ctx} (hΓ : CtxWF S Γ) {t : Exp} {ρ : Role} {C : Exp} {ε : Eff}
    (ht : t.Chk) (hC : C.TyFr) (d : Derivable S true (.tm Γ ρ t C ε)) :
    ∃ r, typeCheck hS Γ hΓ t ρ C = some r := by
  obtain ⟨γ, hCγ⟩ := Derivable.ty_of_tm d
  obtain ⟨rC, hrC⟩ := (complete hS C).1 hΓ hC hCγ
  have hrole := rC.role hCγ
  obtain ⟨⟨ρ', γ'⟩, hC'⟩ := rC
  simp only at hrole
  subst hrole
  obtain ⟨r, hr⟩ := (complete hS t).2.2.1 hΓ ⟨γ', hC'⟩ ht d
  simp only [typeCheck, hrC, ↓reduceDIte, hr]
  exact ⟨r, rfl⟩

/-- Type checking succeeds on every derivable judgment whose term and type are
normal: normal forms lie in the fragment (`normal_fragment`). -/
theorem typeCheck_complete_normal {Γ : Ctx} (hΓ : CtxWF S Γ) {t : Exp} {ρ : Role} {C : Exp}
    {ε : Eff} (ht : Normal t) (hC : Normal C) (d : Derivable S true (.tm Γ ρ t C ε)) :
    ∃ r, typeCheck hS Γ hΓ t ρ C = some r := by
  obtain ⟨γ, hγ⟩ := Derivable.ty_of_tm d
  exact typeCheck_complete hS hΓ ((normal_fragment t).2.1 ht d) ((normal_fragment C).1 hC hγ) d

/-- `thm:decidability`, type checking: on the bidirectional fragment, whether a
term has a given role and type is decidable. -/
def decTyping {Γ : Ctx} (hΓ : CtxWF S Γ) {t : Exp} (ht : t.Chk) (ρ : Role) {C : Exp}
    (hC : C.TyFr) : Decidable (∃ ε, Derivable S true (.tm Γ ρ t C ε)) :=
  match h : typeCheck hS Γ hΓ t ρ C with
  | some ⟨ε, hd⟩ => isTrue ⟨ε, hd⟩
  | none => isFalse fun ⟨_, hd⟩ => by
      obtain ⟨r, hr⟩ := typeCheck_complete hS hΓ ht hC hd
      rw [h] at hr
      cases hr

/-- `thm:decidability`, type formation: on the fragment, whether an expression
is a well-formed type is decidable. -/
def decFormed {Γ : Ctx} (hΓ : CtxWF S Γ) {A : Exp} (hA : A.TyFr) :
    Decidable (∃ ρ α, Derivable S true (.ty Γ ρ A α)) :=
  match h : inferTy hS Γ hΓ A with
  | some ⟨(ρ, α), hd⟩ => isTrue ⟨ρ, α, hd⟩
  | none => isFalse fun ⟨_, _, hd⟩ => by
      obtain ⟨r, hr⟩ := (complete hS A).1 hΓ hA hd
      rw [h] at hr
      cases hr

/-- A pair has no synthesized type. -/
theorem infer_pair {Γ : Ctx} (hΓ : CtxWF S Γ) (a b : Exp) : infer hS Γ hΓ (.pair a b) = none := by
  rw [infer] <;> simp

/-- Outside the fragment the procedure is incomplete: the first projection of a
pair is never checked, although it may be derivable (`Book.Chess.checker_incomplete`). -/
theorem check_fst_pair {Γ : Ctx} (hΓ : CtxWF S Γ) (a b : Exp) {ρ : Role} {C : Exp}
    (hC : ∃ γ, Derivable S true (.ty Γ ρ C γ)) :
    check hS Γ hΓ (.fst (.pair a b)) ρ C hC = none := by
  have h : infer hS Γ hΓ (.fst (.pair a b)) = none := by
    rw [infer, infer_pair]
  rw [check] <;> simp [h]

end Complete

end Artform.Roles.Calculus
