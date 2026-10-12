import ArtformRoles.Calculus.Erasure

/-!
# Acceptance is local

Over a well-formed signature, the policy-validity side condition of every rule
except Ty-Origin over a rendering type follows from the validity of the premises
and from the signature rules: path closure carries a premise's validity at its
role into the conclusion's role through the grade on its edge, a family's and a
gate's parameters have demand `0` into the result role (Sig-Family, Sig-Gate),
and a credential or payload has demand at most `1` into a gate's result.

The constructors `Deriv.mkVar`, `Deriv.mkApp`, … build accepted derivations with
the effect that each rule computes, discharging validity in this way. They are
used to write the book's examples in the calculus. `mkTyFamOf`, `mkGateOf` and
`mkNodeOf` take as hypotheses the conditions of the signature rules that they
use, so that they also apply over signatures formed under the earlier gate rule
of Remark 10.4.
-/

namespace Artform.Roles.Calculus

open Exp

theorem Valid.top {S : Sig} {Γ : Ctx} {ρ : Role} : Valid S Γ ρ ⊤ := fun _ _ _ => le_top

/-- Path closure for effects: an effect valid at `σ`, scaled by a grade at least
`D(σ, ρ)`, is valid at `ρ`. -/
theorem Valid.scale_of_demand {S : Sig} {Γ : Ctx} {σ ρ : Role} {ε : Eff} {q : Grade}
    (hv : Valid S Γ σ ε) (hq : demand σ ρ ≤ q) : Valid S Γ ρ (Eff.scale q ε) := by
  intro z r hz
  have h₁ : demand r ρ ≤ demand r σ ⊔ demand σ ρ := by
    have := demand_pathClosed r σ ρ
    rwa [Grade.seq_eq_sup] at this
  calc demand r ρ ≤ demand r σ ⊔ demand σ ρ := h₁
    _ ≤ ε z ⊔ q := sup_le_sup (hv z r hz) hq
    _ = Eff.scale q ε z := sup_comm _ _

theorem valid_unit_decl {S : Sig} {Γ : Ctx} {i k : ℕ} {r : Role}
    (h : S.declRole? i k = some r) : Valid S Γ r (Eff.unit (.decl i k)) := by
  intro z r' hz
  by_cases hz' : z = .decl i k
  · subst hz'
    simp only [roleOf, h, Option.some.injEq] at hz
    subst hz
    rw [demand_self]; exact bot_le
  · simp [Eff.unit, hz']

theorem Sig.declRole_family {S : Sig} {a : ℕ} {Δ : Tel} {ρ : Role}
    (h : S.family? a = some (Δ, ρ)) : S.declRole? a 0 = some ρ := by
  unfold Sig.family? at h
  unfold Sig.declRole?
  split at h <;> simp_all

theorem Sig.declRole_gate {S : Sig} {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) : S.declRole? g 0 = some ρ := by
  unfold Sig.gate? at h
  unfold Sig.declRole?
  split at h <;> simp_all

theorem Sig.declRole_const {S : Sig} {i k : ℕ} {ρ : Role} {A : Exp}
    (h : S.const? i k = some (ρ, A)) : S.declRole? i k = some ρ := by
  unfold Sig.declRole?
  have hc := h
  unfold Sig.const? at hc
  split
  · next Δ ρ' he => rw [he] at hc; simp at hc
  · next Δ σ A' ρ' B he => rw [he] at hc; simp at hc
  · rw [h]; rfl

/-- The effect of an argument list is valid at every role into which all its
telescope's roles have demand `0`. -/
theorem Deriv.spine_valid {S : Sig} {Γ : Ctx} {ts : Exp} {Δ : Tel} {δ : Eff}
    (d : Deriv S true (.spine Γ ts Δ δ)) {ρ : Role} (h : ∀ p ∈ Δ, demand p.1 ρ = .free) :
    Valid S Γ ρ δ := by
  generalize hj : Judg.spine Γ ts Δ δ = j at d
  induction d generalizing ts Δ δ with
  | spineNil hε => cases hj; rw [hε]; exact Valid.top
  | @spineCons Γ' ρ' t ts' A Δ' ε₁ ε₂ ε dt dts hε _ ihts =>
    cases hj
    rw [hε]
    refine Valid.inf ?_ (ihts (fun p hp => ?_) rfl)
    · have := dt.valid_tm.scale_of_demand (le_of_eq (h (ρ', A) (List.mem_cons_self ..)))
      rwa [← Grade.bot_eq, Eff.scale_free] at this
    · obtain ⟨q, hq, k, rfl⟩ := Tel.mem_subst hp
      exact h q (List.mem_cons_of_mem _ hq)
  | _ => cases hj

namespace Deriv

variable {S : Sig}

/-- Ty-Fam, accepted, for a family whose telescope has demand `0` into its role. -/
def mkTyFamOf {Γ : Ctx} {a : ℕ} {args : Exp} {Δ : Tel} {ρ : Role} {δ : Eff}
    (h : S.family? a = some (Δ, ρ)) (hΔ : ∀ p ∈ Δ, demand p.1 ρ = .free)
    (dargs : Deriv S true (.spine Γ args Δ δ)) :
    Deriv S true (.ty Γ ρ (.fam a args) (Eff.unit (.decl a 0) ⊓ δ)) :=
  .tyFam h dargs rfl fun _ =>
    (valid_unit_decl (Sig.declRole_family h)).inf (dargs.spine_valid hΔ)

/-- Ty-Fam, accepted. -/
def mkTyFam (hS : SigWF S) {Γ : Ctx} {a : ℕ} {args : Exp} {Δ : Tel} {ρ : Role} {δ : Eff}
    (h : S.family? a = some (Δ, ρ)) (dargs : Deriv S true (.spine Γ args Δ δ)) :
    Deriv S true (.ty Γ ρ (.fam a args) (Eff.unit (.decl a 0) ⊓ δ)) :=
  mkTyFamOf h (hS.family_demand h) dargs

/-- Ty-Event, accepted. -/
def mkTyEvent {Γ : Ctx} : Deriv S true (.ty Γ .witness .event ⊤) := .tyEvent rfl

/-- Ty-Origin over a non-rendering type, accepted. -/
def mkTyOrigin {Γ : Ctx} {σ : Role} {A e t : Exp} {α η θ : Eff} (hσ : σ ≠ .rendering)
    (dA : Deriv S true (.ty Γ σ A α)) (de : Deriv S true (.tm Γ .witness e .event η))
    (dt : Deriv S true (.tm Γ σ t A θ)) :
    Deriv S true (.ty Γ .witness (.origin A e t) (α ⊓ η ⊓ θ)) :=
  .tyOrigin dA de dt rfl fun _ =>
    ((dA.valid_ty.toWitness hσ).inf de.valid_tm).inf (dt.valid_tm.toWitness hσ)

/-- Ty-Stamp, accepted. -/
def mkTyStamped {Γ : Ctx} {σ : Role} {A : Exp} {α : Eff} (dA : Deriv S true (.ty Γ σ A α))
    (hσ : σ ≠ .rendering) : Deriv S true (.ty Γ .witness (.stamped σ A) α) :=
  .tyStamped dA hσ rfl fun _ => dA.valid_ty.toWitness hσ

/-- Ty-Pi, accepted. -/
def mkTyPi {Γ : Ctx} {q : Grade} {σ ρ : Role} {A B : Exp} {α β : Eff}
    (dA : Deriv S true (.ty Γ σ A α)) (dB : Deriv S true (.ty ((σ, A) :: Γ) ρ B β))
    (hq : demand σ ρ ≤ q) :
    Deriv S true (.ty Γ ρ (.pi q σ A B) (Eff.scale q α ⊓ β.unbind)) :=
  .tyPi dA dB hq rfl fun _ => (dA.valid_ty.scale_of_demand hq).inf dB.valid_ty.unbind

/-- Ty-Sigma, accepted. -/
def mkTySigma {Γ : Ctx} {ρ : Role} {A B : Exp} {α β : Eff}
    (dA : Deriv S true (.ty Γ ρ A α)) (dB : Deriv S true (.ty ((ρ, A) :: Γ) ρ B β)) :
    Deriv S true (.ty Γ ρ (.sigma ρ A B) (α ⊓ β.unbind)) :=
  .tySigma dA dB rfl fun _ => dA.valid_ty.inf dB.valid_ty.unbind

/-- Var, accepted. -/
def mkVar {Γ : Ctx} {i : ℕ} {ρ : Role} {A : Exp} {γ : Eff} (hΓ : Γ[i]? = some (ρ, A))
    (dC : Deriv S true (.ty Γ ρ (A.ren (· + (i + 1))) γ)) :
    Deriv S true (.tm Γ ρ (.var i) (A.ren (· + (i + 1))) (Eff.unit (.var i))) :=
  .var hΓ rfl dC rfl fun _ => valid_unit_var (by simp [roleOf, hΓ])

/-- Const, accepted. -/
def mkConst {Γ : Ctx} {i k : ℕ} {ρ : Role} {A : Exp} {γ : Eff}
    (hc : S.const? i k = some (ρ, A)) (dA : Deriv S true (.ty Γ ρ A γ)) :
    Deriv S true (.tm Γ ρ (.const i k) A (Eff.unit (.decl i k))) :=
  .const hc dA rfl fun _ => valid_unit_decl (Sig.declRole_const hc)

/-- Lam, accepted. -/
def mkLam {Γ : Ctx} {q : Grade} {σ ρ : Role} {A B t : Exp} {α θ γ : Eff}
    (dA : Deriv S true (.ty Γ σ A α)) (dt : Deriv S true (.tm ((σ, A) :: Γ) ρ t B θ))
    (hq : q ≤ θ (.var 0)) (dC : Deriv S true (.ty Γ ρ (.pi q σ A B) γ)) :
    Deriv S true (.tm Γ ρ (.lam q σ A t) (.pi q σ A B) θ.unbind) :=
  .lam dA dt hq dC rfl fun _ => dt.valid_tm.unbind

/-- App, accepted. -/
def mkApp {Γ : Ctx} {q : Grade} {σ ρ : Role} {A B f u : Exp} {φ η γ : Eff}
    (df : Deriv S true (.tm Γ ρ f (.pi q σ A B) φ)) (du : Deriv S true (.tm Γ σ u A η))
    (dC : Deriv S true (.ty Γ ρ (B.inst u) γ)) :
    Deriv S true (.tm Γ ρ (.app f u) (B.inst u) (φ ⊓ Eff.scale q η)) :=
  .app df du rfl dC rfl fun _ => df.valid_tm.inf (du.valid_tm.scale_of_demand (by
    obtain ⟨γ', ⟨dpi⟩⟩ := df.tm_ty
    exact dpi.tyPi_demand))

/-- Pair, accepted. -/
def mkPair {Γ : Ctx} {ρ : Role} {A B t u : Exp} {θ η γ : Eff}
    (dt : Deriv S true (.tm Γ ρ t A θ)) (du : Deriv S true (.tm Γ ρ u (B.inst t) η))
    (dC : Deriv S true (.ty Γ ρ (.sigma ρ A B) γ)) :
    Deriv S true (.tm Γ ρ (.pair t u) (.sigma ρ A B) (θ ⊓ η)) :=
  .pair dt du dC rfl fun _ => dt.valid_tm.inf du.valid_tm

/-- Fst, accepted. -/
def mkFst {Γ : Ctx} {ρ : Role} {A B p : Exp} {π γ : Eff}
    (dp : Deriv S true (.tm Γ ρ p (.sigma ρ A B) π)) (dA : Deriv S true (.ty Γ ρ A γ)) :
    Deriv S true (.tm Γ ρ (.fst p) A π) :=
  .fst dp dA fun _ => dp.valid_tm

/-- Snd, accepted. -/
def mkSnd {Γ : Ctx} {ρ : Role} {A B p : Exp} {π γ : Eff}
    (dp : Deriv S true (.tm Γ ρ p (.sigma ρ A B) π))
    (dC : Deriv S true (.ty Γ ρ (B.inst (.fst p)) γ)) :
    Deriv S true (.tm Γ ρ (.snd p) (B.inst (.fst p)) π) :=
  .snd dp rfl dC fun _ => dp.valid_tm

/-- Stamp, accepted. -/
def mkStamp {Γ : Ctx} {σ : Role} {A t e o : Exp} {θ η ω γ : Eff}
    (dt : Deriv S true (.tm Γ σ t A θ)) (de : Deriv S true (.tm Γ .witness e .event η))
    (dorg : Deriv S true (.tm Γ .witness o (.origin A e t) ω))
    (dC : Deriv S true (.ty Γ .witness (.stamped σ A) γ)) :
    Deriv S true (.tm Γ .witness (.stamp t e o) (.stamped σ A) (θ ⊓ η ⊓ ω)) :=
  .stamp dt de dorg dC rfl fun _ =>
    ((dt.valid_tm.toWitness dC.inv_tyStamped.2.1).inf de.valid_tm).inf dorg.valid_tm

theorem demand_witness_protected {ρ : Role} (hρ : ρ = .form ∨ ρ = .presentation) :
    demand .witness ρ ≤ .gated := by
  rcases hρ with rfl | rfl <;> decide

/-- Gate, accepted, for a gate with a protected result into which its
parameters have demand `0`. -/
def mkGateOf {Γ : Ctx} {g : ℕ} {ds s : Exp} {Δ : Tel} {σ : Role} {A : Exp}
    {ρ : Role} {B : Exp} {δ η γ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hρ : ρ = .form ∨ ρ = .presentation) (hΔ : ∀ p ∈ Δ, demand p.1 ρ = .free)
    (dds : Deriv S true (.spine Γ ds Δ δ))
    (dst : Deriv S true (.tm Γ .witness s (.stamped σ (instType ds Δ A)) η))
    (dC : Deriv S true (.ty Γ ρ (instType ds Δ B) γ)) :
    Deriv S true (.tm Γ ρ (.gate g ds s) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η)) :=
  .gate hg dds dst rfl dC rfl fun _ =>
    ((valid_unit_decl (Sig.declRole_gate hg)).inf (dds.spine_valid hΔ)).inf
      (dst.valid_tm.scale_of_demand (demand_witness_protected hρ))

/-- Gate, accepted. -/
def mkGate (hS : SigWF S) {Γ : Ctx} {g : ℕ} {ds s : Exp} {Δ : Tel} {σ : Role} {A : Exp}
    {ρ : Role} {B : Exp} {δ η γ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (dds : Deriv S true (.spine Γ ds Δ δ))
    (dst : Deriv S true (.tm Γ .witness s (.stamped σ (instType ds Δ A)) η))
    (dC : Deriv S true (.ty Γ ρ (instType ds Δ B) γ)) :
    Deriv S true (.tm Γ ρ (.gate g ds s) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η)) :=
  mkGateOf hg (hS.gate_cond hg).2.1 (hS.gate_cond hg).2.2.1 dds dst dC

/-- Node, accepted, for a gate with a protected result into which its parameters
have demand `0` and its payload demand at most `1`. -/
def mkNodeOf {Γ : Ctx} {g ℓ : ℕ} {ds t e : Exp} {Δ : Tel} {σ : Role} {A : Exp}
    {ρ : Role} {B : Exp} {δ θ η γ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (hρ : ρ = .form ∨ ρ = .presentation) (hΔ : ∀ p ∈ Δ, demand p.1 ρ = .free)
    (hσρ : demand σ ρ ≤ .gated)
    (dds : Deriv S true (.spine Γ ds Δ δ)) (dt : Deriv S true (.tm Γ σ t (instType ds Δ A) θ))
    (de : Deriv S true (.tm Γ .witness e .event η))
    (dC : Deriv S true (.ty Γ ρ (instType ds Δ B) γ)) :
    Deriv S true (.tm Γ ρ (.node g ℓ ds t e) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η))) :=
  .node hg dds dt de rfl dC rfl fun _ => by
    rw [Eff.scale_inf]
    exact ((valid_unit_decl (Sig.declRole_gate hg)).inf (dds.spine_valid hΔ)).inf
      ((dt.valid_tm.scale_of_demand hσρ).inf
        (de.valid_tm.scale_of_demand (demand_witness_protected hρ)))

/-- Node, accepted. -/
def mkNode (hS : SigWF S) {Γ : Ctx} {g ℓ : ℕ} {ds t e : Exp} {Δ : Tel} {σ : Role} {A : Exp}
    {ρ : Role} {B : Exp} {δ θ η γ : Eff} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
    (dds : Deriv S true (.spine Γ ds Δ δ)) (dt : Deriv S true (.tm Γ σ t (instType ds Δ A) θ))
    (de : Deriv S true (.tm Γ .witness e .event η))
    (dC : Deriv S true (.ty Γ ρ (instType ds Δ B) γ)) :
    Deriv S true (.tm Γ ρ (.node g ℓ ds t e) (instType ds Δ B)
      (Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η))) :=
  mkNodeOf hg (hS.gate_cond hg).2.1 (hS.gate_cond hg).2.2.1 (hS.gate_cond hg).2.2.2.1 dds dt de dC

/-- Spine, empty. -/
def mkSpineNil {Γ : Ctx} : Deriv S true (.spine Γ .nil [] ⊤) := .spineNil rfl

/-- Spine, one more argument. -/
def mkSpineCons {Γ : Ctx} {ρ : Role} {t ts A : Exp} {Δ : Tel} {ε₁ ε₂ : Eff}
    (dt : Deriv S true (.tm Γ ρ t A ε₁)) (dts : Deriv S true (.spine Γ ts (Tel.inst t Δ) ε₂)) :
    Deriv S true (.spine Γ (.cons t ts) ((ρ, A) :: Δ) (ε₁ ⊓ ε₂)) :=
  .spineCons dt dts rfl

/-- Tel-Empty. -/
def mkTelNil {Γ : Ctx} : Deriv S true (.tel Γ [] ⊤) := .telNil rfl

/-- Tel-Extend. -/
def mkTelCons {Γ : Ctx} {ρ : Role} {A : Exp} {Δ : Tel} {α δ : Eff}
    (dA : Deriv S true (.ty Γ ρ A α)) (dΔ : Deriv S true (.tel ((ρ, A) :: Γ) Δ δ)) :
    Deriv S true (.tel Γ ((ρ, A) :: Δ) (α ⊓ δ.unbind)) :=
  .telCons dA dΔ rfl

end Deriv

end Artform.Roles.Calculus
