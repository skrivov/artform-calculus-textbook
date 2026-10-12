import ArtformRoles.Calculus.Signature
import ArtformRoles.Calculus.Reduction

/-!
# The judgments of the calculus

Sections 6.5–6.6 and Appendix A of the paper.

`Deriv S acc j` is the type of derivations of the judgment `j` over the
signature `S`. With `acc = true` they are the *accepted* derivations of the
paper: every formation and typing conclusion carries the side condition that
its effect is policy valid (rule Accept), and every premise is accepted. With
`acc = false` they are the *raw* derivations `⊢⁰`, with the validity side
conditions erased; the binder check `D(σ, ρ) ≤ q` of rule Ty-Pi is part of the
rule and stays.

The judgments are
* `ty Γ ρ A ε`: `S; Γ ⊢_ρ A type ▷ ε`;
* `tm Γ ρ t A ε`: `S; Γ ⊢_ρ t : A ▷ ε`;
* `spine Γ ts Δ ε`: `S; Γ ⊢ t⃗ : Δ ▷ ε` (rule Spine);
* `tel Γ Δ ε`: `S; Γ ⊢ Δ tel ▷ ε` (rules Tel-Empty and Tel-Extend, read from
  the first entry; the effect is the same).

Each rule states its effect, and its displayed result type where the paper
computes one, as an equation, so that inversion never has to match a computed
index. Every term rule has an accepted formation derivation of its displayed
type as a premise (the implicit premise of Appendix A). Derivations are data,
so that the paths of a derivation can be read off it (§8.1).

`SigWF S` is signature formation (rules Sig-Empty, Sig-Family, Sig-Primitive,
Sig-Certificate, Sig-Attest and Sig-Gate) and `CtxWF S Γ` context formation
(Ctx-Empty, Ctx-Extend).
-/

namespace Artform.Roles.Calculus

open Exp

/-- The judgment forms of the calculus. -/
inductive Judg
  | ty (Γ : Ctx) (ρ : Role) (A : Exp) (ε : Eff)
  | tm (Γ : Ctx) (ρ : Role) (t A : Exp) (ε : Eff)
  | spine (Γ : Ctx) (ts : Exp) (Δ : Tel) (ε : Eff)
  | tel (Γ : Ctx) (Δ : Tel) (ε : Eff)

/-- Derivations of the judgments of `RATT` over the signature `S`; accepted when
`acc` holds and raw otherwise. -/
inductive Deriv (S : Sig) (acc : Bool) : Judg → Type
  /-- Ty-Fam. -/
  | tyFam {Γ a args Δ ρ δ ε} (hS : S.family? a = some (Δ, ρ))
      (dargs : Deriv S acc (.spine Γ args Δ δ))
      (hε : ε = Eff.unit (.decl a 0) ⊓ δ) (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.ty Γ ρ (.fam a args) ε)
  /-- Ty-Event. -/
  | tyEvent {Γ ε} (hε : ε = ⊤) : Deriv S acc (.ty Γ .witness .event ε)
  /-- Ty-Origin. -/
  | tyOrigin {Γ σ A e t α η θ ε} (dA : Deriv S acc (.ty Γ σ A α))
      (de : Deriv S acc (.tm Γ .witness e .event η)) (dt : Deriv S acc (.tm Γ σ t A θ))
      (hε : ε = α ⊓ η ⊓ θ) (hv : acc → Valid S Γ .witness ε) :
      Deriv S acc (.ty Γ .witness (.origin A e t) ε)
  /-- Ty-Stamp. -/
  | tyStamped {Γ σ A α ε} (dA : Deriv S acc (.ty Γ σ A α)) (hσ : σ ≠ .rendering)
      (hε : ε = α) (hv : acc → Valid S Γ .witness ε) :
      Deriv S acc (.ty Γ .witness (.stamped σ A) ε)
  /-- Ty-Pi, with the binder check `D(σ, ρ) ≤ q`. -/
  | tyPi {Γ q σ ρ A B α β ε} (dA : Deriv S acc (.ty Γ σ A α))
      (dB : Deriv S acc (.ty ((σ, A) :: Γ) ρ B β)) (hq : demand σ ρ ≤ q)
      (hε : ε = Eff.scale q α ⊓ β.unbind) (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.ty Γ ρ (.pi q σ A B) ε)
  /-- Ty-Sigma: dependent sums are homogeneous in role. -/
  | tySigma {Γ ρ A B α β ε} (dA : Deriv S acc (.ty Γ ρ A α))
      (dB : Deriv S acc (.ty ((ρ, A) :: Γ) ρ B β))
      (hε : ε = α ⊓ β.unbind) (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.ty Γ ρ (.sigma ρ A B) ε)
  /-- Var. -/
  | var {Γ i ρ A C γ ε} (hΓ : Γ[i]? = some (ρ, A)) (hC : C = A.ren (· + (i + 1)))
      (dC : Deriv S acc (.ty Γ ρ C γ)) (hε : ε = Eff.unit (.var i))
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.var i) C ε)
  /-- Const. -/
  | const {Γ i k ρ A γ ε} (hc : S.const? i k = some (ρ, A))
      (dA : Deriv S acc (.ty Γ ρ A γ)) (hε : ε = Eff.unit (.decl i k))
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.const i k) A ε)
  /-- Lam: the declared grade is a lower bound of the body's use of its parameter. -/
  | lam {Γ q σ ρ A B t α θ γ ε} (dA : Deriv S acc (.ty Γ σ A α))
      (dt : Deriv S acc (.tm ((σ, A) :: Γ) ρ t B θ)) (hq : q ≤ θ (.var 0))
      (dC : Deriv S acc (.ty Γ ρ (.pi q σ A B) γ)) (hε : ε = θ.unbind)
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.lam q σ A t) (.pi q σ A B) ε)
  /-- App: the argument's paths are prefixed by the latent grade. -/
  | app {Γ q σ ρ A B f u C φ η γ ε} (df : Deriv S acc (.tm Γ ρ f (.pi q σ A B) φ))
      (du : Deriv S acc (.tm Γ σ u A η)) (hC : C = B.inst u)
      (dC : Deriv S acc (.ty Γ ρ C γ)) (hε : ε = φ ⊓ Eff.scale q η)
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.app f u) C ε)
  /-- Pair. -/
  | pair {Γ ρ A B t u θ η γ ε} (dt : Deriv S acc (.tm Γ ρ t A θ))
      (du : Deriv S acc (.tm Γ ρ u (B.inst t) η))
      (dC : Deriv S acc (.ty Γ ρ (.sigma ρ A B) γ)) (hε : ε = θ ⊓ η)
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.pair t u) (.sigma ρ A B) ε)
  /-- Fst. -/
  | fst {Γ ρ A B p π γ} (dp : Deriv S acc (.tm Γ ρ p (.sigma ρ A B) π))
      (dA : Deriv S acc (.ty Γ ρ A γ)) (hv : acc → Valid S Γ ρ π) :
      Deriv S acc (.tm Γ ρ (.fst p) A π)
  /-- Snd. -/
  | snd {Γ ρ A B C p π γ} (dp : Deriv S acc (.tm Γ ρ p (.sigma ρ A B) π))
      (hC : C = B.inst (.fst p)) (dC : Deriv S acc (.ty Γ ρ C γ))
      (hv : acc → Valid S Γ ρ π) :
      Deriv S acc (.tm Γ ρ (.snd p) C π)
  /-- Stamp: a sealed triple, with no projection. -/
  | stamp {Γ σ A t e o θ η ω γ ε} (dt : Deriv S acc (.tm Γ σ t A θ))
      (de : Deriv S acc (.tm Γ .witness e .event η))
      (dorg : Deriv S acc (.tm Γ .witness o (.origin A e t) ω))
      (dC : Deriv S acc (.ty Γ .witness (.stamped σ A) γ)) (hε : ε = θ ⊓ η ⊓ ω)
      (hv : acc → Valid S Γ .witness ε) :
      Deriv S acc (.tm Γ .witness (.stamp t e o) (.stamped σ A) ε)
  /-- Gate: the credential edge has grade `1`. -/
  | gate {Γ g ds s Δ σ A ρ B C δ η γ ε} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
      (dds : Deriv S acc (.spine Γ ds Δ δ))
      (dst : Deriv S acc (.tm Γ .witness s (.stamped σ (instType ds Δ A)) η))
      (hC : C = instType ds Δ B) (dC : Deriv S acc (.ty Γ ρ C γ))
      (hε : ε = Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η)
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.gate g ds s) C ε)
  /-- Node: the internal record, with grade-`1` payload and event edges. -/
  | node {Γ g ℓ ds t e Δ σ A ρ B C δ θ η γ ε} (hg : S.gate? g = some (Δ, σ, A, ρ, B))
      (dds : Deriv S acc (.spine Γ ds Δ δ))
      (dt : Deriv S acc (.tm Γ σ t (instType ds Δ A) θ))
      (de : Deriv S acc (.tm Γ .witness e .event η))
      (hC : C = instType ds Δ B) (dC : Deriv S acc (.ty Γ ρ C γ))
      (hε : ε = Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η))
      (hv : acc → Valid S Γ ρ ε) :
      Deriv S acc (.tm Γ ρ (.node g ℓ ds t e) C ε)
  /-- Conv: conversion changes only the displayed type. -/
  | conv {Γ ρ t A B θ γ} (dt : Deriv S acc (.tm Γ ρ t A θ)) (hAB : Conv A B)
      (dB : Deriv S acc (.ty Γ ρ B γ)) :
      Deriv S acc (.tm Γ ρ t B θ)
  /-- Spine, empty. -/
  | spineNil {Γ ε} (hε : ε = ⊤) : Deriv S acc (.spine Γ .nil [] ε)
  /-- Spine, one more argument: later entries are instantiated by it. -/
  | spineCons {Γ ρ t ts A Δ ε₁ ε₂ ε} (dt : Deriv S acc (.tm Γ ρ t A ε₁))
      (dts : Deriv S acc (.spine Γ ts (Tel.inst t Δ) ε₂)) (hε : ε = ε₁ ⊓ ε₂) :
      Deriv S acc (.spine Γ (.cons t ts) ((ρ, A) :: Δ) ε)
  /-- Tel-Empty. -/
  | telNil {Γ ε} (hε : ε = ⊤) : Deriv S acc (.tel Γ [] ε)
  /-- Tel-Extend, read from the first entry. -/
  | telCons {Γ ρ A Δ α δ ε} (dA : Deriv S acc (.ty Γ ρ A α))
      (dΔ : Deriv S acc (.tel ((ρ, A) :: Γ) Δ δ)) (hε : ε = α ⊓ δ.unbind) :
      Deriv S acc (.tel Γ ((ρ, A) :: Δ) ε)

/-- A judgment is derivable. -/
abbrev Derivable (S : Sig) (acc : Bool) (j : Judg) : Prop := Nonempty (Deriv S acc j)

/-- Signature formation (Appendix A). Each entry is appended to an already
well-formed signature, whose positions it does not reuse. -/
inductive SigWF : Sig → Prop
  /-- Sig-Empty: only the built-in formers `Event`, `Origin`, `Stamped`. -/
  | nil : SigWF []
  /-- Sig-Family. -/
  | family {S Δ ρ δ} : SigWF S → Derivable S true (.tel [] Δ δ) →
      SigWF (S ++ [.family Δ ρ])
  /-- Sig-Primitive: closed, grade-free, with a declared family as result head. -/
  | prim {S ρ A α} : SigWF S → Derivable S true (.ty [] ρ A α) → A.gradefree →
      OrdinaryHead S A → SigWF (S ++ [.prim ρ A])
  /-- Sig-Certificate: one atomic bundle of payload, event and origin. -/
  | cert {S σ A α} : SigWF S → Derivable S true (.ty [] σ A α) → σ ≠ .rendering →
      A.gradefree → OrdinaryHead S A → SigWF (S ++ [.cert σ A])
  /-- Sig-Attest: an event and origin for an exact, closed, public witness-data
  term; no payload constant. -/
  | attest {S A t θ} : SigWF S → Derivable S true (.tm [] .witness t A θ) → t.IsPublic →
      A.gradefree → WData S A → SigWF (S ++ [.attest A t])
  /-- Sig-Gate: a protected, grade-free result independent of the payload,
  parameters of demand `0` into the result role, a non-rendering payload, and a
  grade-free interface: the parameter and payload types are grade-free as
  well as the result. -/
  | gate {S Δ σ A ρ B δ α β} : SigWF S → Derivable S true (.tel [] Δ δ) →
      Derivable S true (.ty Δ.reverse σ A α) → Derivable S true (.ty Δ.reverse ρ B β) →
      (ρ = .form ∨ ρ = .presentation) → σ ≠ .rendering →
      (∀ p ∈ Δ, demand p.1 ρ = .free) → demand σ ρ ≤ .gated → B.gradefree →
      (∀ p ∈ Δ, p.2.gradefree) → A.gradefree →
      SigWF (S ++ [.gate Δ σ A ρ B])

/-- Context formation (Appendix A). -/
inductive CtxWF (S : Sig) : Ctx → Prop
  /-- Ctx-Empty. -/
  | nil : SigWF S → CtxWF S []
  /-- Ctx-Extend. -/
  | cons {Γ ρ A α} : CtxWF S Γ → Derivable S true (.ty Γ ρ A α) → CtxWF S ((ρ, A) :: Γ)

end Artform.Roles.Calculus
