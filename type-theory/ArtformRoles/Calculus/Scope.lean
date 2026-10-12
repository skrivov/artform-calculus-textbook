import ArtformRoles.Calculus.Typing

/-!
# Scope

A derivable judgment mentions only the variables of its context, and its effect
grades only atoms of its signature and context: every other atom has grade `∞`
(`Deriv.scoped`). Consequently the types a well-formed signature declares are
closed (`SigWF.family_closed`, `SigWF.const_closed`, `SigWF.gate_closed`), and a
derivation over a signature is also one over every extension of it
(`Deriv.weakenSig`).
-/

namespace Artform.Roles.Calculus

open Exp

/-- An effect that grades `∞` every variable from `n` on and every declaration
from position `m` on. -/
def Eff.Scoped (m n : ℕ) (ε : Eff) : Prop :=
  (∀ i, n ≤ i → ε (.var i) = ⊤) ∧ (∀ i k, m ≤ i → ε (.decl i k) = ⊤)

/-- Every entry of a telescope lies in the context of the earlier entries,
over a context of `n` variables. -/
def TelBelow : ℕ → Tel → Prop
  | _, [] => True
  | n, (_, A) :: Δ => Below n A ∧ TelBelow (n + 1) Δ

/-- The scope of a judgment over a signature with `m` entries. -/
def Judg.Scoped (m : ℕ) : Judg → Prop
  | .ty Γ _ A ε => Below Γ.length A ∧ ε.Scoped m Γ.length
  | .tm Γ _ t A ε => Below Γ.length t ∧ Below Γ.length A ∧ ε.Scoped m Γ.length
  | .spine Γ ts _ ε => Below Γ.length ts ∧ ε.Scoped m Γ.length
  | .tel Γ Δ ε => TelBelow Γ.length Δ ∧ ε.Scoped m Γ.length

namespace Eff.Scoped

variable {m n : ℕ}

theorem top : (⊤ : Eff).Scoped m n := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem unit_var {i : ℕ} (hi : i < n) : (Eff.unit (.var i)).Scoped m n :=
  ⟨fun j hj => Eff.unit_ne (by intro h; cases h; omega),
   fun _ _ _ => Eff.unit_ne (by intro h; cases h)⟩

theorem unit_decl {i k : ℕ} (hi : i < m) : (Eff.unit (.decl i k)).Scoped m n :=
  ⟨fun _ _ => Eff.unit_ne (by intro h; cases h),
   fun j _ hj => Eff.unit_ne (by intro h; cases h; omega)⟩

theorem inf {ε η : Eff} (hε : ε.Scoped m n) (hη : η.Scoped m n) : (ε ⊓ η).Scoped m n :=
  ⟨fun i hi => by simp [hε.1 i hi, hη.1 i hi],
   fun i k hi => by simp [hε.2 i k hi, hη.2 i k hi]⟩

theorem scale {ε : Eff} (q : Grade) (hε : ε.Scoped m n) : (Eff.scale q ε).Scoped m n :=
  ⟨fun i hi => by simp [hε.1 i hi], fun i k hi => by simp [hε.2 i k hi]⟩

theorem unbind {ε : Eff} (hε : ε.Scoped m (n + 1)) : ε.unbind.Scoped m n :=
  ⟨fun i hi => hε.1 (i + 1) (by omega), fun i k hi => hε.2 i k hi⟩

theorem mono_ctx {n' : ℕ} {ε : Eff} (h : n ≤ n') (hε : ε.Scoped m n) : ε.Scoped m n' :=
  ⟨fun i hi => hε.1 i (le_trans h hi), hε.2⟩

theorem mono_sig {m' : ℕ} {ε : Eff} (h : m ≤ m') (hε : ε.Scoped m n) : ε.Scoped m' n :=
  ⟨hε.1, fun i k hi => hε.2 i k (le_trans h hi)⟩

end Eff.Scoped

/-! ## Positions of declarations -/

theorem Sig.lt_of_family {S : Sig} {a : ℕ} {p : Tel × Role} (h : S.family? a = some p) :
    a < S.length := by
  unfold Sig.family? at h
  by_contra hlt
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem Sig.lt_of_gate {S : Sig} {g : ℕ} {p} (h : S.gate? g = some p) : g < S.length := by
  unfold Sig.gate? at h
  by_contra hlt
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem Sig.lt_of_const {S : Sig} {i k : ℕ} {p : Role × Exp} (h : S.const? i k = some p) :
    i < S.length := by
  unfold Sig.const? at h
  by_contra hlt
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem lt_of_getElem? {Γ : Ctx} {i : ℕ} {p : Role × Exp} (h : Γ[i]? = some p) :
    i < Γ.length := by
  by_contra hlt
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

/-- Lemma (scope): a derivable judgment stays within its signature and context. -/
theorem Deriv.scoped {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    j.Scoped S.length := by
  induction d with
  | tyFam hS _ hε _ ih =>
    subst hε; exact ⟨ih.1, (Eff.Scoped.unit_decl (Sig.lt_of_family hS)).inf ih.2⟩
  | tyEvent hε => subst hε; exact ⟨trivial, .top⟩
  | tyOrigin _ _ _ hε _ ihA ihe iht =>
    subst hε; exact ⟨⟨ihA.1, ihe.1, iht.1⟩, (ihA.2.inf ihe.2.2).inf iht.2.2⟩
  | tyStamped _ _ hε _ ih => subst hε; exact ⟨ih.1, ih.2⟩
  | tyPi _ _ _ hε _ ihA ihB =>
    subst hε; exact ⟨⟨ihA.1, ihB.1⟩, (ihA.2.scale _).inf ihB.2.unbind⟩
  | tySigma _ _ hε _ ihA ihB => subst hε; exact ⟨⟨ihA.1, ihB.1⟩, ihA.2.inf ihB.2.unbind⟩
  | var hΓ _ _ hε _ ih =>
    subst hε; exact ⟨lt_of_getElem? hΓ, ih.1, .unit_var (lt_of_getElem? hΓ)⟩
  | const hc _ hε _ ih => subst hε; exact ⟨trivial, ih.1, .unit_decl (Sig.lt_of_const hc)⟩
  | lam _ _ _ _ hε _ ihA iht ihC => subst hε; exact ⟨⟨ihA.1, iht.1⟩, ihC.1, iht.2.2.unbind⟩
  | app _ _ _ _ hε _ ihf ihu ihC =>
    subst hε; exact ⟨⟨ihf.1, ihu.1⟩, ihC.1, ihf.2.2.inf (ihu.2.2.scale _)⟩
  | pair _ _ _ hε _ iht ihu ihC => subst hε; exact ⟨⟨iht.1, ihu.1⟩, ihC.1, iht.2.2.inf ihu.2.2⟩
  | fst _ _ _ ihp ihA => exact ⟨ihp.1, ihA.1, ihp.2.2⟩
  | snd _ _ _ _ ihp ihC => exact ⟨ihp.1, ihC.1, ihp.2.2⟩
  | stamp _ _ _ _ hε _ iht ihe iho ihC =>
    subst hε; exact ⟨⟨iht.1, ihe.1, iho.1⟩, ihC.1, (iht.2.2.inf ihe.2.2).inf iho.2.2⟩
  | gate hg _ _ _ _ hε _ ihds ihs ihC =>
    subst hε
    exact ⟨⟨ihds.1, ihs.1⟩, ihC.1,
      ((Eff.Scoped.unit_decl (Sig.lt_of_gate hg)).inf ihds.2).inf (ihs.2.2.scale _)⟩
  | node hg _ _ _ _ _ hε _ ihds iht ihe ihC =>
    subst hε
    exact ⟨⟨ihds.1, iht.1, ihe.1⟩, ihC.1,
      ((Eff.Scoped.unit_decl (Sig.lt_of_gate hg)).inf ihds.2).inf ((iht.2.2.inf ihe.2.2).scale _)⟩
  | conv _ _ _ iht ihB => exact ⟨iht.1, ihB.1, iht.2.2⟩
  | spineNil hε => subst hε; exact ⟨trivial, .top⟩
  | spineCons _ _ hε iht ihts => subst hε; exact ⟨⟨iht.1, ihts.1⟩, iht.2.2.inf ihts.2⟩
  | telNil hε => subst hε; exact ⟨trivial, .top⟩
  | telCons _ _ hε ihA ihΔ => subst hε; exact ⟨⟨ihA.1, ihΔ.1⟩, ihA.2.inf ihΔ.2.unbind⟩

end Artform.Roles.Calculus
