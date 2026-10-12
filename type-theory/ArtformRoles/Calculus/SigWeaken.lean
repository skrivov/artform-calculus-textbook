import ArtformRoles.Calculus.TelFacts

/-!
# Weakening the signature, and the declared telescopes

* `Deriv.weakenSig`: a derivation over `S` is a derivation over `S ++ M`.
  Validity transfers because an effect over `S` grades the declarations of `M`
  as `∞`.
* `SigWF.prefix`: a prefix of a well-formed signature is well formed.
* `SigWF.family_tel`, `SigWF.gate_tel`: the telescope of a declared family or
  gate, and a gate's telescope extended by its payload or result type, are well
  formed in every context.
-/

namespace Artform.Roles.Calculus

open Exp

theorem Valid.mono {S : Sig} {Γ : Ctx} {ρ : Role} {ε ε' : Eff} (hv : Valid S Γ ρ ε)
    (h : ε ≤ ε') : Valid S Γ ρ ε' :=
  fun z r hz => le_trans (hv z r hz) (h z)

theorem Valid.weakenSig {S M : Sig} {Γ : Ctx} {ρ : Role} {ε : Eff} (hv : Valid S Γ ρ ε)
    (hs : ε.Scoped S.length Γ.length) : Valid (S ++ M) Γ ρ ε := by
  intro z r hz
  cases z with
  | var i => exact hv (.var i) r hz
  | decl i k =>
    by_cases hi : i < S.length
    · simp only [roleOf, Sig.declRole?_append_lt hi] at hz
      exact hv (.decl i k) r hz
    · rw [hs.2 i k (by omega)]; exact le_top

/-- A derivation over a signature is a derivation over every extension. -/
noncomputable def Deriv.weakenSig {S : Sig} (M : Sig) {acc : Bool} {j : Judg}
    (d : Deriv S acc j) : Deriv (S ++ M) acc j := by
  induction d with
  | tyFam hS dargs hε hv ih =>
    exact .tyFam (Sig.family?_append hS) ih hε
      (fun h => (hv h).weakenSig (Deriv.tyFam hS dargs hε hv).scoped.2)
  | tyEvent hε => exact .tyEvent hε
  | tyOrigin dA de dt hε hv ihA ihe iht =>
    exact .tyOrigin ihA ihe iht hε
      (fun h => (hv h).weakenSig (Deriv.tyOrigin dA de dt hε hv).scoped.2)
  | tyStamped dA hσ hε hv ih =>
    exact .tyStamped ih hσ hε (fun h => (hv h).weakenSig (Deriv.tyStamped dA hσ hε hv).scoped.2)
  | tyPi dA dB hq hε hv ihA ihB =>
    exact .tyPi ihA ihB hq hε (fun h => (hv h).weakenSig (Deriv.tyPi dA dB hq hε hv).scoped.2)
  | tySigma dA dB hε hv ihA ihB =>
    exact .tySigma ihA ihB hε (fun h => (hv h).weakenSig (Deriv.tySigma dA dB hε hv).scoped.2)
  | var hΓ hC dC hε hv ih =>
    exact .var hΓ hC ih hε (fun h => (hv h).weakenSig (Deriv.var hΓ hC dC hε hv).scoped.2.2)
  | const hc dA hε hv ih =>
    exact .const (Sig.const?_append hc) ih hε
      (fun h => (hv h).weakenSig (Deriv.const hc dA hε hv).scoped.2.2)
  | lam dA dt hq dC hε hv ihA iht ihC =>
    exact .lam ihA iht hq ihC hε
      (fun h => (hv h).weakenSig (Deriv.lam dA dt hq dC hε hv).scoped.2.2)
  | app df du hC dC hε hv ihf ihu ihC =>
    exact .app ihf ihu hC ihC hε
      (fun h => (hv h).weakenSig (Deriv.app df du hC dC hε hv).scoped.2.2)
  | pair dt du dC hε hv iht ihu ihC =>
    exact .pair iht ihu ihC hε
      (fun h => (hv h).weakenSig (Deriv.pair dt du dC hε hv).scoped.2.2)
  | fst dp dA hv ihp ihA =>
    exact .fst ihp ihA (fun h => (hv h).weakenSig (Deriv.fst dp dA hv).scoped.2.2)
  | snd dp hC dC hv ihp ihC =>
    exact .snd ihp hC ihC (fun h => (hv h).weakenSig (Deriv.snd dp hC dC hv).scoped.2.2)
  | stamp dt de dorg dC hε hv iht ihe iho ihC =>
    exact .stamp iht ihe iho ihC hε
      (fun h => (hv h).weakenSig (Deriv.stamp dt de dorg dC hε hv).scoped.2.2)
  | gate hg dds dst hC dC hε hv ihds ihs ihC =>
    exact .gate (Sig.gate?_append hg) ihds ihs hC ihC hε
      (fun h => (hv h).weakenSig (Deriv.gate hg dds dst hC dC hε hv).scoped.2.2)
  | @node Γ g ℓ ds t e Δ σ A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    exact .node (Sig.gate?_append hg) ihds iht ihe hC ihC hε
      (fun h => (hv h).weakenSig (Deriv.node (ℓ := ℓ) hg dds dt de hC dC hε hv).scoped.2.2)
  | conv _ hAB _ iht ihB => exact .conv iht hAB ihB
  | spineNil hε => exact .spineNil hε
  | spineCons _ _ hε iht ihts => exact .spineCons iht ihts hε
  | telNil hε => exact .telNil hε
  | telCons _ _ hε ihA ihΔ => exact .telCons ihA ihΔ hε

theorem Derivable.weakenSig {S : Sig} (M : Sig) {acc : Bool} {j : Judg}
    (d : Derivable S acc j) : Derivable (S ++ M) acc j :=
  let ⟨d⟩ := d; ⟨d.weakenSig M⟩

/-- Removing the last entry of a well-formed signature. -/
theorem SigWF.init {S : Sig} {e : Entry} (h : SigWF (S ++ [e])) : SigWF S := by
  generalize hT : S ++ [e] = T at h
  cases h with
  | nil => simp at hT
  | family hS _ => obtain ⟨rfl, -⟩ := List.append_inj' hT rfl; exact hS
  | prim hS _ _ _ => obtain ⟨rfl, -⟩ := List.append_inj' hT rfl; exact hS
  | cert hS _ _ _ _ => obtain ⟨rfl, -⟩ := List.append_inj' hT rfl; exact hS
  | attest hS _ _ _ _ => obtain ⟨rfl, -⟩ := List.append_inj' hT rfl; exact hS
  | gate hS _ _ _ _ _ _ _ _ => obtain ⟨rfl, -⟩ := List.append_inj' hT rfl; exact hS

/-- A prefix of a well-formed signature is well formed. -/
theorem SigWF.prefix {S M : Sig} (h : SigWF (S ++ M)) : SigWF S := by
  induction M using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton M e ih =>
    apply ih
    rw [← List.append_assoc] at h
    exact h.init

theorem TelBelow.append {n : ℕ} {Δ : Tel} {ρ : Role} {C : Exp} (hΔ : TelBelow n Δ)
    (hC : Below (n + Δ.length) C) : TelBelow n (Δ ++ [(ρ, C)]) := by
  induction Δ generalizing n with
  | nil => exact ⟨by simpa using hC, trivial⟩
  | cons p Δ ih =>
    obtain ⟨ρ', A⟩ := p
    obtain ⟨hA, hrest⟩ := hΔ
    exact ⟨hA, ih hrest (by simpa [Nat.add_assoc, Nat.add_comm 1] using hC)⟩

theorem Eff.declPart_eq_self {m : ℕ} {ε : Eff} (h : ε.Scoped m 0) : Eff.declPart ε = ε := by
  funext z
  cases z with
  | var i => exact (h.1 i (Nat.zero_le i)).symm
  | decl => rfl

/-- A closed telescope formed in the empty context is formed in every context. -/
theorem Deriv.tel_weaken_closed {S : Sig} (hS : SigWF S) {acc : Bool} {Δ : Tel} {δ : Eff}
    (d : Deriv S acc (.tel [] Δ δ)) (hΔ : TelBelow 0 Δ) (Γ : Ctx) :
    Derivable S acc (.tel Γ Δ δ) := by
  have hren : RenOK id [] Γ := fun i _ _ h => by simp at h
  obtain ⟨d'⟩ := d.rename hS hren
  simp only [Judg.substJ, Tel.subst_closed hΔ, List.length_nil, Eff.act, Eff.actVars,
    inf_top_eq] at d'
  rw [Eff.declPart_eq_self d.scoped.2] at d'
  exact ⟨d'⟩

/-- The telescope of a declared family is formed in every context. -/
theorem SigWF.family_tel {S : Sig} (hS : SigWF S) {a : ℕ} {Δ : Tel} {ρ : Role}
    (h : S.family? a = some (Δ, ρ)) (Γ : Ctx) : ∃ δ, Derivable S true (.tel Γ Δ δ) := by
  have key : ∃ δ, Derivable S true (.tel [] Δ δ) := by
    induction hS with
    | nil => simp [Sig.family?] at h
    | @family S' Δ' ρ' δ' _ hΔ' ih =>
      rcases Sig.family?_snoc h with h | ⟨_, Δ'', ρ'', he, hp⟩
      · obtain ⟨δ, hd⟩ := ih h; exact ⟨δ, hd.weakenSig _⟩
      · cases he; cases hp; exact ⟨δ', hΔ'.weakenSig _⟩
    | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih | gate _ _ _ _ _ _ _ _ _ ih =>
      rcases Sig.family?_snoc h with h | ⟨_, _, _, he, _⟩
      · obtain ⟨δ, hd⟩ := ih h; exact ⟨δ, hd.weakenSig _⟩
      · cases he
  obtain ⟨δ, ⟨d⟩⟩ := key
  exact ⟨δ, d.tel_weaken_closed hS (hS.family_closed h) Γ⟩

/-- The telescope of a declared gate, alone and extended by its payload or its
result type, is formed in every context. -/
theorem SigWF.gate_tel {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) (Γ : Ctx) :
    (∃ δ, Derivable S true (.tel Γ Δ δ)) ∧ (∃ δ, Derivable S true (.tel Γ (Δ ++ [(σ, A)]) δ)) ∧
      (∃ δ, Derivable S true (.tel Γ (Δ ++ [(ρ, B)]) δ)) := by
  have key : (∃ δ, Derivable S true (.tel [] Δ δ)) ∧
      (∃ α, Derivable S true (.ty Δ.reverse σ A α)) ∧
      (∃ β, Derivable S true (.ty Δ.reverse ρ B β)) := by
    induction hS with
    | nil => simp [Sig.gate?] at h
    | @gate S' Δ' σ' A' ρ' B' δ' α' β' _ hΔ' hA' hB' _ _ _ _ _ ih =>
      rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, hp⟩
      · obtain ⟨⟨δ, hd⟩, ⟨α, ha⟩, ⟨β, hb⟩⟩ := ih h
        exact ⟨⟨δ, hd.weakenSig _⟩, ⟨α, ha.weakenSig _⟩, ⟨β, hb.weakenSig _⟩⟩
      · cases he; cases hp
        exact ⟨⟨δ', hΔ'.weakenSig _⟩, ⟨α', hA'.weakenSig _⟩, ⟨β', hB'.weakenSig _⟩⟩
    | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih =>
      rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
      · obtain ⟨⟨δ, hd⟩, ⟨α, ha⟩, ⟨β, hb⟩⟩ := ih h
        exact ⟨⟨δ, hd.weakenSig _⟩, ⟨α, ha.weakenSig _⟩, ⟨β, hb.weakenSig _⟩⟩
      · cases he
  obtain ⟨⟨δ, ⟨dΔ⟩⟩, ⟨α, ⟨dA⟩⟩, ⟨β, ⟨dB⟩⟩⟩ := key
  obtain ⟨hΔc, hAc, hBc⟩ := hS.gate_closed h
  rw [← List.append_nil Δ.reverse] at dA dB
  obtain ⟨δA, ⟨dΔA⟩⟩ := dΔ.tel_snoc dA
  obtain ⟨δB, ⟨dΔB⟩⟩ := dΔ.tel_snoc dB
  refine ⟨⟨δ, dΔ.tel_weaken_closed hS hΔc Γ⟩, ⟨δA, dΔA.tel_weaken_closed hS ?_ Γ⟩,
    ⟨δB, dΔB.tel_weaken_closed hS ?_ Γ⟩⟩
  · exact hΔc.append (by simpa using hAc)
  · exact hΔc.append (by simpa using hBc)

end Artform.Roles.Calculus
