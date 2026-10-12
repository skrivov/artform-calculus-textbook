import ArtformRoles.Calculus.Telescope

/-!
# Facts about well-formed signatures

The entries of a well-formed signature are closed: a family's telescope, a
constant's type, a gate's telescope and its payload and result types under that
telescope. Lookups in a signature are unchanged by appending entries.
-/

namespace Artform.Roles.Calculus

open Exp

theorem getElem?_append_singleton {α : Type} (S : List α) (e : α) (x : ℕ) :
    (S ++ [e])[x]? = if x < S.length then S[x]? else if x = S.length then some e else none := by
  split_ifs with h₁ h₂
  · exact List.getElem?_append_left h₁
  · subst h₂; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]

namespace Sig

theorem family?_append_lt {S M : Sig} {a : ℕ} (h : a < S.length) :
    (S ++ M).family? a = S.family? a := by
  simp only [family?, List.getElem?_append_left h]

theorem gate?_append_lt {S M : Sig} {g : ℕ} (h : g < S.length) :
    (S ++ M).gate? g = S.gate? g := by
  simp only [gate?, List.getElem?_append_left h]

theorem const?_append_lt {S M : Sig} {i k : ℕ} (h : i < S.length) :
    (S ++ M).const? i k = S.const? i k := by
  simp only [const?, List.getElem?_append_left h]

theorem declRole?_append_lt {S M : Sig} {i k : ℕ} (h : i < S.length) :
    (S ++ M).declRole? i k = S.declRole? i k := by
  simp only [declRole?, List.getElem?_append_left h, const?_append_lt h]

theorem family?_append {S M : Sig} {a : ℕ} {p} (h : S.family? a = some p) :
    (S ++ M).family? a = some p := by
  rw [family?_append_lt (lt_of_family h), h]

theorem gate?_append {S M : Sig} {g : ℕ} {p} (h : S.gate? g = some p) :
    (S ++ M).gate? g = some p := by
  rw [gate?_append_lt (lt_of_gate h), h]

theorem const?_append {S M : Sig} {i k : ℕ} {p} (h : S.const? i k = some p) :
    (S ++ M).const? i k = some p := by
  rw [const?_append_lt (lt_of_const h), h]

/-- Looking up the last entry of `S ++ [e]`. -/
theorem family?_snoc {S : Sig} {e : Entry} {a : ℕ} {p} (h : (S ++ [e]).family? a = some p) :
    S.family? a = some p ∨ (a = S.length ∧ ∃ Δ ρ, e = .family Δ ρ ∧ p = (Δ, ρ)) := by
  unfold family? at h ⊢
  rw [getElem?_append_singleton] at h
  split_ifs at h with h₁ h₂
  · exact .inl h
  · subst h₂
    right
    refine ⟨rfl, ?_⟩
    cases e <;> simp_all

theorem gate?_snoc {S : Sig} {e : Entry} {g : ℕ} {p} (h : (S ++ [e]).gate? g = some p) :
    S.gate? g = some p ∨
      (g = S.length ∧ ∃ Δ σ A ρ B, e = .gate Δ σ A ρ B ∧ p = (Δ, σ, A, ρ, B)) := by
  unfold gate? at h ⊢
  rw [getElem?_append_singleton] at h
  split_ifs at h with h₁ h₂
  · exact .inl h
  · subst h₂
    right
    refine ⟨rfl, ?_⟩
    cases e <;> simp_all

theorem const?_snoc {S : Sig} {e : Entry} {i k : ℕ} {p} (h : (S ++ [e]).const? i k = some p) :
    S.const? i k = some p ∨ (i = S.length ∧
      ((∃ ρ A, e = .prim ρ A ∧ k = 0 ∧ p = (ρ, A)) ∨
       (∃ σ A, e = .cert σ A ∧ ((k = 0 ∧ p = (σ, A)) ∨ (k = 1 ∧ p = (.witness, .event)) ∨
          (k = 2 ∧ p = (.witness, .origin A (.const i 1) (.const i 0))))) ∨
       (∃ A t, e = .attest A t ∧ ((k = 0 ∧ p = (.witness, .event)) ∨
          (k = 1 ∧ p = (.witness, .origin A (.const i 0) t)))))) := by
  unfold const? at h ⊢
  rw [getElem?_append_singleton] at h
  split_ifs at h with h₁ h₂
  · exact .inl h
  · subst h₂
    right
    refine ⟨rfl, ?_⟩
    rcases e with ⟨Δ, ρ⟩ | ⟨ρ, A⟩ | ⟨σ, A⟩ | ⟨A, t⟩ | ⟨Δ, σ, A, ρ, B⟩
    · simp at h
    · rcases k with _ | k <;> simp_all
    · rcases k with _ | _ | _ | k <;> simp_all
    · rcases k with _ | _ | k <;> simp_all
    · simp at h

end Sig

namespace SigWF

/-- The entries of a well-formed signature are closed. -/
theorem closed {S : Sig} (hS : SigWF S) :
    (∀ a Δ ρ, S.family? a = some (Δ, ρ) → TelBelow 0 Δ) ∧
    (∀ i k ρ A, S.const? i k = some (ρ, A) → Closed A) ∧
    (∀ g Δ σ A ρ B, S.gate? g = some (Δ, σ, A, ρ, B) →
      TelBelow 0 Δ ∧ Below Δ.length A ∧ Below Δ.length B) := by
  induction hS with
  | nil => exact ⟨fun _ _ _ h => by simp [Sig.family?] at h,
      fun _ _ _ _ h => by simp [Sig.const?] at h, fun _ _ _ _ _ _ h => by simp [Sig.gate?] at h⟩
  | @family S Δ ρ δ _ hΔ ih =>
    obtain ⟨d⟩ := hΔ
    refine ⟨fun a Δ' ρ' h => ?_, fun i k ρ' A h => ?_, fun g Δ' σ A ρ' B h => ?_⟩
    · rcases Sig.family?_snoc h with h | ⟨_, Δ'', ρ'', he, hp⟩
      · exact ih.1 a Δ' ρ' h
      · cases he; cases hp; exact d.scoped.1
    · rcases Sig.const?_snoc h with h | ⟨_, h⟩
      · exact ih.2.1 i k ρ' A h
      · rcases h with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ <;> cases he
    · rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
      · exact ih.2.2 g Δ' σ A ρ' B h
      · cases he
  | @prim S ρ A α _ hA _ _ ih =>
    obtain ⟨d⟩ := hA
    refine ⟨fun a Δ' ρ' h => ?_, fun i k ρ' A' h => ?_, fun g Δ' σ A' ρ' B h => ?_⟩
    · rcases Sig.family?_snoc h with h | ⟨_, _, _, he, _⟩
      · exact ih.1 a Δ' ρ' h
      · cases he
    · rcases Sig.const?_snoc h with h | ⟨_, h⟩
      · exact ih.2.1 i k ρ' A' h
      · rcases h with ⟨_, _, he, _, hp⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩
        · cases he; cases hp; exact d.scoped.1
        · cases he
        · cases he
    · rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
      · exact ih.2.2 g Δ' σ A' ρ' B h
      · cases he
  | @cert S σ A α _ hA _ _ _ ih =>
    obtain ⟨d⟩ := hA
    refine ⟨fun a Δ' ρ' h => ?_, fun i k ρ' A' h => ?_, fun g Δ' σ' A' ρ' B h => ?_⟩
    · rcases Sig.family?_snoc h with h | ⟨_, _, _, he, _⟩
      · exact ih.1 a Δ' ρ' h
      · cases he
    · rcases Sig.const?_snoc h with h | ⟨_, h⟩
      · exact ih.2.1 i k ρ' A' h
      · rcases h with ⟨_, _, he, _⟩ | ⟨_, _, he, h⟩ | ⟨_, _, he, _⟩
        · cases he
        · cases he
          rcases h with ⟨_, hp⟩ | ⟨_, hp⟩ | ⟨_, hp⟩ <;> cases hp
          · exact d.scoped.1
          · trivial
          · exact ⟨d.scoped.1, trivial, trivial⟩
        · cases he
    · rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
      · exact ih.2.2 g Δ' σ' A' ρ' B h
      · cases he
  | @attest S A t θ _ ht _ _ _ ih =>
    obtain ⟨d⟩ := ht
    refine ⟨fun a Δ' ρ' h => ?_, fun i k ρ' A' h => ?_, fun g Δ' σ' A' ρ' B h => ?_⟩
    · rcases Sig.family?_snoc h with h | ⟨_, _, _, he, _⟩
      · exact ih.1 a Δ' ρ' h
      · cases he
    · rcases Sig.const?_snoc h with h | ⟨_, h⟩
      · exact ih.2.1 i k ρ' A' h
      · rcases h with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, h⟩
        · cases he
        · cases he
        · cases he
          rcases h with ⟨_, hp⟩ | ⟨_, hp⟩ <;> cases hp
          · trivial
          · exact ⟨d.scoped.2.1, trivial, d.scoped.1⟩
    · rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
      · exact ih.2.2 g Δ' σ' A' ρ' B h
      · cases he
  | @gate S Δ σ A ρ B δ α β _ hΔ hA hB _ _ _ _ _ _ _ ih =>
    obtain ⟨dΔ⟩ := hΔ
    obtain ⟨dA⟩ := hA
    obtain ⟨dB⟩ := hB
    refine ⟨fun a Δ' ρ' h => ?_, fun i k ρ' A' h => ?_, fun g Δ' σ' A' ρ' B' h => ?_⟩
    · rcases Sig.family?_snoc h with h | ⟨_, _, _, he, _⟩
      · exact ih.1 a Δ' ρ' h
      · cases he
    · rcases Sig.const?_snoc h with h | ⟨_, h⟩
      · exact ih.2.1 i k ρ' A' h
      · rcases h with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ <;> cases he
    · rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, hp⟩
      · exact ih.2.2 g Δ' σ' A' ρ' B' h
      · cases he; cases hp
        have hA' := dA.scoped.1
        have hB' := dB.scoped.1
        simp only [List.length_reverse] at hA' hB'
        exact ⟨dΔ.scoped.1, hA', hB'⟩

theorem family_closed {S : Sig} (hS : SigWF S) {a Δ ρ} (h : S.family? a = some (Δ, ρ)) :
    TelBelow 0 Δ := hS.closed.1 a Δ ρ h

theorem const_closed {S : Sig} (hS : SigWF S) {i k ρ A} (h : S.const? i k = some (ρ, A)) :
    Closed A := hS.closed.2.1 i k ρ A h

theorem gate_closed {S : Sig} (hS : SigWF S) {g Δ σ A ρ B}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) :
    TelBelow 0 Δ ∧ Below Δ.length A ∧ Below Δ.length B := hS.closed.2.2 g Δ σ A ρ B h

end SigWF

end Artform.Roles.Calculus
