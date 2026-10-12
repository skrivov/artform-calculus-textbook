import ArtformRoles.Calculus.Scope

/-!
# Telescopes and substitution

Laws of the instantiation of telescopes (`Tel.inst`, `instAt`, `instType`)
under substitution, and the closed telescopes and gate types of a well-formed
signature, which no substitution changes.
-/

namespace Artform.Roles.Calculus

open Exp

theorem Exp.upN_zero (σ : ℕ → Exp) : upN 0 σ = σ := rfl

theorem Exp.upN_succ (k : ℕ) (σ : ℕ → Exp) : upN (k + 1) σ = up (upN k σ) := rfl

theorem Exp.upN_succ' (k : ℕ) (σ : ℕ → Exp) : upN (k + 1) σ = upN k (up σ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [upN_succ, ih, upN_succ]

theorem Exp.upN_subst_comm (k : ℕ) (σ τ : ℕ → Exp) :
    subst (upN k τ) ∘ upN k σ = upN k (subst τ ∘ σ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [upN_succ, up_subst_comm, ih]

/-- `upN k σ` fixes the variables below `k`. -/
theorem Exp.upN_lt {k i : ℕ} (σ : ℕ → Exp) (h : i < k) : upN k σ i = var i := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => simp [upN_succ, ih (by omega : i < k), ren]

/-- An expression below `k` is unchanged by a substitution moved under `k`
binders. -/
theorem Exp.subst_upN_below {k : ℕ} {C : Exp} (h : Below k C) (σ : ℕ → Exp) :
    C.subst (upN k σ) = C := by
  rw [subst_congr_below (τ := var) (fun i hi => upN_lt σ hi) h, subst_var]

/-- The pointwise law behind `subst_inst`. -/
theorem Exp.subst_comp_inst1 (σ : ℕ → Exp) (t : Exp) :
    subst σ ∘ inst1 t = subst (inst1 (t.subst σ)) ∘ up σ := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [subst, subst_ren, inst1_comp_succ]

namespace Tel

@[simp] theorem subst_nil (σ : ℕ → Exp) : Tel.subst σ [] = [] := rfl

@[simp] theorem subst_cons (σ : ℕ → Exp) (ρ : Role) (A : Exp) (Δ : Tel) :
    Tel.subst σ ((ρ, A) :: Δ) = (ρ, A.subst σ) :: Tel.subst (up σ) Δ := rfl

@[simp] theorem length_subst (σ : ℕ → Exp) (Δ : Tel) : (Tel.subst σ Δ).length = Δ.length := by
  induction Δ generalizing σ with
  | nil => rfl
  | cons p Δ ih => obtain ⟨ρ, A⟩ := p; simp [ih]

@[simp] theorem length_inst (t : Exp) (Δ : Tel) : (Tel.inst t Δ).length = Δ.length :=
  length_subst _ _

theorem subst_subst (σ τ : ℕ → Exp) (Δ : Tel) :
    Tel.subst τ (Tel.subst σ Δ) = Tel.subst (Exp.subst τ ∘ σ) Δ := by
  induction Δ generalizing σ τ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨ρ, A⟩ := p
    simp [Exp.subst_subst, ih, up_subst_comm]

theorem subst_var (Δ : Tel) : Tel.subst var Δ = Δ := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih => obtain ⟨ρ, A⟩ := p; simp [up_var, ih]

theorem subst_congr_below {n : ℕ} {σ τ : ℕ → Exp} (h : ∀ i < n, σ i = τ i) {Δ : Tel}
    (hΔ : TelBelow n Δ) : Tel.subst σ Δ = Tel.subst τ Δ := by
  induction Δ generalizing n σ τ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨ρ, A⟩ := p
    obtain ⟨hA, hΔ'⟩ := hΔ
    simp only [subst_cons, Exp.subst_congr_below h hA, ih (up_congr h) hΔ']

/-- A closed telescope is unchanged by every substitution. -/
theorem subst_closed {Δ : Tel} (hΔ : TelBelow 0 Δ) (σ : ℕ → Exp) : Tel.subst σ Δ = Δ := by
  rw [subst_congr_below (τ := var) (fun i hi => absurd hi (Nat.not_lt_zero i)) hΔ, subst_var]

/-- Substitution commutes with instantiation of a telescope. -/
theorem subst_inst (σ : ℕ → Exp) (t : Exp) (Δ : Tel) :
    Tel.subst σ (Tel.inst t Δ) = Tel.inst (t.subst σ) (Tel.subst (up σ) Δ) := by
  simp only [Tel.inst, Tel.subst_subst, Exp.subst_comp_inst1]

end Tel

/-- Substitution commutes with the instantiation of a type under `k` later
entries. -/
theorem instAt_subst (σ : ℕ → Exp) (t : Exp) (k : ℕ) (C : Exp) :
    (instAt t k C).subst (upN k σ) = instAt (t.subst σ) k (C.subst (upN (k + 1) σ)) := by
  simp only [instAt, Exp.subst_subst, upN_subst_comm, upN_succ', subst_comp_inst1]

/-- `ts` is an argument list of `n` arguments. -/
def Exp.IsList : Exp → ℕ → Prop
  | .nil, 0 => True
  | .cons _ ts, n + 1 => IsList ts n
  | _, _ => False

/-- Substitution commutes with the instantiation of a type under a whole
telescope by an argument list. -/
theorem instType_subst (σ : ℕ → Exp) {ds : Exp} {Δ : Tel} (h : ds.IsList Δ.length) (C : Exp) :
    (instType ds Δ C).subst σ =
      instType (ds.subst σ) (Tel.subst σ Δ) (C.subst (upN Δ.length σ)) := by
  induction ds generalizing σ Δ C with
  | nil =>
    cases Δ with
    | nil => simp [instType, Exp.subst, upN_zero]
    | cons => simp [Exp.IsList] at h
  | cons t ts _ ihts =>
    cases Δ with
    | nil => simp [Exp.IsList] at h
    | cons p Δ =>
      obtain ⟨ρ, A⟩ := p
      simp only [Exp.IsList, List.length_cons] at h
      simp only [instType, Exp.subst, Tel.subst_cons, List.length_cons]
      rw [ihts σ (Δ := Tel.inst t Δ) (by rwa [Tel.length_inst]), Tel.length_inst, instAt_subst,
        Tel.subst_inst, Tel.length_subst]
  | _ => cases Δ <;> simp [Exp.IsList] at h

end Artform.Roles.Calculus
