import ArtformStages.Forced

/-!
# Maxwell's equations with a current

The law of light of the research ledger on a layered universe is Pair, with the kick
`S = Cᵀ K C` that finding 440 shows forced. Here a current `J` is added to the kick,
`E' = E + S A - J`, `A' = A - L E'`, and the laws of electrodynamics are proved for it, for every
map `C` from the lines to the squares and gauge `G` with `C G = 0` (finding 441 of the ledger):

* `faraday_pairWith`, `ampere_pairWith`, `pairWith_zero` (MX1): the field `B = C A` loses the
  curl of the electric field `L E'`, and `E` gains the curl of `K B` less the current;
* `divergence_pairWith` (MX2): the divergence of `E` falls by the divergence of the current;
* `gauss_kept_iff` (MX3): Gauss's law is kept exactly when the charge moves by continuity;
* `pairWith_gauge` (MX4): a change `G g` of `A` passes through;
* `qstar_pairWith` (MX5): the kept form `Q⋆` changes by the work of the current,
  `- J ⬝ L (E + E')`;
* `pairWith_still_iff`, `still_current_divergence`, `still_field_zero` (MX6): a state is still
  exactly when `Cᵀ K C A = J` and `C L E = 0`; its current has no divergence; and with no current
  and every `κ > 0` it has no field on the squares;
* `Board.divergence_sum` (MX7): on a board the divergence of every `E` sums to `0`.

Read with `ε = L⁻¹` and `μ = K⁻¹`, these are Maxwell's equations in matter in Yee's staggered form,
with the time step `1`; none of it is new.
-/

open Matrix

namespace Artform.Stages

section Current

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- **Pair with a current**: the kick takes the current `J` from `E`, then the drift. -/
def pairWith (S L : Matrix n n R) (J : n → R) (x : LightState R n) : LightState R n :=
  (x.1 - L *ᵥ (x.2 + S *ᵥ x.1 - J), x.2 + S *ᵥ x.1 - J)

/-- MX1. With no current, Pair with a current is Pair. -/
theorem pairWith_zero (S L : Matrix n n R) : pairWith S L 0 = pair S L := by
  funext x
  simp [pairWith, pair]

/-- The divergence of `E`: at each corner, `E` on the lines that leave less `E` on the lines that
arrive. -/
def divergence {v : Type*} (G : Matrix n v R) (E : n → R) : v → R := -(Gᵀ *ᵥ E)

/-- MX5. With `S` and `L` symmetric, Pair with a current changes the kept form by the work of the
current on the old and the new `E`. -/
theorem qstar_pairWith (S L : Matrix n n R) (hS : Sᵀ = S) (hL : Lᵀ = L) (J : n → R)
    (x : LightState R n) :
    qstar S L (pairWith S L J x) = qstar S L x - J ⬝ᵥ (L *ᵥ (x.2 + (pairWith S L J x).2)) := by
  obtain ⟨A, E⟩ := x
  simp only [qstar, pairWith]
  generalize hE' : E + S *ᵥ A - J = E'
  have h1 : A - L *ᵥ E' + L *ᵥ E' = A := sub_add_cancel _ _
  have h2 : E' - S *ᵥ A = E - J := by
    rw [← hE']
    abel
  calc (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (A - L *ᵥ E')) + E' ⬝ᵥ (L *ᵥ E')
          + (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (L *ᵥ E'))
        = (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (A - L *ᵥ E' + L *ᵥ E')) + E' ⬝ᵥ (L *ᵥ E') := by
          rw [mulVec_add, dotProduct_add]; ring
      _ = (A - L *ᵥ E') ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ E') := by rw [h1]
      _ = A ⬝ᵥ (S *ᵥ A) - E' ⬝ᵥ (L *ᵥ (S *ᵥ A)) + E' ⬝ᵥ (L *ᵥ E') := by
          rw [sub_dotProduct, mulVec_dotProduct_symm L hL]
      _ = A ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ (E' - S *ᵥ A)) := by
          rw [mulVec_sub, dotProduct_sub]; ring
      _ = A ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ (E - J)) := by rw [h2]
      _ = A ⬝ᵥ (S *ᵥ A) + E ⬝ᵥ (L *ᵥ E) + A ⬝ᵥ (S *ᵥ (L *ᵥ E)) - J ⬝ᵥ (L *ᵥ (E + E')) := by
          rw [← hE']
          simp only [mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
            sub_dotProduct]
          rw [dotProduct_mulVec_symm L hL E J, mulVec_dotProduct_symm S hS A (L *ᵥ E),
            dotProduct_mulVec_symm L hL (S *ᵥ A) J]
          ring

variable {f : Type*} [Fintype f]

/-- MX1. Faraday's law: the field on the squares, `B = C A`, loses the curl of the electric field
`L E'`. -/
theorem faraday_pairWith (C : Matrix f n R) (K : Matrix f f R) (L : Matrix n n R) (J : n → R)
    (x : LightState R n) :
    C *ᵥ (pairWith (Cᵀ * K * C) L J x).1 =
      C *ᵥ x.1 - (C * L) *ᵥ (pairWith (Cᵀ * K * C) L J x).2 := by
  simp only [pairWith, mulVec_sub, mulVec_mulVec]

/-- MX1. Ampère's law with the current: `E` gains the curl of `K B` and loses the current. -/
theorem ampere_pairWith (C : Matrix f n R) (K : Matrix f f R) (L : Matrix n n R) (J : n → R)
    (x : LightState R n) :
    (pairWith (Cᵀ * K * C) L J x).2 = x.2 + Cᵀ *ᵥ (K *ᵥ (C *ᵥ x.1)) - J := by
  simp only [pairWith, mulVec_mulVec, Matrix.mul_assoc]

/-- MX6. A state is still exactly when `Cᵀ K C A = J` (Ampère's static law) and `C L E = 0` (the
electric field has no curl). -/
theorem pairWith_still_iff (C : Matrix f n R) (K : Matrix f f R) (L : Matrix n n R) (J : n → R)
    (A E : n → R) :
    (C *ᵥ (pairWith (Cᵀ * K * C) L J (A, E)).1 = C *ᵥ A ∧
        (pairWith (Cᵀ * K * C) L J (A, E)).2 = E) ↔
      ((Cᵀ * K * C) *ᵥ A = J ∧ (C * L) *ᵥ E = 0) := by
  simp only [pairWith]
  constructor
  · rintro ⟨h1, h2⟩
    have hJ : (Cᵀ * K * C) *ᵥ A = J := by
      have h := sub_eq_zero.mpr h2
      rw [show E + (Cᵀ * K * C) *ᵥ A - J - E = (Cᵀ * K * C) *ᵥ A - J by abel] at h
      exact sub_eq_zero.mp h
    refine ⟨hJ, ?_⟩
    rw [h2, mulVec_sub, sub_eq_self, mulVec_mulVec] at h1
    exact h1
  · rintro ⟨hJ, hE⟩
    have h2 : E + (Cᵀ * K * C) *ᵥ A - J = E := by rw [hJ, add_sub_cancel_right]
    refine ⟨?_, h2⟩
    rw [h2, mulVec_sub, mulVec_mulVec, hE, sub_zero]

variable {v : Type*}

theorem gaugeT_mul_kick (C : Matrix f n R) (G : Matrix n v R) (K : Matrix f f R)
    (hCG : C * G = 0) : Gᵀ * (Cᵀ * K * C) = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hCG, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.zero_mul]

/-- MX2. Continuity: with `C G = 0`, the divergence of `E` falls by the divergence of the
current. -/
theorem divergence_pairWith (C : Matrix f n R) (G : Matrix n v R) (K : Matrix f f R)
    (L : Matrix n n R) (hCG : C * G = 0) (J : n → R) (x : LightState R n) :
    divergence G (pairWith (Cᵀ * K * C) L J x).2 = divergence G x.2 - divergence G J := by
  simp only [divergence, pairWith, mulVec_sub, mulVec_add, mulVec_mulVec,
    gaugeT_mul_kick C G K hCG, zero_mulVec, add_zero]
  abel

/-- MX3. With `C G = 0`, Gauss's law is kept exactly when the charge moves by continuity: every
state whose `E` has the divergence `ρ` goes to one whose `E'` has the divergence `ρ'` if and only
if `ρ' = ρ - div J`. -/
theorem gauss_kept_iff (C : Matrix f n R) (G : Matrix n v R) (K : Matrix f f R) (L : Matrix n n R)
    (hCG : C * G = 0) (J : n → R) (ρ ρ' : v → R) (hρ : ∃ E₀, divergence G E₀ = ρ) :
    (∀ A E, divergence G E = ρ → divergence G (pairWith (Cᵀ * K * C) L J (A, E)).2 = ρ') ↔
      ρ' = ρ - divergence G J := by
  constructor
  · intro h
    obtain ⟨E₀, hE₀⟩ := hρ
    have := h 0 E₀ hE₀
    rw [divergence_pairWith C G K L hCG] at this
    dsimp only at this
    rw [hE₀] at this
    exact this.symm
  · rintro rfl A E hE
    rw [divergence_pairWith C G K L hCG]
    dsimp only
    rw [hE]

/-- MX4. With `C G = 0`, a change `G g` of `A` passes through Pair with a current. -/
theorem pairWith_gauge [Fintype v] (C : Matrix f n R) (G : Matrix n v R) (K : Matrix f f R)
    (L : Matrix n n R) (hCG : C * G = 0) (J : n → R) (A E : n → R) (g : v → R) :
    pairWith (Cᵀ * K * C) L J (A + G *ᵥ g, E) =
      ((pairWith (Cᵀ * K * C) L J (A, E)).1 + G *ᵥ g, (pairWith (Cᵀ * K * C) L J (A, E)).2) := by
  have h0 : (Cᵀ * K * C) *ᵥ (G *ᵥ g) = 0 := by
    rw [mulVec_mulVec, Matrix.mul_assoc, hCG, Matrix.mul_zero, zero_mulVec]
  simp only [pairWith, mulVec_add, h0, add_zero, Prod.mk.injEq, and_true]
  abel

/-- MX6. With `C G = 0`, the current of a still state has no divergence. -/
theorem still_current_divergence (C : Matrix f n R) (G : Matrix n v R) (K : Matrix f f R)
    (hCG : C * G = 0) (A J : n → R) (hJ : (Cᵀ * K * C) *ᵥ A = J) : divergence G J = 0 := by
  rw [divergence, ← hJ, mulVec_mulVec, gaugeT_mul_kick C G K hCG, zero_mulVec, neg_zero]

end Current

/-- MX6. Over the real numbers, with every `κ > 0`, a still state with no current has no field on
the squares: `Cᵀ diag κ C A = 0` makes `C A = 0`. -/
theorem still_field_zero {n f : Type*} [Fintype n] [Fintype f] [DecidableEq f] (C : Matrix f n ℝ)
    (κ : f → ℝ) (hκ : ∀ σ, 0 < κ σ) (A : n → ℝ) (h : (Cᵀ * diagonal κ * C) *ᵥ A = 0) :
    C *ᵥ A = 0 := by
  have h0 : A ⬝ᵥ ((Cᵀ * diagonal κ * C) *ᵥ A) = ∑ σ, κ σ * (C *ᵥ A) σ ^ 2 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [h, dotProduct_zero] at h0
  funext σ
  have hs : ∀ τ ∈ Finset.univ, 0 ≤ κ τ * (C *ᵥ A) τ ^ 2 :=
    fun τ _ => mul_nonneg (hκ τ).le (sq_nonneg _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hs).mp h0.symm σ (Finset.mem_univ σ)
  have h2 := (mul_eq_zero.mp h1).resolve_left (hκ σ).ne'
  simpa using h2

/-- MX7. On every board, the divergence of every `E` sums to `0` over the corners: a closed board
carries no net charge. -/
theorem Board.divergence_sum {f e v : Type*} [Fintype e] [Fintype v] [DecidableEq v]
    (B : Board f e v) (E : e → ℝ) : ∑ w, divergence B.gauge E w = 0 := by
  simp only [divergence, Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero, mulVec, dotProduct,
    transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [← Finset.sum_mul]
  simp [Board.gauge, Finset.sum_sub_distrib]

end Artform.Stages
