import ArtformStages.Pair

/-!
# The window of Pair

Astra's dossier of wave 39, in the research ledger on a layered universe, finds that Pair with
real weights is bounded exactly when each level of its kick other than `0`, times the drift,
lies strictly between `0` and `4`. Here that is a theorem, in four steps.

* `four_qstar` (WN1): completing the square,
  `4 Q⋆(A, E) = (2E + S A) ⬝ L (2E + S A) + 4 A ⬝ S A - S A ⬝ L (S A)`.
* `qstar_nonneg_iff` (WN2): over an ordered field, `Q⋆` is nowhere negative exactly when
  `E ⬝ L E` is nowhere negative and `S A ⬝ L (S A) ≤ 4 A ⬝ S A` for every `A`.
* `pair_on_level` (WN3): on a level `S v = s v` of the kick, with the drift `ℓ` on every cell,
  Pair is the Pair of one place.
* `bounded_iff_window` (WN4): the Pair of one place with the numbers `σ` and `ℓ` keeps every
  orbit bounded exactly when `0 < ℓ σ < 4`, or `ℓ = σ = 0`.

None of this is new: it is the stability of the leapfrog step of Störmer and Verlet.
-/

open Matrix

namespace Artform.Stages

section Square

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- WN1. Completing the square. -/
theorem four_qstar (S L : Matrix n n R) (hS : Sᵀ = S) (hL : Lᵀ = L) (A E : n → R) :
    4 * qstar S L (A, E) = ((2 : R) • E + S *ᵥ A) ⬝ᵥ (L *ᵥ ((2 : R) • E + S *ᵥ A)) +
      4 * (A ⬝ᵥ (S *ᵥ A)) - (S *ᵥ A) ⬝ᵥ (L *ᵥ (S *ᵥ A)) := by
  have h1 : E ⬝ᵥ (L *ᵥ (S *ᵥ A)) = (S *ᵥ A) ⬝ᵥ (L *ᵥ E) := dotProduct_mulVec_symm L hL E (S *ᵥ A)
  have h2 : (S *ᵥ A) ⬝ᵥ (L *ᵥ E) = A ⬝ᵥ (S *ᵥ (L *ᵥ E)) := mulVec_dotProduct_symm S hS A (L *ᵥ E)
  simp only [qstar, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h1, h2]
  ring

end Square

section Positive

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {n : Type*} [Fintype n]

/-- WN2. When the staggered energy is nowhere negative. -/
theorem qstar_nonneg_iff (S L : Matrix n n 𝕜) (hS : Sᵀ = S) (hL : Lᵀ = L) :
    (∀ x : LightState 𝕜 n, 0 ≤ qstar S L x) ↔
      (∀ E : n → 𝕜, 0 ≤ E ⬝ᵥ (L *ᵥ E)) ∧
        ∀ A : n → 𝕜, (S *ᵥ A) ⬝ᵥ (L *ᵥ (S *ᵥ A)) ≤ 4 * (A ⬝ᵥ (S *ᵥ A)) := by
  constructor
  · intro h
    refine ⟨fun E => ?_, fun A => ?_⟩
    · simpa [qstar] using h (0, E)
    · have h4 := four_qstar S L hS hL A (-(1 / 2 : 𝕜) • (S *ᵥ A))
      have hw : (2 : 𝕜) • (-(1 / 2 : 𝕜) • (S *ᵥ A)) + S *ᵥ A = 0 := by
        rw [smul_smul]
        norm_num
      rw [hw, mulVec_zero, dotProduct_zero, zero_add] at h4
      have h5 := h (A, -(1 / 2 : 𝕜) • (S *ᵥ A))
      linarith
  · rintro ⟨hE, hA⟩ ⟨A, E⟩
    have h4 := four_qstar S L hS hL A E
    have h5 := hE ((2 : 𝕜) • E + S *ᵥ A)
    have h6 := hA A
    linarith

end Positive

section Level

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- WN3. On a level of the kick, `S v = s v`, with the drift `ℓ` on every cell, Pair is the Pair
of one place: `e' = e + s a` and `a' = a - ℓ e'`. -/
theorem pair_on_level (S : Matrix n n R) (s ℓ : R) (v : n → R) (hv : S *ᵥ v = s • v) (a e : R) :
    pair S (ℓ • (1 : Matrix n n R)) (a • v, e • v) =
      ((a - ℓ * (e + s * a)) • v, (e + s * a) • v) := by
  have h1 : S *ᵥ (a • v) = (a * s) • v := by rw [mulVec_smul, hv, smul_smul]
  have h2 : ∀ w : n → R, (ℓ • (1 : Matrix n n R)) *ᵥ w = ℓ • w := fun w => by
    rw [smul_mulVec, one_mulVec]
  simp only [pair, h1, h2]
  ext i <;> simp <;> ring

end Level

section OnePlace

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The Pair of one place, with the number `σ` of its kick and `ℓ` of its drift. -/
def pairOne (σ ℓ : 𝕜) (x : 𝕜 × 𝕜) : 𝕜 × 𝕜 := (x.1 - ℓ * (x.2 + σ * x.1), x.2 + σ * x.1)

/-- Its staggered energy. -/
def qOne (σ ℓ : 𝕜) (x : 𝕜 × 𝕜) : 𝕜 := σ * x.1 ^ 2 + ℓ * x.2 ^ 2 + σ * ℓ * x.1 * x.2

/-- Every orbit of `f` is bounded: `a² + e²` stays below some bound along it. -/
def OrbitsBounded (f : 𝕜 × 𝕜 → 𝕜 × 𝕜) : Prop :=
  ∀ x, ∃ B : 𝕜, ∀ k : ℕ, (f^[k] x).1 ^ 2 + (f^[k] x).2 ^ 2 ≤ B

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem qOne_pairOne (σ ℓ : 𝕜) (x : 𝕜 × 𝕜) : qOne σ ℓ (pairOne σ ℓ x) = qOne σ ℓ x := by
  simp only [qOne, pairOne]
  ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem qOne_iterate (σ ℓ : 𝕜) (x : 𝕜 × 𝕜) (k : ℕ) :
    qOne σ ℓ ((pairOne σ ℓ)^[k] x) = qOne σ ℓ x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', qOne_pairOne, ih]

/-- Inside the window every orbit is bounded: the energy holds it. -/
theorem bounded_of_window (σ ℓ : 𝕜) (h : 0 < ℓ * σ ∧ ℓ * σ < 4) :
    OrbitsBounded (pairOne σ ℓ) := by
  intro x
  obtain ⟨D, hD⟩ : ∃ D : 𝕜, D = σ * ℓ * (4 - σ * ℓ) := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    have h1 : 0 < σ * ℓ := by rw [mul_comm]; exact h.1
    have h2 : 0 < 4 - σ * ℓ := by rw [mul_comm]; linarith [h.2]
    rw [hD]
    exact mul_pos h1 h2
  refine ⟨4 * (σ + ℓ) * qOne σ ℓ x / D, fun k => ?_⟩
  have hq := qOne_iterate σ ℓ x k
  generalize (pairOne σ ℓ)^[k] x = y at hq ⊢
  have h1 : 4 * σ * qOne σ ℓ y = (2 * σ * y.1 + σ * ℓ * y.2) ^ 2 + D * y.2 ^ 2 := by
    rw [hD]; simp only [qOne]; ring
  have h2 : 4 * ℓ * qOne σ ℓ y = (2 * ℓ * y.2 + σ * ℓ * y.1) ^ 2 + D * y.1 ^ 2 := by
    rw [hD]; simp only [qOne]; ring
  rw [hq] at h1 h2
  rw [le_div_iff₀ hDpos]
  nlinarith [sq_nonneg (2 * σ * y.1 + σ * ℓ * y.2), sq_nonneg (2 * ℓ * y.2 + σ * ℓ * y.1)]

/-- A sequence of the recurrence `u (k + 2) = t u (k + 1) - u k` with `t ≥ 2` that starts at
`0` grows at least as fast as `k u 1`. -/
theorem growth_of_two_le (u : ℕ → 𝕜) (t : 𝕜) (ht : 2 ≤ t) (h0 : u 0 = 0)
    (hrec : ∀ k, u (k + 2) = t * u (k + 1) - u k) (hc : 0 ≤ u 1) (k : ℕ) :
    (k : 𝕜) * u 1 ≤ u k ∧ u 1 ≤ u (k + 1) - u k := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hk : ((k + 1 : ℕ) : 𝕜) * u 1 ≤ u (k + 1) := by push_cast; linarith
    refine ⟨hk, ?_⟩
    have hpos : 0 ≤ u (k + 1) := le_trans (mul_nonneg (Nat.cast_nonneg _) hc) hk
    have hr : u (k + 1 + 1) = t * u (k + 1) - u k := hrec k
    rw [hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hpos]

theorem growth_sq_of_two_le (u : ℕ → 𝕜) (t : 𝕜) (ht : 2 ≤ t) (h0 : u 0 = 0)
    (hrec : ∀ k, u (k + 2) = t * u (k + 1) - u k) (k : ℕ) : ((k : 𝕜) * u 1) ^ 2 ≤ u k ^ 2 := by
  rcases le_total 0 (u 1) with hc | hc
  · have h1 := (growth_of_two_le u t ht h0 hrec hc k).1
    have h2 : 0 ≤ (k : 𝕜) * u 1 := mul_nonneg (Nat.cast_nonneg k) hc
    nlinarith
  · have h1 : (k : 𝕜) * -u 1 ≤ -u k := (growth_of_two_le (fun j => -u j) t ht (by simp [h0])
      (fun j => by simp only [hrec j]; ring) (by simpa using hc) k).1
    have h2 : 0 ≤ (k : 𝕜) * -u 1 := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    nlinarith

theorem exists_gt_sq [Archimedean 𝕜] (w : ℕ → 𝕜) (c : 𝕜) (hc : c ≠ 0)
    (hw : ∀ j : ℕ, ((j : 𝕜) * c) ^ 2 ≤ w j ^ 2) (B : 𝕜) : ∃ j, B < w j ^ 2 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (B / c ^ 2)
  have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))
  refine ⟨j + 1, ?_⟩
  have h1 := hw (j + 1)
  have h2 : B < (j : 𝕜) * c ^ 2 := by rwa [div_lt_iff₀ hc2] at hj
  have hj0 : (0 : 𝕜) ≤ j := Nat.cast_nonneg j
  push_cast at h1
  nlinarith [mul_nonneg (mul_nonneg hj0 hj0) hc2.le, mul_nonneg hj0 hc2.le]

/-- An orbit whose first number, read at the times `s j`, keeps a recurrence with `t ≥ 2`
from `0` to `c ≠ 0`, is not bounded. -/
theorem not_bounded_of_growth [Archimedean 𝕜] (f : 𝕜 × 𝕜 → 𝕜 × 𝕜) (x : 𝕜 × 𝕜) (s : ℕ → ℕ)
    (t c : 𝕜) (ht : 2 ≤ t) (hc : c ≠ 0) (h0 : (f^[s 0] x).1 = 0) (h1 : (f^[s 1] x).1 = c)
    (hrec : ∀ j, (f^[s (j + 2)] x).1 = t * (f^[s (j + 1)] x).1 - (f^[s j] x).1) :
    ¬ ∃ B : 𝕜, ∀ k : ℕ, (f^[k] x).1 ^ 2 + (f^[k] x).2 ^ 2 ≤ B := by
  rintro ⟨B, hB⟩
  have hg := growth_sq_of_two_le (fun j => (f^[s j] x).1) t ht h0 hrec
  obtain ⟨j, hj⟩ := exists_gt_sq (fun j => (f^[s j] x).1) c hc
    (fun j => by have h := hg j; rw [h1] at h; exact h) B
  have h := hB (s j)
  nlinarith [sq_nonneg (f^[s j] x).2]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The first number of an orbit of the Pair of one place keeps the recurrence of its trace. -/
theorem pairOne_rec (σ ℓ : 𝕜) (x : 𝕜 × 𝕜) (k : ℕ) :
    ((pairOne σ ℓ)^[k + 2] x).1 =
      (2 - ℓ * σ) * ((pairOne σ ℓ)^[k + 1] x).1 - ((pairOne σ ℓ)^[k] x).1 := by
  rw [show k + 2 = (k + 1) + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply']
  simp only [pairOne]
  ring

/-- WN4. The window: the Pair of one place keeps every orbit bounded exactly when
`0 < ℓ σ < 4`, or `ℓ = σ = 0`. -/
theorem bounded_iff_window [Archimedean 𝕜] (σ ℓ : 𝕜) :
    OrbitsBounded (pairOne σ ℓ) ↔ (0 < ℓ * σ ∧ ℓ * σ < 4) ∨ (ℓ = 0 ∧ σ = 0) := by
  constructor
  · intro hb
    by_contra hw
    rcases eq_or_ne ℓ 0 with hl | hl
    · have hs : σ ≠ 0 := fun hs => hw (Or.inr ⟨hl, hs⟩)
      subst hl
      have horbit : ∀ k : ℕ, (pairOne σ 0)^[k] (1, 0) = (1, (k : 𝕜) * σ) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Function.iterate_succ_apply', ih, pairOne]
          push_cast
          ext <;> dsimp only <;> ring
      obtain ⟨B, hB⟩ := hb (1, 0)
      obtain ⟨j, hj⟩ := exists_gt_sq (fun k => ((pairOne σ 0)^[k] (1, 0)).2) σ hs
        (fun j => by simp [horbit]) B
      have h := hB j
      simp only [horbit] at hj h
      nlinarith
    · have hnw : ℓ * σ ≤ 0 ∨ 4 ≤ ℓ * σ := by
        by_contra hc
        push Not at hc
        exact hw (Or.inl ⟨hc.1, hc.2⟩)
      have hu0 : ((pairOne σ ℓ)^[0] (0, 1)).1 = 0 := rfl
      have hu1 : ((pairOne σ ℓ)^[1] (0, 1)).1 = -ℓ := by simp [pairOne]
      rcases hnw with hn | hn
      · exact not_bounded_of_growth (pairOne σ ℓ) (0, 1) (fun j => j) (2 - ℓ * σ) (-ℓ)
          (by linarith) (neg_ne_zero.mpr hl) hu0 hu1 (fun j => pairOne_rec σ ℓ (0, 1) j)
          (hb (0, 1))
      · have ht : 2 - ℓ * σ ≤ -2 := by linarith
        have hw1 : ((pairOne σ ℓ)^[2 * 1] (0, 1)).1 = (2 - ℓ * σ) * -ℓ := by
          have h := pairOne_rec σ ℓ (0, 1) 0
          rw [hu1, hu0] at h
          rw [show 2 * 1 = 0 + 2 from rfl, h]
          ring
        have hwrec : ∀ j, ((pairOne σ ℓ)^[2 * (j + 2)] (0, 1)).1 =
            ((2 - ℓ * σ) ^ 2 - 2) * ((pairOne σ ℓ)^[2 * (j + 1)] (0, 1)).1 -
              ((pairOne σ ℓ)^[2 * j] (0, 1)).1 := by
          intro j
          have e1 : ((pairOne σ ℓ)^[2 * j + 2 + 2] (0, 1)).1 =
              (2 - ℓ * σ) * ((pairOne σ ℓ)^[2 * j + 2 + 1] (0, 1)).1 -
                ((pairOne σ ℓ)^[2 * j + 2] (0, 1)).1 := pairOne_rec σ ℓ (0, 1) (2 * j + 2)
          have e2 : ((pairOne σ ℓ)^[2 * j + 2 + 1] (0, 1)).1 =
              (2 - ℓ * σ) * ((pairOne σ ℓ)^[2 * j + 2] (0, 1)).1 -
                ((pairOne σ ℓ)^[2 * j + 1] (0, 1)).1 := pairOne_rec σ ℓ (0, 1) (2 * j + 1)
          have e3 : ((pairOne σ ℓ)^[2 * j + 2] (0, 1)).1 =
              (2 - ℓ * σ) * ((pairOne σ ℓ)^[2 * j + 1] (0, 1)).1 -
                ((pairOne σ ℓ)^[2 * j] (0, 1)).1 := pairOne_rec σ ℓ (0, 1) (2 * j)
          rw [show 2 * (j + 2) = 2 * j + 2 + 2 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
          linear_combination e1 + (2 - ℓ * σ) * e2 + e3
        have hne : (2 - ℓ * σ) * -ℓ ≠ 0 :=
          mul_ne_zero (by intro h0; linarith) (neg_ne_zero.mpr hl)
        exact not_bounded_of_growth (pairOne σ ℓ) (0, 1) (fun j => 2 * j)
          ((2 - ℓ * σ) ^ 2 - 2) ((2 - ℓ * σ) * -ℓ) (by nlinarith) hne hu0 hw1 hwrec (hb (0, 1))
  · rintro (h | ⟨rfl, rfl⟩)
    · exact bounded_of_window σ ℓ h
    · intro x
      refine ⟨x.1 ^ 2 + x.2 ^ 2, fun k => ?_⟩
      have hx : (pairOne (0 : 𝕜) 0)^[k] x = x := Function.iterate_fixed (by simp [pairOne]) k
      simp only [hx, le_refl]

end OnePlace

end Artform.Stages
