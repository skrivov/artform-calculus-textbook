import ArtformScores.Statements

/-!
# Ringing on a lattice only transports

The ledger's finding 082 reads Theorem K of finding 016 for ringing: a linear permutation law can
only transport. Theorem K rests on Laurent's theorem on torsion points, which Mathlib does not have.
For permutation laws no such tool is needed. A permutation of `Λ × Fin c` that commutes with the
shifts is `(z, i) ↦ (z + n i, π i)`, with `π` a permutation of the channels. So `q = ord π` brings
each channel back to itself, shifted by the sum of `n` along its cycle.
-/

namespace Artform.Scores.Bells

open Equiv

variable {Λ : Type*} [AddCommGroup Λ] {c : ℕ}

theorem exists_transport (σ : Perm (Λ × Fin c))
    (hσ : ∀ w z i, σ (z + w, i) = ((σ (z, i)).1 + w, (σ (z, i)).2)) :
    ∃ (q : ℕ) (v : Fin c → Λ), 0 < q ∧ ∀ z i, (σ ^ q) (z, i) = (z + v i, i) := by
  -- the channels and the shifts
  let n : Fin c → Λ := fun i => (σ (0, i)).1
  let f : Fin c → Fin c := fun i => (σ (0, i)).2
  have hform : ∀ z i, σ (z, i) = (z + n i, f i) := by
    intro z i
    have := hσ z 0 i
    rw [zero_add] at this
    rw [this, add_comm]
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 := hform (n j) i
    have h2 := hform (n i) j
    have : σ (n j, i) = σ (n i, j) := by
      rw [h1, h2, add_comm, hij]
    have h3 := σ.injective this
    exact congrArg Prod.snd h3
  let π : Perm (Fin c) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hπ : ∀ i, π i = f i := fun _ => rfl
  -- the iterates
  let w : ℕ → Fin c → Λ := fun k i => ∑ t ∈ Finset.range k, n ((π ^ t) i)
  have hiter : ∀ (k : ℕ) (z : Λ) (i : Fin c), (σ ^ k) (z, i) = (z + w k i, (π ^ k) i) := by
    intro k
    induction k with
    | zero => simp [w]
    | succ k ih =>
      intro z i
      rw [pow_succ', Perm.mul_apply, ih, hform, pow_succ' π, Perm.mul_apply, hπ]
      simp only [w, Finset.sum_range_succ, add_assoc]
  refine ⟨orderOf π, w (orderOf π), orderOf_pos π, fun z i => ?_⟩
  rw [hiter, pow_orderOf_eq_one]
  rfl

end Artform.Scores.Bells

namespace Artform.Scores

/-- **T15** (ringing on a lattice only transports). -/
@[ledger "T15"]
theorem permutationLawsTransport : Statement.permutationLawsTransport := by
  intro Λ _ c σ hσ
  obtain ⟨q, v, hq, h⟩ := Bells.exists_transport σ hσ
  refine ⟨q, v, hq, h, fun R u z i => ?_⟩
  rw [← h]
  simp

/-! ## Non-vacuity

- Two-dimensional ringing on `ℤ²`, with two channels that swap as they step: the first channel
  steps along `x`, the second along `y`. Two ticks shift each channel by `(1, 1)`.
- Plain hunt on a line of bells, blocked by the even cells: `(z, 0) ↦ (z + 1, 0)` and
  `(z, 1) ↦ (z - 1, 1)`, right- and left-moving light.
-/

/-- Two-dimensional ringing: `(z, 0) ↦ (z + e₁, 1)` and `(z, 1) ↦ (z + e₂, 0)`. -/
def ring2D : Equiv.Perm ((ℤ × ℤ) × Fin 2) where
  toFun p := if p.2 = 0 then (p.1 + (1, 0), 1) else (p.1 + (0, 1), 0)
  invFun p := if p.2 = 1 then (p.1 - (1, 0), 0) else (p.1 - (0, 1), 1)
  left_inv p := by
    obtain ⟨z, i⟩ := p
    fin_cases i <;> simp
  right_inv p := by
    obtain ⟨z, i⟩ := p
    fin_cases i <;> simp

/-- The two-dimensional law commutes with the shifts, and two ticks shift both channels by
`(1, 1)`. -/
example : (∀ w z i, ring2D (z + w, i) = ((ring2D (z, i)).1 + w, (ring2D (z, i)).2)) ∧
    ∀ z i, (ring2D ^ 2) (z, i) = (z + (1, 1), i) := by
  constructor
  · intro w z i
    fin_cases i <;> simp [ring2D, add_right_comm]
  · intro z i
    fin_cases i <;> simp [ring2D, pow_two, add_assoc]

end Artform.Scores
