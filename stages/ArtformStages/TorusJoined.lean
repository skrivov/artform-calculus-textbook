import ArtformStages.BookBoard
import ArtformStages.Coulomb

/-!
# The torus is joined

Finding 453 of the research ledger on a layered universe showed the torus wide and of one paint.
Here its squares and its corners are shown joined (finding 454 of the ledger), so that each kick
the askings leave on it has exactly one weight, and Coulomb's problem is solved on it:

* `torus_joined`, `torus_corners_joined` (JN1, JN2): the squares of the torus are joined, and so
  are its corners;
* `torus_kick_unique`, `torus_kick_one_weight` (JN3, JN4): for `n, m ≥ 3` a kick of reach 1 that
  meets A10 and A11 is `Cᵀ diag K C` for exactly one `K`, and with one rule for exactly one `κ`;
* `torus_coulomb`, `torus_coulomb_unique`, `torus_coulomb_field` (JN5): Coulomb's problem on the
  torus.
-/

open Matrix

namespace Artform.Stages

variable (n m : ℕ) [NeZero n] [NeZero m]

/-- Each point of the torus is a point plus a whole number of steps along each axis. -/
theorem torus_point_steps (σ τ : ZMod n × ZMod m) :
    τ = σ + ((((τ - σ).1.val : ℕ) : ZMod n), (0 : ZMod m)) +
      ((0 : ZMod n), (((τ - σ).2.val : ℕ) : ZMod m)) := by
  simp [Prod.ext_iff]

/-- A relation that links each point of the torus to the next one along each axis links any two
points. -/
theorem torus_steps_join (R : ZMod n × ZMod m → ZMod n × ZMod m → Prop)
    (hr : ∀ σ, R σ (σ + (1, 0))) (hu : ∀ σ, R σ (σ + (0, 1))) (σ τ : ZMod n × ZMod m) :
    Relation.ReflTransGen R σ τ := by
  have right : ∀ (ρ : ZMod n × ZMod m) (k : ℕ),
      Relation.ReflTransGen R ρ (ρ + ((k : ZMod n), (0 : ZMod m))) := by
    intro ρ k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, Prod.mk_zero_zero, add_zero]
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      have e : ρ + (((k + 1 : ℕ) : ZMod n), (0 : ZMod m)) =
          ρ + ((k : ZMod n), (0 : ZMod m)) + (1, 0) := by
        simp [add_assoc]
      rw [e]
      exact ih.tail (hr _)
  have up : ∀ (ρ : ZMod n × ZMod m) (k : ℕ),
      Relation.ReflTransGen R ρ (ρ + ((0 : ZMod n), (k : ZMod m))) := by
    intro ρ k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, Prod.mk_zero_zero, add_zero]
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      have e : ρ + ((0 : ZMod n), ((k + 1 : ℕ) : ZMod m)) =
          ρ + ((0 : ZMod n), (k : ZMod m)) + (0, 1) := by
        simp [add_assoc]
      rw [e]
      exact ih.tail (hu _)
  rw [torus_point_steps n m σ τ]
  exact (right σ _).trans (up _ _)

/-- The torus of sides at least 3 has more than two squares. -/
theorem torus_card (hn : 2 < n) (hm : 2 < m) : 2 < Fintype.card (ZMod n × ZMod m) := by
  rw [Fintype.card_prod, ZMod.card, ZMod.card]
  have := Nat.mul_le_mul hn hm
  omega

variable [Fact (1 < n)] [Fact (1 < m)]

/-- **JN1.** The squares of the torus are joined: the square `σ` shares a side with `σ + (1, 0)`
and with `σ + (0, 1)`. -/
theorem torus_joined : (torus n m).Joined :=
  torus_steps_join n m _ (fun σ => ⟨1, 3, by simp [torus]⟩) (fun σ => ⟨2, 0, by simp [torus]⟩)

/-- **JN2.** The corners of the torus are joined: the corner `w` is joined to `w + (1, 0)` by the
line `(w, 0)` and to `w + (0, 1)` by the line `(w, 1)`. -/
theorem torus_corners_joined : (torus n m).CornersJoined :=
  torus_steps_join n m _ (fun w => ⟨(w, 0), Or.inl ⟨rfl, by simp [torus]⟩⟩)
    (fun w => ⟨(w, 1), Or.inl ⟨rfl, by simp [torus]⟩⟩)

/-- **JN3.** For `n, m ≥ 3`, a kick of reach 1 on the torus that is blind to a change at a corner
(A10) and keeps Gauss's law (A11) is `Cᵀ diag K C` for exactly one `K`. -/
theorem torus_kick_unique (hn : 2 < n) (hm : 2 < m)
    (M : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (hR : (torus n m).ReachOne M) (h10 : M * (torus n m).gauge = 0)
    (h11 : (torus n m).gaugeᵀ * M = 0) :
    ∃! K : ZMod n × ZMod m → ℝ, M = (torus n m).incidenceᵀ * diagonal K * (torus n m).incidence :=
  (torus n m).kick_forced_unique (torus_wide n m hn hm) (torus_joined n m) (torus_card n m hn hm) M
    hR h10 h11

/-- **JN4.** For `n, m ≥ 3`, such a kick that is also one rule for the far weights is
`Cᵀ diag κ C` for exactly one number `κ`. -/
theorem torus_kick_one_weight (hn : 2 < n) (hm : 2 < m)
    (M : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (hR : (torus n m).ReachOne M) (h10 : M * (torus n m).gauge = 0)
    (h11 : (torus n m).gaugeᵀ * M = 0) (h1 : (torus n m).OneRuleFar M) :
    ∃! κ : ℝ, M = (torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
      (torus n m).incidence := by
  obtain ⟨κ, hκ⟩ := torus_kick_forced n m hn hm M hR h10 h11 h1
  refine ⟨κ, hκ, fun κ' hκ' => ?_⟩
  have h := kick_injective _ (Board.joined_image (torus n m) (torus_joined n m))
    (torus_card n m hn hm) (hκ'.symm.trans hκ)
  exact congrFun h 0

/-- **JN5.** On the torus, with every `λ > 0`, a charge is `M φ` for some potential `φ` exactly
when it sums to `0`. -/
theorem torus_coulomb (l : (ZMod n × ZMod m) × Fin 2 → ℝ) (hl : ∀ ℓ, 0 < l ℓ)
    (ρ : ZMod n × ZMod m → ℝ) :
    (∃ φ : ZMod n × ZMod m → ℝ, (torus n m).laplacian l *ᵥ φ = ρ) ↔ ∑ w, ρ w = 0 :=
  (torus n m).coulomb (torus_corners_joined n m) l hl ρ

/-- **JN5.** There the potential is unique up to a constant. -/
theorem torus_coulomb_unique (l : (ZMod n × ZMod m) × Fin 2 → ℝ) (hl : ∀ ℓ, 0 < l ℓ)
    (φ ψ : ZMod n × ZMod m → ℝ) (h : (torus n m).laplacian l *ᵥ φ = (torus n m).laplacian l *ᵥ ψ)
    (a b : ZMod n × ZMod m) : φ a - ψ a = φ b - ψ b :=
  (torus n m).coulomb_unique (torus_corners_joined n m) l hl φ ψ h a b

/-- **JN5.** There a charge is the divergence of a still field exactly when it sums to `0`. -/
theorem torus_coulomb_field (l : (ZMod n × ZMod m) × Fin 2 → ℝ) (hl : ∀ ℓ, 0 < l ℓ)
    (ρ : ZMod n × ZMod m → ℝ) :
    (∃ E : (ZMod n × ZMod m) × Fin 2 → ℝ, divergence (torus n m).gauge E = ρ ∧
      ((torus n m).incidence * diagonal l) *ᵥ E = 0) ↔ ∑ w, ρ w = 0 :=
  (torus n m).coulomb_field (torus_corners_joined n m) l hl ρ

end Artform.Stages
