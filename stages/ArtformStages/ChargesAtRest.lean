import ArtformStages.Coulomb

/-!
# The energy of two charges at rest (finding 493)

Wave N3 of campaign 15 of road DP. Finding 444 solved Coulomb's problem on a board: a charge that
sums to `0` is the divergence of a still field, the gradient of a potential. Here the energy of
that field is found. The divergence is the ledger's, `divergence G E = -(Gᵀ E)` (`Maxwell.lean`);
the energy of a field `E` with the weight `l ℓ` on the line `ℓ` is `Σ l E²`; the Coulomb field of a
potential `φ` is `-(G φ) / l`, whose divergence is finding 444's Laplacian of `φ`.

* `fieldEnergy`, `coulombField`, `thomson_split` (CR1): a field with the divergence of the Coulomb
  field has the Coulomb field's energy plus the energy of their difference;
* `coulombField_energy` (CR2): the Coulomb field's energy is `φ ⬝ ρ`, `ρ` its divergence;
* `thomson_least`, `thomson_eq_iff` (CR3): with positive weights every field with the divergence
  `ρ` has at least that energy, and only the Coulomb field has it: Thomson's principle;
* `pair_least_energy`, `Board.pair_least` (CR4): for a pair of opposite clicks at `a` and `b` the
  least energy is `φ a - φ b`, and on a board whose corners are joined such a `φ` exists;
* `coulombField_still` (CR5): with no field on the squares Pair keeps the Coulomb field and moves
  the potential by a change of gauge: the pair is still;
* `whole_field_energy` (CR6): a field of whole counts with the divergence `ρ` has `Σ E² ≥ π ⬝ ρ` for
  every `π` that changes by at most one along each line: for a pair, the distance on the board.

None of this is new: it is Thomson's principle of least energy for a network of resistors, and the
energy of a flow of whole units, at least the length of a path.
-/

open Matrix

namespace Artform.Stages

section ChargesAtRest

variable {e v : Type*} [Fintype e] [Fintype v]

/-- **The energy of a field** `E` on the lines, with the weight `l ℓ` on the line `ℓ`: `Σ l E²`. -/
def fieldEnergy (l : e → ℝ) (E : e → ℝ) : ℝ := ∑ ℓ, l ℓ * E ℓ ^ 2

/-- **The Coulomb field** of a potential `φ`: on each line, minus the potential's step `G φ`, over
the line's weight. -/
noncomputable def coulombField (G : Matrix e v ℝ) (l : e → ℝ) (φ : v → ℝ) : e → ℝ :=
  fun ℓ => -(G *ᵥ φ) ℓ / l ℓ

omit [Fintype e] in
/-- On every line, the weight times the Coulomb field is minus the potential's step. -/
theorem weight_mul_coulombField (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, l ℓ ≠ 0) (φ : v → ℝ)
    (ℓ : e) : l ℓ * coulombField G l φ ℓ = -(G *ᵥ φ) ℓ := by
  rw [coulombField]
  field_simp [hl ℓ]

/-- The step of a potential against a field is the potential against minus the field's
divergence. -/
theorem sum_step_mul (G : Matrix e v ℝ) (φ : v → ℝ) (D : e → ℝ) :
    ∑ ℓ, (G *ᵥ φ) ℓ * D ℓ = -(φ ⬝ᵥ divergence G D) := by
  rw [divergence, dotProduct_neg, neg_neg, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- CR1. **The energy splits**: a field with the divergence of the Coulomb field of `φ` has the
Coulomb field's energy plus the energy of their difference. -/
theorem thomson_split (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, l ℓ ≠ 0) (φ : v → ℝ)
    (E : e → ℝ) (hE : divergence G E = divergence G (coulombField G l φ)) :
    fieldEnergy l E =
      fieldEnergy l (coulombField G l φ) + fieldEnergy l (E - coulombField G l φ) := by
  set c := coulombField G l φ with hc
  have hD : divergence G (E - c) = 0 := by
    rw [divergence, divergence] at hE
    rw [divergence, Matrix.mulVec_sub, neg_sub, ← neg_neg (Gᵀ *ᵥ E), hE, neg_neg, sub_self]
  have hcross : ∑ ℓ, l ℓ * c ℓ * (E - c) ℓ = 0 := by
    have h1 : ∀ ℓ, l ℓ * c ℓ * (E - c) ℓ = -((G *ᵥ φ) ℓ * (E - c) ℓ) := fun ℓ => by
      rw [hc, weight_mul_coulombField G l hl φ ℓ]
      ring
    rw [Finset.sum_congr rfl fun ℓ _ => h1 ℓ, Finset.sum_neg_distrib, sum_step_mul, hD,
      dotProduct_zero, neg_zero, neg_zero]
  have h2 : ∀ ℓ, l ℓ * E ℓ ^ 2 =
      l ℓ * c ℓ ^ 2 + l ℓ * (E - c) ℓ ^ 2 + 2 * (l ℓ * c ℓ * (E - c) ℓ) := fun ℓ => by
    rw [Pi.sub_apply]
    ring
  rw [fieldEnergy, Finset.sum_congr rfl fun ℓ _ => h2 ℓ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]
  rfl

/-- CR2. **The Coulomb field's energy** is the potential against its divergence. -/
theorem coulombField_energy (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, l ℓ ≠ 0) (φ : v → ℝ) :
    fieldEnergy l (coulombField G l φ) = φ ⬝ᵥ divergence G (coulombField G l φ) := by
  have h : ∀ ℓ, l ℓ * coulombField G l φ ℓ ^ 2 =
      -((G *ᵥ φ) ℓ * coulombField G l φ ℓ) := fun ℓ => by
    rw [sq, ← mul_assoc, weight_mul_coulombField G l hl φ ℓ]
    ring
  rw [fieldEnergy, Finset.sum_congr rfl fun ℓ _ => h ℓ, Finset.sum_neg_distrib, sum_step_mul,
    neg_neg]

/-- With positive weights a field's energy is not below `0`. -/
theorem fieldEnergy_nonneg (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (E : e → ℝ) : 0 ≤ fieldEnergy l E :=
  Finset.sum_nonneg fun ℓ _ => mul_nonneg (hl ℓ).le (sq_nonneg _)

/-- With positive weights a field's energy is `0` only for the field `0`. -/
theorem fieldEnergy_eq_zero_iff (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (E : e → ℝ) :
    fieldEnergy l E = 0 ↔ E = 0 := by
  rw [fieldEnergy,
    Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => mul_nonneg (hl ℓ).le (sq_nonneg _)]
  constructor
  · intro h
    funext ℓ
    have := h ℓ (Finset.mem_univ ℓ)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (hl ℓ).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  · rintro rfl ℓ _
    simp

/-- CR3. **Thomson's principle**: with positive weights, every field with the divergence `ρ` of the
Coulomb field of `φ` has at least the energy `φ ⬝ ρ`. -/
theorem thomson_least (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (φ : v → ℝ)
    (ρ : v → ℝ) (hφ : divergence G (coulombField G l φ) = ρ) (E : e → ℝ)
    (hE : divergence G E = ρ) : φ ⬝ᵥ ρ ≤ fieldEnergy l E := by
  have hl' : ∀ ℓ, l ℓ ≠ 0 := fun ℓ => (hl ℓ).ne'
  rw [thomson_split G l hl' φ E (hE.trans hφ.symm), coulombField_energy G l hl' φ, hφ]
  linarith [fieldEnergy_nonneg l hl (E - coulombField G l φ)]

/-- CR3. **Only the Coulomb field has the least energy.** -/
theorem thomson_eq_iff (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (φ : v → ℝ)
    (ρ : v → ℝ) (hφ : divergence G (coulombField G l φ) = ρ) (E : e → ℝ)
    (hE : divergence G E = ρ) : fieldEnergy l E = φ ⬝ᵥ ρ ↔ E = coulombField G l φ := by
  have hl' : ∀ ℓ, l ℓ ≠ 0 := fun ℓ => (hl ℓ).ne'
  rw [thomson_split G l hl' φ E (hE.trans hφ.symm), coulombField_energy G l hl' φ, hφ,
    add_eq_left, fieldEnergy_eq_zero_iff l hl, sub_eq_zero]

/-- CR4. **For a pair of opposite clicks** at `a` and `b` the least energy is the potential's
difference `φ a - φ b`. -/
theorem pair_least_energy [DecidableEq v] (G : Matrix e v ℝ) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ)
    (φ : v → ℝ) (a b : v)
    (hφ : divergence G (coulombField G l φ) = Pi.single a 1 - Pi.single b 1) (E : e → ℝ)
    (hE : divergence G E = Pi.single a 1 - Pi.single b 1) :
    φ a - φ b ≤ fieldEnergy l E ∧ (fieldEnergy l E = φ a - φ b ↔ E = coulombField G l φ) := by
  have h : φ ⬝ᵥ (Pi.single a 1 - Pi.single b 1) = φ a - φ b := by
    rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  rw [← h]
  exact ⟨thomson_least G l hl φ _ hφ E hE, thomson_eq_iff G l hl φ _ hφ E hE⟩

/-- CR4. **On a board whose corners are joined**, with positive weights, every pair of opposite
clicks has a potential whose Coulomb field has the least energy `φ a - φ b`, and only it. -/
theorem Board.pair_least {f : Type*} [DecidableEq v] [Nonempty v]
    (B : Board f e v) (hJ : B.CornersJoined) (l : e → ℝ) (hl : ∀ ℓ, 0 < l ℓ) (a b : v) :
    ∃ φ : v → ℝ, ∀ E : e → ℝ, divergence B.gauge E = Pi.single a 1 - Pi.single b 1 →
      φ a - φ b ≤ fieldEnergy l E ∧
        (fieldEnergy l E = φ a - φ b ↔ E = coulombField B.gauge l φ) := by
  classical
  have hsum : ∑ w, (Pi.single a 1 - Pi.single b 1 : v → ℝ) w = 0 := by
    simp [Finset.sum_sub_distrib]
  obtain ⟨φ, hφ⟩ := (B.coulomb hJ l hl _).mpr hsum
  refine ⟨φ, fun E hE => pair_least_energy B.gauge l hl φ a b ?_ E hE⟩
  rw [← hφ, Board.laplacian, divergence]
  have hc : coulombField B.gauge l φ = -(diagonal (fun ℓ => 1 / l ℓ) *ᵥ (B.gauge *ᵥ φ)) := by
    funext ℓ
    rw [coulombField, Pi.neg_apply, Matrix.mulVec_diagonal]
    ring
  rw [hc, Matrix.mulVec_neg, neg_neg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- CR5. **The pair is still**: where `C G = 0` and the potential has no field on the squares,
Pair with the kick `Cᵀ K C` and the drift `diag(l)` keeps the Coulomb field and moves the potential
by `G φ`, a change of gauge, which leaves it with no field on the squares. -/
theorem coulombField_still {f : Type*} [Fintype f] [DecidableEq e] (G : Matrix e v ℝ)
    (C : Matrix f e ℝ) (hCG : C * G = 0) (K : Matrix f f ℝ) (l : e → ℝ) (hl : ∀ ℓ, l ℓ ≠ 0)
    (φ : v → ℝ) (A : e → ℝ) (hA : C *ᵥ A = 0) :
    pair (Cᵀ * K * C) (diagonal l) (A, coulombField G l φ) = (A + G *ᵥ φ, coulombField G l φ) ∧
      C *ᵥ (A + G *ᵥ φ) = 0 := by
  have hS : (Cᵀ * K * C) *ᵥ A = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  have hL : diagonal l *ᵥ coulombField G l φ = -(G *ᵥ φ) := by
    funext ℓ
    rw [Matrix.mulVec_diagonal, weight_mul_coulombField G l hl φ ℓ, Pi.neg_apply]
  refine ⟨?_, ?_⟩
  · rw [pair, hS, add_zero, hL, sub_neg_eq_add]
  · rw [Matrix.mulVec_add, hA, Matrix.mulVec_mulVec, hCG, Matrix.zero_mulVec, zero_add]

/-- CR6. **A field of whole counts** with the divergence `ρ` has `Σ E² ≥ π ⬝ ρ` for every `π` that
changes by at most one along each line. -/
theorem whole_field_energy (G : Matrix e v ℝ) (ρ : v → ℝ) (E : e → ℤ)
    (hE : divergence G (fun ℓ => (E ℓ : ℝ)) = ρ) (π : v → ℝ) (hπ : ∀ ℓ, |(G *ᵥ π) ℓ| ≤ 1) :
    π ⬝ᵥ ρ ≤ ∑ ℓ, ((E ℓ : ℝ)) ^ 2 := by
  have h := sum_step_mul G π (fun ℓ => (E ℓ : ℝ))
  rw [hE] at h
  rw [show π ⬝ᵥ ρ = ∑ ℓ, -((G *ᵥ π) ℓ * (E ℓ : ℝ)) by rw [Finset.sum_neg_distrib, h, neg_neg]]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  have h1 : -((G *ᵥ π) ℓ * (E ℓ : ℝ)) ≤ |(E ℓ : ℝ)| := by
    calc -((G *ᵥ π) ℓ * (E ℓ : ℝ)) ≤ |(G *ᵥ π) ℓ * (E ℓ : ℝ)| := neg_le_abs _
      _ = |(G *ᵥ π) ℓ| * |(E ℓ : ℝ)| := abs_mul _ _
      _ ≤ 1 * |(E ℓ : ℝ)| := mul_le_mul_of_nonneg_right (hπ ℓ) (abs_nonneg _)
      _ = |(E ℓ : ℝ)| := one_mul _
  have h2 : |(E ℓ : ℝ)| ≤ (E ℓ : ℝ) ^ 2 := by
    have h3 : |E ℓ| ≤ |E ℓ| ^ 2 := Int.le_self_sq _
    rw [sq_abs] at h3
    exact_mod_cast h3
  linarith

end ChargesAtRest

end Artform.Stages
