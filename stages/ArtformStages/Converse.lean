import ArtformStages.Bounded

/-!
# The window is exact

Finding 436 of the research ledger on a layered universe proved that inside the window
`4 L⁻¹ - S` every orbit of Pair whose `E` is `S w` is bounded. Here is the converse: a level of
`L S` below `0`, or at `4` or more, has an orbit that starts with `E = S w` and grows. So the
window is exact, on any number of places and on every board (finding 438).

* `pair_iterate_on_pair_level` (BG1): along a level `L S v = μ v`, Pair is the Pair of one place
  with `σ = 1` and `λ = μ`, at every step.
* `exists_not_orbitBounded_of_level` (BG2): a level `μ < 0` or `4 ≤ μ` has an orbit from some
  `(A, S w)` that is not bounded.
* `orbit_bounded_iff_window` (BG3): with `S` positive semidefinite and `L = D D`, every orbit with
  `E = S w` is bounded exactly when `4 D' D' - S` is positive definite.
* `Board.orbit_bounded_iff` (BG4): on a board, exactly when `diag (4 / λ) - Cᵀ diag κ C` is.
-/

open Matrix

namespace Artform.Stages

section Converse

variable {n : Type*} [Fintype n]

/-- BG1. Along a level of the pair `(S, L)`, `L S v = μ v`, the orbit of Pair from `(a v, e S v)`
is the orbit of the Pair of one place with `σ = 1` and `λ = μ`, carried by `v` and `S v`. -/
theorem pair_iterate_on_pair_level (S L : Matrix n n ℝ) (v : n → ℝ) (μ : ℝ)
    (hv : L *ᵥ (S *ᵥ v) = μ • v) (x : ℝ × ℝ) (k : ℕ) :
    (pair S L)^[k] (x.1 • v, x.2 • (S *ᵥ v)) =
      (((pairOne 1 μ)^[k] x).1 • v, ((pairOne 1 μ)^[k] x).2 • (S *ᵥ v)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have e1 : pairOne 1 μ x = (x.1 - μ * (x.2 + x.1), x.2 + x.1) := by simp [pairOne]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pair_on_pair_level S L v μ hv,
      e1]
    exact ih (x.1 - μ * (x.2 + x.1), x.2 + x.1)

/-- BG2. A level of `L S` below `0`, or at `4` or more, has an orbit that starts with `E = S w`
and is not bounded. -/
theorem exists_not_orbitBounded_of_level (S L : Matrix n n ℝ) (v : n → ℝ) (μ : ℝ)
    (hv : L *ᵥ (S *ᵥ v) = μ • v) (hv0 : v ≠ 0) (hμ : μ < 0 ∨ 4 ≤ μ) :
    ∃ A w : n → ℝ, ¬ OrbitBounded (pair S L) (A, S *ᵥ w) := by
  -- the Pair of one place on that level has an orbit that is not bounded
  have hnb : ¬ OrbitsBounded (pairOne (1 : ℝ) μ) := by
    rw [bounded_iff_window]
    rintro (⟨h0, h4⟩ | ⟨_, h1⟩)
    · rw [mul_one] at h0 h4
      rcases hμ with hμ | hμ <;> linarith
    · exact one_ne_zero h1
  simp only [OrbitsBounded, not_forall, not_exists, not_le] at hnb
  obtain ⟨x, hx⟩ := hnb
  -- `v` and `S v` each have an entry that is not `0`
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rcases hμ with hμ | hμ <;> linarith
  have hSv : S *ᵥ v ≠ 0 := by
    intro h
    apply hv0
    have hz : μ • v = 0 := by rw [← hv, h, mulVec_zero]
    exact (smul_eq_zero.mp hz).resolve_left hμ0
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨i, hi⟩ : ∃ i, (S *ᵥ v) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hSv (funext h)
  refine ⟨x.1 • v, x.2 • v, ?_⟩
  rw [mulVec_smul]
  rintro ⟨B, hB⟩
  have hvj : 0 < |v j| := abs_pos.mpr hj
  have hsi : 0 < |(S *ᵥ v) i| := abs_pos.mpr hi
  obtain ⟨k, hk⟩ := hx ((B / |v j|) ^ 2 + (B / |(S *ᵥ v) i|) ^ 2)
  have h1 := (hB k j).1
  have h2 := (hB k i).2
  rw [pair_iterate_on_pair_level S L v μ hv x k] at h1 h2
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul] at h1 h2
  have ha : |((pairOne 1 μ)^[k] x).1| ≤ B / |v j| := by rw [le_div_iff₀ hvj]; exact h1
  have he : |((pairOne 1 μ)^[k] x).2| ≤ B / |(S *ᵥ v) i| := by rw [le_div_iff₀ hsi]; exact h2
  have ha2 : ((pairOne 1 μ)^[k] x).1 ^ 2 ≤ (B / |v j|) ^ 2 := by
    nlinarith [abs_nonneg ((pairOne 1 μ)^[k] x).1, sq_abs ((pairOne 1 μ)^[k] x).1]
  have he2 : ((pairOne 1 μ)^[k] x).2 ^ 2 ≤ (B / |(S *ᵥ v) i|) ^ 2 := by
    nlinarith [abs_nonneg ((pairOne 1 μ)^[k] x).2, sq_abs ((pairOne 1 μ)^[k] x).2]
  linarith

variable [DecidableEq n]

/-- BG3. The window is exact: with `S` positive semidefinite and `L = D D` for a symmetric `D`
with an inverse `D'`, every orbit of Pair that starts with `E = S w` is bounded exactly when
`4 D' D' - S` is positive definite. -/
theorem orbit_bounded_iff_window (S D D' : Matrix n n ℝ) (hS : S.PosSemidef) (hD : Dᵀ = D)
    (h1 : D * D' = 1) (h2 : D' * D = 1) :
    (∀ A w : n → ℝ, OrbitBounded (pair S (D * D)) (A, S *ᵥ w)) ↔
      ((4 : ℝ) • (D' * D') - S).PosDef := by
  refine ⟨fun hb => ?_, fun hW A w => orbit_bounded_of_window S D D' hS hD h1 h2 hW A w⟩
  by_contra hW
  have hDh : Dᴴ = D := by rw [conjTranspose_eq_transpose_of_trivial, hD]
  have hMp : (D * S * D).PosSemidef := by
    simpa only [hDh] using hS.conjTranspose_mul_mul_same D
  obtain ⟨U, hUtU, hUUt, hMU⟩ := exists_orthogonal_diag _ hMp.1
  set μ := hMp.1.eigenvalues
  -- some level of `D S D` is at least `4`: else `4 D' D' - S` is positive definite
  obtain ⟨j, hj⟩ : ∃ j, 4 ≤ μ j := by
    by_contra h
    push Not at h
    apply hW
    have hD' : D'ᵀ = D' := by
      calc D'ᵀ = D'ᵀ * (D * D') := by rw [h1, Matrix.mul_one]
        _ = (D'ᵀ * Dᵀ) * D' := by rw [hD, Matrix.mul_assoc]
        _ = D' := by rw [← transpose_mul, h1, transpose_one, Matrix.one_mul]
    have hdiag : (diagonal fun i => 4 - μ i).PosDef :=
      posDef_diagonal_iff.mpr fun i => by linarith [h i]
    have hinj : Function.Injective (Uᵀ * D').mulVec := by
      intro x y hxy
      have e0 : D * U * (Uᵀ * D') = 1 := by
        calc D * U * (Uᵀ * D') = D * (U * Uᵀ) * D' := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hUUt, Matrix.mul_one, h1]
      have h := congrArg (fun z => (D * U) *ᵥ z) hxy
      simpa only [mulVec_mulVec, e0, one_mulVec] using h
    have hP := hdiag.conjTranspose_mul_mul_same hinj
    have e1 : (Uᵀ * D')ᴴ = D' * U := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose, hD']
    have e2 : (diagonal fun i => 4 - μ i) = (4 : ℝ) • (1 : Matrix n n ℝ) - diagonal μ := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · simp [one_apply, hab]
    have e3 : U * diagonal μ * Uᵀ = D * S * D := by
      rw [← hMU, Matrix.mul_assoc, hUUt, Matrix.mul_one]
    have e4 : D' * (D * S * D) * D' = S := by
      calc D' * (D * S * D) * D' = (D' * D) * S * (D * D') := by simp only [Matrix.mul_assoc]
        _ = S := by rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
    have key : (Uᵀ * D')ᴴ * (diagonal fun i => 4 - μ i) * (Uᵀ * D') =
        (4 : ℝ) • (D' * D') - S := by
      rw [e1, e2]
      calc D' * U * ((4 : ℝ) • 1 - diagonal μ) * (Uᵀ * D')
          = (4 : ℝ) • (D' * (U * Uᵀ) * D') - D' * (U * diagonal μ * Uᵀ) * D' := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_one, Matrix.mul_assoc]
        _ = (4 : ℝ) • (D' * D') - S := by rw [hUUt, Matrix.mul_one, e3, e4]
    rwa [key] at hP
  -- that level of `D S D` gives a level of `L S`, along `D u`
  have hu : (D * S * D) *ᵥ (fun i => U i j) = μ j • (fun i => U i j) := by
    ext i
    have h := congrFun (congrFun hMU i) j
    rw [mul_diagonal, Matrix.mul_apply] at h
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h, mul_comm]
  have hu0 : (fun i => U i j) ≠ 0 := by
    intro h0
    have h := congrFun (congrFun hUtU j) j
    rw [Matrix.mul_apply, one_apply_eq] at h
    simp only [transpose_apply] at h
    have hz : ∀ i, U i j = 0 := fun i => congrFun h0 i
    simp [hz] at h
  have hv : (D * D) *ᵥ (S *ᵥ (D *ᵥ fun i => U i j)) = μ j • (D *ᵥ fun i => U i j) := by
    calc (D * D) *ᵥ (S *ᵥ (D *ᵥ fun i => U i j)) = D *ᵥ ((D * S * D) *ᵥ fun i => U i j) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = μ j • (D *ᵥ fun i => U i j) := by rw [hu, mulVec_smul]
  have hv0 : (D *ᵥ fun i => U i j) ≠ 0 := by
    intro h0
    apply hu0
    have h := congrArg (fun z => D' *ᵥ z) h0
    simpa only [mulVec_mulVec, h2, one_mulVec, mulVec_zero] using h
  obtain ⟨A, w, hAw⟩ := exists_not_orbitBounded_of_level S (D * D) _ (μ j) hv hv0 (Or.inr hj)
  exact hAw (hb A w)

end Converse

/-- BG4. On a board, with `κ > 0` and `λ > 0`, every orbit of Pair whose `E` is `S w` is bounded
exactly when `diag (4 / λ) - Cᵀ diag κ C` is positive definite. -/
theorem Board.orbit_bounded_iff {f e v : Type*} [Fintype f] [Fintype e] [DecidableEq f]
    [DecidableEq e] (B : Board f e v) (κ : f → ℝ) (l : e → ℝ) (hκ : ∀ σ, 0 < κ σ)
    (hl : ∀ ℓ, 0 < l ℓ) :
    (∀ A w : e → ℝ, OrbitBounded (pair (B.incidenceᵀ * diagonal κ * B.incidence) (diagonal l))
        (A, (B.incidenceᵀ * diagonal κ * B.incidence) *ᵥ w)) ↔
      ((diagonal fun ℓ => 4 / l ℓ) - B.incidenceᵀ * diagonal κ * B.incidence).PosDef := by
  have hS : (B.incidenceᵀ * diagonal κ * B.incidence).PosSemidef := by
    have h0 := (PosSemidef.diagonal (fun σ => (hκ σ).le) :
      (diagonal κ).PosSemidef).conjTranspose_mul_mul_same B.incidence
    rwa [conjTranspose_eq_transpose_of_trivial] at h0
  have hs : ∀ ℓ, 0 < Real.sqrt (l ℓ) := fun ℓ => Real.sqrt_pos.mpr (hl ℓ)
  have h1 : (diagonal fun ℓ => Real.sqrt (l ℓ)) * (diagonal fun ℓ => 1 / Real.sqrt (l ℓ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext ℓ
    field_simp [(hs ℓ).ne']
  have h2 : (diagonal fun ℓ => 1 / Real.sqrt (l ℓ)) * (diagonal fun ℓ => Real.sqrt (l ℓ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext ℓ
    field_simp [(hs ℓ).ne']
  have hDD : (diagonal fun ℓ => Real.sqrt (l ℓ)) * (diagonal fun ℓ => Real.sqrt (l ℓ)) =
      diagonal l := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext ℓ
    exact Real.mul_self_sqrt (hl ℓ).le
  have e1 : (4 : ℝ) • ((diagonal fun ℓ => 1 / Real.sqrt (l ℓ)) *
      (diagonal fun ℓ => 1 / Real.sqrt (l ℓ))) = diagonal fun ℓ => 4 / l ℓ := by
    ext i j
    simp only [diagonal_mul_diagonal, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (hl i).le]
      ring
    · simp
  rw [← hDD, ← e1]
  exact orbit_bounded_iff_window _ _ _ hS (diagonal_transpose _) h1 h2

end Artform.Stages
