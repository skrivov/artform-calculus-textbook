import ArtformStages.Incidence
import ArtformStages.Relabel
import ArtformStages.Scale
import ArtformStages.Window

/-!
# The window holds the orbits

Finding 425 of the research ledger on a layered universe proved that the Pair of one place keeps
its orbits bounded exactly in its window, and finding 427 read the window of Pair on many places as
the positivity of `4 L⁻¹ - S`. Here the step from that positivity to bounded orbits is a theorem, on
any number of places and on every board (finding 436).

* `orbit_bounded_of_window` (BO1): with `S` positive semidefinite, `L = D D` for a symmetric `D`
  with an inverse `D'`, and `4 D' D' - S` positive definite, every orbit of Pair that starts at
  `(A, S w)` is bounded. The drift is scaled away (`pair_scale`), the kick is turned to its levels
  by the spectral theorem (`pair_conj`), and at each level Pair is the Pair of one place, which
  its window holds (`bounded_of_window`).
* `Board.orbit_bounded` (BO2): on a board, the local test of finding 434 is enough.
* `pair_iterate_kernel`, `not_orbitBounded_of_kernel` (BO3): an orbit whose `E` lies on the
  level 0 of `S` grows, so the condition on `E` cannot be dropped.
-/

open Matrix

namespace Artform.Stages

section Bounded

variable {n : Type*}

/-- An orbit of `f` from `x` is bounded: every entry of every state along it stays within one
bound. -/
def OrbitBounded (f : LightState ℝ n → LightState ℝ n) (x : LightState ℝ n) : Prop :=
  ∃ B : ℝ, ∀ k : ℕ, ∀ j, |(f^[k] x).1 j| ≤ B ∧ |(f^[k] x).2 j| ≤ B

variable [Fintype n]

/-- A table moves a bounded vector within a bound. -/
theorem abs_mulVec_le (M : Matrix n n ℝ) (v : n → ℝ) {B : ℝ} (hv : ∀ j, |v j| ≤ B) (i : n) :
    |(M *ᵥ v) i| ≤ (∑ j, |M i j|) * B := by
  change |∑ j, M i j * v j| ≤ _
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)

theorem row_le_total (N N' : Matrix n n ℝ) (i : n) :
    ∑ j, |N i j| ≤ ∑ i', ∑ j, (|N i' j| + |N' i' j|) ∧
      ∑ j, |N' i j| ≤ ∑ i', ∑ j, (|N i' j| + |N' i' j|) := by
  have hrow : ∀ i', 0 ≤ ∑ j, (|N i' j| + |N' i' j|) := fun i' =>
    Finset.sum_nonneg fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h := Finset.single_le_sum (f := fun i' => ∑ j, (|N i' j| + |N' i' j|))
    (fun i' _ => hrow i') (Finset.mem_univ i)
  exact ⟨le_trans (Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (abs_nonneg _)) h,
    le_trans (Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (abs_nonneg _)) h⟩

variable [DecidableEq n]

/-- Pair with a diagonal kick and the drift `1` is the Pair of one place at each place. -/
theorem pair_diagonal_apply (μ : n → ℝ) (y : LightState ℝ n) (j : n) :
    ((pair (diagonal μ) 1 y).1 j, (pair (diagonal μ) 1 y).2 j) =
      pairOne (μ j) 1 (y.1 j, y.2 j) := by
  simp [pair, pairOne, mulVec_diagonal]

theorem pair_diagonal_iterate (μ : n → ℝ) (y : LightState ℝ n) (k : ℕ) (j : n) :
    (((pair (diagonal μ) 1)^[k] y).1 j, ((pair (diagonal μ) 1)^[k] y).2 j) =
      (pairOne (μ j) 1)^[k] (y.1 j, y.2 j) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, pair_diagonal_apply]

/-- A level of the kick in `[0, 4)`, with no `e` when the level is `0`, keeps its orbit bounded. -/
theorem pairOne_mode_bounded (μ a e : ℝ) (h0 : 0 ≤ μ) (h4 : μ < 4) (he : μ = 0 → e = 0) :
    ∃ B : ℝ, ∀ k : ℕ,
      ((pairOne μ 1)^[k] (a, e)).1 ^ 2 + ((pairOne μ 1)^[k] (a, e)).2 ^ 2 ≤ B := by
  rcases h0.lt_or_eq with hμ | hμ
  · exact bounded_of_window μ 1 ⟨by linarith, by linarith⟩ (a, e)
  · subst hμ
    obtain rfl := he rfl
    refine ⟨a ^ 2, fun k => ?_⟩
    have hk : (pairOne (0 : ℝ) 1)^[k] (a, 0) = (a, 0) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        simp [pairOne]
    rw [hk]
    simp

/-- The spectral theorem, for a real symmetric table: an orthogonal `U` turns it to the diagonal
of its levels. -/
theorem exists_orthogonal_diag (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix n n ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ M * U = U * diagonal hM.eigenvalues := by
  refine ⟨hM.eigenvectorUnitary, ?_, ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using h
  · have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using h
  · ext i j
    have h := congrFun (hM.mulVec_eigenvectorBasis j) i
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [IsHermitian.eigenvectorUnitary_apply]
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [h, mul_comm]

/-- BO1. Inside the window `4 L⁻¹ - S`, every orbit of Pair whose `E` is `S w` is bounded. -/
theorem orbit_bounded_of_window (S D D' : Matrix n n ℝ) (hS : S.PosSemidef) (hD : Dᵀ = D)
    (h1 : D * D' = 1) (h2 : D' * D = 1) (hW : ((4 : ℝ) • (D' * D') - S).PosDef) (A w : n → ℝ) :
    OrbitBounded (pair S (D * D)) (A, S *ᵥ w) := by
  have hDh : Dᴴ = D := by rw [conjTranspose_eq_transpose_of_trivial, hD]
  have hMp : (D * S * D).PosSemidef := by
    simpa only [hDh] using hS.conjTranspose_mul_mul_same D
  obtain ⟨U, hUtU, hUUt, hMU⟩ := exists_orthogonal_diag _ hMp.1
  set μ := hMp.1.eigenvalues
  have hμ0 : ∀ j, 0 ≤ μ j := fun j => hMp.eigenvalues_nonneg j
  -- the levels lie below `4`
  have hμ4 : ∀ j, μ j < 4 := by
    intro j
    have e0 : Uᵀ * D' * (D * U) = 1 := by
      calc Uᵀ * D' * (D * U) = Uᵀ * (D' * D) * U := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hUtU]
    have hinj : Function.Injective (D * U).mulVec := by
      intro x y hxy
      have h := congrArg (fun z => (Uᵀ * D') *ᵥ z) hxy
      simpa only [mulVec_mulVec, e0, one_mulVec] using h
    have e1 : (D * U)ᴴ = Uᵀ * D := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, hD]
    have e2 : Uᵀ * D * (D' * D') * (D * U) = 1 := by
      calc Uᵀ * D * (D' * D') * (D * U) = Uᵀ * (D * D') * (D' * D) * U := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hUtU]
    have e3 : Uᵀ * D * S * (D * U) = diagonal μ := by
      calc Uᵀ * D * S * (D * U) = Uᵀ * (D * S * D * U) := by simp only [Matrix.mul_assoc]
        _ = diagonal μ := by rw [hMU, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]
    have hP := hW.conjTranspose_mul_mul_same hinj
    rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, e2, e3] at hP
    have hd := hP.diag_pos (i := j)
    have h4 : ((4 : ℝ) • (1 : Matrix n n ℝ) - diagonal μ) j j = 4 - μ j := by simp
    linarith
  -- the scaled and turned state
  have hPP : Uᵀᵀ * Uᵀ = 1 := by rw [transpose_transpose]; exact hUUt
  have hPMP : Uᵀ * (D * S * D) * Uᵀᵀ = diagonal μ := by
    rw [transpose_transpose, Matrix.mul_assoc, hMU, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]
  have hP1 : Uᵀ * 1 * Uᵀᵀ = 1 := by rw [Matrix.mul_one, transpose_transpose, hUtU]
  have hsemi : Function.Semiconj (fun x => relabel Uᵀ (scale D D' x)) (pair S (D * D))
      (pair (diagonal μ) 1) := by
    intro x
    dsimp only
    rw [pair_scale D D' S h1 h2, ← pair_conj Uᵀ hPP, hPMP, hP1]
  have hrr : ∀ z : LightState ℝ n, relabel Uᵀᵀ (relabel Uᵀ z) = z := by
    rintro ⟨a, b⟩
    simp only [relabel, mulVec_mulVec, hPP, one_mulVec]
  have hss : ∀ z : LightState ℝ n, scale D' D (scale D D' z) = z := by
    rintro ⟨a, b⟩
    simp only [scale, mulVec_mulVec, h1, h2, one_mulVec]
  have hback : ∀ x : LightState ℝ n, scale D' D (relabel Uᵀᵀ (relabel Uᵀ (scale D D' x))) = x :=
    fun x => by rw [hrr, hss]
  have hPM : Uᵀ * D * S = diagonal μ * Uᵀ * D' := by
    have hPM0 : Uᵀ * (D * S * D) = diagonal μ * Uᵀ := by
      calc Uᵀ * (D * S * D) = Uᵀ * (D * S * D) * (U * Uᵀ) := by rw [hUUt, Matrix.mul_one]
        _ = Uᵀ * (D * S * D * U) * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = diagonal μ * Uᵀ := by rw [hMU, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]
    calc Uᵀ * D * S = Uᵀ * (D * S * D) * D' := by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = diagonal μ * Uᵀ * D' := by rw [hPM0]
  obtain ⟨y, hy⟩ : ∃ y, y = relabel Uᵀ (scale D D' (A, S *ᵥ w)) := ⟨_, rfl⟩
  have hy2 : ∀ j, y.2 j = μ j * ((Uᵀ * D') *ᵥ w) j := by
    intro j
    have hv : y.2 = diagonal μ *ᵥ ((Uᵀ * D') *ᵥ w) := by
      rw [hy]
      change Uᵀ *ᵥ (D *ᵥ (S *ᵥ w)) = _
      simp only [mulVec_mulVec]
      simpa only [Matrix.mul_assoc] using congrArg (· *ᵥ w) hPM
    rw [hv, mulVec_diagonal]
  -- each level holds its part of the orbit
  have hmode : ∀ j, ∃ B : ℝ, ∀ k : ℕ, ((pairOne (μ j) 1)^[k] (y.1 j, y.2 j)).1 ^ 2 +
      ((pairOne (μ j) 1)^[k] (y.1 j, y.2 j)).2 ^ 2 ≤ B := fun j =>
    pairOne_mode_bounded (μ j) _ _ (hμ0 j) (hμ4 j) fun h0 => by rw [hy2, h0, zero_mul]
  choose B hB using hmode
  have hB0 : ∀ j, 0 ≤ B j := fun j =>
    le_trans (add_nonneg (sq_nonneg _) (sq_nonneg _)) (hB j 0)
  have hsq : ∀ a b c : ℝ, a ^ 2 + b ^ 2 ≤ c → |a| ≤ 1 + c ∧ |b| ≤ 1 + c := by
    intro a b c h
    constructor <;> nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
      sq_nonneg (|a| - 1), sq_nonneg (|b| - 1), sq_nonneg a, sq_nonneg b]
  have hBm : ∀ j, 1 + B j ≤ ∑ j', (1 + B j') := fun j =>
    Finset.single_le_sum (f := fun j' => 1 + B j') (fun i _ => by linarith [hB0 i])
      (Finset.mem_univ j)
  have hBm0 : 0 ≤ ∑ j', (1 + B j') := Finset.sum_nonneg fun j _ => by linarith [hB0 j]
  have hyk : ∀ k j, |((pair (diagonal μ) 1)^[k] y).1 j| ≤ ∑ j', (1 + B j') ∧
      |((pair (diagonal μ) 1)^[k] y).2 j| ≤ ∑ j', (1 + B j') := by
    intro k j
    have e := pair_diagonal_iterate μ y k j
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    dsimp only at e1 e2
    rw [e1, e2]
    have hb := hsq _ _ _ (hB j k)
    exact ⟨hb.1.trans (hBm j), hb.2.trans (hBm j)⟩
  refine ⟨(∑ i', ∑ j, (|(D * Uᵀᵀ) i' j| + |(D' * Uᵀᵀ) i' j|)) * ∑ j', (1 + B j'), fun k i => ?_⟩
  have hx : (pair S (D * D))^[k] (A, S *ᵥ w) =
      scale D' D (relabel Uᵀᵀ ((pair (diagonal μ) 1)^[k] y)) := by
    have hit := hsemi.iterate_right k (A, S *ᵥ w)
    rw [hy, ← hit, hback]
  rw [hx]
  have hr := row_le_total (D * Uᵀᵀ) (D' * Uᵀᵀ) i
  constructor
  · change |(D *ᵥ (Uᵀᵀ *ᵥ ((pair (diagonal μ) 1)^[k] y).1)) i| ≤ _
    rw [mulVec_mulVec]
    exact (abs_mulVec_le _ _ (fun j => (hyk k j).1) i).trans
      (mul_le_mul_of_nonneg_right hr.1 hBm0)
  · change |(D' *ᵥ (Uᵀᵀ *ᵥ ((pair (diagonal μ) 1)^[k] y).2)) i| ≤ _
    rw [mulVec_mulVec]
    exact (abs_mulVec_le _ _ (fun j => (hyk k j).2) i).trans
      (mul_le_mul_of_nonneg_right hr.2 hBm0)

/-- BO3. An orbit whose `E` lies on the level 0 of the kick drifts: from `(0, L' y)` with
`S y = 0` and `L L' = 1`, Pair reaches `(-k y, L' y)` at step `k`. -/
theorem pair_iterate_kernel (S L L' : Matrix n n ℝ) (hLL : L * L' = 1) (y : n → ℝ)
    (hy : S *ᵥ y = 0) (k : ℕ) :
    (pair S L)^[k] (0, L' *ᵥ y) = (-(k : ℝ) • y, L' *ᵥ y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 : S *ᵥ (-(k : ℝ) • y) = 0 := by rw [mulVec_smul, hy, smul_zero]
    have h2 : L *ᵥ (L' *ᵥ y) = y := by rw [mulVec_mulVec, hLL, one_mulVec]
    simp only [pair, h1, add_zero, h2]
    refine Prod.ext ?_ rfl
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_succ]
    ring

/-- BO3. So, with `y ≠ 0`, that orbit is not bounded: the condition on `E` cannot be dropped. -/
theorem not_orbitBounded_of_kernel (S L L' : Matrix n n ℝ) (hLL : L * L' = 1) (y : n → ℝ)
    (hy : S *ᵥ y = 0) (hy0 : y ≠ 0) : ¬ OrbitBounded (pair S L) (0, L' *ᵥ y) := by
  rintro ⟨B, hB⟩
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (funext h)
  have hyj : 0 < |y j| := abs_pos.mpr hj
  obtain ⟨k, hk⟩ := exists_nat_gt (B / |y j|)
  have h := (hB k j).1
  rw [pair_iterate_kernel S L L' hLL y hy k] at h
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, Nat.abs_cast] at h
  rw [div_lt_iff₀ hyj] at hk
  linarith

end Bounded

/-- BO2. On a board, with `κ > 0`, `λ > 0`, and `κ σ` times the sum of `λ` over the four sides of
`σ` below `2` at every square, every orbit of Pair whose `E` is `S w` is bounded. -/
theorem Board.orbit_bounded {f e v : Type*} [Fintype f] [Fintype e] [DecidableEq f]
    [DecidableEq e] (B : Board f e v) (κ : f → ℝ) (l : e → ℝ) (hκ : ∀ σ, 0 < κ σ)
    (hl : ∀ ℓ, 0 < l ℓ) (h : ∀ σ, κ σ * ∑ i, l (B.side σ i) < 2) (A w : e → ℝ) :
    OrbitBounded (pair (B.incidenceᵀ * diagonal κ * B.incidence) (diagonal l))
      (A, (B.incidenceᵀ * diagonal κ * B.incidence) *ᵥ w) := by
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
  have hW : ((4 : ℝ) • ((diagonal fun ℓ => 1 / Real.sqrt (l ℓ)) *
      (diagonal fun ℓ => 1 / Real.sqrt (l ℓ))) -
        B.incidenceᵀ * diagonal κ * B.incidence).PosDef := by
    have e1 : (4 : ℝ) • ((diagonal fun ℓ => 1 / Real.sqrt (l ℓ)) *
        (diagonal fun ℓ => 1 / Real.sqrt (l ℓ))) = diagonal fun ℓ => 4 / l ℓ := by
      ext i j
      simp only [diagonal_mul_diagonal, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
      split_ifs
      · rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (hl i).le]
        ring
      · simp
    rw [e1]
    exact B.window κ l hκ hl h
  rw [← hDD]
  exact orbit_bounded_of_window _ _ _ hS (diagonal_transpose _) h1 h2 hW A w

end Artform.Stages
