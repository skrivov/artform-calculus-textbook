import ArtformScores.GravityBridge.MemoryStatements
import ArtformScores.Rules

/-! # Exact memory, graph preparation and a visible Markov counterexample -/

namespace Artform.Scores.GravityBridge

open Finset

variable {K Y Z : Type*} [Semiring K] [AddCommMonoid Y] [AddCommMonoid Z]
  [Module K Y] [Module K Z]

lemma forced_memory (D : Z →ₗ[K] Z) (f z : ℕ → Z)
    (hz : ∀ n, z (n + 1) = f n + D (z n)) (n : ℕ) :
    z n = (D ^ n) (z 0) + ∑ j ∈ range n, (D ^ (n - 1 - j)) (f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hz, ih, map_add, map_sum, sum_range_succ]
    have hsum : (∑ j ∈ range n, D ((D ^ (n - 1 - j)) (f j))) =
        ∑ j ∈ range n, (D ^ (n + 1 - 1 - j)) (f j) := by
      apply sum_congr rfl
      intro j hj
      have he : n + 1 - 1 - j = (n - 1 - j) + 1 := by
        have := mem_range.mp hj
        omega
      rw [he, pow_succ']
      rfl
    rw [hsum, pow_succ']
    simp [Module.End.mul_apply, add_comm, add_left_comm]

lemma visible_memory (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y)
    (C : Y →ₗ[K] Z) (D : Z →ₗ[K] Z) (x : ℕ → Y) (z : ℕ → Z)
    (hx : ∀ n, x (n + 1) = A (x n) + B (z n))
    (hz : ∀ n, z (n + 1) = C (x n) + D (z n)) (n : ℕ) :
    x (n + 1) = A (x n) + B ((D ^ n) (z 0)) +
      ∑ j ∈ range n, B ((D ^ (n - 1 - j)) (C (x j))) := by
  rw [hx, forced_memory D (fun j => C (x j)) z hz n, map_add, map_sum]
  simp [add_assoc]

lemma prepared_block (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y)
    (C : Y →ₗ[K] Z) (D : Z →ₗ[K] Z) (J : Y →ₗ[K] Z)
    (hJ : ∀ y, C y + D (J y) = J (A y + B (J y))) (n : ℕ) (y : Y) :
    ((blockStep A B C D)^[n]) (y, J y) =
      (((fun x => A x + B (J x))^[n]) y,
        J (((fun x => A x + B (J x))^[n]) y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    dsimp [blockStep]
    rw [hJ]

lemma full_visible_autonomy (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y) :
    (∃ U : Y → Y, ∀ x z, A x + B z = U x) ↔ B = 0 := by
  constructor
  · rintro ⟨U, h⟩
    have hu : U 0 = 0 := by simpa using (h 0 0).symm
    ext z
    have hz := h 0 z
    simpa [hu] using hz
  · rintro rfl
    exact ⟨A, by simp⟩

lemma no_quarter_visible_autonomy :
    ¬ ∃ U : ℚ → ℚ, ∀ (x : ℚ) (n : ℕ), quarterVisible (n + 1) x = U (quarterVisible n x) := by
  rintro ⟨U, h⟩
  have h0 := h 0 1
  have h1 := h 1 1
  norm_num [quarterVisible, quarterTurn, Function.iterate_succ_apply'] at h0 h1
  linarith

/-- **GAC:block-memory** (exact block elimination retains history and preparation). -/
@[ledger "GAC:block-memory"]
theorem blockMemory : Statement.blockMemory := by
  refine ⟨?_, ?_, ?_, no_quarter_visible_autonomy⟩
  · intro K Y Z _ _ _ _ _ A B C D x z hx hz n
    exact ⟨forced_memory D (fun j => C (x j)) z hz n,
      visible_memory A B C D x z hx hz n⟩
  · intro K Y Z _ _ _ _ _ A B C D J hJ n y
    exact prepared_block A B C D J hJ n y
  · intro K Y Z _ _ _ _ _ A B
    exact full_visible_autonomy A B

/-! ## Non-vacuity -/

example : blockStep (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id (-LinearMap.id) 0 = quarterTurn := by
  funext p
  simp [blockStep, quarterTurn]

example : ∀ x : ℚ,
    blockStep (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id (-LinearMap.id) 0 (x, 0) = (0, -x) := by
  simp [blockStep]

example (p : ℚ × ℚ) :
    Matrix.mulVec (realize (whitehead (1 : ℚˣ)) : Matrix (Fin 2) (Fin 2) ℚ) ![p.1, p.2] =
      ![(quarterTurn p).1, (quarterTurn p).2] := by
  rw [whitehead_mat]
  ext i
  fin_cases i <;> simp [quarterTurn, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : ∃ k : ℝ, 0 < k ∧ k ^ 2 + k = 1 ∧
    ∀ (n : ℕ) (y : ℝ),
      ((blockStep (K := ℝ) (Y := ℝ) (Z := ℝ) ((2 : ℝ) • LinearMap.id)
          LinearMap.id LinearMap.id LinearMap.id)^[n])
        (y, k * y) =
      (((fun x : ℝ => 2 * x + k * x)^[n]) y,
        k * (((fun x : ℝ => 2 * x + k * x)^[n]) y)) := by
  let k : ℝ := (Real.sqrt 5 - 1) / 2
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hk : k ^ 2 + k = 1 := by dsimp [k]; nlinarith
  have hkp : 0 < k := by
    have hp := Real.sqrt_nonneg (5 : ℝ)
    dsimp [k]
    nlinarith
  refine ⟨k, hkp, hk, ?_⟩
  intro n y
  let J : ℝ →ₗ[ℝ] ℝ := k • LinearMap.id
  have hJ : ∀ y : ℝ, y + J y = J (2 * y + J y) := by
    intro y
    dsimp [J]
    linear_combination -y * hk
  exact prepared_block (K := ℝ) (Y := ℝ) (Z := ℝ) ((2 : ℝ) • LinearMap.id) LinearMap.id LinearMap.id
    LinearMap.id J hJ n y

end Artform.Scores.GravityBridge
