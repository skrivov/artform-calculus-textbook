import ArtformStages.SolidWaves
import ArtformStages.EulerCount

/-!
# The momenta and the modes of a solid

Finding 465 of the research ledger on a layered universe found light in a solid of cubes. Here the
fields of the cubic torus are counted (finding 466 of the ledger):

* `cube_energy`, `cube_stencil_const` (SM1): the sum of `g` times its stencil is the sum of the
  squares of its steps, so a function with stencil `0` is the same at every corner;
* `cube_harmonic_iff` (SM2): a field on the lines is harmonic exactly when it is uniform;
* `cube_harmonic_finrank` (SM3): the harmonic fields form a space of dimension `3`;
* `cube_gradient_finrank`, `cube_transverse_finrank` (SM4): the gradients and the transverse fields
  form spaces of dimensions `N - 1` and `2 (N - 1)`, with `N = n³`;
* `cube_pair_mean` (SM5): Pair keeps the three means of `E`.
-/

open Matrix Module

namespace Artform.Stages

variable (n : ℕ) [NeZero n]

/-- A shift of the cubic torus keeps sums over its corners. -/
theorem cube_sum_shift (g : CubePoint n → ℝ) (t : CubePoint n) : ∑ w, g (w + t) = ∑ w, g w :=
  Equiv.sum_comp (Equiv.addRight t) g

/-- So does a shift back, on each direction of the lines. -/
theorem cube_line_sum_shift_sub (y : CubePoint n × Fin 3 → ℝ) (t : CubePoint n) (k : Fin 3) :
    ∑ w, y (w - t, k) = ∑ w, y (w, k) :=
  Equiv.sum_comp (Equiv.subRight t) (fun w => y (w, k))

/-- **SM1.** The sum of `g` times its stencil of seven points is the sum of the squares of its
steps. -/
theorem cube_energy (g : CubePoint n → ℝ) :
    ∑ w, g w * ∑ k, ((g w - g (w + cubeStep n k)) + (g w - g (w - cubeStep n k))) =
      ∑ k, ∑ w, (g w - g (w + cubeStep n k)) ^ 2 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : ∑ w, g w * (g w - g (w - cubeStep n k)) =
      ∑ w, g (w + cubeStep n k) * (g (w + cubeStep n k) - g w) :=
    (cube_sum_shift n (fun w => g w * (g w - g (w - cubeStep n k))) (cubeStep n k)).symm.trans
      (by simp only [add_sub_cancel_right])
  calc ∑ w, g w * ((g w - g (w + cubeStep n k)) + (g w - g (w - cubeStep n k)))
      = ∑ w, g w * (g w - g (w + cubeStep n k)) + ∑ w, g w * (g w - g (w - cubeStep n k)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ = ∑ w, (g w - g (w + cubeStep n k)) ^ 2 := by
        rw [hs, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring

/-- A function that every step leaves the same is the same at every corner. -/
theorem cube_steps_const (g : CubePoint n → ℝ) (h : ∀ w k, g (w + cubeStep n k) = g w)
    (w : CubePoint n) : g w = g 0 := by
  have hm : ∀ (x : CubePoint n) (k : Fin 3) (m : ℕ), g (x + Pi.single k (m : ZMod n)) = g x := by
    intro x k m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, Pi.single_add, ← add_assoc]
      have hs := h (x + Pi.single k (m : ZMod n)) k
      unfold cubeStep at hs
      rw [hs, ih]
  have hw : w = 0 + Pi.single 0 ((w 0).val : ZMod n) + Pi.single 1 ((w 1).val : ZMod n) +
      Pi.single 2 ((w 2).val : ZMod n) := by
    funext d
    fin_cases d <;> simp
  rw [hw, hm, hm, hm]

/-- **SM1.** A function on the corners whose stencil of seven points is `0` everywhere is the same
at every corner. -/
theorem cube_stencil_const (g : CubePoint n → ℝ)
    (h : ∀ w, ∑ k, ((g w - g (w + cubeStep n k)) + (g w - g (w - cubeStep n k))) = 0)
    (w : CubePoint n) : g w = g 0 := by
  have hE := cube_energy n g
  simp only [h, mul_zero, Finset.sum_const_zero] at hE
  have hk : ∀ k, ∑ w, (g w - g (w + cubeStep n k)) ^ 2 = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg fun w _ => sq_nonneg _)).mp
      hE.symm k (Finset.mem_univ k)
  refine cube_steps_const n g (fun x k => ?_) w
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg _)).mp (hk k) x
    (Finset.mem_univ x)
  have h0 : g x - g (x + cubeStep n k) = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  linarith

/-- **SM2.** A field on the lines of the cubic torus is harmonic exactly when it is uniform. -/
theorem cube_harmonic_iff (h : CubePoint n × Fin 3 → ℝ) :
    ((cubeGauge n)ᵀ *ᵥ h = 0 ∧ cubeIncidence n *ᵥ h = 0) ↔
      ∃ c : Fin 3 → ℝ, ∀ w d, h (w, d) = c d := by
  constructor
  · rintro ⟨h1, h2⟩
    have hL := cube_hodge_laplacian n h
    rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h1, h2, mulVec_zero, mulVec_zero,
      add_zero] at hL
    refine ⟨fun d => h (0, d), fun w d => ?_⟩
    exact cube_stencil_const n (fun x => h (x, d)) (fun x => by
      have hx := congrFun hL (x, d)
      simp only [lineStencil, Pi.zero_apply] at hx
      exact hx.symm) w
  · rintro ⟨c, hc⟩
    constructor
    · funext w
      rw [cube_gaugeT_mulVec, Pi.zero_apply]
      simp [hc]
    · funext σ
      rw [cubeIncidence_mulVec, Pi.zero_apply]
      simp only [hc]
      ring

/-- The uniform field of three numbers, as a linear map. -/
def cubeUniformMap : (Fin 3 → ℝ) →ₗ[ℝ] (CubePoint n × Fin 3 → ℝ) where
  toFun c := fun ℓ => c ℓ.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **SM3.** The harmonic fields of the cubic torus form a space of dimension `3`. -/
theorem cube_harmonic_finrank :
    finrank ℝ ↥(LinearMap.ker (cubeGauge n)ᵀ.mulVecLin ⊓
      LinearMap.ker (cubeIncidence n).mulVecLin) = 3 := by
  have hrange : LinearMap.ker (cubeGauge n)ᵀ.mulVecLin ⊓ LinearMap.ker (cubeIncidence n).mulVecLin =
      LinearMap.range (cubeUniformMap n) := by
    ext h
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.mem_range]
    simp only [Matrix.mulVecLin_apply]
    rw [cube_harmonic_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, funext fun ℓ => (hc ℓ.1 ℓ.2).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, fun w d => rfl⟩
  have hinj : Function.Injective (cubeUniformMap n) := by
    intro c c' h
    funext d
    exact congrFun h (0, d)
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- `G φ = 0` on the cubic torus only for `φ` the same at every corner. -/
theorem cube_gauge_const (φ : CubePoint n → ℝ) (h : cubeGauge n *ᵥ φ = 0) (w : CubePoint n) :
    φ w = φ 0 :=
  cube_steps_const n φ (fun x k => by
    have hx := congrFun h (x, k)
    rw [cubeGauge_mulVec, Pi.zero_apply, sub_eq_zero] at hx
    exact hx) w

/-- **SM4.** The gradients of the cubic torus form a space of dimension `n³ - 1`. -/
theorem cube_gradient_finrank :
    finrank ℝ (LinearMap.range (cubeGauge n).mulVecLin) = n ^ 3 - 1 := by
  have hker : LinearMap.ker (cubeGauge n).mulVecLin = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext φ
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton, Matrix.mulVecLin_apply]
    constructor
    · intro h
      exact ⟨φ 0, funext fun w => by simp [cube_gauge_const n φ h w]⟩
    · rintro ⟨c, rfl⟩
      funext ℓ
      rw [cubeGauge_mulVec]
      simp
  have h1 : finrank ℝ (LinearMap.ker (cubeGauge n).mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton fun h0 => ?_
    have := congrFun h0 0
    simp at this
  have hT := LinearMap.finrank_range_add_finrank_ker (cubeGauge n).mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card] at hT
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hT
  omega

/-- **SM4.** The transverse fields of the cubic torus form a space of dimension `2 (n³ - 1)`. -/
theorem cube_transverse_finrank :
    finrank ℝ (LinearMap.range (cubeIncidence n)ᵀ.mulVecLin) = 2 * (n ^ 3 - 1) := by
  have h := harmonic_count (cubeIncidence n) (cubeGauge n) (cube_incidence_mul_gauge n)
  rw [cube_harmonic_finrank] at h
  have hG := cube_gradient_finrank n
  have hr : (cubeIncidence n)ᵀ.rank = (cubeIncidence n).rank := rank_transpose _
  have hpos : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne n))
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
  change (cubeGauge n).rank = _ at hG
  change (cubeIncidence n)ᵀ.rank = _
  omega

/-- The transverse fields have the means `0` on each direction. -/
theorem cube_sum_transpose (y : CubePoint n × Fin 3 → ℝ) (d : Fin 3) :
    ∑ w, ((cubeIncidence n)ᵀ *ᵥ y) (w, d) = 0 := by
  simp only [cube_transpose_mulVec, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    cube_line_sum_shift_sub]
  ring

/-- **SM5.** Pair with every kick `Cᵀ K C` keeps the three means of `E`. -/
theorem cube_pair_mean (K L : Matrix (CubePoint n × Fin 3) (CubePoint n × Fin 3) ℝ)
    (x : LightState ℝ (CubePoint n × Fin 3)) (d : Fin 3) :
    ∑ w, (pair ((cubeIncidence n)ᵀ * K * cubeIncidence n) L x).2 (w, d) = ∑ w, x.2 (w, d) := by
  simp only [pair]
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  simp only [Pi.add_apply, Finset.sum_add_distrib, cube_sum_transpose, add_zero]

end Artform.Stages
