import ArtformScores.NonabelianGravity.NonlinearNativeChart

/-! # The arbitrary native correction chart is physically admitted near flat space -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable def minkowski : Mat := Matrix.diagonal (fun i => (eta i : ℝ))

def Physical (q : Env) : Prop :=
  0 < q.1.1.det ∧ 0 < q.1.2.det ∧ ∀ k, (q.2 k).transpose * minkowski * q.2 k = minkowski ∧
    (q.2 k).det = 1 ∧ 0 < q.2 k 0 0

lemma lie_half_skew (A : Biv ℝ) :
    ((1 / 2 : ℝ) • lie A).transpose * minkowski +
      minkowski * ((1 / 2 : ℝ) • lie A) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lie, minkowski, eta, Matrix.mul_apply, Matrix.diagonal,
      Fin.sum_univ_succ]

lemma cayley_lorentz_matrix (A : Biv ℝ)
    (hN : (1 - (1 / 2 : ℝ) • lie A).det ≠ 0) :
    (cayleyLink A).transpose * minkowski * cayleyLink A = minkowski := by
  let X : Mat := (1 / 2 : ℝ) • lie A
  let P : Mat := 1 + X
  let N : Mat := 1 - X
  have hX : X.transpose * minkowski + minkowski * X = 0 := lie_half_skew A
  have hPN : P.transpose * minkowski * P = N.transpose * minkowski * N := by
    dsimp [P, N]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have he : (1 + X.transpose) * minkowski * (1 + X) -
        (1 - X.transpose) * minkowski * (1 - X) =
        (X.transpose * minkowski + minkowski * X) +
          (X.transpose * minkowski + minkowski * X) := by noncomm_ring
    rw [hX, add_zero] at he
    exact sub_eq_zero.mp he
  have hNN : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N (isUnit_iff_ne_zero.mpr hN)
  change (P * N⁻¹).transpose * minkowski * (P * N⁻¹) = _
  calc
    _ = N⁻¹.transpose * (P.transpose * minkowski * P) * N⁻¹ := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = N⁻¹.transpose * (N.transpose * minkowski * N) * N⁻¹ := by rw [hPN]
    _ = (N * N⁻¹).transpose * minkowski * (N * N⁻¹) := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = minkowski := by rw [hNN]; simp

lemma lorentz_det_square (U : Mat) (h : U.transpose * minkowski * U = minkowski) :
    U.det ^ 2 = 1 := by
  have hη : minkowski.det = -1 := by
    norm_num [minkowski, eta, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hd := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_transpose, hη] at hd
  nlinarith

lemma chart_eventually_physical : ∀ᶠ p : Chart in 𝓝 0, Physical (nativeChart p) := by
  have hC := smooth_native_chart
  have hF (j : Fin 2) : ContinuousAt
      (fun p : Chart => (if j = 0 then (nativeChart p).1.1 else (nativeChart p).1.2).det) 0 := by
    apply (smooth_det (n := 1) _).continuousAt
    intro i k
    split_ifs <;> fun_prop
  have hentry (k i j : Fin 4) : ContDiffAt ℝ 1
      (fun p : Chart => (nativeChart p).2 k i j) 0 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_pi.mp hC.snd k) i) j
  have hU (k : Fin 4) : ContinuousAt (fun p : Chart => ((nativeChart p).2 k).det) 0 := by
    apply (smooth_det (n := 1) _).continuousAt
    intro i j
    exact hentry k i j
  have hT (k : Fin 4) : ContinuousAt (fun p : Chart => (nativeChart p).2 k 0 0) 0 := by
    exact (hentry k 0 0).continuousAt
  have hD (k : Fin 4) : ContinuousAt (fun p : Chart =>
      (1 - (1 / 2 : ℝ) • lie (p.2 k)).det) 0 := by
    apply (smooth_det (n := 1) _).continuousAt
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [lie] <;> fun_prop
  have hposF : ∀ᶠ p : Chart in 𝓝 0, ∀ j : Fin 2,
      0 < (if j = 0 then (nativeChart p).1.1 else (nativeChart p).1.2).det := by
    apply Filter.eventually_all.mpr
    intro j
    apply (hF j).tendsto.eventually
    apply eventually_gt_nhds
    simp [native_chart_zero, flat]
  have hposU : ∀ᶠ p : Chart in 𝓝 0, ∀ k : Fin 4, 0 < ((nativeChart p).2 k).det := by
    apply Filter.eventually_all.mpr
    intro k
    apply (hU k).tendsto.eventually
    apply eventually_gt_nhds
    simp [native_chart_zero, flat]
  have hposT : ∀ᶠ p : Chart in 𝓝 0, ∀ k : Fin 4, 0 < (nativeChart p).2 k 0 0 := by
    apply Filter.eventually_all.mpr
    intro k
    apply (hT k).tendsto.eventually
    apply eventually_gt_nhds
    simp [native_chart_zero, flat]
  have hden : ∀ᶠ p : Chart in 𝓝 0, ∀ k : Fin 4,
      (1 - (1 / 2 : ℝ) • lie (p.2 k)).det ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro k
    apply (hD k).eventually_ne
    simp only [Prod.snd_zero, Pi.zero_apply, lie_zero, smul_zero, sub_zero, Matrix.det_one]
    norm_num
  filter_upwards [hposF, hposU, hposT, hden] with p hF hU hT hD
  refine ⟨by simpa using hF 0, by simpa using hF 1, ?_⟩
  intro k
  have hL := cayley_lorentz_matrix (p.2 k) (hD k)
  refine ⟨hL, ?_, hT k⟩
  have hd := lorentz_det_square _ hL
  have hp := hU k
  change 0 < (cayleyLink (p.2 k)).det at hp
  change (cayleyLink (p.2 k)).det = 1
  nlinarith

lemma corrected_native_eventually_physical (f b g : ℝ) (w : Chart) :
    ∀ᶠ e in 𝓝 (0 : ℝ), Physical (nativeChart (nativeRate f b g e + e ^ 2 • w)) := by
  have hc : ContinuousAt (fun e : ℝ => nativeRate f b g e + e ^ 2 • w) 0 :=
    (native_rate_continuous f b g).add (by fun_prop)
  have ht : Tendsto (fun e : ℝ => nativeRate f b g e + e ^ 2 • w) (𝓝 0) (𝓝 0) := by
    simpa only [native_rate_zero, zero_pow (by decide : 2 ≠ 0), zero_smul, add_zero] using
      hc.tendsto
  exact ht.eventually chart_eventually_physical

end Artform.Scores.NonabelianGravity.NonlinearAmbient
