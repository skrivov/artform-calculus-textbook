import ArtformScores.NonabelianGravity.NonlinearMatrixCritical

/-! # Spatial curvature is critical in every ambient coframe/link direction -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

lemma smooth_mat_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {x : X} {A B : X → Mat}
    (hA : ∀ i j, ContDiffAt ℝ n (fun q => A q i j) x)
    (hB : ∀ i j, ContDiffAt ℝ n (fun q => B q i j) x) (i j : Fin 4) :
    ContDiffAt ℝ n (fun q => (A q * B q) i j) x := by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun k _ => (hA i k).mul (hB k j))

noncomputable def spatialComm (q : Env) (k l : Fin 4) : Mat :=
  (q.2 l)⁻¹ * (q.2 k)⁻¹ * q.2 l * q.2 k -
    (q.2 k)⁻¹ * (q.2 l)⁻¹ * q.2 k * q.2 l

lemma spatial_comm_critical (k l : Fin 4) :
    MatrixCritical (fun q : Env => spatialComm q k l) flat := by
  let A : Env → Mat := fun q => q.2 k - 1
  let B : Env → Mat := fun q => q.2 l - 1
  have hA (i j : Fin 4) : ContDiffAt ℝ 1 (fun q => A q i j) flat := by
    dsimp [A]
    fun_prop
  have hB (i j : Fin 4) : ContDiffAt ℝ 1 (fun q => B q i j) flat := by
    dsimp [B]
    fun_prop
  have ha : A flat = 0 := by simp [A, flat]
  have hb : B flat = 0 := by simp [B, flat]
  have hBA := matrix_product_critical (fun i j => (hB i j).differentiableAt (by norm_num))
    (fun i j => (hA i j).differentiableAt (by norm_num)) hb ha
  have hAB := matrix_product_critical (fun i j => (hA i j).differentiableAt (by norm_num))
    (fun i j => (hB i j).differentiableAt (by norm_num)) ha hb
  have hbr := matrix_sub_critical hBA hAB
  have hU (k i j : Fin 4) : ContDiffAt ℝ 1 (fun q : Env => q.2 k i j) flat := by fun_prop
  have hV (k i j : Fin 4) : ContDiffAt ℝ 1 (fun q : Env => (q.2 k)⁻¹ i j) flat := by
    simpa only [inverseLinks, links, ite_true] using!
      (smooth_inverse_links (n := 1) flat flat_regular 0 k i j)
  let J : Env → Mat := fun q => (q.2 k)⁻¹ * (q.2 l)⁻¹ * q.2 k * q.2 l
  let C : Env → Mat := fun q => (1 + J q) * ((q.2 l)⁻¹ * (q.2 k)⁻¹)
  have hJ (i j : Fin 4) : ContDiffAt ℝ 1 (fun q => J q i j) flat :=
    smooth_mat_mul (smooth_mat_mul (smooth_mat_mul (hV k) (hV l)) (hU k)) (hU l) i j
  have hC (i j : Fin 4) : ContDiffAt ℝ 1 (fun q => C q i j) flat :=
    smooth_mat_mul (fun i j => contDiffAt_const.add (hJ i j))
      (smooth_mat_mul (hV l) (hV k)) i j
  have hc := matrix_mul_critical_left
    (fun i j => (hC i j).differentiableAt (by norm_num)) hbr
  have hn (k : Fin 4) : ∀ᶠ q : Env in 𝓝 flat, (q.2 k).det ≠ 0 :=
    (smooth_det (hU k)).continuousAt.eventually_ne (by simp [flat])
  have he : (fun q => spatialComm q k l) =ᶠ[𝓝 flat]
      fun q => C q * (B q * A q - A q * B q) := by
    filter_upwards [hn k, hn l] with q hk hl
    exact commutator_factor (q.2 k) (q.2 l) hk hl
  intro i j
  refine ⟨by simp [spatialComm, flat], (hc i j).2.congr_of_eventuallyEq ?_⟩
  filter_upwards [he] with q hq
  exact congrFun (congrFun hq i) j

noncomputable def reading (q : Env) (r : Fin 6) : Biv ℝ :=
  internalStar (lieCoordinates ((-(1 / 2) : ℝ) •
    (cellHolonomy (links q) (inverseLinks q) r -
      cellInverseHolonomy (links q) (inverseLinks q) r)))

lemma critical_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} (hf : Critical f x) : Critical (fun q => -f q) x := by
  constructor
  · simpa using! congrArg Neg.neg hf.1
  · simpa using! hf.2.fun_neg

lemma star_coordinates_critical {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M : X → Mat} {x : X} (hm : MatrixCritical M x) (a : Fin 6) :
    Critical (fun q => internalStar (lieCoordinates ((-(1 / 2) : ℝ) • M q)) a) x := by
  have hc (i j : Fin 4) := critical_mul_left
    (differentiableAt_const (-(1 / 2) : ℝ)) (hm i j)
  fin_cases a
  · simpa [internalStar, lieCoordinates] using! critical_neg (hc 2 3)
  · simpa [internalStar, lieCoordinates] using! critical_neg (hc 3 1)
  · simpa [internalStar, lieCoordinates] using! critical_neg (hc 1 2)
  · simpa [internalStar, lieCoordinates] using! hc 0 1
  · simpa [internalStar, lieCoordinates] using! hc 0 2
  · simpa [internalStar, lieCoordinates] using! hc 0 3

lemma reading_spatial_form (q : Env) (r : Fin 6) (hr : 3 ≤ r.val) :
    reading q r = internalStar (lieCoordinates ((-(1 / 2) : ℝ) •
      spatialComm q (face r).1 (face r).2)) := by
  fin_cases r <;> norm_num at hr
  all_goals norm_num [reading, spatialComm, cellHolonomy, cellInverseHolonomy, links,
      inverseLinks, face, NonlinearIsotropic.shift]

lemma reading_spatial_critical (r a : Fin 6) (hr : 3 ≤ r.val) :
    Critical (fun q : Env => reading q r a) flat := by
  simp_rw [reading_spatial_form _ r hr]
  exact star_coordinates_critical (spatial_comm_critical (face r).1 (face r).2) a

noncomputable def average (q : Env) (r : Fin 6) : Biv ℝ :=
  cellAverage (frames q) (inverseLinks q) r


end Artform.Scores.NonabelianGravity.NonlinearAmbient
