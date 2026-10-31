import ArtformScores.NonabelianGravity.NonlinearAmbient

/-! # Scalar rational regularity of all original finite source factors -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic
open scoped Matrix.Norms.Elementwise
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n : WithTop ℕ∞} {x : X}

lemma smooth_det {M : X → Mat}
    (h : ∀ i j, ContDiffAt ℝ n (fun q => M q i j) x) :
    ContDiffAt ℝ n (fun q => (M q).det) x := by
  simp only [Matrix.det_apply']
  fun_prop

lemma smooth_adjugate {M : X → Mat}
    (h : ∀ i j, ContDiffAt ℝ n (fun q => M q i j) x) (i j : Fin 4) :
    ContDiffAt ℝ n (fun q => (M q).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply smooth_det
  intro k l
  by_cases hl : k = j
  · have he : (fun q : X => (M q).updateRow j (Pi.single i 1) k l) =
        fun _ : X => if l = i then (1 : ℝ) else 0 := by
      funext q
      simp [Matrix.updateRow, Matrix.of_apply, Function.update, hl, Pi.single]
    rw [he]
    exact contDiffAt_const
  · have he : (fun q : X => (M q).updateRow j (Pi.single i 1) k l) =
        fun q => M q k l := by
      funext q
      simp [Matrix.updateRow, Matrix.of_apply, Function.update, hl, Pi.single]
    rw [he]
    exact h k l

lemma smooth_inverse {M : X → Mat}
    (h : ∀ i j, ContDiffAt ℝ n (fun q => M q i j) x)
    (hd : (M x).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ n (fun q => (M q)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((smooth_det h).inv hd).mul (smooth_adjugate h i j)

def Regular (q : Env) : Prop := q.1.1.det ≠ 0 ∧ ∀ k, (q.2 k).det ≠ 0

lemma flat_regular : Regular flat := by simp [Regular, flat]

lemma smooth_frames (q₀ : Env) (t : ℕ) (i j : Fin 4) :
    ContDiffAt ℝ n (fun q : Env => frames q t i j) q₀ := by
  dsimp [frames]
  split_ifs <;> fun_prop

lemma smooth_links (q₀ : Env) (t : ℕ) (k i j : Fin 4) :
    ContDiffAt ℝ n (fun q : Env => links q t k i j) q₀ := by
  dsimp [links]
  split_ifs <;> fun_prop

lemma smooth_inverse_links (q₀ : Env) (hq : Regular q₀) (t : ℕ) (k i j : Fin 4) :
    ContDiffAt ℝ n (fun q : Env => inverseLinks q t k i j) q₀ := by
  apply smooth_inverse (fun i j => smooth_links q₀ t k i j)
  by_cases ht : t = 0
  · simpa [links, ht] using hq.2 k
  · simp [links, ht]

lemma smooth_metric (q₀ : Env) (hq : Regular q₀) (i j : Fin 4) :
    ContDiffAt ℝ n (fun q : Env => metric q.1.1 i j) q₀ := by
  have hi (i j : Fin 4) : ContDiffAt ℝ n (fun q : Env => q.1.1⁻¹ i j) q₀ :=
    smooth_inverse (M := fun q : Env => q.1.1) (n := n) (fun i j => by fun_prop) hq.1 i j
  have he (q : Env) : metric q.1.1 i j =
      ∑ k, (q.1.1⁻¹ i k * (eta k : ℝ)) * q.1.1⁻¹ j k := by
    simp [metric, Matrix.mul_apply, Matrix.diagonal_apply]
  simp_rw [he]
  exact ContDiffAt.sum (fun k _ => ((hi i k).mul contDiffAt_const).mul (hi j k))

lemma smooth_weight (q₀ : Env) (hq : Regular q₀) (r s : Fin 6) :
    ContDiffAt ℝ n (fun q : Env => weight q r s) q₀ := by
  have hd : ContDiffAt ℝ n (fun q : Env => q.1.1.det) q₀ :=
    smooth_det (fun i j => by fun_prop)
  have hm := smooth_metric (n := n) q₀ hq
  unfold weight
  fun_prop

lemma smooth_tau (q₀ : Env) (hq : Regular q₀) (r : Fin 6) (i : Fin 4) :
    ContDiffAt ℝ n (fun q : Env => tau q r i) q₀ := by
  have hE := smooth_frames (n := n) q₀
  have hV := smooth_inverse_links (n := n) q₀ hq
  simp only [tau, cellTorsionFace, Matrix.mul_apply]
  fun_prop

lemma smooth_average (q₀ : Env) (hq : Regular q₀) (r a : Fin 6) :
    ContDiffAt ℝ n (fun q : Env => cellAverage (frames q) (inverseLinks q) r a) q₀ := by
  have hE := smooth_frames (n := n) q₀
  have hV := smooth_inverse_links (n := n) q₀ hq
  fin_cases a <;>
    norm_num [cellAverage, transported, wedgeColumns, Pi.smul_apply,
      zsmul_eq_mul, Matrix.mul_apply] <;> fun_prop

lemma smooth_reading (q₀ : Env) (hq : Regular q₀) (r a : Fin 6) :
    ContDiffAt ℝ n (fun q : Env =>
      internalStar (lieCoordinates ((-(1 / 2) : ℝ) •
        (cellHolonomy (links q) (inverseLinks q) r -
          cellInverseHolonomy (links q) (inverseLinks q) r))) a) q₀ := by
  have hU := smooth_links (n := n) q₀
  have hV := smooth_inverse_links (n := n) q₀ hq
  fin_cases a <;>
    norm_num [internalStar, lieCoordinates, cellHolonomy, cellInverseHolonomy,
      Matrix.mul_apply] <;> fun_prop


end Artform.Scores.NonabelianGravity.NonlinearAmbient
