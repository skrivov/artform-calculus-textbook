import ArtformScores.NonabelianGravity.NonlinearForceData

/-! # Smoothness of the complete original two-cell action -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open scoped Matrix.Norms.Elementwise
variable {n : WithTop ℕ∞}

lemma smooth_cell_average {E : Env → ℕ → Mat} {V : Env → ℕ → Fin 4 → Mat}
    {x : Env} (hE : ∀ t i j, ContDiffAt ℝ n (fun q => E q t i j) x)
    (hV : ∀ t k i j, ContDiffAt ℝ n (fun q => V q t k i j) x) (r a : Fin 6) :
    ContDiffAt ℝ n (fun q => cellAverage (E q) (V q) r a) x := by
  fin_cases a <;>
    norm_num [cellAverage, transported, wedgeColumns, Pi.smul_apply,
      zsmul_eq_mul, Matrix.mul_apply] <;> fun_prop

lemma smooth_cell_tau {E : Env → ℕ → Mat} {V : Env → ℕ → Fin 4 → Mat}
    {x : Env} (hE : ∀ t i j, ContDiffAt ℝ n (fun q => E q t i j) x)
    (hV : ∀ t k i j, ContDiffAt ℝ n (fun q => V q t k i j) x) (r : Fin 6) (i : Fin 4) :
    ContDiffAt ℝ n (fun q => cellTorsionFace (E q) (V q) r i) x := by
  simp only [cellTorsionFace, Matrix.mul_apply]
  fun_prop

lemma smooth_cell_reading {U V : Env → ℕ → Fin 4 → Mat}
    {x : Env} (hU : ∀ t k i j, ContDiffAt ℝ n (fun q => U q t k i j) x)
    (hV : ∀ t k i j, ContDiffAt ℝ n (fun q => V q t k i j) x) (r a : Fin 6) :
    ContDiffAt ℝ n (fun q => internalStar (lieCoordinates ((-(1 / 2) : ℝ) •
      (cellHolonomy (U q) (V q) r - cellInverseHolonomy (U q) (V q) r))) a) x := by
  fin_cases a <;>
    norm_num [internalStar, lieCoordinates, cellHolonomy, cellInverseHolonomy,
      Matrix.mul_apply] <;> fun_prop

lemma smooth_cell_curvature {E : Env → ℕ → Mat} {U V : Env → ℕ → Fin 4 → Mat}
    {x : Env} (hE : ∀ t i j, ContDiffAt ℝ n (fun q => E q t i j) x)
    (hU : ∀ t k i j, ContDiffAt ℝ n (fun q => U q t k i j) x)
    (hV : ∀ t k i j, ContDiffAt ℝ n (fun q => V q t k i j) x) (r : Fin 6) :
    ContDiffAt ℝ n (fun q => cellCurvatureFace (E q) (U q) (V q) r) x := by
  unfold cellCurvatureFace bivPair
  exact ContDiffAt.sum (fun a _ => (contDiffAt_const.mul
    (smooth_cell_average hE hV r a)).mul (smooth_cell_reading hU hV r a))

lemma smooth_action (q₀ : Env) (hq : Regular q₀) : ContDiffAt ℝ n action q₀ := by
  have hpE (t : ℕ) (i j : Fin 4) :
      ContDiffAt ℝ n (fun q : Env => precedingFrames q t i j) q₀ := by
    dsimp [precedingFrames]
    split_ifs <;> fun_prop
  have hpU (t : ℕ) (k i j : Fin 4) :
      ContDiffAt ℝ n (fun q : Env => precedingLinks q t k i j) q₀ := by
    dsimp [precedingLinks]
    split_ifs <;> fun_prop
  have hpV (t : ℕ) (k i j : Fin 4) :
      ContDiffAt ℝ n (fun q : Env => (precedingLinks q t k)⁻¹ i j) q₀ := by
    apply smooth_inverse (hpU t k)
    by_cases ht : t = 1
    · simpa [precedingLinks, ht] using hq.2 k
    · simp [precedingLinks, ht]
  have hc : ContDiffAt ℝ n localCurvature q₀ := by
    unfold localCurvature
    exact ContDiffAt.sum (fun r _ => smooth_cell_curvature
      (smooth_frames q₀) (smooth_links q₀) (smooth_inverse_links q₀ hq) r)
  have ht : ContDiffAt ℝ n localTorsion q₀ := by
    have hw := smooth_weight (n := n) q₀ hq
    have hT := smooth_tau (n := n) q₀ hq
    unfold localTorsion etaPair
    fun_prop
  have hpc : ContDiffAt ℝ n precedingCurvature q₀ := by
    unfold precedingCurvature
    exact ContDiffAt.sum (fun r _ => smooth_cell_curvature hpE hpU hpV r)
  have hpt : ContDiffAt ℝ n precedingTorsion q₀ := by
    have hT := smooth_cell_tau hpE hpV
    unfold precedingTorsion etaPair
    fun_prop
  exact ((hpc.add hpt).add hc).add ht

lemma smooth_force_formula (q₀ : Env) (hq : Regular q₀) :
    ContDiffAt ℝ 1 forceFormula q₀ := by
  have hw := smooth_weight (n := 1) q₀ hq
  have ht := smooth_tau (n := 1) q₀ hq
  have ha (r a : Fin 6) : ContDiffAt ℝ 1 (fun q => average q r a) q₀ :=
    smooth_average q₀ hq r a
  have hr (r a : Fin 6) : ContDiffAt ℝ 1 (fun q => reading q r a) q₀ :=
    smooth_reading q₀ hq r a
  have hda (r a : Fin 6) : ContDiffAt ℝ 1
      (directional lapseDirection (fun q => average q r a)) q₀ :=
    smooth_partial (smooth_average (n := 2) q₀ hq r a)
  have hdt (r : Fin 6) (i : Fin 4) : ContDiffAt ℝ 1
      (directional lapseDirection (fun q => tau q r i)) q₀ :=
    smooth_partial (smooth_tau (n := 2) q₀ hq r i)
  have hdw (r s : Fin 6) : ContDiffAt ℝ 1
      (directional lapseDirection (fun q => weight q r s)) q₀ :=
    smooth_partial (smooth_weight (n := 2) q₀ hq r s)
  unfold forceFormula curvatureForce torsionForce
  fun_prop

end Artform.Scores.NonabelianGravity.NonlinearAmbient
