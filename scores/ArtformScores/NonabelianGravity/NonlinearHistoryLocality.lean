import ArtformScores.NonabelianGravity.NonlinearNativeChart

/-! # Original four-cell lapse variation, retaining arbitrary neighboring fields -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable def densityWeight (E : Mat) (r s : Fin 6) : ℝ :=
  E.det * (metric E (face r).1 (face s).1 * metric E (face r).2 (face s).2 -
    metric E (face r).1 (face s).2 * metric E (face r).2 (face s).1)
noncomputable def density (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) : ℝ :=
  (∑ r, cellCurvatureFace E U (fun t k => (U t k)⁻¹) r) +
  (1 / 101 : ℝ) * ∑ r, ∑ s, densityWeight (E 0) r s *
    etaPair (cellTorsionFace E (fun t k => (U t k)⁻¹) r)
      (cellTorsionFace E (fun t k => (U t k)⁻¹) s)

lemma density_congr {E F : ℕ → Mat} {U V : ℕ → Fin 4 → Mat}
    (hE₀ : E 0 = F 0) (hE₁ : E 1 = F 1) (hU₀ : U 0 = V 0) (hU₁ : U 1 = V 1) :
    density E U = density F V := by
  have ha (r : Fin 6) : cellAverage E (fun t k => (U t k)⁻¹) r =
      cellAverage F (fun t k => (V t k)⁻¹) r := by
    fin_cases r <;> simp [cellAverage, face, NonlinearIsotropic.shift, hE₀, hE₁, hU₀, hU₁]
  have hH (r : Fin 6) : cellHolonomy U (fun t k => (U t k)⁻¹) r =
      cellHolonomy V (fun t k => (V t k)⁻¹) r := by
    fin_cases r <;> simp [cellHolonomy, face, NonlinearIsotropic.shift, hU₀, hU₁]
  have hV (r : Fin 6) : cellInverseHolonomy U (fun t k => (U t k)⁻¹) r =
      cellInverseHolonomy V (fun t k => (V t k)⁻¹) r := by
    fin_cases r <;> simp [cellInverseHolonomy, face, NonlinearIsotropic.shift, hU₀, hU₁]
  have ht (r : Fin 6) : cellTorsionFace E (fun t k => (U t k)⁻¹) r =
      cellTorsionFace F (fun t k => (V t k)⁻¹) r := by
    fin_cases r <;> simp [cellTorsionFace, face, NonlinearIsotropic.shift, hE₀, hE₁, hU₀]
  simp only [density, cellCurvatureFace, ha, hH, hV, ht, hE₀]

lemma density_incoming_independent (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) (s : ℝ) :
    density (bumpAt E 1 s) U = density E U := by
  simp only [density, curvature_future_lapse_independent, torsion_future_lapse_independent]
  simp [bumpAt]

noncomputable def cellEnv (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) : Env := ((E 0, E 1), U 0)

lemma density_lapse_difference (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) (s : ℝ) :
    density (bumpAt E 0 s) U - density E U =
      (localCurvature (cellEnv E U + s • lapseDirection) +
        localTorsion (cellEnv E U + s • lapseDirection)) -
      (localCurvature (cellEnv E U) + localTorsion (cellEnv E U)) := by
  have hc (r : Fin 6) :
      cellCurvatureFace (bumpAt E 0 s) U (fun t k => (U t k)⁻¹) r -
        cellCurvatureFace E U (fun t k => (U t k)⁻¹) r =
      cellCurvatureFace (frames (cellEnv E U + s • lapseDirection))
        (links (cellEnv E U + s • lapseDirection))
        (inverseLinks (cellEnv E U + s • lapseDirection)) r -
      cellCurvatureFace (frames (cellEnv E U)) (links (cellEnv E U))
        (inverseLinks (cellEnv E U)) r := by
    by_cases hr : r.val < 3
    · have hT := average_current_temporal_independent E (fun t k => (U t k)⁻¹) s r hr
      have hA := average_temporal_line (cellEnv E U) s r hr
      have hL : links (cellEnv E U + s • lapseDirection) = links (cellEnv E U) := by
        funext t k
        simp [links, lapseDirection]
      simp only [inverseLinks_lapse_line] at hA
      simp only [cellCurvatureFace, hT, inverseLinks_lapse_line, hA, hL, sub_self]
    · fin_cases r <;> norm_num at hr
      all_goals simp [cellCurvatureFace, cellAverage, cellHolonomy, cellInverseHolonomy,
        frames, links, inverseLinks, cellEnv, bumpAt, lapseDirection, face,
        NonlinearIsotropic.shift]
  have ht (r : Fin 6) : cellTorsionFace E (fun t k => (U t k)⁻¹) r = tau (cellEnv E U) r := by
    fin_cases r <;> simp [tau, cellTorsionFace, cellEnv, frames, inverseLinks, links,
      face, NonlinearIsotropic.shift]
  have hts (r : Fin 6) : cellTorsionFace (bumpAt E 0 s) (fun t k => (U t k)⁻¹) r =
      tau (cellEnv E U + s • lapseDirection) r := by
    fin_cases r <;> simp [tau, cellTorsionFace, cellEnv, frames, inverseLinks, links,
      bumpAt, lapseDirection, face, NonlinearIsotropic.shift]
  have hC : (∑ r, cellCurvatureFace (bumpAt E 0 s) U (fun t k => (U t k)⁻¹) r) -
      (∑ r, cellCurvatureFace E U (fun t k => (U t k)⁻¹) r) =
      localCurvature (cellEnv E U + s • lapseDirection) - localCurvature (cellEnv E U) := by
    simp only [localCurvature, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => hc r)
  have hW (r t : Fin 6) : densityWeight (E 0) r t = weight (cellEnv E U) r t := rfl
  have hWs (r t : Fin 6) : densityWeight ((bumpAt E 0 s) 0) r t =
      weight (cellEnv E U + s • lapseDirection) r t := by
    simp [densityWeight, weight, cellEnv, bumpAt, lapseDirection]
  simp only [density, ht, hts, hW, hWs]
  change _ = _
  dsimp only [localTorsion]
  linear_combination hC

noncomputable def cellAt (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) (t : ℕ) : ℝ :=
  density (fun k => E (t + k)) (fun k => U (t + k))
noncomputable def fourCellAction (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) : ℝ :=
  ∑ t : Fin 4, cellAt E U t.val

lemma other_cell_independent (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat)
    (n t : ℕ) (hnt : n ≠ t) (s : ℝ) :
    cellAt (bumpAt E n s) U t = cellAt E U t := by
  by_cases hn : n = t + 1
  · have he : cellAt (bumpAt E n s) U t =
        density (bumpAt (fun k => E (t + k)) 1 s) (fun k => U (t + k)) := by
      apply density_congr <;> simp [bumpAt, hn]
    rw [he, density_incoming_independent]
    rfl
  · apply density_congr <;> simp [bumpAt, Ne.symm hnt, Ne.symm hn]

lemma full_history_lapse_difference (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat)
    (n : Fin 4) (s : ℝ) :
    fourCellAction (bumpAt E n.val s) U - fourCellAction E U =
      action (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)) + s • lapseDirection) -
        action (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k))) := by
  have hsum : fourCellAction (bumpAt E n.val s) U - fourCellAction E U =
      cellAt (bumpAt E n.val s) U n.val - cellAt E U n.val := by
    unfold fourCellAction
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single n
    · intro t _ htn
      rw [other_cell_independent E U n.val t.val (fun h => htn (Fin.ext h.symm)) s, sub_self]
    · simp
  rw [hsum]
  have he : cellAt (bumpAt E n.val s) U n.val =
      density (bumpAt (fun k => E (n.val + k)) 0 s) (fun k => U (n.val + k)) := by
    apply density_congr <;> simp [bumpAt]
  rw [he]
  have hd := density_lapse_difference (fun k => E (n.val + k)) (fun k => U (n.val + k)) s
  simp only [action, preceding_curvature_lapse_line, preceding_torsion_lapse_line]
  dsimp only [cellAt] at hd ⊢
  linear_combination hd

lemma full_history_force_binding (E : ℕ → Mat) (U : ℕ → Fin 4 → Mat) (n : Fin 4)
    (hq : Regular (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)))) :
    HasDerivAt (fun s => fourCellAction (bumpAt E n.val s) U)
      (force (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)))) 0 := by
  let q := cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k))
  have hd := directional_hasDerivAt (v := lapseDirection)
    ((smooth_action (n := 1) q hq).differentiableAt (by norm_num))
  have h := hd.const_add (fourCellAction E U - action q)
  apply h.congr_of_eventuallyEq
  filter_upwards [] with s
  have he := full_history_lapse_difference E U n s
  dsimp [q] at h ⊢
  linear_combination he

end Artform.Scores.NonabelianGravity.NonlinearAmbient
