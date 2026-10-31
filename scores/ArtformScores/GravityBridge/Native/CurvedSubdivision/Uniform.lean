import ArtformScores.GravityBridge.Native.CurvedSubdivision.UniformStatements

/-! # Original uniform subdivision has an interior detail residual -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



noncomputable section

lemma source_incidence_consistency {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)) :
    vertexVariation k e.castSucc = rootVariation k e ∧
    vertexVariation k e.succ - rootVariation k e = edgeVariation k e := by
  have hi : e.succ = (outgoingSlot k).castSucc ↔ e = incomingSlot k := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [outgoingSlot, Fin.val_succ, Fin.val_castSucc] at hv
      dsimp [incomingSlot]
      omega
    · intro h
      subst e
      rfl
  have hb : e.castSucc = (outgoingSlot k).castSucc ↔ e = outgoingSlot k := by
    exact Fin.castSucc_inj
  constructor
  · simp only [vertexVariation, rootVariation, hb]
  · simp only [vertexVariation, rootVariation, edgeVariation, hi]

lemma actual_coarse_endpoint_phases {N : ℕ} (k : Fin (N + 1)) (u t : ℝ) :
    perturbedPhase k u t 0 = 0 ∧
      perturbedPhase k u t (Fin.last (N + 2)) = (N + 2 : ℝ) * u := by
  have h0 : (0 : Fin (N + 3)) ≠ (outgoingSlot k).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [outgoingSlot, Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hv
    omega
  have hn : Fin.last (N + 2) ≠ (outgoingSlot k).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, outgoingSlot, Fin.val_castSucc, Fin.val_succ] at hv
    have hk := k.isLt
    omega
  simp [perturbedPhase, vertexVariation, h0, hn]

lemma exact_owned_phase_difference {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)) (u t : ℝ) :
    perturbedPhase k u t e.succ - perturbedPhase k u t e.castSucc =
      u + t * edgeVariation k e := by
  have h := source_incidence_consistency k e
  simp only [perturbedPhase, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, h.1]
  linear_combination t * h.2

lemma actual_full_native_chain_binding {N : ℕ} (k : Fin (N + 1)) (b u t : ℝ) (hb : b ≠ 0) :
    literalNativeChain b (perturbedPhase k u t) = uniformNativeDetail k b u t := by
  have hh : (1 / (N + 2 : ℝ)) ≠ 0 := by positivity
  have hcell (e : Fin (N + 2)) :
      fullOriginalCell (1 / (N + 2 : ℝ)) b
        (Real.cosh (perturbedPhase k u t e.castSucc)) (Real.sinh (perturbedPhase k u t e.castSucc))
        (Real.cosh (perturbedPhase k u t e.succ)) (Real.sinh (perturbedPhase k u t e.succ)) =
      -b * Real.sinh (u + t * edgeVariation k e)-
        (2 / 101 : ℝ) * (1 / (N + 2)) * b *
          (Real.cosh ((e.val : ℝ) * u + t * rootVariation k e) - 1) := by
    rw [complete_original_cell_value _ _ _ _ _ _ hh hb
      (Real.cosh_sq_sub_sinh_sq (perturbedPhase k u t e.castSucc))]
    have hf :
        Real.cosh (perturbedPhase k u t e.castSucc) * Real.sinh (perturbedPhase k u t e.succ)-
          Real.sinh (perturbedPhase k u t e.castSucc) * Real.cosh (perturbedPhase k u t e.succ) =
        Real.sinh (u + t * edgeVariation k e) := by
      rw [← exact_owned_phase_difference k e u t, Real.sinh_sub]
      ring
    rw [hf]
    simp only [perturbedPhase, Fin.val_castSucc, (source_incidence_consistency k e).1]
  unfold literalNativeChain
  simp_rw [hcell]
  unfold uniformNativeDetail
  rw [Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma actual_native_chain_detail_residual {N : ℕ} (k : Fin (N + 1)) (b u : ℝ)
    (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (fun t => literalNativeChain b (perturbedPhase k u t))
      (-(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u)) 0 ∧
    -(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) ≠ 0 := by
  have he : (fun t => literalNativeChain b (perturbedPhase k u t)) = uniformNativeDetail k b u := by
    funext t
    exact actual_full_native_chain_binding k b u t (ne_of_gt hb)
  rw [he]
  exact ⟨exact_interior_source_derivative k b u,
    every_uniform_subdivision_has_detail_residual k b u hb hu⟩

/-- **GAC2:native-uniform-detail-residual**
(original uniform subdivision has an interior detail residual). -/
@[ledger "GAC2:native-uniform-detail-residual"]
theorem uniformLaw : Statement.uniformLaw := by
  exact ⟨source_incidence_consistency,
    actual_coarse_endpoint_phases,
    exact_owned_phase_difference,
    actual_full_native_chain_binding,
    actual_native_chain_detail_residual⟩

/-! ## Non-vacuity -/
example : literalNativeChain (N := 0) 1 (perturbedPhase 0 (Real.log 2) 0) =
    uniformNativeDetail (N := 0) 0 1 (Real.log 2) 0 :=
  actual_full_native_chain_binding 0 1 (Real.log 2) 0 (by norm_num)
end

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
