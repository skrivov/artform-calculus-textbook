import ArtformScores.GravityBridge.Native.GreenComposition.PanelStatements

/-! # Finite owned-panel variation and source covectors -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [CommRing K]

open scoped BigOperators
lemma panel_exact_variation (c e : K) (u v : ℕ → K) (N : ℕ) :
    panelAction c (fun i => u i + e * v i) N = panelAction c u N +
      e * (∑ i ∈ Finset.range N, panelFlux c u i * (v (i + 1) - v i)) +
      e ^ 2 * panelAction c v N := by
  simp only [panelAction, panelFlux, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma factorized_flux_green (p v : ℕ → K) (N : ℕ) :
    (∑ i ∈ Finset.range N, p i * (v (i + 1) - v i)) +
      (∑ i ∈ Finset.range N, (p (i + 1) - p i) * v (i + 1)) =
      p N * v N - p 0 * v 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination ih

lemma panel_source_interior (p v : ℕ → K) (N : ℕ) :
    (∑ i ∈ Finset.range N, p i * (v (i + 1) - v i)) =
      p N * v N - p 0 * v 0-
        (∑ i ∈ Finset.range N, (p (i + 1) - p i) * v (i + 1)) := by
  have he := factorized_flux_green p v N
  linear_combination he

lemma owned_panel_endpoints (p v : ℕ → K) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), p i * (v (i + 1) - v i)) =
      p N * v (N + 1) - p 0 * v 0-
        (∑ i ∈ Finset.range N, (p (i + 1) - p i) * v (i + 1)) := by
  rw [Finset.sum_range_succ]
  have he := factorized_flux_green p v N
  linear_combination he

/-- **GAC2:factorized-owned-panel-variation**
(finite owned-panel variation and source covectors). -/
@[ledger "GAC2:factorized-owned-panel-variation"]
theorem panelLaw : Statement.panelLaw := by
  intro K _
  exact ⟨panel_exact_variation,
    factorized_flux_green,
    owned_panel_endpoints⟩

/-! ## Non-vacuity -/
example : panelAction (1 / 101 : ℚ) (fun i => (i : ℚ)) 2 = 2 / 101 ∧
    panelFlux (1 / 101 : ℚ) (fun i => (i : ℚ)) 0 = 2 / 101 := by
  norm_num [panelAction, panelFlux]

end Artform.Scores.GravityBridge.Native.GreenComposition
