import ArtformScores.GravityBridge.Native.GreenComposition.PanelDefs

/-! # Finite owned-panel variation and source covectors -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:factorized-owned-panel-variation**
(finite owned-panel variation and source covectors). -/
@[ledger "GAC2:factorized-owned-panel-variation"]
def panelLaw : Prop :=
  ∀ (K : Type) [CommRing K],
    (∀ (c e : K) (u v : ℕ → K) (N : ℕ),
    panelAction c (fun i => u i + e * v i) N = panelAction c u N +
      e * (∑ i ∈ Finset.range N, panelFlux c u i * (v (i + 1) - v i)) +
      e ^ 2 * panelAction c v N) ∧
    (∀ (p v : ℕ → K) (N : ℕ),
    (∑ i ∈ Finset.range N, p i * (v (i + 1) - v i)) +
      (∑ i ∈ Finset.range N, (p (i + 1) - p i) * v (i + 1)) =
      p N * v N - p 0 * v 0) ∧
    (∀ (p v : ℕ → K) (N : ℕ),
    (∑ i ∈ Finset.range (N + 1), p i * (v (i + 1) - v i)) =
      p N * v (N + 1) - p 0 * v 0-
        (∑ i ∈ Finset.range N, (p (i + 1) - p i) * v (i + 1)))

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
