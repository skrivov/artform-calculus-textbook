import ArtformScores.NonabelianGravity.NonlinearIsotropicLeading
import ArtformScores.Meta.Ledger

/-! # Exact source-bound nonlinear isotropic lapse claim -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open NonlinearIsotropic Legendre Filter Topology
open Artform.Scores.GravityBridge.Native.Full40

/-- **NGB:native-isotropic-lapse-constraint** (an exact finite native nonlinear test). -/
@[ledger "NGB:native-isotropic-lapse-constraint"]
def nativeIsotropicLapseConstraint : Prop :=
  (∀ N a : ℝ, (frame N a).det = N * a ^ 3) ∧
  (∀ N a : ℝ, N ≠ 0 → a ≠ 0 → frame N a * frame N⁻¹ a⁻¹ = 1) ∧
  (∀ N a : ℝ, inverseMetric N a = frame N⁻¹ a⁻¹ *
    Matrix.diagonal (fun i => (eta i : ℝ)) * (frame N⁻¹ a⁻¹).transpose) ∧
  (∀ C S : ℝ, C ^ 2 - S ^ 2 = 1 → ∀ k : Fin 4,
    link C (-S) k * link C S k = 1 ∧
    (link C S k).transpose * Matrix.diagonal (fun i => (eta i : ℝ)) * link C S k =
      Matrix.diagonal (fun i => (eta i : ℝ)) ∧ (link C S k).det = 1) ∧
  (∀ κ C S N a c : ℝ, N ≠ 0 → a ≠ 0 → C ^ 2 - S ^ 2 = 1 →
    totalAction κ C S N a c - totalAction κ C S 1 a c =
      (N - 1) * a * closedLapse C S - 3 * κ * a *
        ((c - a) ^ 2 / N - (c - a) ^ 2 + 2 * (N - 1) * (C - 1))) ∧
  (∀ κ C S N a c : ℝ, N ≠ 0 → a ≠ 0 → C ^ 2 - S ^ 2 = 1 →
    HasDerivAt (fun ell => totalAction κ C S ell a c) (lapseForceAt κ C S N a c) N) ∧
  (∀ C S N a c : ℝ, N ≠ 0 → 0 < a → 1 ≤ C → C ≤ 3 / 2 → C ^ 2 - S ^ 2 = 1 →
    (lapseForceAt (1 / 101) C S N a c = 0 ↔ S = 0 ∧ c = a)) ∧
  (post 0 preparedMiddle - pre preparedMiddle preparedFinal = 0) ∧
  (∀ i j : Fin 4, HasDerivAt (fun e : ℝ => frame 1 (1 + (101 / 402) * e) i j)
    ((fieldPoint preparedMiddle).1 i j : ℝ) 0) ∧
  (∀ i j : Fin 4, HasDerivAt (fun e : ℝ => frame 1 (1 + e) i j)
    ((fieldPoint preparedFinal).1 i j : ℝ) 0) ∧
  (∀ k i j : Fin 4, HasDerivAt (fun e : ℝ =>
    link (cayleyC ((-50 / 201) * e)) (cayleyS ((-50 / 201) * e)) k i j)
    ((lie ((fieldPoint preparedMiddle).2 k)) i j : ℝ) 0) ∧
  Tendsto (fun e : ℝ => preparedForce e / e ^ 2) (𝓝[≠] 0) (𝓝 (40501 / 53868)) ∧
  (∀ N : ℝ, N ≠ 0 →
    deriv (fun ell => totalAction (1 / 101) (161605 / 161603) (-804 / 161603)
      ell (40301 / 40200) (101 / 100)) N ≠ 0)

end Artform.Scores.NonabelianGravity.Statement
