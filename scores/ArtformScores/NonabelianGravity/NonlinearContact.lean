import ArtformScores.NonabelianGravity.NonlinearDifferential
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Actual second-order force contact at a complete critical point -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearDifferential
open Filter Topology Asymptotics
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {f : X → ℝ} {x : X}

lemma second_order_contact {u v : ℝ → X}
    (hf : HasStrictFDerivAt f (0 : X →L[ℝ] ℝ) x)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 x)) (hv : Tendsto v (𝓝[≠] 0) (𝓝 x))
    (hd : (fun e => u e - v e) =O[𝓝[≠] 0] (fun e => e ^ 2)) :
    Tendsto (fun e => (f (u e) - f (v e)) / e ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have h := hf.isLittleO.comp_tendsto (hu.prodMk_nhds hv)
  have h' : (fun e => f (u e) - f (v e)) =o[𝓝[≠] 0] (fun e => u e - v e) := by
    simpa using! h
  exact (h'.trans_isBigO hd).tendsto_div_nhds_zero

lemma second_order_limit {u v : ℝ → X} {a : ℝ}
    (hf : HasStrictFDerivAt f (0 : X →L[ℝ] ℝ) x)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 x)) (hv : Tendsto v (𝓝[≠] 0) (𝓝 x))
    (hd : (fun e => u e - v e) =O[𝓝[≠] 0] (fun e => e ^ 2))
    (ha : Tendsto (fun e => f (v e) / e ^ 2) (𝓝[≠] 0) (𝓝 a)) :
    Tendsto (fun e => f (u e) / e ^ 2) (𝓝[≠] 0) (𝓝 a) := by
  have hh := (second_order_contact hf hu hv hd).add ha
  convert hh using 1
  · funext e
    rw [sub_div]
    ring
  · ring

end Artform.Scores.NonabelianGravity.NonlinearDifferential
