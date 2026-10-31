import ArtformScores.NonabelianGravity.NonlinearAdmission

/-! # Every Full40 second-order corrector fails to repair the prepared native history -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic
open Filter Topology
open scoped Matrix.Norms.Elementwise
abbrev OwnedCorrector := Mat × (Fin 4 → Biv ℝ)
noncomputable def ownedChartCorrector (w : OwnedCorrector) : Chart := ((w.1, 0), w.2)
noncomputable def correctedPrepared (w : OwnedCorrector) (e : ℝ) : Env :=
  nativeChart (nativeRate (101 / 402) (-100 / 201) 1 e + e ^ 2 • ownedChartCorrector w)

lemma full40_no_repair (w : OwnedCorrector) :
    Tendsto (fun e : ℝ => force (correctedPrepared w e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (40501 / 53868)) ∧
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), Physical (correctedPrepared w e) ∧ force (correctedPrepared w e) ≠ 0 := by
  have ht : Tendsto (fun e : ℝ => force (correctedPrepared w e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (40501 / 53868)) := by
    convert native_all_corrections_limit (101 / 402) (-100 / 201) 1
      (ownedChartCorrector w) using 1 <;> norm_num [correctedPrepared]
  refine ⟨ht, ?_⟩
  have hn := ht.eventually (eventually_ne_nhds (show (40501 / 53868 : ℝ) ≠ 0 by norm_num))
  have hp : ∀ᶠ e in 𝓝[≠] (0 : ℝ), Physical (correctedPrepared w e) :=
    (corrected_native_eventually_physical (101 / 402) (-100 / 201) 1
    (ownedChartCorrector w)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hn] with e he hn
  refine ⟨he, ?_⟩
  intro hz
  exact hn (by rw [hz, zero_div])

lemma future_boundary_fixed (w : OwnedCorrector) (e : ℝ) :
    (correctedPrepared w e).1.2 = frame 1 (1 + e) := by
  simp [correctedPrepared, nativeChart, nativeRate, ownedChartCorrector, add_comm]

end Artform.Scores.NonabelianGravity.NonlinearAmbient
