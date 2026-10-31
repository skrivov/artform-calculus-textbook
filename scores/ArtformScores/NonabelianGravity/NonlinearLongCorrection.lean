import ArtformScores.NonabelianGravity.NonlinearHistoryLocality
import ArtformScores.NonabelianGravity.NonlinearAdmission

/-! # One consistent corrected four-cell history, with all120 native correctors -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearLongCorrection
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearAmbient
open NonlinearLongHistory NonlinearDifferential Filter Topology
open scoped Matrix.Norms.Elementwise
abbrev Corrector := Mat × (Fin 4 → Biv ℝ)
abbrev Corrections := Fin 3 → Corrector

def site (t : Fin 3) : Fin 4 := ⟨t.val + 1, by omega⟩

noncomputable def E (w : Corrections) (e : ℝ) (t : ℕ) : Mat :=
  match t with
  | 1 => frame 1 (1 + (frameRate 0 : ℝ) * e) + e ^ 2 • (w 0).1
  | 2 => frame 1 (1 + (frameRate 1 : ℝ) * e) + e ^ 2 • (w 1).1
  | 3 => frame 1 (1 + (frameRate 2 : ℝ) * e) + e ^ 2 • (w 2).1
  | 4 => frame 1 (1 + e)
  | _ => 1
noncomputable def U (w : Corrections) (e : ℝ) (t : ℕ) (k : Fin 4) : Mat :=
  match t with
  | 1 => cayleyLink (boostCoordinates ((boostRate 0 : ℝ) * e) k + e ^ 2 • (w 0).2 k)
  | 2 => cayleyLink (boostCoordinates ((boostRate 1 : ℝ) * e) k + e ^ 2 • (w 1).2 k)
  | 3 => cayleyLink (boostCoordinates ((boostRate 2 : ℝ) * e) k + e ^ 2 • (w 2).2 k)
  | _ => 1
noncomputable def localCorrector (w : Corrections) (t : Fin 3) : Chart :=
  match t.val with
  | 0 => (((w 0).1, (w 1).1), (w 0).2)
  | 1 => (((w 1).1, (w 2).1), (w 1).2)
  | _ => (((w 2).1, 0), (w 2).2)

lemma local_chart_binding (w : Corrections) (t : Fin 3) (e : ℝ) :
    cellEnv (fun k => E w e ((site t).val + k)) (fun k => U w e ((site t).val + k)) =
      nativeChart (nativeRate (frameRate t) (boostRate t) (nextRate t) e +
        e ^ 2 • localCorrector w t) := by
  fin_cases t
  all_goals
    apply Prod.ext
    · apply Prod.ext
      all_goals
        simp only [cellEnv, E, site, nativeChart, nativeRate, localCorrector,
          frameRate, nextRate]
        simp <;> abel
    · funext k
      simp [cellEnv, U, site, nativeChart, nativeRate, localCorrector, boostRate]

noncomputable def lapseForce (w : Corrections) (t : Fin 3) (e : ℝ) : ℝ :=
  deriv (fun s : ℝ => fourCellAction (bumpAt (E w e) (site t).val s) (U w e)) 0

lemma full_force_limit (w : Corrections) (t : Fin 3) :
    Tendsto (fun e : ℝ => lapseForce w t e / e ^ 2) (𝓝[≠] 0) (𝓝 (coefficient t : ℝ)) := by
  have hreg : ∀ᶠ e in 𝓝 (0 : ℝ),
      Regular (cellEnv (fun k => E w e ((site t).val + k))
        (fun k => U w e ((site t).val + k))) := by
    filter_upwards [corrected_native_eventually_physical
      (frameRate t) (boostRate t) (nextRate t) (localCorrector w t)] with e he
    rw [local_chart_binding]
    exact ⟨ne_of_gt he.1, fun k => by rw [(he.2.2 k).2.1]; norm_num⟩
  have hF : (fun e : ℝ => lapseForce w t e / e ^ 2) =ᶠ[𝓝[≠] 0]
      fun e => force (nativeChart (nativeRate (frameRate t) (boostRate t) (nextRate t) e +
        e ^ 2 • localCorrector w t)) / e ^ 2 := by
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds] with e he
    unfold lapseForce
    rw [(full_history_force_binding (E w e) (U w e) (site t) he).deriv, local_chart_binding]
  apply (show Tendsto (fun e : ℝ =>
      force (nativeChart (nativeRate (frameRate t) (boostRate t) (nextRate t) e +
        e ^ 2 • localCorrector w t)) / e ^ 2) (𝓝[≠] 0) (𝓝 (coefficient t : ℝ))
    from ?_).congr' hF.symm
  convert native_all_corrections_limit (frameRate t) (boostRate t) (nextRate t)
    (localCorrector w t) using 1
  push_cast [coefficient]
  rfl

lemma every_lapse_eventually_nonzero (w : Corrections) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), ∀ t : Fin 3, lapseForce w t e ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro t
  have hp : (coefficient t : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (coefficient t : ℝ) := by exact_mod_cast coefficients_positive t
    exact ne_of_gt h
  have ht := (full_force_limit w t).eventually (eventually_ne_nhds hp)
  filter_upwards [ht] with e he
  intro hz
  exact he (by rw [hz, zero_div])

lemma no_source_free_extension (w : Corrections) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), ¬∀ t : Fin 3, lapseForce w t e = 0 := by
  filter_upwards [every_lapse_eventually_nonzero w] with e he
  intro h
  exact he 0 (h 0)

lemma fixed_endpoints (w : Corrections) (e : ℝ) :
    E w e 0 = 1 ∧ E w e 4 = frame 1 (1 + e) := by simp [E]

lemma every_owned_chart_admitted (w : Corrections) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ t : Fin 3,
      Physical (cellEnv (fun k => E w e ((site t).val + k))
        (fun k => U w e ((site t).val + k))) := by
  apply Filter.eventually_all.mpr
  intro t
  filter_upwards [corrected_native_eventually_physical
    (frameRate t) (boostRate t) (nextRate t) (localCorrector w t)] with e he
  rw [local_chart_binding]
  exact he

end Artform.Scores.NonabelianGravity.NonlinearLongCorrection
