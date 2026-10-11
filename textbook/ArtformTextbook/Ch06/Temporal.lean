import Mathlib.Logic.Function.Iterate
import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# Gauge changes from tick to tick (Proposition 6.7, Theorem 6.9)

The kick reads the potential only through `curl*(curl ·)`, and `curl D = 0`,
so a gauge change at every tick keeps every kick; Gauss's law reads `E` and
`ρ`, which do not change; and the Faraday move, with `Dχ_{t+1}` added to both
sides, fails by `D(χ_{t+1} − χ_t)`. With temporal links the failure is taken up
by the links, and the gauge change `χ_{t+1} = χ_t − a₀(t)` sets them all to
`0`.
-/

namespace Artform

variable {K : Canvas}

/-- The kick, with its charge update, does not see a gauge change. -/
theorem maxwellTick_gauge_E (J : K.E → ZMod 8) (g : K.V → ZMod 8) (s : MaxwellState K) :
    (maxwellTick K J (s.gauge g)).E = (maxwellTick K J s).E := by
  simp [maxwellTick, MaxwellState.gauge]

theorem maxwellTick_gauge_ρ (J : K.E → ZMod 8) (g : K.V → ZMod 8) (s : MaxwellState K) :
    (maxwellTick K J (s.gauge g)).ρ = (maxwellTick K J s).ρ := rfl

/-- **Proposition 6.7** (a gauge change that varies from tick to tick). Adding
`Dχ_t` to the potential at every tick of a run keeps every kick and Gauss's
law, and each Faraday move fails by exactly `D(χ_{t+1} − χ_t)`. -/
@[book "prop:gauge-defect"]
theorem gaugeDefect : Statement.gaugeDefect := by
  intro K J s χ hrun t
  refine ⟨?_, ?_, Iff.rfl, ?_⟩
  · rw [maxwellTick_gauge_E, hrun t]
    rfl
  · rw [maxwellTick_gauge_ρ, hrun t]
    rfl
  · -- the run's Faraday move is `A_{t+1} = A_t − E_{t+1}`
    have hA : (s (t + 1)).A = (s t).A - (s (t + 1)).E := by
      rw [hrun t]
      rfl
    rw [hA, Canvas.diff_sub]
    abel

/-- **Theorem 6.9** (temporal links). Every gauge change carries runs of the
extended tick to runs, and the gauge change with `χ_0 = 0` and
`χ_{t+1} = χ_t − a₀(t)` carries every run of the extended tick to a run of the
Maxwell tick with all temporal links `0`, the same `E`, the same `curl A` and
the same `div E − ρ`. -/
@[book "thm:temporal-links"]
theorem temporalLinks : Statement.temporalLinks := by
  intro K J
  -- (i) the gauge change keeps the kick, and `Dχ_t + D(χ_{t+1} − χ_t) = Dχ_{t+1}`
  have hcarry : ∀ (s : ℕ → MaxwellState K) (a : TemporalLinks K) (χ : ℕ → K.V → ZMod 8),
      IsExtendedRun K J s a → IsExtendedRun K J (gaugeStates χ s) (gaugeLinks χ a) := by
    intro s a χ hrun t
    simp only [gaugeStates, gaugeLinks, hrun t, extendedTick, maxwellTick, MaxwellState.gauge,
      MaxwellState.mk.injEq, Canvas.curl_add, Canvas.curl_diff, add_zero, Canvas.diff_add,
      Canvas.diff_sub, and_true]
    abel
  refine ⟨hcarry, fun s a χ _h0 hχ hrun => ?_⟩
  have hlinks : ∀ t, gaugeLinks χ a t = 0 := fun t => by
    simp only [gaugeLinks, hχ t]
    abel
  refine ⟨hlinks, fun t => ?_, fun t => ⟨rfl, ?_, rfl⟩⟩
  · -- with every temporal link `0`, the extended tick is the Maxwell tick
    rw [hcarry s a χ hrun t, hlinks t]
    obtain ⟨A, E, ρ⟩ := gaugeStates χ s t
    simp [extendedTick]
  · simp [gaugeStates, MaxwellState.gauge]

/-! ## Non-vacuity -/

/-- A run of the Maxwell tick, on the face of Figure 6.7 from the state
`A = (1, 2, 0, 3)`, `E = (0, 0, 1, 0)`, with no current. -/
noncomputable def oneFaceRun : ℕ → MaxwellState oneFace :=
  fun t => (maxwellTick oneFace 0)^[t] ⟨![1, 2, 0, 3], ![0, 0, 1, 0], ![0, 0, 1, 7]⟩

/-- The hypothesis of Proposition 6.7 met: `oneFaceRun` is a run. -/
example : IsMaxwellRun oneFace 0 oneFaceRun := fun _ =>
  Function.iterate_succ_apply' _ _ _

/-- The temporal links of Figure 6.11(b) on its first tick, `1` at `v₀`, and
`0` after it. -/
def oneFaceLinks : TemporalLinks oneFace := fun t => if t = 0 then ![1, 0, 0, 0] else 0

/-- The run of the extended tick with the temporal links `oneFaceLinks`, from
the potential `(1, 0, 0, 0)` at rest of Figure 6.11(a). -/
def oneFaceExtendedRun : ℕ → MaxwellState oneFace
  | 0 => ⟨![1, 0, 0, 0], 0, 0⟩
  | t + 1 => extendedTick oneFace 0 (oneFaceLinks t) (oneFaceExtendedRun t)

/-- The gauge change of Theorem 6.9(ii) for `oneFaceLinks`. -/
def oneFaceFix : ℕ → oneFace.V → ZMod 8
  | 0 => 0
  | t + 1 => oneFaceFix t - oneFaceLinks t

/-- The hypotheses of Theorem 6.9 met: `oneFaceExtendedRun` is a run of the
extended tick whose temporal links are not all `0`, and `oneFaceFix` starts at
`0` with `χ_{t+1} = χ_t − a₀(t)`. -/
example : IsExtendedRun oneFace 0 oneFaceExtendedRun oneFaceLinks ∧ oneFaceLinks 0 ≠ 0 ∧
    oneFaceFix 0 = 0 ∧ ∀ t, oneFaceFix (t + 1) = oneFaceFix t - oneFaceLinks t := by
  refine ⟨fun t => rfl, fun h => ?_, rfl, fun t => rfl⟩
  have h1 := congrFun h 0
  revert h1
  decide

end Artform
