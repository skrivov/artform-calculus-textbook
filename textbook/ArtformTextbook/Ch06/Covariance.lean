import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# Gauge covariance of the Maxwell tick (Theorem 6.3)

The kick reads the potential only through `curl A`, and `curl D = 0`, so it
writes the same `E'` after a gauge change; the Faraday move then writes
`A + Dg − E' = A' + Dg`. Each move of the law keeps its footprints and
proposes the gauge change of its old proposal; Gauss's law does not read `A`;
and the realizer selects every move of the open step, whatever the gauge.
-/

namespace Artform

variable {K : Canvas}

/-- The gauge change adds `Dg` to the potential of a table. -/
theorem potentialOf_smul (g : K.V → ZMod 8) (x : (maxwellFrame K).Table) :
    potentialOf ((maxwellGaugeAction K).smul g x) = potentialOf x + K.diff g := rfl

/-- The gauge change fixes the electric links of a table. -/
theorem electricOf_smul (g : K.V → ZMod 8) (x : (maxwellFrame K).Table) :
    electricOf ((maxwellGaugeAction K).smul g x) = electricOf x := rfl

/-- The gauge change fixes the current of a table. -/
theorem currentOf_smul (g : K.V → ZMod 8) (x : (maxwellFrame K).Table) :
    currentOf ((maxwellGaugeAction K).smul g x) = currentOf x := rfl

/-- The gauge change fixes the charges of a table. -/
theorem chargeOf_smul (g : K.V → ZMod 8) (x : (maxwellFrame K).Table) :
    chargeOf ((maxwellGaugeAction K).smul g x) = chargeOf x := rfl

/-- The kick at a link is gauge covariant: it reads the potential through
`curl A` alone. -/
theorem kickMove_covariant (e : K.E) : (maxwellGaugeAction K).CovariantMove (kickMove K e) := by
  intro g x _
  refine ⟨trivial, fun p hp => ?_⟩
  obtain rfl : p = .E e := hp
  change x (.E e) + K.curlStar (K.curl (potentialOf ((maxwellGaugeAction K).smul g x))) e
      - x (.J e) = x (.E e) + K.curlStar (K.curl (potentialOf x)) e - x (.J e)
  rw [potentialOf_smul, Canvas.curl_add, Canvas.curl_diff, add_zero]

/-- The Faraday move at a link is gauge covariant: it proposes `A + Dg − E`. -/
theorem faradayMove_covariant (e : K.E) :
    (maxwellGaugeAction K).CovariantMove (faradayMove K e) := by
  intro g x _
  refine ⟨trivial, fun p hp => ?_⟩
  obtain rfl : p = .A e := hp
  change x (.A e) + K.diff g e - x (.E e) = x (.A e) - x (.E e) + K.diff g e
  abel

/-- The charge update at a site is gauge covariant: it reads no potential. -/
theorem chargeMove_covariant (v : K.V) :
    (maxwellGaugeAction K).CovariantMove (chargeMove K v) := by
  intro g x _
  refine ⟨trivial, fun p hp => ?_⟩
  obtain rfl : p = .ρ v := hp
  rfl

/-- The batch the realizer selects in a step is the list of that step's moves,
at every state. -/
theorem maxwellSelect_moves (σ : MaxwellStep) (x : (maxwellFrame K).Table) :
    (maxwellSelect K σ x).moves = maxwellStepMoves K σ := by
  cases σ <;>
    simp [maxwellSelect, Batch.moves, maxwellStepMoves, List.map_append, Function.comp_def]

/-- **Theorem 6.3** (gauge covariance of the Maxwell tick). The macro-tick
commutes with `A ↦ A + Dg`, which fixes `E` and `ρ`; the law's moves and its
invariant are gauge covariant; and its realizer selects the same batch at
`g · x` as at `x`. -/
@[book "thm:maxwell-covariant"]
theorem maxwellCovariant : Statement.maxwellCovariant := by
  refine ⟨fun K J g s => ?_, fun K => ⟨fun u hu => ?_, fun g x => ?_⟩,
    fun K σ g x _ => ?_⟩
  · -- `curl (A + Dg) = curl A`, so the kick writes the same `E'`.
    obtain ⟨A, E, ρ⟩ := s
    simp only [maxwellTick, MaxwellState.gauge, MaxwellState.mk.injEq, Canvas.curl_add,
      Canvas.curl_diff, add_zero, and_true]
    abel
  · simp only [maxwellMoves, maxwellStepMoves, List.mem_append, List.mem_map,
      Finset.mem_toList, Finset.mem_univ, true_and] at hu
    rcases hu with (⟨e, rfl⟩ | ⟨v, rfl⟩) | ⟨e, rfl⟩
    · exact kickMove_covariant e
    · exact chargeMove_covariant v
    · exact faradayMove_covariant e
  · -- Gauss's law reads `E` and `ρ`, which the gauge change fixes.
    simp only [maxwellInvariants, List.mem_singleton, forall_eq]
    exact Iff.rfl
  · rw [maxwellSelect_moves, maxwellSelect_moves]

/-! ## Non-vacuity -/

/-- On the face of Figure 6.7, the tick of the state `A = (1, 2, 0, 3)`,
`E = (0, 0, 1, 0)` with no current commutes with the gauge change by `1` at the
corner `c₁`, which changes the potential. -/
example : let s : MaxwellState oneFace := ⟨![1, 2, 0, 3], ![0, 0, 1, 0], ![0, 0, 1, 7]⟩
    let g : oneFace.V → ZMod 8 := ![1, 0, 0, 0]
    s.gauge g ≠ s ∧ maxwellTick oneFace 0 (s.gauge g) = (maxwellTick oneFace 0 s).gauge g := by
  intro s g
  refine ⟨fun h => ?_, maxwellCovariant.1 oneFace 0 g s⟩
  have h1 := congrFun (congrArg MaxwellState.A h) 0
  revert h1
  decide

/-- The law has a legal state: on the face of Figure 6.7, the potential
`A = (1, 2, 0, 3)`, the electric links `E = (0, 0, 1, 0)`, no current, and the
charges `0, 0, 1, 7` at the corners satisfy Gauss's law, as Figure 6.8 shows. -/
example : maxwellLegal oneFace (fun p => match p with
    | .A e => ![1, 2, 0, 3] e
    | .E e => ![0, 0, 1, 0] e
    | .J _ => 0
    | .ρ v => ![0, 0, 1, 7] v) := by
  intro J hJ
  rw [maxwellInvariants, List.mem_singleton] at hJ
  subst hJ
  unfold gaussLaw
  decide

end Artform
