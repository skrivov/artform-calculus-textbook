import Mathlib.Logic.Function.Iterate
import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# Time reversal of the Maxwell tick (Corollary 6.2)

The book derives the involution from Proposition 5.39, as flip-then-move
`M ∘ R` with the flip `R(A, E, J, ρ) = (−A, E, −J, ρ)`. Here the identities are
checked by computation, which needs only that `curl*(curl ·)` and `div` are
additive: one tick, the reversal, a tick and the reversal again give back the
state, in either order.
-/

namespace Artform

variable (K : Canvas)

/-- The reversal undoes itself. -/
theorem maxwellTimeReversal_involutive (s : MaxwellSourceState K) :
    maxwellTimeReversal K (maxwellTimeReversal K s) = s := by
  obtain ⟨A, E, J, ρ⟩ := s
  simp only [maxwellTimeReversal, neg_neg, sub_neg_eq_add, neg_sub,
    MaxwellSourceState.mk.injEq, and_true]
  abel

/-- `I ∘ F ∘ I ∘ F = id`. -/
theorem maxwellReversal_tick_left (s : MaxwellSourceState K) :
    maxwellTimeReversal K (maxwellSourceTick K (maxwellTimeReversal K (maxwellSourceTick K s)))
      = s := by
  obtain ⟨A, E, J, ρ⟩ := s
  simp only [maxwellTimeReversal, maxwellSourceTick, maxwellTick, MaxwellSourceState.mk.injEq]
  refine ⟨?_, ?_, neg_neg J, ?_⟩
  · simp only [Canvas.curl_sub, Canvas.curl_neg, Canvas.curl_add, Canvas.curlStar_sub,
      Canvas.curlStar_neg, Canvas.curlStar_add]
    abel
  · simp only [Canvas.curl_sub, Canvas.curl_neg, Canvas.curl_add, Canvas.curlStar_sub,
      Canvas.curlStar_neg, Canvas.curlStar_add]
    abel
  · simp only [Canvas.div_neg]
    abel

/-- `F ∘ I ∘ F ∘ I = id`. -/
theorem maxwellReversal_tick_right (s : MaxwellSourceState K) :
    maxwellSourceTick K (maxwellTimeReversal K (maxwellSourceTick K (maxwellTimeReversal K s)))
      = s := by
  obtain ⟨A, E, J, ρ⟩ := s
  simp only [maxwellTimeReversal, maxwellSourceTick, maxwellTick, MaxwellSourceState.mk.injEq]
  refine ⟨?_, ?_, neg_neg J, ?_⟩
  · simp only [Canvas.curl_sub, Canvas.curl_neg, Canvas.curl_add, Canvas.curlStar_sub,
      Canvas.curlStar_neg, Canvas.curlStar_add]
    abel
  · simp only [Canvas.curl_sub, Canvas.curl_neg, Canvas.curl_add, Canvas.curlStar_sub,
      Canvas.curlStar_neg, Canvas.curlStar_add]
    abel
  · simp only [Canvas.div_neg]
    abel

/-- **Corollary 6.2** (time reversal of the Maxwell tick). The map
`I(A, E, J, ρ) = (−A − E, E, −J, ρ)` is an involution that reads each link and
each site alone, `I ∘ F ∘ I` is the inverse of `F`, and a run read backwards
through `I` is a run. -/
@[book "cor:maxwell-reversal"]
theorem maxwellReversal : Statement.maxwellReversal := by
  intro K
  refine ⟨funext (maxwellTimeReversal_involutive K), ?_, ?_,
    funext (maxwellReversal_tick_left K), funext (maxwellReversal_tick_right K), ?_⟩
  · intro s t e hA hE hJ
    simp only [maxwellTimeReversal, Pi.sub_apply, Pi.neg_apply, hA, hE, hJ, and_self]
  · intro s t v hρ
    simp only [maxwellTimeReversal, hρ]
  · -- `F(I(x_{k+1})) = I(x_k)`, from `F ∘ I ∘ F = I`, along the run.
    intro x m t ht
    induction t with
    | zero => simp [DetLaw.run]
    | succ t ih =>
      have hm : m - t = (m - (t + 1)) + 1 := by omega
      simp only [DetLaw.run] at ih ⊢
      rw [Function.iterate_succ_apply', ih (by omega), hm, Function.iterate_succ_apply']
      have h := congrArg (maxwellTimeReversal K)
        (maxwellReversal_tick_left K ((maxwellSourceLaw K).tick^[m - (t + 1)] x))
      rw [maxwellTimeReversal_involutive] at h
      exact h

/-! ## Non-vacuity -/

/-- On the face of Figure 6.7, the state with `A = (1, 2, 0, 3)`,
`E = (0, 0, 1, 0)` and the current `J = (1, 0, 0, 0)` of the checkpoint after
it is not fixed by `I`, and `I` reverses its tick. -/
example : let s : MaxwellSourceState oneFace :=
      ⟨![1, 2, 0, 3], ![0, 0, 1, 0], ![1, 0, 0, 0], ![0, 0, 1, 7]⟩
    maxwellTimeReversal oneFace s ≠ s ∧
    maxwellTimeReversal oneFace (maxwellSourceTick oneFace
      (maxwellTimeReversal oneFace (maxwellSourceTick oneFace s))) = s := by
  intro s
  refine ⟨fun h => ?_, maxwellReversal_tick_left oneFace s⟩
  have h1 := congrFun (congrArg MaxwellSourceState.J h) 0
  revert h1
  decide

end Artform
