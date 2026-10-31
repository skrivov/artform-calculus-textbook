import ArtformScores.NonabelianGravity.LegendreSchur
import ArtformScores.GravityBridge.Native.Full40.Ward

/-! # Boundary-respecting compact Lorentz fields for a three-cell native history -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundaryHistory
open Artform.Scores.GravityBridge.Native.Full40
open Artform.Scores.NonabelianGravity.Legendre
variable {K : Type*} [Field K] [CharZero K]

abbrev HistoryTime := Fin 5

def historyStep : Fin 4 → HistoryTime := ![1, 0, 0, 0]

def parameter (w : Biv K) (t : HistoryTime) : Biv K := if t = 2 then w else 0

def gaugeFirst (w : Biv K) (n : Fin 40) : K :=
  if h : 16 ≤ n.val ∧ n.val < 22 then w ⟨n.val - 16, by omega⟩ else 0

def gaugeSecond (w : Biv K) (n : Fin 40) : K :=
  if h : n.val < 16 then
    lie w ⟨n.val / 4, by omega⟩ ⟨n.val % 4, by omega⟩
  else if h : 16 ≤ n.val ∧ n.val < 22 then -w ⟨n.val - 16, by omega⟩ else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Bind the boundary-respecting pair to the original Full40 gauge field.
omit [CharZero K] in
lemma first_binding (w : Biv K) : fieldPoint (gaugeFirst w) =
    gaugeField historyStep (parameter w) 1 := by
  apply Prod.ext
  · funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fieldPoint, gaugeFirst, frameSlot, gaugeField, parameter, lie]
  · funext i a
    fin_cases i <;> fin_cases a <;>
      norm_num [fieldPoint, gaugeFirst, connectionSlot, gaugeField,
        gaugeConnection, parameter, historyStep]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The next site retains the full coframe, including inactive time-column entries.
omit [CharZero K] in
lemma second_binding (w : Biv K) : fieldPoint (gaugeSecond w) =
    gaugeField historyStep (parameter w) 2 := by
  apply Prod.ext
  · funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fieldPoint, gaugeSecond, frameSlot, gaugeField, parameter]
  · funext i a
    fin_cases i <;> fin_cases a <;>
      norm_num [fieldPoint, gaugeSecond, connectionSlot, gaugeField,
        gaugeConnection, parameter, historyStep]

omit [CharZero K] in
lemma endpoint_binding (w : Biv K) (t : HistoryTime) (ht : t = 0 ∨ t = 3 ∨ t = 4) :
    gaugeField historyStep (parameter w) t = 0 := by
  rcases ht with rfl | rfl | rfl
  all_goals
    apply Prod.ext
    · funext i j
      fin_cases i <;> fin_cases j <;> norm_num [gaugeField, parameter, lie]
    · funext i a
      fin_cases i <;> fin_cases a <;>
        norm_num [gaugeField, gaugeConnection, parameter, historyStep]

end Artform.Scores.NonabelianGravity.BoundaryHistory
