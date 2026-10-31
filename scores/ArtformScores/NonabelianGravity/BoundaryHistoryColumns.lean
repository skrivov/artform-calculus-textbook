import ArtformScores.NonabelianGravity.BoundaryHistoryDefs

/-! # Sparse exact Lorentz columns in the actual three-cell interior Hessian -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundaryHistory
open Artform.Scores.NonabelianGravity.Legendre

def firstColumns : Matrix (Fin 40) (Fin 6) ℚ := fun i j =>
  match i.val with
  | 16 => match j.val with
    | 0 => 1
    | _ => 0
  | 17 => match j.val with
    | 1 => 1
    | _ => 0
  | 18 => match j.val with
    | 2 => 1
    | _ => 0
  | 19 => match j.val with
    | 3 => 1
    | _ => 0
  | 20 => match j.val with
    | 4 => 1
    | _ => 0
  | 21 => match j.val with
    | 5 => 1
    | _ => 0
  | _ => 0

def secondColumns : Matrix (Fin 40) (Fin 6) ℚ := fun i j =>
  match i.val with
  | 1 => match j.val with
    | 0 => 1
    | _ => 0
  | 2 => match j.val with
    | 1 => 1
    | _ => 0
  | 3 => match j.val with
    | 2 => 1
    | _ => 0
  | 4 => match j.val with
    | 0 => 1
    | _ => 0
  | 6 => match j.val with
    | 5 => 1
    | _ => 0
  | 7 => match j.val with
    | 4 => -1
    | _ => 0
  | 8 => match j.val with
    | 1 => 1
    | _ => 0
  | 9 => match j.val with
    | 5 => -1
    | _ => 0
  | 11 => match j.val with
    | 3 => 1
    | _ => 0
  | 12 => match j.val with
    | 2 => 1
    | _ => 0
  | 13 => match j.val with
    | 4 => 1
    | _ => 0
  | 14 => match j.val with
    | 3 => -1
    | _ => 0
  | 16 => match j.val with
    | 0 => -1
    | _ => 0
  | 17 => match j.val with
    | 1 => -1
    | _ => 0
  | 18 => match j.val with
    | 2 => -1
    | _ => 0
  | 19 => match j.val with
    | 3 => -1
    | _ => 0
  | 20 => match j.val with
    | 4 => -1
    | _ => 0
  | 21 => match j.val with
    | 5 => -1
    | _ => 0
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- The certificate checks all40 equations for each of the six source-bound columns.
lemma first_columns_null : middleH * firstColumns + mixed * secondColumns = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- The second owned point is varied as well; no row is discarded.
lemma second_columns_null : mixed.transpose * firstColumns + middleH * secondColumns = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The first fixed endpoint remains untouched by the admitted compact parameter.
lemma incoming_columns_zero : mixed * firstColumns = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The final fixed endpoint also has no residual pairing.
lemma outgoing_columns_zero : mixed.transpose * secondColumns = 0 := by decide +kernel

end Artform.Scores.NonabelianGravity.BoundaryHistory
