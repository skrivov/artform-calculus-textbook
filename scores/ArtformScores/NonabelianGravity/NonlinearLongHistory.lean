import ArtformScores.NonabelianGravity.NonlinearIsotropicLeading
import ArtformScores.NonabelianGravity.HistoryBinding

/-! # A four-cell history satisfying every original linear matching equation -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearLongHistory
open Legendre HistoryElimination NonlinearIsotropic

def frameRate : Fin 3 → ℚ := ![30401 / 82804, 20501 / 41402, 31803 / 82804]
def boostRate : Fin 3 → ℚ := ![-5150 / 20701, -200 / 20701, -5150 / 20701]
def nextRate : Fin 3 → ℚ := ![20501 / 41402, 31803 / 82804, 1]
def field (t : Fin 3) : Point ℚ := fun i =>
  if i = 5 ∨ i = 10 ∨ i = 15 then frameRate t
  else if i = 22 ∨ i = 29 ∨ i = 36 then boostRate t else 0

def history : Vector 3 := fun ti => field ti.1 ti.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- All120 original equations, with both endpoint cells and all40 components per site.
lemma complete_linear_match : NativeMatch 0 preparedFinal 0 history := by
  intro t
  fin_cases t <;>
    norm_num [previous, following, row, history] <;>
    rw [matching_iff] <;> decide +kernel

def coefficient (t : Fin 3) : ℚ :=
  3 * ((100 / 101) * boostRate t ^ 2 + (1 / 101) * (nextRate t - frameRate t) ^ 2)

lemma coefficient_values : coefficient =
    ![1263813303 / 6856502416, 4414503 / 6856502416, 1337735703 / 6856502416] := by
  decide +kernel

lemma coefficients_positive (t : Fin 3) : 0 < coefficient t := by
  rw [coefficient_values]
  fin_cases t <;> norm_num

end Artform.Scores.NonabelianGravity.NonlinearLongHistory
