import ArtformScores.NonabelianGravity.LegendreSource
import ArtformScores.NonabelianGravity.LegendreMatrixData

/-! # Sparse row evaluation of the native Hessian blocks over any characteristic-zero field -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre
variable {K : Type*} [Field K] [CharZero K]

noncomputable def castMatrix (M : Matrix (Fin 40) (Fin 40) ℚ) :
    Matrix (Fin 40) (Fin 40) K := fun i j => (M i j : K)

def oldHProduct (u : Point K) (i : Fin 40) : K :=
  match i.val with
  | 1 => (2 / 101 : K) * u 1 +
      (2 / 101 : K) * u 16 +
      (-1 / 2 : K) * u 33 +
      (1 / 2 : K) * u 38
  | 2 => (2 / 101 : K) * u 2 +
      (2 / 101 : K) * u 17 +
      (1 / 2 : K) * u 27 +
      (-1 / 2 : K) * u 37
  | 3 => (2 / 101 : K) * u 3 +
      (2 / 101 : K) * u 18 +
      (-1 / 2 : K) * u 26 +
      (1 / 2 : K) * u 31
  | 5 => (-2 / 101 : K) * u 5 +
      (2 / 101 : K) * u 22 +
      (1 / 2 : K) * u 29 +
      (1 / 2 : K) * u 36
  | 6 => (-2 / 101 : K) * u 6 +
      (-2 / 101 : K) * u 21 +
      (-1 / 2 : K) * u 23 +
      (2 / 101 : K) * u 28
  | 7 => (-2 / 101 : K) * u 7 +
      (2 / 101 : K) * u 20 +
      (-1 / 2 : K) * u 24 +
      (2 / 101 : K) * u 34
  | 9 => (-2 / 101 : K) * u 9 +
      (2 / 101 : K) * u 21 +
      (2 / 101 : K) * u 23 +
      (-1 / 2 : K) * u 28
  | 10 => (-2 / 101 : K) * u 10 +
      (1 / 2 : K) * u 22 +
      (2 / 101 : K) * u 29 +
      (1 / 2 : K) * u 36
  | 11 => (-2 / 101 : K) * u 11 +
      (-2 / 101 : K) * u 19 +
      (-1 / 2 : K) * u 30 +
      (2 / 101 : K) * u 35
  | 13 => (-2 / 101 : K) * u 13 +
      (-2 / 101 : K) * u 20 +
      (2 / 101 : K) * u 24 +
      (-1 / 2 : K) * u 34
  | 14 => (-2 / 101 : K) * u 14 +
      (2 / 101 : K) * u 19 +
      (2 / 101 : K) * u 30 +
      (-1 / 2 : K) * u 35
  | 15 => (-2 / 101 : K) * u 15 +
      (1 / 2 : K) * u 22 +
      (1 / 2 : K) * u 29 +
      (2 / 101 : K) * u 36
  | 16 => (2 / 101 : K) * u 1 +
      (2 / 101 : K) * u 16 +
      (1 / 2 : K) * u 33 +
      (-1 / 2 : K) * u 38
  | 17 => (2 / 101 : K) * u 2 +
      (2 / 101 : K) * u 17 +
      (-1 / 2 : K) * u 27 +
      (1 / 2 : K) * u 37
  | 18 => (2 / 101 : K) * u 3 +
      (2 / 101 : K) * u 18 +
      (1 / 2 : K) * u 26 +
      (-1 / 2 : K) * u 31
  | 19 => (-2 / 101 : K) * u 11 +
      (2 / 101 : K) * u 14 +
      (-4 / 101 : K) * u 19 +
      (97 / 202 : K) * u 30 +
      (-97 / 202 : K) * u 35
  | 20 => (2 / 101 : K) * u 7 +
      (-2 / 101 : K) * u 13 +
      (-4 / 101 : K) * u 20 +
      (-97 / 202 : K) * u 24 +
      (97 / 202 : K) * u 34
  | 21 => (-2 / 101 : K) * u 6 +
      (2 / 101 : K) * u 9 +
      (-4 / 101 : K) * u 21 +
      (97 / 202 : K) * u 23 +
      (-97 / 202 : K) * u 28
  | 22 => (2 / 101 : K) * u 5 +
      (1 / 2 : K) * u 10 +
      (1 / 2 : K) * u 15 +
      (-2 / 101 : K) * u 22 +
      (1 : K) * u 29 +
      (1 : K) * u 36
  | 23 => (-1 / 2 : K) * u 6 +
      (2 / 101 : K) * u 9 +
      (97 / 202 : K) * u 21 +
      (-4 / 101 : K) * u 23 +
      (-99 / 101 : K) * u 28
  | 24 => (-1 / 2 : K) * u 7 +
      (2 / 101 : K) * u 13 +
      (-97 / 202 : K) * u 20 +
      (-4 / 101 : K) * u 24 +
      (-99 / 101 : K) * u 34
  | 25 => (4 / 101 : K) * u 25 +
      (-99 / 101 : K) * u 32 +
      (-99 / 101 : K) * u 39
  | 26 => (-1 / 2 : K) * u 3 +
      (1 / 2 : K) * u 18 +
      (2 / 101 : K) * u 26 +
      (1 : K) * u 31
  | 27 => (1 / 2 : K) * u 2 +
      (-1 / 2 : K) * u 17 +
      (2 / 101 : K) * u 27 +
      (1 : K) * u 37
  | 28 => (2 / 101 : K) * u 6 +
      (-1 / 2 : K) * u 9 +
      (-97 / 202 : K) * u 21 +
      (-99 / 101 : K) * u 23 +
      (-4 / 101 : K) * u 28
  | 29 => (1 / 2 : K) * u 5 +
      (2 / 101 : K) * u 10 +
      (1 / 2 : K) * u 15 +
      (1 : K) * u 22 +
      (-2 / 101 : K) * u 29 +
      (1 : K) * u 36
  | 30 => (-1 / 2 : K) * u 11 +
      (2 / 101 : K) * u 14 +
      (97 / 202 : K) * u 19 +
      (-4 / 101 : K) * u 30 +
      (-99 / 101 : K) * u 35
  | 31 => (1 / 2 : K) * u 3 +
      (-1 / 2 : K) * u 18 +
      (1 : K) * u 26 +
      (2 / 101 : K) * u 31
  | 32 => (-99 / 101 : K) * u 25 +
      (4 / 101 : K) * u 32 +
      (-99 / 101 : K) * u 39
  | 33 => (-1 / 2 : K) * u 1 +
      (1 / 2 : K) * u 16 +
      (2 / 101 : K) * u 33 +
      (1 : K) * u 38
  | 34 => (2 / 101 : K) * u 7 +
      (-1 / 2 : K) * u 13 +
      (97 / 202 : K) * u 20 +
      (-99 / 101 : K) * u 24 +
      (-4 / 101 : K) * u 34
  | 35 => (2 / 101 : K) * u 11 +
      (-1 / 2 : K) * u 14 +
      (-97 / 202 : K) * u 19 +
      (-99 / 101 : K) * u 30 +
      (-4 / 101 : K) * u 35
  | 36 => (1 / 2 : K) * u 5 +
      (1 / 2 : K) * u 10 +
      (2 / 101 : K) * u 15 +
      (1 : K) * u 22 +
      (1 : K) * u 29 +
      (-2 / 101 : K) * u 36
  | 37 => (-1 / 2 : K) * u 2 +
      (1 / 2 : K) * u 17 +
      (1 : K) * u 27 +
      (2 / 101 : K) * u 37
  | 38 => (1 / 2 : K) * u 1 +
      (-1 / 2 : K) * u 16 +
      (1 : K) * u 33 +
      (2 / 101 : K) * u 38
  | 39 => (-99 / 101 : K) * u 25 +
      (-99 / 101 : K) * u 32 +
      (4 / 101 : K) * u 39
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Normalize one sparse row at a time to keep the exact certificate small.
lemma oldH_product (u : Point K) (i : Fin 40) :
    (castMatrix oldH).mulVec u i = oldHProduct u i := by
  fin_cases i <;>
    norm_num [castMatrix, oldH, oldHProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def newHProduct (u : Point K) (i : Fin 40) : K :=
  match i.val with
  | 1 => (2 / 101 : K) * u 1 +
      (1 / 2 : K) * u 33 +
      (-1 / 2 : K) * u 38
  | 2 => (2 / 101 : K) * u 2 +
      (-1 / 2 : K) * u 27 +
      (1 / 2 : K) * u 37
  | 3 => (2 / 101 : K) * u 3 +
      (1 / 2 : K) * u 26 +
      (-1 / 2 : K) * u 31
  | 5 => (-2 / 101 : K) * u 5 +
      (-1 / 2 : K) * u 29 +
      (-1 / 2 : K) * u 36
  | 6 => (-2 / 101 : K) * u 6 +
      (1 / 2 : K) * u 23
  | 7 => (-2 / 101 : K) * u 7 +
      (1 / 2 : K) * u 24
  | 9 => (-2 / 101 : K) * u 9 +
      (1 / 2 : K) * u 28
  | 10 => (-2 / 101 : K) * u 10 +
      (-1 / 2 : K) * u 22 +
      (-1 / 2 : K) * u 36
  | 11 => (-2 / 101 : K) * u 11 +
      (1 / 2 : K) * u 30
  | 13 => (-2 / 101 : K) * u 13 +
      (1 / 2 : K) * u 34
  | 14 => (-2 / 101 : K) * u 14 +
      (1 / 2 : K) * u 35
  | 15 => (-2 / 101 : K) * u 15 +
      (-1 / 2 : K) * u 22 +
      (-1 / 2 : K) * u 29
  | 22 => (-1 / 2 : K) * u 10 +
      (-1 / 2 : K) * u 15
  | 23 => (1 / 2 : K) * u 6
  | 24 => (1 / 2 : K) * u 7
  | 26 => (1 / 2 : K) * u 3
  | 27 => (-1 / 2 : K) * u 2
  | 28 => (1 / 2 : K) * u 9
  | 29 => (-1 / 2 : K) * u 5 +
      (-1 / 2 : K) * u 15
  | 30 => (1 / 2 : K) * u 11
  | 31 => (-1 / 2 : K) * u 3
  | 33 => (1 / 2 : K) * u 1
  | 34 => (1 / 2 : K) * u 13
  | 35 => (1 / 2 : K) * u 14
  | 36 => (-1 / 2 : K) * u 5 +
      (-1 / 2 : K) * u 10
  | 37 => (1 / 2 : K) * u 2
  | 38 => (-1 / 2 : K) * u 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Normalize one sparse row at a time to keep the exact certificate small.
lemma newH_product (u : Point K) (i : Fin 40) :
    (castMatrix newH).mulVec u i = newHProduct u i := by
  fin_cases i <;>
    norm_num [castMatrix, newH, newHProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def mixedProduct (u : Point K) (i : Fin 40) : K :=
  match i.val with
  | 1 => (-2 / 101 : K) * u 1 +
      (1 / 2 : K) * u 33 +
      (-1 / 2 : K) * u 38
  | 2 => (-2 / 101 : K) * u 2 +
      (-1 / 2 : K) * u 27 +
      (1 / 2 : K) * u 37
  | 3 => (-2 / 101 : K) * u 3 +
      (1 / 2 : K) * u 26 +
      (-1 / 2 : K) * u 31
  | 5 => (2 / 101 : K) * u 5 +
      (-1 / 2 : K) * u 29 +
      (-1 / 2 : K) * u 36
  | 6 => (2 / 101 : K) * u 6 +
      (1 / 2 : K) * u 23
  | 7 => (2 / 101 : K) * u 7 +
      (1 / 2 : K) * u 24
  | 9 => (2 / 101 : K) * u 9 +
      (1 / 2 : K) * u 28
  | 10 => (2 / 101 : K) * u 10 +
      (-1 / 2 : K) * u 22 +
      (-1 / 2 : K) * u 36
  | 11 => (2 / 101 : K) * u 11 +
      (1 / 2 : K) * u 30
  | 13 => (2 / 101 : K) * u 13 +
      (1 / 2 : K) * u 34
  | 14 => (2 / 101 : K) * u 14 +
      (1 / 2 : K) * u 35
  | 15 => (2 / 101 : K) * u 15 +
      (-1 / 2 : K) * u 22 +
      (-1 / 2 : K) * u 29
  | 16 => (-2 / 101 : K) * u 1 +
      (1 / 2 : K) * u 33 +
      (-1 / 2 : K) * u 38
  | 17 => (-2 / 101 : K) * u 2 +
      (-1 / 2 : K) * u 27 +
      (1 / 2 : K) * u 37
  | 18 => (-2 / 101 : K) * u 3 +
      (1 / 2 : K) * u 26 +
      (-1 / 2 : K) * u 31
  | 19 => (2 / 101 : K) * u 11 +
      (-2 / 101 : K) * u 14 +
      (1 / 2 : K) * u 30 +
      (-1 / 2 : K) * u 35
  | 20 => (-2 / 101 : K) * u 7 +
      (2 / 101 : K) * u 13 +
      (-1 / 2 : K) * u 24 +
      (1 / 2 : K) * u 34
  | 21 => (2 / 101 : K) * u 6 +
      (-2 / 101 : K) * u 9 +
      (1 / 2 : K) * u 23 +
      (-1 / 2 : K) * u 28
  | 22 => (-2 / 101 : K) * u 5 +
      (1 / 2 : K) * u 10 +
      (1 / 2 : K) * u 15
  | 23 => (-1 / 2 : K) * u 6 +
      (-2 / 101 : K) * u 9
  | 24 => (-1 / 2 : K) * u 7 +
      (-2 / 101 : K) * u 13
  | 26 => (-1 / 2 : K) * u 3
  | 27 => (1 / 2 : K) * u 2
  | 28 => (-2 / 101 : K) * u 6 +
      (-1 / 2 : K) * u 9
  | 29 => (1 / 2 : K) * u 5 +
      (-2 / 101 : K) * u 10 +
      (1 / 2 : K) * u 15
  | 30 => (-1 / 2 : K) * u 11 +
      (-2 / 101 : K) * u 14
  | 31 => (1 / 2 : K) * u 3
  | 33 => (-1 / 2 : K) * u 1
  | 34 => (-2 / 101 : K) * u 7 +
      (-1 / 2 : K) * u 13
  | 35 => (-2 / 101 : K) * u 11 +
      (-1 / 2 : K) * u 14
  | 36 => (1 / 2 : K) * u 5 +
      (1 / 2 : K) * u 10 +
      (-2 / 101 : K) * u 15
  | 37 => (-1 / 2 : K) * u 2
  | 38 => (1 / 2 : K) * u 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Normalize one sparse row at a time to keep the exact certificate small.
lemma mixed_product (u : Point K) (i : Fin 40) :
    (castMatrix mixed).mulVec u i = mixedProduct u i := by
  fin_cases i <;>
    norm_num [castMatrix, mixed, mixedProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

end Artform.Scores.NonabelianGravity.Legendre
