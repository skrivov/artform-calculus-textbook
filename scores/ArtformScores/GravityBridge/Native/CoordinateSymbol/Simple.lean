import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverse
/-! # Supporting original coordinate algebra -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol
open Matrix
variable {K : Type*} [Field K] [CharZero K]

abbrev Vec4 := Fin 4 → K
abbrev Mat4 := Matrix (Fin 4) (Fin 4) K

def signature : Fin 4 → K := ![-1, 1, 1, 1]
def lorentzDot (u v : Vec4 (K := K)) : K := ∑ i, signature i * u i * v i

def simpleFace (u p : Vec4 (K := K)) : Mat4 (K := K) :=
  fun i j => (u i * p j - u j * p i) / 2

def lorentzK (u p : Vec4 (K := K)) : Mat4 (K := K) :=
  fun i j => ∑ l, signature l * simpleFace u p i l * simpleFace u p j l

def raisedK (u p : Vec4 (K := K)) : Mat4 (K := K) :=
  fun i j => signature i * lorentzK u p i j

def simpleDiscriminant (u p : Vec4 (K := K)) : K :=
  (lorentzDot u u * lorentzDot p p - lorentzDot u p ^ 2) / 4

def componentSquares (p : Vec4 (K := K)) : Vec4 (K := K) := fun i => (p i) ^ 2

def nativeUpperSymbol (p : Vec4 (K := K)) : Mat4 (K := K) :=
  let u := componentSquares p
  let eta : Mat4 (K := K) := Matrix.diagonal (signature (K := K))
  (2 / 101 : K) • ((((9999 / 9991 : K) * simpleDiscriminant u p) • eta) +
    ((10201 / 10300 - 9999 / 9991 : K) • lorentzK u p))

lemma simple_face_antisymmetric (u p : Vec4 (K := K)) (i j : Fin 4) :
    simpleFace u p j i = -simpleFace u p i j := by
  unfold simpleFace
  ring

set_option maxHeartbeats 8000000 in
-- Every entry is a finite polynomial identity; no inverse at d=0 is asserted.
lemma original_simple_bivector_relation (u p : Vec4 (K := K)) :
    raisedK u p * raisedK u p = simpleDiscriminant u p • raisedK u p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisedK, lorentzK, simpleFace, simpleDiscriminant, lorentzDot, signature,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
lemma native_face_is_componentwise (p : Vec4 (K := K)) (i j : Fin 4) :
    simpleFace (componentSquares p) p i j = ((p i) ^ 2 * p j - (p j) ^ 2 * p i) / 2 := rfl

/-! ## Non-vacuity -/

example : simpleDiscriminant (![1, 0, 0, 0] : Vec4 (K := ℚ)) ![0, 1, 0, 0] = -1 / 4 := by
  norm_num [simpleDiscriminant, lorentzDot, signature, Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
