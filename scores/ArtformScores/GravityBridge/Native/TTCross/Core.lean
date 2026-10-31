import ArtformScores.GravityBridge.Native.CoordinateSymbol.Growing
import ArtformScores.GravityBridge.Native.CoordinateSymbol.Axis
import ArtformScores.GravityBridge.Native.Full40.Quadratic
/-! # Supporting full-coordinate TT source algebra -/

namespace Artform.Scores.GravityBridge.Native.TTCross
open Matrix CoordinateSymbol
variable {K : Type*} [Field K] [CharZero K]

abbrev Three := Matrix (Fin 3) (Fin 3) K

def timeT : Three (K := K) := !![-1,1,0;1,0,-1;0,-1,-1]
def timeB : Three (K := K) := !![-4 / 101,-99 / 101,-99 / 101;-99 / 101,-4 / 101,99 / 101;-99 /
  101,99 / 101,-4 / 101]
def timeH : Three (K := K) := !![-9595 / 19982,-9999 / 19982,-9999 / 19982;
  -9999 / 19982,-9595 / 19982,9999 / 19982;-9999 / 19982,9999 / 19982,-9595 / 19982]
def signS : Three (K := K) := !![1,0,0;0,-1,0;0,0,-1]
def spaceT : Three (K := K) := !![1,1,0;-1,0,-1;0,1,1]
def spaceB : Three (K := K) := -(signS * timeB * signS)
def spaceH : Three (K := K) := -(signS * timeH * signS)

def timeZ (j z a : K) : Fin 3 → K := ![(z - j * a) * z / 4,z ^ 2 / 4,j * a * z / 4]
def spaceZ (a : K) : Fin 3 → K := ![0,-a ^ 2 / 2,-a ^ 2 / 2]
def timeQ (j z a : K) : Fin 3 → K :=
  -timeZ j z a - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ timeZ j z a)
def spaceQ (a : K) : Fin 3 → K :=
  spaceZ a - (2 / 101 : K) • ((spaceT * spaceH * spaceT.transpose) *ᵥ spaceZ a)

def crossMetric : Mat4 (K := K) := !![0,0,0,0;0,0,0,1;0,0,0,1;0,1,1,0]
def derivativeVector (j z a : K) : Vec4 (K := K) := ![z,j * a,-j * a,0]
def literalChristoffelZ (j z a : K) : Matrix (Fin 6) (Fin 4) K := fun r b =>
  let i := Full40.faceFirst r
  let l := Full40.faceSecond r
  let d := derivativeVector j z a
  (d i - d l) * signature b * (d i * crossMetric l b + d l * crossMetric i b - d b * crossMetric
    i l) / 4

def threeBlockFace (p m s : Fin 3 → K) : Matrix (Fin 6) (Fin 4) K :=
  !![0,0,0,p 0;0,0,0,m 0;0,p 1,m 1,0;0,0,0,s 0;p 2,0,s 1,0;m 2,s 2,0,0]

def crossQFaces (j z a : K) : Matrix (Fin 6) (Fin 4) K :=
  threeBlockFace (timeQ j z a) (timeQ j z (-a)) (spaceQ a)

def originalFaceInput (F : Matrix (Fin 6) (Fin 4) K) : Fin 4 → Fin 4 → Fin 4 → K :=
  fun i l b => if i = 0 ∧ l = 1 then F 0 b else if i = 0 ∧ l = 2 then F 1 b else
    if i = 0 ∧ l = 3 then F 2 b else if i = 1 ∧ l = 2 then F 3 b else
      if i = 1 ∧ l = 3 then F 4 b else if i = 2 ∧ l = 3 then F 5 b else 0

lemma actual_three_block_inverse :
    timeB (K := K) * timeH = 1 ∧ timeH (K := K) * timeB = 1 ∧
    spaceB (K := K) * spaceH = 1 ∧ spaceH (K := K) * spaceB = 1 := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [timeB,timeH,spaceB,spaceH,signS,Matrix.mul_apply,Fin.sum_univ_succ]

lemma original_cross_face_support (j z a : K) (hj : j ^ 2 = -1) :
    literalChristoffelZ j z a = threeBlockFace (timeZ j z a) (timeZ j z (-a)) (spaceZ a) := by
  ext r b
  fin_cases r <;> fin_cases b <;>
    norm_num [literalChristoffelZ,threeBlockFace,timeZ,spaceZ,derivativeVector,crossMetric,
      Full40.faceFirst,Full40.faceSecond,signature] <;> ring_nf <;> simp only [hj] <;> ring

lemma time_Q_first (j z a : K) :
    timeQ j z a 0 = -(101 / 412 : K) * z ^ 2 + (10201 / 39964 : K) * j * a * z := by
  simp only [timeQ,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  norm_num [timeZ,timeT,timeH,Matrix.transpose_apply]
  ring

lemma space_Q_first (a : K) : spaceQ a 0 = 0 := by
  simp only [spaceQ,spaceH,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.neg_apply,
    Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  norm_num [spaceZ,spaceT,signS,timeH,Matrix.transpose_apply]

lemma actual_complete_cross_source (j z a : K) (hj : j ^ 2 = -1) :
    mixedFaceSource j (timeMomentum j z ![a,-a,0]) (originalFaceInput (crossQFaces j z a)) =
      ((1 / 101 : K) * (9999 / 9991) * a ^ 2 * z ^ 3) • ![0,0,0,1] := by
  have hj4 : j ^ 4 = 1 := by calc j ^ 4 = (j ^ 2) ^ 2 := by ring
                             _ = 1 := by rw [hj];norm_num
  ext b
  fin_cases b <;>
    norm_num [mixedFaceSource,originalFaceInput,crossQFaces,threeBlockFace,
      time_Q_first,space_Q_first,timeMomentum,simpleFace,componentSquares,signature]
  ring_nf
  simp only [hj,hj4]
  ring

omit [CharZero K] in
lemma actual_cross_TT (a : K) :
    (!![0,0,1;0,0,1;1,1,0] : Three (K := K)) *ᵥ ![a,-a,0] = 0 := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

lemma on_TT_source_reduction (j z a : K) (hj : j ^ 2 = -1) (hz : z ^ 2 = -2 * a ^ 2) :
    mixedFaceSource j (timeMomentum j z ![a,-a,0]) (originalFaceInput (crossQFaces j z a)) =
      (-(2 / 101 : K) * (9999 / 9991) * a ^ 4 * z) • ![0,0,0,1] := by
  rw [actual_complete_cross_source j z a hj]
  congr 1
  calc
    _ = (1 / 101 : K) * (9999 / 9991) * a ^ 2 * z ^ 2 * z := by ring
    _ = _ := by rw [hz];ring

/-! ## Non-vacuity -/
example : mixedFaceSource Complex.I (timeMomentum Complex.I (1 : ℂ) ![3,-3,0])
    (originalFaceInput (crossQFaces Complex.I 1 3)) = (891 / 9991 : ℂ) • ![0,0,0,1] := by
  rw [actual_complete_cross_source Complex.I 1 3 Complex.I_sq]
  norm_num
end Artform.Scores.GravityBridge.Native.TTCross
