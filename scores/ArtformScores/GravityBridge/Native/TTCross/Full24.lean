import ArtformScores.GravityBridge.Native.TTCross.Core
import ArtformScores.GravityBridge.Native.Retrospective.Homogeneous
/-! # Supporting full-coordinate TT source algebra -/

namespace Artform.Scores.GravityBridge.Native.TTCross
open Matrix Full40
variable {K : Type*} [Field K] [CharZero K]

def gDistinctInput (s : Fin 4) (z : Fin 3 → K) : Connection K := fun i =>
  ∑ j : Fin 3,if i = Retrospective.distinctIndices s j then z j •
    wedge (basisVector (Retrospective.distinctIndices s (j + 1)))
      (basisVector (Retrospective.distinctIndices s (j + 2))) else 0

def gRepeatedInput (b : Fin 4) (z : Fin 3 → K) : Connection K := fun i =>
  ∑ j : Fin 3,if i = b.succAbove j then z j • wedge (basisVector (b.succAbove j)) (basisVector
    b) else 0

def gAssemble (d e : Fin 4 → Fin 3 → K) : Connection K :=
  (∑ s : Fin 4,gDistinctInput s (d s)) + (∑ b : Fin 4,gRepeatedInput b (e b))

def gOriented (A : Connection K) (mu i l : Fin 4) : K :=
  ∑ a : Fin 6,wedge (basisVector i) (basisVector l) a * A mu a

def gDistinct (A : Connection K) (s : Fin 4) (j : Fin 3) : K :=
  gOriented A (Retrospective.distinctIndices s j) (Retrospective.distinctIndices s (j + 1))
    (Retrospective.distinctIndices s (j + 2))

def gRepeated (A : Connection K) (b : Fin 4) (j : Fin 3) : K :=
  gOriented A (b.succAbove j) (b.succAbove j) b

def distinctB (s : Fin 4) : Three (K := K) := if s = 3 then spaceB else timeB
def distinctH (s : Fin 4) : Three (K := K) := if s = 3 then spaceH else timeH

def repeatB (b : Fin 4) : Three (K := K) :=
  (eta (K := K) b) • !![2 / 101,-1,-1;-1,2 / 101,-1;-1,-1,2 / 101]
def repeatH (b : Fin 4) : Three (K := K) :=
  (eta (K := K) b) • !![9999 / 20600,-10201 / 20600,-10201 / 20600;
    -10201 / 20600,9999 / 20600,-10201 / 20600;-10201 / 20600,-10201 / 20600,9999 / 20600]

def fullBApply (A : Connection K) : Connection K :=
  gAssemble (fun s => distinctB s *ᵥ gDistinct A s) (fun b => repeatB b *ᵥ gRepeated A b)
def fullHApply (A : Connection K) : Connection K :=
  gAssemble (fun s => distinctH s *ᵥ gDistinct A s) (fun b => repeatH b *ᵥ gRepeated A b)

def nativeConnectionT (A : Connection K) : Matrix (Fin 6) (Fin 4) K := fun r a =>
  -lie (A (faceFirst r)) a (faceSecond r) + lie (A (faceSecond r)) a (faceFirst r)

def nativeFaceGram (Z : Matrix (Fin 6) (Fin 4) K) : Matrix (Fin 6) (Fin 4) K :=
  fun r a => eta (faceFirst r) * eta (faceSecond r) * eta a * Z r a

def connectionBasis (mu : Fin 4) (a : Fin 6) : Connection K :=
  fun i b => if i = mu ∧ b = a then 1 else 0

def nativeSourceAdjoint (Z : Matrix (Fin 6) (Fin 4) K) : Connection K := fun mu a =>
  ∑ r,∑ b,nativeConnectionT (connectionBasis mu a) r b * nativeFaceGram Z r b

def nativeConstitutiveQ (Z : Matrix (Fin 6) (Fin 4) K) : Matrix (Fin 6) (Fin 4) K :=
  nativeFaceGram (Z - (2 / 101 : K) • nativeConnectionT (fullHApply (nativeSourceAdjoint Z)))

def threeConnection (p m s : Fin 3 → K) : Connection K :=
  gAssemble ![0,p,m,s] (fun _ => 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Same original24 coordinates, now over the coefficient field of the Fourier symbols.
omit [CharZero K] in
lemma generic_partition_left (A : Connection K) : gAssemble (gDistinct A) (gRepeated A) = A := by
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    simp [gAssemble,gDistinct,gRepeated,gOriented,gDistinctInput,gRepeatedInput,
      Retrospective.distinctIndices,Fin.succAbove,Fin.lt_def,wedge,basisVector,Fin.sum_univ_succ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Every oriented distinct coordinate is recovered, including the31 convention.
omit [CharZero K] in
lemma generic_partition_distinct (d e : Fin 4 → Fin 3 → K) :
    gDistinct (gAssemble d e) = d := by
  ext s j
  fin_cases s <;> fin_cases j <;>
    simp [gAssemble,gDistinct,gOriented,gDistinctInput,gRepeatedInput,
      Retrospective.distinctIndices,Fin.succAbove,Fin.lt_def,wedge,basisVector,Fin.sum_univ_succ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The twelve repeated-index slots are recovered as well.
omit [CharZero K] in
lemma generic_partition_repeated (d e : Fin 4 → Fin 3 → K) :
    gRepeated (gAssemble d e) = e := by
  ext b j
  fin_cases b <;> fin_cases j <;>
    simp [gAssemble,gRepeated,gOriented,gDistinctInput,gRepeatedInput,
      Retrospective.distinctIndices,Fin.succAbove,Fin.lt_def,wedge,basisVector,Fin.sum_univ_succ]

lemma all_distinct_inverses (s : Fin 4) : distinctB (K := K) s * distinctH s = 1 ∧
    distinctH (K := K) s * distinctB s = 1 := by
  by_cases hs : s = 3
  · simp only [distinctB,distinctH,hs,ite_true]
    exact ⟨actual_three_block_inverse.2.2.1,actual_three_block_inverse.2.2.2⟩
  · simp only [distinctB,distinctH,hs,ite_false]
    exact ⟨actual_three_block_inverse.1,actual_three_block_inverse.2.1⟩

lemma all_repeated_inverses (b : Fin 4) : repeatB (K := K) b * repeatH b = 1 ∧
    repeatH (K := K) b * repeatB b = 1 := by
  constructor <;> ext i l <;> fin_cases b <;> fin_cases i <;> fin_cases l <;>
    norm_num [repeatB,repeatH,eta,Matrix.mul_apply,Fin.sum_univ_succ]

lemma original_full24_inverse (A : Connection K) :
    fullBApply (fullHApply A) = A ∧ fullHApply (fullBApply A) = A := by
  have hd (s : Fin 4) (v : Fin 3 → K) : distinctB s *ᵥ (distinctH s *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,(all_distinct_inverses s).1,Matrix.one_mulVec]
  have hd' (s : Fin 4) (v : Fin 3 → K) : distinctH s *ᵥ (distinctB s *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,(all_distinct_inverses s).2,Matrix.one_mulVec]
  have hr (b : Fin 4) (v : Fin 3 → K) : repeatB b *ᵥ (repeatH b *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,(all_repeated_inverses b).1,Matrix.one_mulVec]
  have hr' (b : Fin 4) (v : Fin 3 → K) : repeatH b *ᵥ (repeatB b *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,(all_repeated_inverses b).2,Matrix.one_mulVec]
  constructor <;>
    simp only [fullBApply,fullHApply,generic_partition_distinct,generic_partition_repeated,
      hd,hd',hr,hr',generic_partition_left]

omit [CharZero K] in
lemma original_native_T_correspondence (A : Connection K) :
    nativeConnectionT A = fun r => nativeTheta (fun _ : Fin 4 => Unit.unit)
      (fun _ : Unit => (0,A)) Unit.unit r := by
  ext r a
  simp [nativeConnectionT,nativeTheta,torsion]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- All24 torsion outputs retain the original Lie signs.
omit [CharZero K] in
lemma native_T_three_blocks (p m s : Fin 3 → K) :
    nativeConnectionT (threeConnection p m s) =
      threeBlockFace (-(timeT *ᵥ p)) (-(timeT *ᵥ m)) (spaceT *ᵥ s) := by
  ext r a
  fin_cases r <;> fin_cases a <;>
    norm_num [nativeConnectionT,threeConnection,gAssemble,gDistinctInput,gRepeatedInput,
      Retrospective.distinctIndices,threeBlockFace,timeT,spaceT,faceFirst,faceSecond,
      lie,wedge,basisVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The true coordinate adjoint is computed on every one of the24 connection columns.
omit [CharZero K] in
lemma native_adjoint_three_blocks (p m s : Fin 3 → K) :
    nativeSourceAdjoint (threeBlockFace p m s) =
      threeConnection (timeT.transpose *ᵥ p) (timeT.transpose *ᵥ m)
        (spaceT.transpose *ᵥ s) := by
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    norm_num [nativeSourceAdjoint,nativeConnectionT,connectionBasis,nativeFaceGram,
      threeConnection,gAssemble,gDistinctInput,gRepeatedInput,Retrospective.distinctIndices,
      threeBlockFace,timeT,spaceT,faceFirst,faceSecond,eta,lie,wedge,basisVector,
      Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
lemma native_H_three_blocks (p m s : Fin 3 → K) :
    fullHApply (threeConnection p m s) =
      threeConnection (timeH *ᵥ p) (timeH *ᵥ m) (spaceH *ᵥ s) := by
  unfold fullHApply threeConnection
  rw [generic_partition_distinct,generic_partition_repeated]
  congr 1
  · funext i
    fin_cases i <;> simp [distinctH]
  · funext i
    simp

/-! ## Non-vacuity -/
example : fullBApply (fullHApply (gDistinctInput 1 (![1,2,3] : Fin 3 → ℚ))) =
    gDistinctInput 1 ![1,2,3] := (original_full24_inverse _).1
end Artform.Scores.GravityBridge.Native.TTCross
