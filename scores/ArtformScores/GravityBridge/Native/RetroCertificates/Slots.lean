import ArtformScores.GravityBridge.Native.TTCross.Full24
/-! # Supporting original native source and circuit slots -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective
open Matrix Full40 TTCross
variable {K : Type*} [Field K] [CharZero K]

def directNativeT (A : Connection K) : Matrix (Fin 6) (Fin 4) K :=
  !![-A 0 0, A 1 0, A 0 5 + A 1 1, -A 0 4 + A 1 2;
  -A 0 1, -A 0 5 + A 2 0, A 2 1, A 0 3 + A 2 2;
  -A 0 2, A 0 4 + A 3 0, -A 0 3 + A 3 1, A 3 2;
  -A 1 1 + A 2 0, -A 1 5, -A 2 5, A 1 3 + A 2 4;
  -A 1 2 + A 3 0, A 1 4, -A 1 3 - A 3 5, A 3 4;
  -A 2 2 + A 3 1, A 2 4 + A 3 5, -A 2 3, -A 3 3]

def directNativeAdjoint (Z : Matrix (Fin 6) (Fin 4) K) : Connection K :=
  !![-Z 0 0, -Z 1 0, -Z 2 0, -Z 1 3 + Z 2 2, Z 0 3 - Z 2 1, -Z 0 2 + Z 1 1;
  -Z 0 1, -Z 0 2 + Z 3 0, -Z 0 3 + Z 4 0, Z 3 3 - Z 4 2, Z 4 1, -Z 3 1;
  -Z 1 1 - Z 3 0, -Z 1 2, -Z 1 3 + Z 5 0, -Z 5 2, Z 3 3 + Z 5 1, -Z 3 2;
  -Z 2 1 - Z 4 0, -Z 2 2 - Z 5 0, -Z 2 3, -Z 5 3, Z 4 3, -Z 4 2 + Z 5 1]

def directNativeH (A : Connection K) : Connection K :=
  !![(9999 / 20600) * A 0 0 + (10201 / 20600) * A 2 5 + (-10201 / 20600) * A 3 4, (9999 / 20600)
    * A 0 1 + (-10201 / 20600) * A 1 5 + (10201 / 20600) * A 3 3, (9999 / 20600) * A 0 2 +
    (10201 / 20600) * A 1 4 + (-10201 / 20600) * A 2 3, (-9595 / 19982) * A 0 3 + (9999 / 19982)
    * A 2 2 + (-9999 / 19982) * A 3 1, (-9595 / 19982) * A 0 4 + (-9999 / 19982) * A 1 2 + (9999
    / 19982) * A 3 0, (-9595 / 19982) * A 0 5 + (9999 / 19982) * A 1 1 + (-9999 / 19982) * A 2
    0;
  (-9999 / 20600) * A 1 0 + (10201 / 20600) * A 2 1 + (10201 / 20600) * A 3 2, (9999 / 19982) *
    A 0 5 + (-9595 / 19982) * A 1 1 + (-9999 / 19982) * A 2 0, (-9999 / 19982) * A 0 4 + (-9595
    / 19982) * A 1 2 + (-9999 / 19982) * A 3 0, (9595 / 19982) * A 1 3 + (-9999 / 19982) * A 2 4
    + (-9999 / 19982) * A 3 5, (10201 / 20600) * A 0 2 + (9999 / 20600) * A 1 4 + (10201 /
    20600) * A 2 3, (-10201 / 20600) * A 0 1 + (9999 / 20600) * A 1 5 + (10201 / 20600) * A 3 3;
  (-9999 / 19982) * A 0 5 + (-9999 / 19982) * A 1 1 + (-9595 / 19982) * A 2 0, (10201 / 20600) *
    A 1 0 + (-9999 / 20600) * A 2 1 + (10201 / 20600) * A 3 2, (9999 / 19982) * A 0 3 + (-9595 /
    19982) * A 2 2 + (-9999 / 19982) * A 3 1, (-10201 / 20600) * A 0 2 + (10201 / 20600) * A 1 4
    + (9999 / 20600) * A 2 3, (-9999 / 19982) * A 1 3 + (9595 / 19982) * A 2 4 + (-9999 / 19982)
    * A 3 5, (10201 / 20600) * A 0 0 + (9999 / 20600) * A 2 5 + (10201 / 20600) * A 3 4;
  (9999 / 19982) * A 0 4 + (-9999 / 19982) * A 1 2 + (-9595 / 19982) * A 3 0, (-9999 / 19982) *
    A 0 3 + (-9999 / 19982) * A 2 2 + (-9595 / 19982) * A 3 1, (10201 / 20600) * A 1 0 + (10201
    / 20600) * A 2 1 + (-9999 / 20600) * A 3 2, (10201 / 20600) * A 0 1 + (10201 / 20600) * A 1
    5 + (9999 / 20600) * A 3 3, (-10201 / 20600) * A 0 0 + (10201 / 20600) * A 2 5 + (9999 /
    20600) * A 3 4, (-9999 / 19982) * A 1 3 + (-9999 / 19982) * A 2 4 + (9595 / 19982) * A 3 5]


def directDistinctRead (A : Connection K) : Fin 4 → Fin 3 → K :=
  !![A 0 5, -A 1 1, A 2 0;
  -A 0 4, -A 1 2, A 3 0;
  A 0 3, -A 2 2, A 3 1;
  A 1 3, A 2 4, A 3 5]

def directRepeatedRead (A : Connection K) : Fin 4 → Fin 3 → K :=
  !![-A 1 0, -A 2 1, -A 3 2;
  A 0 0, -A 2 5, A 3 4;
  A 0 1, A 1 5, -A 3 3;
  A 0 2, -A 1 4, A 2 3]

def directAssembly (d e : Fin 4 → Fin 3 → K) : Connection K :=
  !![e 1 0, e 2 0, e 3 0, d 2 0, -d 1 0, d 0 0;
  -e 0 0, -d 0 1, -d 1 1, d 3 0, -e 3 1, e 2 1;
  d 0 2, -e 0 1, -d 2 1, e 3 2, d 3 1, -e 1 1;
  d 1 2, d 2 2, -e 0 2, -e 2 2, e 1 2, d 3 2]

omit [CharZero K] in
lemma original_distinct_read_slots (A : Connection K) : gDistinct A = directDistinctRead A := by
  ext s i
  fin_cases s <;> fin_cases i <;>
    norm_num [gDistinct, gOriented, directDistinctRead, Retrospective.distinctIndices,
      wedge, basisVector, Fin.sum_univ_succ]

omit [CharZero K] in
lemma original_repeated_read_slots (A : Connection K) : gRepeated A = directRepeatedRead A := by
  ext s i
  fin_cases s <;> fin_cases i <;>
    norm_num [gRepeated, gOriented, directRepeatedRead, Fin.succAbove, Fin.lt_def,
      wedge, basisVector, Fin.sum_univ_succ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Reduce the24 signed assembly wires before composing with an inverse matrix.
omit [CharZero K] in
lemma original_assembly_slots (d e : Fin 4 → Fin 3 → K) : gAssemble d e = directAssembly d e := by
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    simp [gAssemble, gDistinctInput, gRepeatedInput, directAssembly,
      Retrospective.distinctIndices, Fin.succAbove, Fin.lt_def, wedge, basisVector,
        Fin.sum_univ_succ]

omit [CharZero K] in
lemma original_native_T_slots (A : Connection K) : nativeConnectionT A = directNativeT A := by
  ext r a
  fin_cases r <;> fin_cases a <;>
    norm_num [nativeConnectionT, directNativeT, lie, faceFirst, faceSecond, sub_eq_add_neg]

set_option maxHeartbeats 1000000 in
-- Retain every original transpose column before reducing its signed source slots.
omit [CharZero K] in
lemma original_native_adjoint_slots (Z : Matrix (Fin 6) (Fin 4) K) :
    nativeSourceAdjoint Z = directNativeAdjoint Z := by
  unfold nativeSourceAdjoint
  simp_rw [original_native_T_slots]
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    norm_num [directNativeT, nativeFaceGram, directNativeAdjoint, connectionBasis,
      faceFirst, faceSecond, eta, Fin.sum_univ_succ, sub_eq_add_neg]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Expand every original oriented source coordinate before composing the face operator.
lemma original_native_H_slots (A : Connection K) : fullHApply A = directNativeH A := by
  unfold fullHApply
  rw [original_distinct_read_slots, original_repeated_read_slots, original_assembly_slots]
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    norm_num [directNativeH, directAssembly, directDistinctRead, directRepeatedRead,
      distinctH, repeatH, spaceH, signS, timeH, eta, Matrix.mulVec, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

/-! ## Non-vacuity -/
example : nativeConnectionT (0 : Connection ℚ) = 0 := by
  rw [original_native_T_slots]
  ext r a
  fin_cases r <;> fin_cases a <;> norm_num [directNativeT]
end Artform.Scores.GravityBridge.Native.RetroCertificates
