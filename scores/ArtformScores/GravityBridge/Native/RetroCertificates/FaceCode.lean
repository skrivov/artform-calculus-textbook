import ArtformScores.GravityBridge.Native.RetroCertificates.ConstitutiveInverse
import ArtformScores.GravityBridge.Native.Retrospective.BlockPrograms
/-! # Supporting original native source and circuit slots -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates
open Matrix Full40 TTCross Retrospective

def circuitAlpha (inverse : Bool) (s : Fin 8) : ℚ :=
  if inverse then faceAlpha s else (faceAlpha s)⁻¹
def circuitBeta (inverse : Bool) (s : Fin 8) : ℚ :=
  if inverse then faceBeta s else -faceBeta s / (faceAlpha s * (faceAlpha s + 3 * faceBeta s))

def denseFaceCode (inverse : Bool) (s : Fin 8) : List ScalarGate :=
  let a := circuitAlpha inverse s
  let b := circuitBeta inverse s
  [.scale (a + b) (.input 0), .scale b (.input 1), .add (.slot 0) (.slot 1),
   .scale b (.input 2), .add (.slot 2) (.slot 3),
   .scale b (.input 0), .scale (a + b) (.input 1), .add (.slot 5) (.slot 6),
   .scale b (.input 2), .add (.slot 7) (.slot 8),
   .scale b (.input 0), .scale b (.input 1), .add (.slot 10) (.slot 11),
   .scale (a + b) (.input 2), .add (.slot 12) (.slot 13)]

def rankFaceCode (inverse : Bool) (s : Fin 8) : List ScalarGate :=
  let a := circuitAlpha inverse s
  let b := circuitBeta inverse s
  [.scale a (.input 0), .scale a (.input 1), .scale a (.input 2),
   .add (.input 0) (.input 1), .add (.slot 3) (.input 2), .scale b (.slot 4),
   .add (.slot 0) (.slot 5), .add (.slot 1) (.slot 5), .add (.slot 2) (.slot 5)]

def fullFaceProgram (inverse rank : Bool) (Z : NativeFace ℚ) : NativeFace ℚ :=
  faceAssemble (fun s => if rank then programOutput (rankFaceCode inverse s) ![6, 7, 8]
    (faceRead Z s)
    else programOutput (denseFaceCode inverse s) ![4, 9, 14] (faceRead Z s))

def faceProgramScales (inverse rank : Bool) : ℕ :=
  ∑ s : Fin 8, scaleCount (if rank then rankFaceCode inverse s else denseFaceCode inverse s)
def faceProgramAdds (inverse rank : Bool) : ℕ :=
  ∑ s : Fin 8, addCount (if rank then rankFaceCode inverse s else denseFaceCode inverse s)

lemma face_code_values (inverse rank : Bool) (s : Fin 8) (z : Fin 3 → ℚ) :
    (if rank then programOutput (rankFaceCode inverse s) ![6, 7, 8] z
      else programOutput (denseFaceCode inverse s) ![4, 9, 14] z) =
      (fun i => circuitAlpha inverse s * z i + circuitBeta inverse s * (z 0 + z 1 + z 2)) := by
  ext i
  fin_cases i <;> cases rank <;>
    norm_num [programOutput, runScalarProgram, evaluateGate, resolveRef, rankFaceCode,
      denseFaceCode] <;>
      ring

lemma rank_one_block_circuit (inverse : Bool) (s : Fin 8) (z : Fin 3 → ℚ) :
    (fun i => circuitAlpha inverse s * z i + circuitBeta inverse s * (z 0 + z 1 + z 2)) =
      (if inverse then faceInverseBlock s else faceForwardBlock s) *ᵥ z := by
  ext i
  fin_cases i <;> cases inverse <;>
    norm_num [circuitAlpha, circuitBeta, faceInverseBlock, faceForwardBlock, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

lemma full_face_code_semantics (inverse rank : Bool) (Z : NativeFace ℚ) :
    fullFaceProgram inverse rank Z = faceAssemble
      (fun s => (if inverse then faceInverseBlock s else faceForwardBlock s) *ᵥ faceRead Z s) := by
  unfold fullFaceProgram
  congr 1
  funext s
  rw [face_code_values, rank_one_block_circuit]

lemma face_codes_valid_and_costs (inverse : Bool) :
    (∀ s : Fin 8, validProgram 0 (rankFaceCode inverse s) = true ∧
      validProgram 0 (denseFaceCode inverse s) = true) ∧
    faceProgramScales inverse false = 72 ∧ faceProgramAdds inverse false = 48 ∧
    faceProgramScales inverse true = 32 ∧ faceProgramAdds inverse true = 40 := by
  cases inverse <;> decide +kernel

lemma face_code_output_slots (inverse : Bool) (s : Fin 8) :
    (∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < (denseFaceCode inverse s).length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < (rankFaceCode inverse s).length) := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [denseFaceCode, rankFaceCode]

/-! ## Non-vacuity -/
example : faceProgramScales false true = 32 := (face_codes_valid_and_costs false).2.2.2.1
end Artform.Scores.GravityBridge.Native.RetroCertificates
