import ArtformScores.GravityBridge.Native.RetroCertificates.All24ProgramsStatements

/-! # Verified arbitrary-input original24 inverse programs -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates



open Matrix Full40 TTCross Retrospective

lemma repeated_programs_correct (z : Fin 3 → ℚ) (rank : Bool) :
    runBlock rank true z = repeatH 1 *ᵥ z := by
  ext i
  fin_cases i <;> cases rank <;>
    norm_num [runBlock, programOutput, runScalarProgram, evaluateGate, resolveRef,
      repeatedRank, repeatedDense, repeatH, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        <;> ring

lemma distinct_programs_correct (z : Fin 3 → ℚ) (rank : Bool) :
    runBlock rank false z = timeH *ᵥ z := by
  ext i
  fin_cases i <;> cases rank <;>
    norm_num [runBlock, programOutput, runScalarProgram, evaluateGate, resolveRef,
      rankBlockProgram, denseBlockProgram, timeH, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        <;> ring

lemma actual_full24_program (rank : Bool) (A : Connection ℚ) :
    fullProgram rank A = fullHApply A := by
  unfold fullProgram fullHApply
  congr 1
  · funext s
    by_cases hs : s = 3
    · simp only [hs, distinctH]
      rw [distinct_programs_correct]
      ext i
      fin_cases i <;>
        norm_num [signVector, spaceH, signS, timeH, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply,
          dotProduct, Fin.sum_univ_succ] <;> ring
    · simp only [distinctH, hs, ite_false]
      exact distinct_programs_correct _ rank
  · funext b
    rw [repeated_programs_correct]
    ext i
    fin_cases i <;> fin_cases b <;>
      norm_num [repeatH, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma full_program_two_sided (rank : Bool) (A : Connection ℚ) :
    fullBApply (fullProgram rank A) = A ∧ fullProgram rank (fullBApply A) = A := by
  simp only [actual_full24_program]
  exact original_full24_inverse A

lemma actual_all24_costs :
    validProgram 0 repeatedRank = true ∧ validProgram 0 repeatedDense = true ∧
    fullScaleCount false = 72 ∧ fullAddCount false = 48 ∧
    fullScaleCount true = 32 ∧ fullAddCount true = 40 := by
  decide +kernel

lemma weighted_full24_saving (cs ca : ℚ) (hs : 0 < cs) (ha : 0 ≤ ca) :
    (fullScaleCount true : ℚ) * cs + (fullAddCount true : ℚ) * ca <
      (fullScaleCount false : ℚ) * cs + (fullAddCount false : ℚ) * ca := by
  norm_num [fullScaleCount, fullAddCount, scaleCount, addCount, rankBlockProgram,
    denseBlockProgram, repeatedRank, repeatedDense]
  nlinarith

lemma all_original_block_output_slots :
    (∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < repeatedDense.length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < repeatedRank.length) ∧
    (∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < denseBlockProgram.length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < rankBlockProgram.length) := by decide +kernel

lemma all_original_reference_guards :
    validProgram 0 denseBlockProgram = true ∧ validProgram 0 rankBlockProgram = true ∧
    validProgram 0 repeatedDense = true ∧ validProgram 0 repeatedRank = true := by decide +kernel

/-- **GAC2:verified-all24-rank-return**
(verified arbitrary-input original24 inverse programs). -/
@[ledger "GAC2:verified-all24-rank-return"]
theorem all24ProgramsLaw : Statement.all24ProgramsLaw := by
  exact ⟨actual_full24_program,
    full_program_two_sided,
    actual_all24_costs,
    all_original_block_output_slots,
    weighted_full24_saving,
    all_original_reference_guards⟩

/-! ## Non-vacuity -/
example : fullBApply (fullProgram true (gRepeatedInput 2 (![1, 2, 3] : Fin 3 → ℚ))) =
    gRepeatedInput 2 ![1, 2, 3] := (full_program_two_sided true _).1

end Artform.Scores.GravityBridge.Native.RetroCertificates
