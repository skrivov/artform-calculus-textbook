import ArtformScores.GravityBridge.Native.RetroCertificates.OddInverseStatements

/-! # Original full24 inverse as an odd degree-five polynomial -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



open Matrix Full40 TTCross

lemma exact_eight_odd_inverse :
    (∀ s : Fin 4, oddInverse (distinctB s) = distinctH s) ∧
    (∀ b : Fin 4, oddInverse (repeatB b) = repeatH b) := by
  decide +kernel

lemma distinct_linear (a b c : ℚ) (A B C : Connection ℚ) (s : Fin 4) :
    gDistinct (a • A + b • B + c • C) s = a • gDistinct A s + b • gDistinct B s + c • gDistinct
      C s := by
  ext i
  simp only [gDistinct, gOriented, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma repeated_linear (a b c : ℚ) (A B C : Connection ℚ) (s : Fin 4) :
    gRepeated (a • A + b • B + c • C) s = a • gRepeated A s + b • gRepeated B s + c • gRepeated
      C s := by
  ext i
  simp only [gRepeated, gOriented, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma native_power_coordinates (n : ℕ) (A : Connection ℚ) :
    (∀ s, gDistinct (nativePower n A) s = (distinctB s) ^ n *ᵥ gDistinct A s) ∧
    (∀ b, gRepeated (nativePower n A) b = (repeatB b) ^ n *ᵥ gRepeated A b) := by
  induction n with
  | zero => simp [nativePower]
  | succ n ih =>
    constructor
    · intro s
      rw [nativePower, fullBApply, generic_partition_distinct, ih.1, pow_succ',
        Matrix.mulVec_mulVec]
    · intro b
      rw [nativePower, fullBApply, generic_partition_repeated, ih.2, pow_succ',
        Matrix.mulVec_mulVec]

lemma original_global_odd_inverse (A : Connection ℚ) : globalOddInverse A = fullHApply A := by
  have hd : gDistinct (globalOddInverse A) = gDistinct (fullHApply A) := by
    funext s
    simp only [globalOddInverse, distinct_linear, native_power_coordinates,
      fullHApply, generic_partition_distinct]
    rw [← exact_eight_odd_inverse.1 s]
    simp [oddInverse, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hr : gRepeated (globalOddInverse A) = gRepeated (fullHApply A) := by
    funext b
    simp only [globalOddInverse, repeated_linear, native_power_coordinates,
      fullHApply, generic_partition_repeated]
    rw [← exact_eight_odd_inverse.2 b]
    simp [oddInverse, Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [← generic_partition_left (globalOddInverse A), ← generic_partition_left (fullHApply A),
    hd, hr]

lemma odd_full_inverse_both (A : Connection ℚ) :
    fullBApply (globalOddInverse A) = A ∧ globalOddInverse (fullBApply A) = A := by
  simp only [original_global_odd_inverse]
  exact original_full24_inverse A

/-- **GAC2:original-global-odd-inverse**
(original full24 inverse as an odd degree-five polynomial). -/
@[ledger "GAC2:original-global-odd-inverse"]
theorem oddInverseLaw : Statement.oddInverseLaw := by
  exact ⟨exact_eight_odd_inverse,
    native_power_coordinates,
    original_global_odd_inverse,
    odd_full_inverse_both⟩

/-! ## Non-vacuity -/
example : fullBApply (globalOddInverse (gRepeatedInput 1 (![2, 0, -3] : Fin 3 → ℚ))) =
    gRepeatedInput 1 ![2, 0, -3] := (odd_full_inverse_both _).1

end Artform.Scores.GravityBridge.Native.RetroCertificates
