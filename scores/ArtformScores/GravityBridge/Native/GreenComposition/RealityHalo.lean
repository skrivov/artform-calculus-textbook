import ArtformScores.GravityBridge.Native.GreenComposition.RealityHaloStatements

/-! # Fourier reality and the actual temporal halo duty -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators



noncomputable section

lemma scalar_even_but_vector_real_odd (k : ℝ) :
    evenScalarSeed (-k) = evenScalarSeed k ∧
    derivedVectorSeed (-k) = star (derivedVectorSeed k) ∧
    derivedVectorSeed (-k) = -derivedVectorSeed k := by
  constructor
  · simp only [evenScalarSeed, neg_sq]
  constructor
  · simp only [derivedVectorSeed, evenScalarSeed, neg_sq, Complex.ofReal_neg,
      star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  · simp only [derivedVectorSeed, evenScalarSeed, neg_sq, Complex.ofReal_neg]
    ring

lemma vector_need_not_be_even : derivedVectorSeed (-1) ≠ derivedVectorSeed 1 := by
  have hr := (scalar_even_but_vector_real_odd 1).2.2
  rw [hr]
  intro he
  have hh : derivedVectorSeed 1 = 0 := by linear_combination -he / 2
  have hn : derivedVectorSeed 1 ≠ 0 := by
    simp [derivedVectorSeed, evenScalarSeed, Complex.I_ne_zero ]
  exact hn hh

lemma cut_needs_temporal_halo :
    haloRight 0 = 0 ∧ haloRight 1 = 0 ∧
    cutSum (operatorEdge (fun r (a b : ℚ) => if r = 2 then a * b else 0) haloLeft haloRight) 2 0
      = 1 ∧
    cutSum (operatorEdge (fun r (a b : ℚ) => if r = 2 then a * b else 0) haloLeft (fun _ => 0))
      2 0 = 0 := by
  norm_num [haloRight, haloLeft, cutSum, operatorEdge, Finset.sum_range_succ]

/-- **GAC2:fourier-reality-temporal-halo**
(fourier reality and the actual temporal halo duty). -/
@[ledger "GAC2:fourier-reality-temporal-halo"]
theorem realityHaloLaw : Statement.realityHaloLaw := by
  exact ⟨scalar_even_but_vector_real_odd,
    vector_need_not_be_even,
    cut_needs_temporal_halo⟩

/-! ## Non-vacuity -/
example : derivedVectorSeed (-1) = star (derivedVectorSeed 1) ∧
    derivedVectorSeed (-1) ≠ derivedVectorSeed 1 :=
  ⟨(scalar_even_but_vector_real_odd 1).2.1, vector_need_not_be_even⟩
end

end Artform.Scores.GravityBridge.Native.GreenComposition
