import ArtformScores.GravityBridge.Native.SlowCompanion.CauchyStatements

/-! # Original mixed Cauchy polynomial and lower-basis contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

lemma complete_cauchy_expansion (g : Fin 5 → Module.End K V) (z : K) (x : Fin 4 → V) :
    coordinateCauchy g z x =
      g 1 (x 0) + z • g 2 (x 0) + g 2 (x 1) + z ^ 2 • g 3 (x 0) +
      z • g 3 (x 1) + g 3 (x 2) + z ^ 3 • g 4 (x 0) + z ^ 2 • g 4 (x 1) +
      z • g 4 (x 2) + g 4 (x 3) := by
  simp only [coordinateCauchy, map_add, map_smul]
  abel

lemma lower_cauchy_congruence (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (z : K) (x : Fin 4 → V) (hJ : J * J = 1) :
    coordinateCauchy (lowerCoefficients J g) z (lowerJets J x) =
      J (coordinateCauchy g z x) := by
  have hj (v : V) : J (J v) = v := congrArg (fun f : Module.End K V => f v) hJ
  simp [coordinateCauchy, lowerCoefficients, lowerJets, map_add, map_smul, hj]

lemma lower_polynomial_congruence (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (z : K) : coordinatePolynomial (lowerCoefficients J g) z =
      J * (coordinatePolynomial g z) * J := by
  ext v
  simp [coordinatePolynomial, lowerCoefficients, map_add, map_smul]

lemma lower_mixed_source_contact (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (C1 : T →ₗ[K] V) (z : K) (t₀ t₁ : T) (x : Fin 4 → V) (hJ : J * J = 1) :
    mixedCauchy (lowerCoefficients J g) (J.comp C1) z t₀ t₁ (lowerJets J x) =
      (z • t₀ + t₁, J ((mixedCauchy g C1 z t₀ t₁ x).2)) := by
  apply Prod.ext
  · rfl
  · change coordinateCauchy (lowerCoefficients J g) z (lowerJets J x) + J (C1 t₀) =
      J (coordinateCauchy g z x + C1 t₀)
    rw [lower_cauchy_congruence J g z x hJ, map_add]

lemma zero_coordinate_jets_keep_mixed_contact (g : Fin 5 → Module.End K V)
    (C1 : T →ₗ[K] V) (z : K) (t₀ t₁ : T) :
    mixedCauchy g C1 z t₀ t₁ 0 = (z • t₀ + t₁, C1 t₀) := by
  simp [mixedCauchy, coordinateCauchy]

/-- **GAC2:native-cauchy-polynomial-lower-basis**
(original mixed cauchy polynomial and lower-basis contact). -/
@[ledger "GAC2:native-cauchy-polynomial-lower-basis"]
theorem cauchyLaw : Statement.cauchyLaw := by
  intro K V T _ _ _ _ _
  exact ⟨complete_cauchy_expansion,
    lower_cauchy_congruence,
    lower_polynomial_congruence,
    lower_mixed_source_contact,
    zero_coordinate_jets_keep_mixed_contact⟩

/-! ## Non-vacuity -/

example : mixedCauchy (0 : Fin 5 → Module.End ℚ ℚ) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    2 3 4 0 = (10, 3) := by
  norm_num [mixedCauchy, coordinateCauchy]

end Artform.Scores.GravityBridge.Native.SlowCompanion
