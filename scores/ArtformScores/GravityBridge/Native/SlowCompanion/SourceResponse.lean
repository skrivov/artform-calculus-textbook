import ArtformScores.GravityBridge.Native.SlowCompanion.SourceResponseStatements

/-! # Complete mixed source response and preparation contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

lemma mixed_source_right_inverse (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V)
    (L : Module.End K V) (r z : K) (source : T × V)
    (hz : z ^ 2 + r ≠ 0) (hL : coordinatePolynomial g z * L = 1) :
    mixedSymbol g C0 C1 r z (sourceResponse L C0 C1 r z source) = source := by
  have hp (v : V) : coordinatePolynomial g z (L v) = v :=
    congrArg (fun F : Module.End K V => F v) hL
  apply Prod.ext
  · simp [mixedSymbol, sourceResponse, smul_smul, mul_inv_cancel₀ hz]
  · simp only [mixedSymbol, sourceResponse, hp]
    abel

lemma mixed_source_left_inverse (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V)
    (L : Module.End K V) (r z : K) (x : T × V)
    (hz : z ^ 2 + r ≠ 0) (hL : L * coordinatePolynomial g z = 1) :
    sourceResponse L C0 C1 r z (mixedSymbol g C0 C1 r z x) = x := by
  have hp (v : V) : L (coordinatePolynomial g z v) = v :=
    congrArg (fun F : Module.End K V => F v) hL
  have ht : (z ^ 2 + r)⁻¹ • ((z ^ 2 + r) • x.1) = x.1 := by
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
  apply Prod.ext
  · exact ht
  · change L (C0 x.1 + z • C1 x.1 + coordinatePolynomial g z x.2-
      C0 ((z ^ 2 + r)⁻¹ • ((z ^ 2 + r) • x.1))-
      z • C1 ((z ^ 2 + r)⁻¹ • ((z ^ 2 + r) • x.1))) = x.2
    rw [ht]
    convert hp x.2 using 2
    abel

lemma same_TT_changed_coordinate_preparation
    (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V) (L : Module.End K V)
    (r z : K) (q v : T) (x y : Fin 4 → V) :
    sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v x)-
      sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v y) =
      (0, L (coordinateCauchy g z x - coordinateCauchy g z y)) := by
  apply Prod.ext
  · simp [sourceResponse, mixedCauchy]
  · simp only [sourceResponse, mixedCauchy, Prod.snd_sub, ← map_sub]
    congr 1
    abel

lemma omitted_mixed_contact_changes_response
    (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V) (L : Module.End K V)
    (r z : K) (q v : T) (x : Fin 4 → V) :
    sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v x)-
      sourceResponse L C0 C1 r z (z • q + v, coordinateCauchy g z x) =
      (0, L (C1 q)) := by
  apply Prod.ext
  · simp [sourceResponse, mixedCauchy]
  · simp only [sourceResponse, mixedCauchy, Prod.snd_sub, ← map_sub]
    congr 1
    abel

/-- **GAC2:mixed-source-response-contacts**
(complete mixed source response and preparation contact). -/
@[ledger "GAC2:mixed-source-response-contacts"]
theorem sourceResponseLaw : Statement.sourceResponseLaw := by
  intro K V T _ _ _ _ _
  exact ⟨mixed_source_right_inverse,
    mixed_source_left_inverse,
    same_TT_changed_coordinate_preparation,
    omitted_mixed_contact_changes_response⟩

/-! ## Non-vacuity -/

example : sourceResponse (LinearMap.id : Module.End ℚ ℚ)
    (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id 14 2 (2, 3) = (1 / 9, 25 / 9) := by
  norm_num [sourceResponse]

example :
    (2 ^ 2 + (14 : ℚ)) ≠ 0 ∧
    mixedSymbol referencePolynomialCoefficients (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id 14 2
      (sourceResponse referenceCoordinateInverse 0 LinearMap.id 14 2 (2, 3)) = (2, 3) := by
  constructor
  · norm_num
  · exact mixed_source_right_inverse referencePolynomialCoefficients 0 LinearMap.id
      referenceCoordinateInverse 14 2 (2, 3) (by norm_num) reference_polynomial_guards.2.2.1

end Artform.Scores.GravityBridge.Native.SlowCompanion
