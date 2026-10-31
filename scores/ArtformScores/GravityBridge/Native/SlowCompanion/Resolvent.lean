import ArtformScores.GravityBridge.Native.SlowCompanion.ResolventStatements

/-! # Guarded resolvent of the complete four-jet companion -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma complete_resolvent_residual (g : Fin 5 → Module.End K V) (H : Module.End K V)
    (z : K) (v : V) (b : Fin 4 → V) (hH : H * g 4 = 1) :
    z • resolventState z v b - coordinateStep g H (resolventState z v b) - b =
      ![0, 0, 0, H (coordinatePolynomial g z v - coordinateCauchy g z b)] := by
  have hreturn (w : V) : H (g 4 w) = w := congrArg (fun F : Module.End K V => F w) hH
  ext i
  fin_cases i <;> simp [coordinateStep, resolventState, coordinatePolynomial, coordinateCauchy,
    map_add, map_sub, map_smul, hreturn] <;> module

lemma companion_resolvent_solves (g : Fin 5 → Module.End K V) (H L : Module.End K V)
    (z : K) (b : Fin 4 → V) (hH : H * g 4 = 1) (hL : coordinatePolynomial g z * L = 1) :
    z • companionResolvent g L z b - coordinateStep g H (companionResolvent g L z b) = b := by
  have hreturn (w : V) : coordinatePolynomial g z (L w) = w :=
    congrArg (fun F : Module.End K V => F w) hL
  have he := complete_resolvent_residual g H z (L (coordinateCauchy g z b)) b hH
  rw [hreturn, sub_self, map_zero] at he
  have hz : (![0, 0, 0, 0] : Fin 4 → V) = 0 := by ext i; fin_cases i <;> rfl
  rw [hz] at he
  exact sub_eq_zero.mp he

lemma first_three_resolvent_reconstruct (g : Fin 5 → Module.End K V) (H : Module.End K V)
    (z : K) (x b : Fin 4 → V)
    (hres : z • x - coordinateStep g H x = b) : x = resolventState z (x 0) b := by
  have h0 := congrFun hres 0
  have h1 := congrFun hres 1
  have h2 := congrFun hres 2
  change z • x 0 - x 1 = b 0 at h0
  change z • x 1 - x 2 = b 1 at h1
  change z • x 2 - x 3 = b 2 at h2
  have hx1 : x 1 = z • x 0 - b 0 := by rw [← h0]; abel
  have hx2 : x 2 = z ^ 2 • x 0 - z • b 0 - b 1 := by
    rw [← h1, hx1, smul_sub, smul_smul]
    module
  have hx3 : x 3 = z ^ 3 • x 0 - z ^ 2 • b 0 - z • b 1 - b 2 := by
    rw [← h2, hx2, smul_sub, smul_sub, smul_smul, smul_smul]
    module
  ext i
  fin_cases i
  · rfl
  · exact hx1
  · exact hx2
  · exact hx3

lemma companion_resolvent_unique (g : Fin 5 → Module.End K V) (H L : Module.End K V)
    (z : K) (x b : Fin 4 → V) (hH : H * g 4 = 1) (hH' : g 4 * H = 1)
    (hL : L * coordinatePolynomial g z = 1) (hres : z • x - coordinateStep g H x = b) :
    x = companionResolvent g L z b := by
  have hx := first_three_resolvent_reconstruct g H z x b hres
  have herr := complete_resolvent_residual g H z (x 0) b hH
  have hz : z • resolventState z (x 0) b - coordinateStep g H (resolventState z (x 0) b) - b = 0
    := by
    rw [← hx, hres, sub_self]
  rw [hz] at herr
  have hv := congrFun herr 3
  change 0 = H (coordinatePolynomial g z (x 0) - coordinateCauchy g z b) at hv
  have hg4 (w : V) : g 4 (H w) = w := congrArg (fun F : Module.End K V => F w) hH'
  have hpoly : coordinatePolynomial g z (x 0) = coordinateCauchy g z b := by
    have hf := congrArg (g 4) hv
    rw [map_zero, hg4] at hf
    exact (sub_eq_zero.mp hf.symm)
  have hinv (w : V) : L (coordinatePolynomial g z w) = w :=
    congrArg (fun F : Module.End K V => F w) hL
  have hzero : x 0 = L (coordinateCauchy g z b) := by rw [← hpoly, hinv]
  rw [hx, hzero]
  rfl

lemma reference_polynomial_guards :
    (1 : Module.End ℚ ℚ) * referencePolynomialCoefficients 4 = 1 ∧
    referencePolynomialCoefficients 4 * (1 : Module.End ℚ ℚ) = 1 ∧
    coordinatePolynomial referencePolynomialCoefficients 2 * referenceCoordinateInverse = 1 ∧
    referenceCoordinateInverse * coordinatePolynomial referencePolynomialCoefficients 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [referencePolynomialCoefficients]
  · simp [referencePolynomialCoefficients]
  · ext
    norm_num [referencePolynomialCoefficients, referenceCoordinateInverse, coordinatePolynomial]
  · ext
    norm_num [referencePolynomialCoefficients, referenceCoordinateInverse, coordinatePolynomial]

/-- **GAC2:native-companion-resolvent**
(guarded resolvent of the complete four-jet companion). -/
@[ledger "GAC2:native-companion-resolvent"]
theorem resolventLaw : Statement.resolventLaw := by
  intro K V _ _ _
  exact ⟨complete_resolvent_residual,
    companion_resolvent_solves,
    first_three_resolvent_reconstruct,
    companion_resolvent_unique,
    reference_polynomial_guards⟩

/-! ## Non-vacuity -/

example : resolventState (2 : ℚ) (3 : ℚ) ![1, 4, 5, 6] = ![3, 5, 6, 7] := by
  ext i
  fin_cases i <;> norm_num [resolventState]

example :
    (2 : ℚ) • companionResolvent referencePolynomialCoefficients referenceCoordinateInverse 2
      ![1, 4, 5, 6] - coordinateStep referencePolynomialCoefficients 1
        (companionResolvent referencePolynomialCoefficients referenceCoordinateInverse 2 ![1, 4,
          5, 6]) =
      ![1, 4, 5, 6] := by
  exact companion_resolvent_solves referencePolynomialCoefficients 1 referenceCoordinateInverse 2
    ![1, 4, 5, 6] reference_polynomial_guards.1 reference_polynomial_guards.2.2.1

end Artform.Scores.GravityBridge.Native.SlowCompanion
