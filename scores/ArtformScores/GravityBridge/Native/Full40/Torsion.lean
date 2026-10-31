import ArtformScores.GravityBridge.Native.Full40.TorsionStatements

/-! # The full flat torsion map and Lorentz columns -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]

omit [CharZero K] in
lemma lie_sub (a b : Biv K) : lie (a - b) = lie a - lie b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lie, sub_eq_add_neg, add_comm]
omit [CharZero K] in
lemma torsion_antisymmetric (d : Fin 4 → X) (f : X → Frame K) (A : X → Connection K)
    (x : X) (i j a : Fin 4) : torsion d f A x i j a = -torsion d f A x j i a := by
  dsimp [torsion]
  ring
omit [CharZero K] in
lemma torsion_gauge_zero (d : Fin 4 → X) (w : X → Biv K) (x : X) (i j a : Fin 4) :
    torsion d (gaugeFrame w) (gaugeConnection d w) x i j a = 0 := by
  simp [torsion, gaugeFrame, gaugeConnection, lie_sub]
omit [CharZero K] in
lemma curvature_gauge_zero (d : Fin 4 → X) (w : X → Biv K) (x : X) (i j : Fin 4) :
    linearCurvature d (gaugeConnection d w) x i j = 0 := by
  funext a
  simp [linearCurvature, gaugeConnection, add_assoc, add_comm (d i) (d j)]
  ring
omit [AddCommGroup X] [CharZero K] in
lemma torsion_exact_variation (kappa epsilon : K) (theta test : Fin 4 → Fin 4 → Vec K) :
    torsionDensity kappa (theta + epsilon • test) = torsionDensity kappa theta +
      epsilon * torsionMixed kappa theta test + epsilon ^ 2 * torsionDensity kappa test := by
  simp [torsionDensity, torsionMixed, etaPair, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply]
  ring

/-- **GAC2:native-flat-torsion-gauge**
(the full flat torsion map and lorentz columns). -/
@[ledger "GAC2:native-flat-torsion-gauge"]
theorem torsionLaw : Statement.torsionLaw := by
  intro X K _ _ _
  exact ⟨lie_sub,
    torsion_antisymmetric,
    torsion_gauge_zero,
    curvature_gauge_zero,
    torsion_exact_variation⟩

/-! ## Non-vacuity -/
def torsionTest : Fin 4 → Fin 4 → Vec ℚ := fun i j a =>
  if i = 0 ∧ j = 1 ∧ a = 2 then 1 else if i = 1 ∧ j = 0 ∧ a = 2 then -1 else 0
example : torsionDensity (1 / 101) torsionTest = -1 / 101 ∧
    torsionMixed (1 / 101) torsionTest torsionTest = -2 / 101 := by
  norm_num [torsionDensity, torsionMixed, torsionTest, faceFirst, faceSecond,
    etaPair, eta, Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.Full40
