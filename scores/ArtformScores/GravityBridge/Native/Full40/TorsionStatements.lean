import ArtformScores.GravityBridge.Native.Full40.TorsionDefs

/-! # The full flat torsion map and Lorentz columns -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:native-flat-torsion-gauge**
(the full flat torsion map and lorentz columns). -/
@[ledger "GAC2:native-flat-torsion-gauge"]
def torsionLaw : Prop :=
  ∀ (X K : Type) [AddCommGroup X] [Field K] [CharZero K],
    (∀ (a b : Biv K),
    lie (a - b) = lie a - lie b) ∧
    (∀ (d : Fin 4 → X) (f : X → Frame K) (A : X → Connection K)
    (x : X) (i j a : Fin 4),
    torsion d f A x i j a = -torsion d f A x j i a) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K) (x : X) (i j a : Fin 4),
    torsion d (gaugeFrame w) (gaugeConnection d w) x i j a = 0) ∧
    (∀ (d : Fin 4 → X) (w : X → Biv K) (x : X) (i j : Fin 4),
    linearCurvature d (gaugeConnection d w) x i j = 0) ∧
    (∀ (kappa epsilon : K) (theta test : Fin 4 → Fin 4 → Vec K),
    torsionDensity kappa (theta + epsilon • test) = torsionDensity kappa theta +
      epsilon * torsionMixed kappa theta test + epsilon ^ 2 * torsionDensity kappa test)

end Artform.Scores.GravityBridge.Native.Full40.Statement
