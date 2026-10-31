import ArtformScores.GravityBridge.Native.CurvedSubdivision.TorsionDefs

/-! # Full ordered nonlinear torsion on the inherited coframe -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-curved-ordered-torsion**
(full ordered nonlinear torsion on the inherited coframe). -/
@[ledger "GAC2:native-curved-ordered-torsion"]
def torsionLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (h b c s : K),
    exactTorsion h b c s = fun i l =>
      if i = 0 ∧ l = 1 then h • ![1 - c, s, 0, 0] else
        if i = 1 ∧ l = 0 then -(h • ![1 - c, s, 0, 0]) else 0) ∧
    (∀ (h b : K) (_hh : h ≠ 0) (_hb : b ≠ 0),
    ((inheritedCoframe h b).transpose * internalMetric * inheritedCoframe h b) *
      exactMetricInverse h b = 1) ∧
    (∀ (h b c s : K) (_hh : h ≠ 0) (_hb : b ≠ 0)
    (_hc : c ^ 2 - s ^ 2 = 1),
    exactTorsionDensity h b c s = -2 * h * b * (c - 1))

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
