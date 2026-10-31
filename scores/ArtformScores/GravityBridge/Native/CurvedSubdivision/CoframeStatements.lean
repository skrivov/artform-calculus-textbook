import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoframeDefs

/-! # Coframe source retained after connection detail stationarity -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Filter

open Matrix Full40

/-- **GAC2:native-stationary-coframe-source**
(coframe source retained after connection detail stationarity). -/
@[ledger "GAC2:native-stationary-coframe-source"]
noncomputable def coframeLaw : Prop :=
    (∀ (b c s : ℝ),
    HasDerivAt (fun x => stationaryValue x c s)
      ((1 / 101 : ℝ) - Real.sqrt (detailD c s)) b) ∧
    (∀ (b u r : ℝ) (_hb : b ≠ 0) (_hu : 0 < u)
    (_hrc : Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u))
    (_hrs : Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u)),
    HasDerivAt (fun x => literalTwoChildAction x u r)
      ((1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u))) b) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r : ℝ, nativeSplitFirst b u r 0 = 0 ∧
      HasDerivAt (fun x => literalTwoChildAction x u r)
        ((1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u))) b ∧
      (1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) < 0)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
