import ArtformScores.GravityBridge.Native.CurvedSubdivision.DetailDefs

/-! # Corrected stationary real detail in the original split action -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-current-stationary-detail**
(corrected stationary real detail in the original split action). -/
@[ledger "GAC2:native-current-stationary-detail"]
noncomputable def detailLaw : Prop :=
    (∀ (C S : ℝ) (_hC : 0 < C) (_hL : C ^ 2 - S ^ 2 = 1),
    ∃ r : ℝ, Real.cosh r = C ∧ Real.sinh r = S) ∧
    (∀ (b u r j : ℝ),
    nativeSplitFirst b u r j =
      currentDetailForce b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r) j ∧
    nativeSplitSecond b u r =
      currentDetailHessian b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r)) ∧
    (∀ (b u r j : ℝ),
    nativeSplitAction b u r j =
      currentFineValue b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r) - j * r) ∧
    (∀ (b u : ℝ) (_hu : 0 < u),
    ∃ r : ℝ, Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u) ∧
      Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u) ∧
      nativeSplitFirst b u r 0 = 0 ∧
      nativeSplitSecond b u r = -b * Real.sqrt (detailD (Real.cosh u) (Real.sinh u))) ∧
    (∀ (u r : ℝ) (_hu : 0 < u)
    (_hrc : Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u))
    (_hrs : Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u)),
    -u < r ∧ r < 0) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ nativeSplitFirst b u r 0 = 0 ∧
      literalTwoChildAction b u r = stationaryValue b (Real.cosh u) (Real.sinh u)) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ HasDerivAt (literalTwoChildAction b u) 0 r ∧
      literalTwoChildAction b u r = stationaryValue b (Real.cosh u) (Real.sinh u)) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    nativeSplitFirst b u 0 0 ≠ 0) ∧
    (∀ (b u r j : ℝ),
    HasDerivAt (fun t => nativeSplitAction b u t j) (nativeSplitFirst b u r j) r) ∧
    (∀ (b u r j : ℝ),
    HasDerivAt (fun t => nativeSplitFirst b u t j) (nativeSplitSecond b u r) r) ∧
    (∀ (c s : ℝ) (_hc : c ^ 2 - s ^ 2 = 1) (_hco : 1 < c) (_hs : 0 < s),
    0 < detailD c s ∧ (1 / 101 : ℝ) < Real.sqrt (detailD c s))

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
