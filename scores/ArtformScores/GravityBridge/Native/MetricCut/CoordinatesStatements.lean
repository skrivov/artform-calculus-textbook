import ArtformScores.GravityBridge.Native.MetricCut.CoordinatesDefs
/-! # The original metric Cauchy organization and exact inverses -/
namespace Artform.Scores.GravityBridge.Native.MetricCut.Statement
open Matrix
/-- **GAC2:metric-cauchy-organization**
(the original metric cauchy organization and exact inverses). -/
@[ledger "GAC2:metric-cauchy-organization"]
def coordinatesLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (_hj : j ≠ 0) (_hR : rho2 k ≠ 0) (_hq : q *ᵥ k = 0),
    coulomb3 j k (spatialCompose j k q s u) = u) ∧
    (∀ (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (_hR : rho2 k ≠ 0) (_hq : q *ᵥ k = 0) (_ht : trace q = 0),
    scalar3 k (spatialCompose j k q s u) = s) ∧
    (∀ (j : K) (k : SVec K) (m : SMat K)
    (_hj : j ≠ 0) (_hR : rho2 k ≠ 0),
    tt3 j k m *ᵥ k = 0) ∧
    (∀ (j : K) (k : SVec K) (m : SMat K)
    (_hj : j ≠ 0) (_hR : rho2 k ≠ 0),
    trace (tt3 j k m) = 0) ∧
    (∀ (j : K) (k : SVec K) (m : SMat K)
    (_hm : ∀ i l, m i l = m l i),
    ∀ i l, tt3 j k m i l = tt3 j k m l i) ∧
    (∀ (j : K) (k : SVec K) (m : SMat K),
    spatialCompose j k (tt3 j k m) (scalar3 k m) (coulomb3 j k m) = m) ∧
    (∀ (j : K) (k : SVec K) (x : CauchyData K)
    (_hj : j ≠ 0) (_hj2 : j * j = -1) (_hR : rho2 k ≠ 0),
    reconstruct j k (organize j k x) = x) ∧
    (∀ (j : K) (k : SVec K) (z : Organized K)
    (_hj : j ≠ 0) (_hj2 : j * j = -1) (_hR : rho2 k ≠ 0)
    (_hq : z.tt *ᵥ k = 0) (_ht : trace z.tt = 0)
    (_hp : z.ttVelocity *ᵥ k = 0) (_hpt : trace z.ttVelocity = 0),
    organize j k (reconstruct j k z) = z) ∧
    (∀ (j : K) (k : SVec K) (x : CauchyData K)
    (_hx : symmetricCauchy x),
    symmetricOrganized (organize j k x)) ∧
    (∀ (j : K) (k : SVec K) (z : Organized K)
    (_hz : symmetricOrganized z),
    symmetricCauchy (reconstruct j k z))
end Artform.Scores.GravityBridge.Native.MetricCut.Statement
