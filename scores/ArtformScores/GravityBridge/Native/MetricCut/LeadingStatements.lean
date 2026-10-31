import ArtformScores.GravityBridge.Native.MetricCut.LeadingDefs
/-! # The original leading normal range and visible source return -/
namespace Artform.Scores.GravityBridge.Native.MetricCut.Statement
open Matrix
/-- **GAC2:metric-leading-range-return**
(the original leading normal range and visible source return). -/
@[ledger "GAC2:metric-leading-range-return"]
def leadingLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (k : SVec K) (x : K × SVec K),
    dot3 k (normalLeading k x).2 = 0) ∧
    (∀ (k : SVec K) (rhs : K × SVec K) (a : K)
    (_hR : rho2 k ≠ 0) (_hr : dot3 k rhs.2 = 0),
    normalLeading k (normalLift k rhs a) = rhs) ∧
    (∀ (k : SVec K) (rhs : K × SVec K) (_hR : rho2 k ≠ 0),
    (∃ x, normalLeading k x = rhs) ↔ dot3 k rhs.2 = 0) ∧
    (∀ (k : SVec K) (x : K × SVec K) (_hR : rho2 k ≠ 0),
    normalLeading k x = 0 ↔ x.1 = 0 ∧ ∃ a : K, x.2 = a • k) ∧
    (∀ {v n : Type*} [Fintype v]
    (h : K) (Y : Matrix n v K) (E : Matrix v v K) (X : Matrix v n K),
    ((h ^ 2) • Y) * E * ((h ^ 2) • X) = h ^ 4 • (Y * E * X)) ∧
    (∀ {v n : Type*} [Fintype v] [Fintype n] [DecidableEq v]
    (C : Matrix n v K) (E : Matrix v v K) (X : Matrix v n K)
    (V : Matrix v v K) (s target : v → K) (c : n → K)
    (_hE : E * V = 1) (_hs : V *ᵥ s + X *ᵥ c = target),
    C *ᵥ s = C *ᵥ (E *ᵥ target) - (C * E * X) *ᵥ c)
end Artform.Scores.GravityBridge.Native.MetricCut.Statement
