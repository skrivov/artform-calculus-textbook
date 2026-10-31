import ArtformScores.GravityBridge.Native.Full40.TemporalProfileDefs
/-! # Higher temporal Lorentz jets with explicit real profile bounds -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:higher-temporal-profile-budget**
(higher temporal lorentz jets with explicit real profile bounds). -/
@[ledger "GAC2:higher-temporal-profile-budget"]
def temporalProfileLaw : Prop :=
    (∀ (h c : ℝ),
    temporalGaugeProfile h c 0 = 0) ∧
    (∀ (h c : ℝ) (_hh : h ≠ 0),
    temporalGaugeProfile h c h = c) ∧
    (∀ (h c : ℝ),
    HasDerivAt (temporalGaugeProfile h c) 0 0) ∧
    (∀ (h c : ℝ) (_hh : h ≠ 0),
    temporalGaugeProfile h (-c) h - temporalGaugeProfile h (-c) 0 = -c) ∧
    (∀ (h c : ℝ) (_hh : h ≠ 0),
    -(temporalGaugeProfile h (-c) h - temporalGaugeProfile h (-c) 0) / h = c / h) ∧
    (∀ (h a : ℝ) (_hh : h ≠ 0) (t : ℝ),
    temporalGaugeProfile h (h ^ 3 * a / 4) t = h * a * t ^ 2 / 4) ∧
    (∀ (h c : ℝ)
    (g : ℝ → ℝ) (_h0 : g 0 = 0) (_h1 : g h = 0)
    (_hc : g h - g 0 = -c),
    c = 0) ∧
    (∀ (h c : ℝ),
    boundedTemporalProfile h c 0 = 0) ∧
    (∀ (h c : ℝ) (_hh : h ≠ 0),
    boundedTemporalProfile h c h = c) ∧
    (∀ (h c : ℝ),
    HasDerivAt (boundedTemporalProfile h c) 0 0) ∧
    (∀ (h c t : ℝ),
    |boundedTemporalProfile h c t| ≤ |c * ((1 + h ^ 2) / h ^ 2)|) ∧
    (∀ (h a t : ℝ) (_hh : 0 < h),
    |boundedTemporalProfile h (h ^ 3 * a / 4) t| ≤ h * |a| * (1 + h ^ 2) / 4)
end Artform.Scores.GravityBridge.Native.Full40.Statement
