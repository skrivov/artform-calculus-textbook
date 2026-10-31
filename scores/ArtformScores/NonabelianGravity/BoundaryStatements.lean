import ArtformScores.NonabelianGravity.BoundaryConditioning
import ArtformScores.NonabelianGravity.BoundaryHistoryKernel
import ArtformScores.NonabelianGravity.BoundaryQuantum
import ArtformScores.Meta.Ledger

/-! # Literal source-bound spatial, history and quantum boundary claims -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Legendre BoundarySymbol BoundaryHistory BoundaryQuantum
open Artform.Scores.GravityBridge.Native.Full40

/-- **NGB:native-boundary-conditioning** (the actual reciprocal-character boundary test). -/
@[ledger "NGB:native-boundary-conditioning"]
def nativeBoundaryConditioning : Prop :=
  (∀ z : ℂ, z ≠ 0 → ∀ u v : Point ℂ,
    nativeMixed z u v = dotProduct u (mixedApply z v)) ∧
  (∀ (n : ℤ) (u v : Point ℂ),
    circleMixed n u v = dotProduct u (mixedApply (rotationValue ^ n) v)) ∧
  ‖rotationValue‖ = 1 ∧
  Irrational (Complex.arg rotationValue / (2 * Real.pi)) ∧
  DenseRange (fun n : ℤ => BoundarySymbol.rotation ^ n) ∧
  (∀ n : ℤ, rotationValue ^ n ≠ -1) ∧
  (∀ z : ℂ, z ≠ 0 → ∀ v : Point ℂ,
    dotProduct (witnessWeight z) (mixedApply z v) =
      ((10201 + 10589 * z) * (1 + z) / 2) * v 22) ∧
  (∀ z : ℂ, mixedApply z boostUnit =
    fun i => if i = 10 ∨ i = 15 then -(1 + z) / 4 else 0) ∧
  (∀ z : ℂ, ‖mixedApply z boostUnit‖ = ‖1 + z‖ / 4) ∧
  (∀ (n : ℤ) (v : Point ℂ), mixedApply (rotationValue ^ n) v = 0 →
    v 22 = 0 ∧ dotProduct (fun i => star (v i)) boostUnit = 0) ∧
  (¬ ∃ C : ℝ, ∀ (n : ℤ) (v : Point ℂ),
    ‖v 22‖ ≤ C * ‖mixedApply (rotationValue ^ n) v‖)

/-- **NGB:native-history-source-guard** (extra compatibility beyond the two-cell guard). -/
@[ledger "NGB:native-history-source-guard"]
def nativeHistorySourceGuard : Prop :=
  (∀ w : Biv ℚ,
    fieldPoint (gaugeFirst w) = gaugeField historyStep (parameter w) 1 ∧
    fieldPoint (gaugeSecond w) = gaugeField historyStep (parameter w) 2 ∧
    middleH.mulVec (gaugeFirst w) + mixed.mulVec (gaugeSecond w) = 0 ∧
    mixed.transpose.mulVec (gaugeFirst w) + middleH.mulVec (gaugeSecond w) = 0 ∧
    mixed.mulVec (gaugeFirst w) = 0 ∧ mixed.transpose.mulVec (gaugeSecond w) = 0 ∧
    ∀ t : HistoryTime, t = 0 ∨ t = 3 ∨ t = 4 →
      gaugeField historyStep (parameter w) t = 0) ∧
  (∀ x y v z j₁ j₂ : Point ℚ, ThreeCellMatch x y v z j₁ j₂ → ∀ w : Biv ℚ,
    pair (gaugeFirst w) j₁ + pair (gaugeSecond w) j₂ = 0) ∧
  activeProjector.mulVec source16 = source16 ∧
  (∀ x z : Point ℚ, ¬ ∃ y v, ThreeCellMatch x y v z source16 0) ∧
  ThreeCellMatch 0 0 0 0 0 0

/-- **NGB:native-quantum-kernel-tests** (finite real action and naive phase-kernel tests). -/
@[ledger "NGB:native-quantum-kernel-tests"]
def nativeQuantumKernelTests : Prop :=
  outputDirection ≠ 0 ∧
  (∀ (u v : Point ℝ) (t : ℝ),
    cutAction u (v + t • outputDirection) = cutAction u v) ∧
  (∀ t : ℝ, cutAction (t • negativeDirection) 0 = -(291 / 101 : ℝ) * t ^ 2) ∧
  (∀ (ℏ : ℝ) (u v : Point ℝ) (t : ℝ),
    naivePhaseKernel ℏ u (v + t • outputDirection) = naivePhaseKernel ℏ u v)

end Artform.Scores.NonabelianGravity.Statement
