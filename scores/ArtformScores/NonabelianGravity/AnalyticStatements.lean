import ArtformScores.NonabelianGravity.AnalyticWitness
import ArtformScores.NonabelianGravity.Stabilizers
import ArtformScores.NonabelianGravity.GeometryPreflight
import ArtformScores.Meta.Ledger

/-! # Exact analytic interpretation and orbit-type submissions -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Statement

/-- **NGB:analytic-interpretation** (actual quaternion curve derivatives and fused form values). -/
@[ledger "NGB:analytic-interpretation"]
def analyticInterpretation : Prop :=
  (∀ (c : ℕ → ℝ → Maurer.H) (g : ℕ → Maurer.Hˣ) (x : ℕ → Maurer.H) (t : ℝ),
    (∀ i, c i t = (g i : Maurer.H)) →
    (∀ i, HasDerivAt (c i) (x i * (g i : Maurer.H)) t) →
    ∀ w, HasDerivAt (Maurer.curveWord c w)
      (Maurer.oneValue g x (Maurer.right w)*(Maurer.evalWord g w : Maurer.Hˣ)) t) ∧
  (∀ (g : ℕ → Maurer.Hˣ) (x y : ℕ → Maurer.H) (a b : Maurer.OneForm),
    Maurer.twoValue g x y (Maurer.wedge a b)=
      Maurer.pairing (Maurer.oneValue g x a) (Maurer.oneValue g y b)-
        Maurer.pairing (Maurer.oneValue g x b) (Maurer.oneValue g y a)) ∧
  (∀ (c d : ℕ → ℝ → Maurer.H) (g : ℕ → Maurer.Hˣ) (x y : ℕ → Maurer.H) (t : ℝ),
    (∀ i, c i t = (g i : Maurer.H)) → (∀ i, d i t = (g i : Maurer.H)) →
    (∀ i, HasDerivAt (c i) (x i * (g i : Maurer.H)) t) →
    (∀ i, HasDerivAt (d i) (y i * (g i : Maurer.H)) t) →
    (∀ s, Maurer.analyticTwiceOmega c d t s=Maurer.twoValue g x y (Maurer.twiceOmega s)) ∧
    Maurer.analyticTwiceOmega c d t (Maurer.wordKick 0 Maurer.original)=
      Maurer.analyticTwiceOmega c d t Maurer.original ∧
    Maurer.analyticTwiceOmega c d t (Maurer.wordKick 1 Maurer.original)=
      Maurer.analyticTwiceOmega c d t Maurer.original ∧
    Maurer.analyticTwiceOmega c d t (Maurer.wordDrift Maurer.original)=
      Maurer.analyticTwiceOmega c d t Maurer.original) ∧
  (∀ j i t, Quaternion.normSq (Maurer.witnessCurve j i t)=1) ∧
  Maurer.analyticTwiceOmega (Maurer.witnessCurve 0) (Maurer.witnessCurve 7) 0
    Maurer.original=8

/-- **NGB:stabilizer-preservation** (exact orbit stabilizers for the actual complete scores). -/
@[ledger "NGB:stabilizer-preservation"]
def stabilizerPreservation : Prop :=
  ∀ (G : Type) [Group G] (w : List Instruction) (s : State G),
    Function.Injective (run (G:=G) w) ∧ stabilizer (run w s)=stabilizer s

/-- **NGB:geometric-preflight** (valence gap and a fixed-conjugacy adverse control). -/
@[ledger "NGB:geometric-preflight"]
def geometricPreflight : Prop :=
  (∀ v, (star v).length<4) ∧
  Gauss (cycleState quaternionI) ∧ Gauss (kick 0 false (cycleState quaternionI)) ∧
  (∀ e, Quaternion.normSq ((cycleState quaternionI).U e : Maurer.H)=1 ∧
    Quaternion.normSq ((cycleState quaternionI).P e : Maurer.H)=1) ∧
  (∀ e, Quaternion.normSq ((kick 0 false (cycleState quaternionI)).U e : Maurer.H)=1 ∧
    Quaternion.normSq ((kick 0 false (cycleState quaternionI)).P e : Maurer.H)=1) ∧
  ((cycleState quaternionI).P 0 : Maurer.H).re=0 ∧
  ((kick 0 false (cycleState quaternionI)).P 0 : Maurer.H).re = -1 ∧
  ¬ ∃ h : Maurer.Hˣ,
    h*(cycleState quaternionI).P 0*h⁻¹=(kick 0 false (cycleState quaternionI)).P 0
end Artform.Scores.NonabelianGravity.Statement
