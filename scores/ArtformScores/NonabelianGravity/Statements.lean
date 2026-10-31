import ArtformScores.NonabelianGravity.Process
import ArtformScores.NonabelianGravity.Descent
import ArtformScores.NonabelianGravity.Controls
import ArtformScores.NonabelianGravity.Double
import ArtformScores.NonabelianGravity.WordBinding
import ArtformScores.NonabelianGravity.Scaling
import ArtformScores.Meta.Ledger

/-! # NGB: literal canonical submissions with their physical scope kept separate -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Statement

/-- **NGB:two-face-geometry** (opposite orientations and complete ordered stars). -/
@[ledger "NGB:two-face-geometry"]
def twoFaceGeometry : Prop :=
  canvas.src=![0,1,4,3,1,2,5] ∧ canvas.tgt=![1,4,3,0,2,5,4] ∧
  canvas.boundary 0=[(0,true),(1,true),(2,true),(3,true)] ∧
  canvas.boundary 1=[(4,true),(5,true),(6,true),(1,false)] ∧
  (∀ v a, a ∈ star v ↔ endpoint a=v) ∧ (∀ v, (star v).Nodup) ∧
  ∀ (G : Type) [Group G] (s : State G) (h : canvas.V → G),
    (∀ v, defect s v=((star v).map (fun a => if a.2 then s.P a.1 else outgoing s a.1)).prod) ∧
    (∀ v, defect (gauge h s) v=h v*defect s v*(h v)⁻¹) ∧
    (Gauss (gauge h s) ↔ Gauss s) ∧
    (∀ f i, holonomy (gauge h s).U f i=
      h (stepTarget f i)*holonomy s.U f i*(h (stepTarget f i))⁻¹)

/-- **NGB:oriented-score** (exact defects and reverses through gauge reduction). -/
@[ledger "NGB:oriented-score"]
def orientedScore : Prop :=
  ∀ (G : Type) [Group G] (w : List Instruction) (s : State G) (h : canvas.V → G),
    run (w.reverse.map inverseInstruction) (run w s)=s ∧
    run w (run (w.reverse.map inverseInstruction) s)=s ∧
    (∀ n, defect (run (w.take n) s)=defect s) ∧ run w (gauge h s)=gauge h (run w s) ∧
    (∀ f b, defect (kick f b s)=defect s ∧ kick f (!b) (kick f b s)=s) ∧
    (∀ b, defect (drift b s)=defect s ∧ drift (!b) (drift b s)=s) ∧
    (∀ b, outgoing (kick 1 b s) 1=multiplier b s.U 1 3*outgoing s 1) ∧
    (∀ b c, kick 0 b (kick 1 c s)=kick 1 c (kick 0 b s)) ∧
    (∀ x : Admitted G, runAdmitted (w.reverse.map inverseInstruction) (runAdmitted w x)=x) ∧
    (∀ x : GaugeReduced G, runPhysical (w.reverse.map inverseInstruction) (runPhysical w x)=x ∧
      runPhysical w (runPhysical (w.reverse.map inverseInstruction) x)=x)

/-- **NGB:legal-overlap** (commuting maps with overlapping writes are scheduled sequentially). -/
@[ledger "NGB:legal-overlap"]
def legalOverlap : Prop :=
  ∀ (G : Type) [Group G],
    (∀ g (x : (frame G).Table), (profile g).guard x ∧
      (profile (G:=G) g).reads=reads g ∧ (profile (G:=G) g).writes=writes g ∧
      (profile g).apply x=encode (execute g (decode x))) ∧
    (∀ g h (x : (frame G).Table),
      (profile g).apply (tableGauge h x)=tableGauge h ((profile g).apply x)) ∧
    (∀ b c (x : (frame G).Table),
      ¬ Artform.EnabledApp.Compatible (app (.face 0 b) x) (app (.face 1 c) x)) ∧
    (law G).score.period=3 ∧ (∀ t, ¬ (law G).score.allowsEmpty t) ∧
    (∀ t x, (law G).LegalAt t x ↔ Gauss (decode x)) ∧
    (∀ i (x : (frame G).Table), (phaseBatch i x).apps.length=1) ∧
    (realizer G).WellPosed ∧
    (∀ s : State G, decode (((realizer G).select 2 (((realizer G).select 1
      (((realizer G).select 0 (encode s)).apply)).apply)).apply)=tick s)

/-- **NGB:noncommuting-controls** (admitted quotient motion and specified failed shortcuts). -/
@[ledger "NGB:noncommuting-controls"]
def noncommutingControls : Prop :=
  Gauss witness ∧ Gauss (tick witness) ∧ (holonomy witness.U 1 3*outgoing witness 1 ≠
    outgoing witness 1*holonomy witness.U 1 3) ∧
  holonomy witness.U 0 0*holonomy witness.U 0 0=1 ∧
  holonomy (tick witness).U 0 0*holonomy (tick witness).U 0 0 ≠ 1 ∧
  (¬ ∃ h, gauge h witness=tick witness) ∧
  (¬ Gauss (partialKick witness)) ∧ (¬ Gauss (wrongOrientation witness)) ∧
  wrongDefect witness=1 ∧ wrongDefect (kick 1 false witness) ≠ 1 ∧
  kick 1 false (drift false (kick 0 false witness)) ≠
    drift false (kick 1 false (kick 0 false witness))

/-- **NGB:double-dictionary** (the actual endpoint algebra of the AMM double). -/
@[ledger "NGB:double-dictionary"]
def doubleDictionary : Prop :=
  ∀ (G : Type) [Group G] (U P ht hs a b : G),
    (doubleTarget (doubleA U P) (doubleB U P)=P ∧
      doubleSource (doubleA U P) (doubleB U P)=U⁻¹*P⁻¹*U) ∧
    (doubleA (ht*U*hs⁻¹) (ht*P*ht⁻¹)=ht*doubleA U P*hs⁻¹ ∧
      doubleB (ht*U*hs⁻¹) (ht*P*ht⁻¹)=hs*doubleB U P*ht⁻¹) ∧
    (doubleA a (a*b)=a ∧ doubleB a (a*b)=b) ∧
    (doubleA (P*U) P=doubleA U P*doubleB U P*doubleA U P ∧
      doubleB (P*U) P=(doubleA U P)⁻¹)

/-- **NGB:formal-two-form** (universal finite Maurer algebra, with a nonzero baseline). -/
@[ledger "NGB:formal-two-form"]
def formalTwoForm : Prop :=
  Maurer.collect (Maurer.defect (Maurer.wordKick 0))=[] ∧
  Maurer.collect (Maurer.defect (Maurer.wordKick 1))=[] ∧
  Maurer.collect (Maurer.defect Maurer.wordDrift)=[] ∧
  Maurer.value Maurer.witnessPair (Maurer.twiceOmega Maurer.original)=1 ∧
  ∀ (R : Type) [CommRing R] (pair : Maurer.Key → R),
    Maurer.value pair (Maurer.defect (Maurer.wordKick 0))=0 ∧
    Maurer.value pair (Maurer.defect (Maurer.wordKick 1))=0 ∧
    Maurer.value pair (Maurer.defect Maurer.wordDrift)=0

/-- **NGB:word-binding** (normalization and the formal constructor have exact group semantics). -/
@[ledger "NGB:word-binding"]
def wordBinding : Prop :=
  ∀ (G : Type) [Group G] (g : ℕ → G),
    (∀ u v, Maurer.evalWord g (Maurer.wm u v)=Maurer.evalWord g u*Maurer.evalWord g v) ∧
    (∀ w, Maurer.evalWord g (Maurer.wi w)=(Maurer.evalWord g w)⁻¹) ∧
    (∀ s f, Maurer.evalState g (Maurer.wordKick f s)=kick f false (Maurer.evalState g s)) ∧
    (∀ s, Maurer.evalState g (Maurer.wordDrift s)=drift false (Maurer.evalState g s)) ∧
    (∀ s : State G, Maurer.evalState (Maurer.assignment s) Maurer.original=s)

/-- **NGB:neighbor-scaling** (noncommutative jets and a conditional pointwise norm budget). -/
@[ledger "NGB:neighbor-scaling"]
def neighborScaling : Prop :=
  (∀ (G : Type) [Group G] (s : State G), (kick 1 false (kick 0 false s)).P 1=
    holonomy s.U 0 1*s.P 1*(holonomy s.U 1 2)⁻¹) ∧
  (∀ (R : Type) [Ring R] (E J F KL KR A B C : R),
    Scaling.times (Scaling.times (Scaling.field F KL) (Scaling.field E J))
      (Scaling.inverseField F KR)=Scaling.field E (KL+J-KR) ∧
    Scaling.times (Scaling.field E J) (Scaling.link A B C)=
      Scaling.link A (B+E) (C+E*A+J)) ∧
  ∀ (R : Type) [NormedDivisionRing R] (L K P : R), ‖K‖ = 1 → ‖P‖ = 1 →
    (‖L*P*K⁻¹-P‖ ≤ ‖L - K‖+2*‖K - 1‖*‖P - 1‖) ∧
    ∀ (h CF CK CP : ℝ), 0 < h → 0 ≤ CK → 0 ≤ CP →
      ‖L - K‖ ≤ CF*h ^ 3 → ‖K - 1‖ ≤ CK*h ^ 2 → ‖P - 1‖ ≤ CP*h ^ 2 →
      ‖L*P*K⁻¹-P‖ ≤ CF*h ^ 3+2*CK*CP*h ^ 4 ∧
      ‖L*P*K⁻¹-P‖ / h ^ 2 ≤ CF*h+2*CK*CP*h ^ 2
end Artform.Scores.NonabelianGravity.Statement
