import ArtformScores.ClassicalNonabelian.Process
import ArtformScores.ClassicalNonabelian.Descent
import ArtformScores.ClassicalNonabelian.Controls
import ArtformScores.Meta.Ledger

/-! # Submitted classical non-Abelian impulse and Gauss claims -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.ClassicalNonabelian.Statement
open Artform

/-- **CNI:geometry-gauss** (complete ordered stars and actual face holonomies). -/
@[ledger "CNI:geometry-gauss"]
def geometryGauss : Prop :=
  canvas.src 4=0 ∧ canvas.tgt 4=2 ∧
  canvas.boundary 0=[(0,true),(1,true),(2,true),(3,true)] ∧
  (∀ v a, a ∈ star v ↔ endpoint a=v) ∧ (∀ v, (star v).Nodup) ∧
  (∀ (G : Type) [Group G] (s : State G) (h : canvas.V → G),
    (∀ v, defect s v=((star v).map (fun a => if a.2 then s.P a.1 else outgoing s a.1)).prod) ∧
    (∀ v, defect (gauge h s) v=h v*defect s v*(h v)⁻¹) ∧
    (Gauss (gauge h s) ↔ Gauss s) ∧
    (∀ (l : List G) n, (l.rotate n).prod=1 ↔ l.prod=1) ∧
    (∀ e, holonomy s.U e=
      ![s.U 0*s.U 3*s.U 2*s.U 1,s.U 1*s.U 0*s.U 3*s.U 2,
        s.U 2*s.U 1*s.U 0*s.U 3,s.U 3*s.U 2*s.U 1*s.U 0,1] e) ∧
    (∀ e, (s.U e)⁻¹*holonomy s.U e*s.U e=holonomy s.U (previous e)) ∧
    (∀ e, holonomy (gauge h s).U e=h (canvas.tgt e)*holonomy s.U e*(h (canvas.tgt e))⁻¹))

/-- **CNI:two-shear-score** (raw reversibility, exact Gauss defect and orbit descent). -/
@[ledger "CNI:two-shear-score"]
def twoShearScore : Prop :=
  ∀ (G : Type) [Group G] (w : List Instruction) (s : State G) (h : canvas.V → G),
    run (w.reverse.map inverseInstruction) (run w s)=s ∧
    run w (run (w.reverse.map inverseInstruction) s)=s ∧
    (∀ n, defect (run (w.take n) s)=defect s) ∧
    run w (gauge h s)=gauge h (run w s) ∧
    (∀ b, defect (kick b s)=defect s ∧ defect (drift b s)=defect s ∧
      kick (!b) (kick b s)=s ∧ drift (!b) (drift b s)=s ∧
      (kick b s).P 4=s.P 4) ∧
    (∀ b e, defect (driftOne b e s)=defect s ∧ driftOne (!b) e (driftOne b e s)=s) ∧
    (∀ e, (tick s).P e=holonomy s.U e*s.P e ∧ (tick s).U e=(tick s).P e*s.U e) ∧
    (∀ x : Admitted G, runAdmitted (w.reverse.map inverseInstruction) (runAdmitted w x)=x ∧
      runAdmitted w (runAdmitted (w.reverse.map inverseInstruction) x)=x) ∧
    (∀ x : Physical G, runPhysical (w.reverse.map inverseInstruction) (runPhysical w x)=x ∧
      runPhysical w (runPhysical (w.reverse.map inverseInstruction) x)=x)

/-- **CNI:legal-native** (actual local ownership, nonempty Gauss law and parallel drift). -/
@[ledger "CNI:legal-native"]
def legalNative : Prop :=
  ∀ (G : Type) [Group G],
    (∀ (g : Instruction) (x : (frame G).Table), (profile g).guard x ∧
      (profile (G:=G) g).reads=reads g ∧ (profile (G:=G) g).writes=writes g ∧
      (profile g).apply x=encode (execute g (decode x))) ∧
    (∀ g (h : canvas.V → G) (x : (frame G).Table),
      (profile g).apply (tableGauge h x)=tableGauge h ((profile g).apply x)) ∧
    (∀ b e f (x : (frame G).Table), e ≠ f →
      EnabledApp.Compatible (app (.link b e) x) (app (.link b f) x)) ∧
    (∀ (x : (frame G).Table), (kickBatch x).apps.length=1 ∧ (driftBatch x).apps.length=5 ∧
      (kickBatch x).apply=encode (kick false (decode x)) ∧
      (driftBatch x).apply=encode (drift false (decode x))) ∧
    (law G).score.period=2 ∧ (∀ t, ¬ (law G).score.allowsEmpty t) ∧
    (∀ t x, (law G).LegalAt t x ↔ Gauss (decode x)) ∧
    (realizer G).WellPosed ∧
    (∀ (x : (frame G).Table) (b : Batch (frame G) x) l,
      l.Perm b.apps → applyAll l x=b.apply) ∧
    (∀ s : State G, decode (((realizer G).select 1
      (((realizer G).select 0 (encode s)).apply)).apply)=tick s)

/-- **CNI:noncommuting-control** (physical curvature change and failed shortcuts). -/
@[ledger "CNI:noncommuting-control"]
def noncommutingControl : Prop :=
  Gauss witness ∧
  holonomy witness.U 0*witness.P 0 ≠ witness.P 0*holonomy witness.U 0 ∧
  holonomy witness.U 3 ≠ 1 ∧ holonomy (tick witness).U 3=1 ∧ Gauss (tick witness) ∧
  (¬ ∃ h, gauge h witness=tick witness) ∧ kick false witness ≠ witness ∧
  (¬ Gauss (partialKick witness)) ∧
  wrongDefect witness=1 ∧ wrongDefect (kick false witness) ≠ 1 ∧
  (∀ (G : Type) [Group G] (U P Q k : G),
    U⁻¹*Q⁻¹*U=k*(U⁻¹*P⁻¹*U) ↔ Q=P*U*k⁻¹*U⁻¹) ∧
  (∀ (G : Type) [Group G] (a : G),
    (∃ k, ∀ p : G, k*p=p*a) ↔ ∀ p : G, a*p=p*a) ∧
  (¬ ∃ k : S3, ∀ p : S3, k*p=p*rotation) ∧
  Gauss witness5 ∧
  holonomy witness5.U 0*witness5.P 0 ≠ witness5.P 0*holonomy witness5.U 0 ∧
  holonomy witness5.U 3 ≠ 1 ∧ holonomy (tick witness5).U 3=1

end Artform.Scores.ClassicalNonabelian.Statement
