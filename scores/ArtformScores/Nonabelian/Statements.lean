import ArtformScores.Nonabelian.Process
import ArtformScores.Nonabelian.Probability
import ArtformScores.Meta.Ledger

/-! # Literal claims for the curvature-dependent S3 score -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Nonabelian.Statement
open Artform Finset

/-- **NQS:geometry** (the actual commutator torus). -/
@[ledger "NQS:geometry"]
def geometry : Prop :=
  torus.boundary ()=[(0,true),(1,true),(0,false),(1,false)] ∧
  Fintype.card G=6 ∧ Fintype.card Raw=36 ∧
  (∀ x, curvature x=x.1*x.2*x.1⁻¹*x.2⁻¹) ∧
  (∀ h x, curvature (gauge h x)=conjugate h (curvature x)) ∧
  (∀ x, curvature x=1 ↔ x.1*x.2=x.2*x.1) ∧
  (univ.filter (fun x : Raw => curvature x ≠ 1)).card=18 ∧
  curvature (elements 1,elements 2) ≠ 1 ∧ (∀ e : torus.E, torus.inc e ()=0)

/-- **NQS:legal-coherent** (selected legal batches, weights and native cadence). -/
@[ledger "NQS:legal-coherent"]
def legalCoherent : Prop :=
  (∀ e c (x : frame.Table), (replacement e c).guard x ∧
    (replacement e c).reads={edge e} ∧ (replacement e c).writes={edge e} ∧
    (replacement e c).apply x=Function.update x (edge e) c) ∧
  (∀ x : frame.Table, curvatureProfile.guard x ∧ curvatureProfile.reads=Set.univ ∧
    curvatureProfile.writes=∅ ∧ curvatureProfile.apply x=x) ∧
  (∀ e x c, coefficient (.electric e) x (some c)=
    1/3-if c=table x (edge e) then 1 else 0) ∧
  (∀ active x, coefficient (.curvature active) x (some ())=phaseSign active x) ∧
  (∀ e x, coefficient (.electric e) x none=0) ∧
  (∀ active x, coefficient (.curvature active) x none=0) ∧
  (∀ g x, Function.Injective (batch g x)) ∧
  (∀ e x b, Admitted (.electric e) x b ↔
    b.apps=[] ∨ ∃ c : G, b.apps=[⟨replacement e c,trivial⟩]) ∧
  (∀ active x b, Admitted (.curvature active) x b ↔
    b.apps=[] ∨ b.apps=[⟨curvatureProfile,trivial⟩]) ∧
  (∀ g x (r : Branch g), (batch g x r).apps.length ≤ 1) ∧
  (∀ g x y (r : Branch g),
    (∀ a ∈ (batch g (table x) r).apps, ∀ p ∈ a.profile.reads, table x p = table y p) →
      coefficient g x r=coefficient g y r) ∧
  (∀ g h x (r : Branch g),
    commit g (gauge h x) (transport g h r)=gauge h (commit g x r) ∧
    coefficient g (gauge h x) (transport g h r)=coefficient g x r) ∧
  (∀ g x y, branchKernel g y x=gateMatrix g y x) ∧
  (∀ active t x (r : (nativeRealizer active).alternatives t),
    (nativeLaw active).AllowsAt t ((nativeRealizer active).select t x r)) ∧
  (∀ active, (nativeLaw active).invariants=[] ∧ (nativeLaw active).score.period=3) ∧
  (∀ active, realizerKernel active 2*realizerKernel active 1*realizerKernel active 0=tick active) ∧
  (∀ active t, realizerKernel active (t+3)=realizerKernel active t) ∧
  (∀ active, realizerKernel active 5*realizerKernel active 4*realizerKernel active 3*
    realizerKernel active 2*realizerKernel active 1*realizerKernel active 0=
      compile (tickWord active++tickWord active)) ∧
  (∀ w x y, historyAmplitude w x y=compile w y x) ∧
  magnetic false=1 ∧
  (∀ active x, (batch (.curvature active) x (some ())).apps.length=1)

/-- **NQS:unitary-score** (raw words, reverse order and vacuum prefixes). -/
@[ledger "NQS:unitary-score"]
def unitaryScore : Prop :=
  (∀ u v, compile (u++v)=compile v*compile u) ∧
  (∀ g, (gateMatrix g).transpose=gateMatrix g ∧ gateMatrix g*gateMatrix g=1) ∧
  (∀ w, (toComplex (compile w)).conjTranspose*toComplex (compile w)=1 ∧
    toComplex (compile w)*(toComplex (compile w)).conjTranspose=1 ∧
    toComplex (compile w.reverse)=(toComplex (compile w)).conjTranspose ∧
    Covariant (toComplex (compile w)) ∧
    (∀ ψ, Vacuum ψ → Vacuum ((toComplex (compile w)).mulVec ψ)))

/-- **NQS:physical-carrier** (full quotient, Gram and normalized image). -/
@[ledger "NQS:physical-carrier"]
def physicalCarrier : Prop :=
  (∀ x y, orbitIndex x=orbitIndex y ↔ ∃ h, gauge h x=y) ∧
  (∀ i, orbitIndex (representative i)=i ∧
    (univ.filter (fun x => orbitIndex x=i)).card=orbitWeight i ∧ 0 < orbitWeight i) ∧
  Nonempty (Physical ≃ Fin 11) ∧ Fintype.card Physical=11 ∧
  rawInclusion.transpose*rawInclusion=Matrix.diagonal (fun i => (orbitWeight i : ℚ)) ∧
  inclusion.conjTranspose*inclusion=1 ∧
  (∀ ψ, Vacuum ψ ↔ ∃ v, inclusion.mulVec v=ψ) ∧
  gaugeProjector.conjTranspose=gaugeProjector ∧ gaugeProjector*gaugeProjector=gaugeProjector ∧
  (∀ ψ, gaugeProjector.mulVec ψ=ψ ↔ Vacuum ψ)

/-- **NQS:physical-descent** (full normalized intertwiner and declared field). -/
@[ledger "NQS:physical-descent"]
def physicalDescent : Prop :=
  (∀ i, normalizer i ∈ physicalScalars) ∧
  (∀ w, compile w*rawInclusion=rawInclusion*compileOrbit w ∧
    (compileOrbit w).transpose*Matrix.diagonal (fun i => (orbitWeight i : ℚ))*compileOrbit w=
      Matrix.diagonal (fun i => (orbitWeight i : ℚ)) ∧
    toComplex (compile w)*inclusion=inclusion*physicalCompile w ∧
    inclusion.conjTranspose*toComplex (compile w)*inclusion=physicalCompile w ∧
    (physicalCompile w).conjTranspose*physicalCompile w=1 ∧
    physicalCompile w*(physicalCompile w).conjTranspose=1 ∧
    physicalCompile w.reverse=(physicalCompile w).conjTranspose ∧
    (∀ i j, physicalCompile w i j ∈ physicalScalars))

/-- **NQS:two-tick-curvature** (normalized Born measurement with a witnessed control). -/
@[ledger "NQS:two-tick-curvature"]
def twoTickCurvature : Prop :=
  representative 1=(1,Equiv.swap 0 1) ∧ orbitWeight 1=3 ∧
  source=inclusion.mulVec (Pi.single 1 (1:ℂ)) ∧
  mass source=1 ∧ Vacuum source ∧ curvedMass source=0 ∧
  curvatureProjector.conjTranspose=curvatureProjector ∧
  curvatureProjector*curvatureProjector=curvatureProjector ∧ Covariant curvatureProjector ∧
  (∀ ψ, mass (curvatureProjector.mulVec ψ)=curvedMass ψ) ∧
  (∀ active, mass (evolved active)=1 ∧ Vacuum (evolved active) ∧
    probability (evolved active)=if active then (32:ℝ)/81 else 0) ∧
  evolved false=source

end Artform.Scores.Nonabelian.Statement
