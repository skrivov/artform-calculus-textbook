import ArtformScores.NonabelianGravity.Geometry

/-! # The four-edge dipole and its first oriented digon

The dipole is a known graph used for two tetrahedra. Here it is an actual
Canvas with complete ordered stars. No geometric reconstruction is hidden
in its carrier. Only the first digon is evolved in this diagnostic.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Dipole
open Artform

abbrev canvas : Canvas where
  V := Fin 2
  E := Fin 4
  F := Fin 3
  src _ := 0
  tgt _ := 1
  boundary f := [(f.castSucc,true),(f.succ,false)]
  closed f := by simp [IsClosedWalk,stepStart,stepEnd]

@[ext] structure State (G : Type) where
  U : canvas.E → G
  P : canvas.E → G

def star : canvas.V → List (canvas.E × Bool) :=
  ![[(0,false),(1,false),(2,false),(3,false)],
    [(3,true),(2,true),(1,true),(0,true)]]
def endpoint (a : canvas.E × Bool) : canvas.V := if a.2 then 1 else 0
lemma star_complete : ∀ v a, a ∈ star v ↔ endpoint a=v := by decide +kernel
lemma star_nodup : ∀ v, (star v).Nodup := by decide +kernel
lemma star_valence : ∀ v, (star v).length=4 := by decide +kernel

variable {G : Type} [Group G]
def outgoing (s : State G) (e : canvas.E) : G := (s.U e)⁻¹*(s.P e)⁻¹*s.U e
def defect (s : State G) : canvas.V → G :=
  ![outgoing s 0*outgoing s 1*outgoing s 2*outgoing s 3,
    s.P 3*s.P 2*s.P 1*s.P 0]
lemma defect_star (s : State G) (v : canvas.V) : defect s v=
    ((star v).map (fun a => if a.2 then s.P a.1 else outgoing s a.1)).prod := by
  fin_cases v <;> simp [defect,star,mul_assoc]
def Gauss (s : State G) : Prop := defect s=1
def gauge (h : canvas.V → G) (s : State G) : State G :=
  ⟨fun e => h 1*s.U e*(h 0)⁻¹,fun e => h 1*s.P e*(h 1)⁻¹⟩
lemma defect_gauge (h : canvas.V → G) (s : State G) (v : canvas.V) :
    defect (gauge h s) v=h v*defect s v*(h v)⁻¹ := by
  fin_cases v <;> simp [defect,outgoing,gauge,mul_assoc]

/-- Holonomy based at the positive traversal's target of the first digon. -/
def holonomy (s : State G) : G := s.U 0*(s.U 1)⁻¹
lemma holonomy_boundary (s : State G) : holonomy s=
    (((canvas.boundary 0).rotate 1).map
      (fun a => if a.2 then s.U a.1 else (s.U a.1)⁻¹)).reverse.prod := by
  simp [holonomy,canvas,List.rotate]
def factor (backward : Bool) (s : State G) : G :=
  if backward then (holonomy s)⁻¹ else holonomy s
def kick (backward : Bool) (s : State G) : State G :=
  ⟨s.U,![factor backward s*s.P 0,s.P 1*(factor backward s)⁻¹,s.P 2,s.P 3]⟩
lemma kick_inverse (backward : Bool) (s : State G) : kick (!backward) (kick backward s)=s := by
  apply State.ext
  · rfl
  · funext e
    cases backward <;> fin_cases e <;> simp [kick,factor,holonomy,mul_assoc]
lemma kick_defect (backward : Bool) (s : State G) : defect (kick backward s)=defect s := by
  cases backward <;> funext v <;> fin_cases v <;>
    simp [defect,outgoing,kick,factor,holonomy] <;> group
lemma kick_gauss (backward : Bool) (s : State G) : Gauss (kick backward s) ↔ Gauss s := by
  simp only [Gauss,kick_defect]
lemma kick_gauge (backward : Bool) (h : canvas.V → G) (s : State G) :
    kick backward (gauge h s)=gauge h (kick backward s) := by
  apply State.ext
  · rfl
  · funext e
    cases backward <;> fin_cases e <;> simp [kick,factor,holonomy,gauge,mul_assoc]

/-! ## Non-vacuity -/
example (U : canvas.E → G) : Gauss (State.mk U 1) := by
  funext v
  fin_cases v <;> simp [defect,outgoing]
end Artform.Scores.NonabelianGravity.Dipole
