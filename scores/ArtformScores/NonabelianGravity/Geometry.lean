import ArtformScores.ClassicalNonabelian.Controls

/-! # NGB: an actual two-face canvas with opposite shared-edge orientations -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Artform

abbrev canvas : Canvas where
  V := Fin 6
  E := Fin 7
  F := Fin 2
  src := ![0,1,4,3,1,2,5]
  tgt := ![1,4,3,0,2,5,4]
  boundary f := if f=0 then [(0,true),(1,true),(2,true),(3,true)]
    else [(4,true),(5,true),(6,true),(1,false)]
  closed f := by fin_cases f <;> unfold IsClosedWalk <;> decide

@[ext] structure State (G : Type) where
  U : canvas.E → G
  P : canvas.E → G

variable {G : Type} [Group G]
def gauge (h : canvas.V → G) (s : State G) : State G :=
  ⟨fun e => h (canvas.tgt e)*s.U e*(h (canvas.src e))⁻¹,
    fun e => h (canvas.tgt e)*s.P e*(h (canvas.tgt e))⁻¹⟩
lemma gauge_one (s : State G) : gauge 1 s=s := by
  apply State.ext <;> funext e <;> simp [gauge]
lemma gauge_mul (h k : canvas.V → G) (s : State G) :
    gauge (h*k) s=gauge h (gauge k s) := by
  apply State.ext <;> funext e <;> simp [gauge,mul_assoc]
def outgoing (s : State G) (e : canvas.E) : G := (s.U e)⁻¹*(s.P e)⁻¹*s.U e
def star : canvas.V → List (canvas.E × Bool) :=
  ![[(0,false),(3,true)],[(4,false),(1,false),(0,true)],
    [(5,false),(4,true)],[(3,false),(2,true)],
    [(2,false),(1,true),(6,true)],[(6,false),(5,true)]]
def endpoint (a : canvas.E × Bool) : canvas.V :=
  if a.2 then canvas.tgt a.1 else canvas.src a.1
lemma star_complete : ∀ v a, a ∈ star v ↔ endpoint a=v := by decide +kernel
lemma star_nodup : ∀ v, (star v).Nodup := by decide +kernel
def defect (s : State G) : canvas.V → G :=
  ![outgoing s 0*s.P 3,outgoing s 4*outgoing s 1*s.P 0,
    outgoing s 5*s.P 4,outgoing s 3*s.P 2,
    outgoing s 2*s.P 1*s.P 6,outgoing s 6*s.P 5]
lemma defect_star (s : State G) (v : canvas.V) : defect s v=
    ((star v).map (fun a => if a.2 then s.P a.1 else outgoing s a.1)).prod := by
  fin_cases v <;> simp [defect,star,mul_assoc]
def Gauss (s : State G) : Prop := defect s=1
lemma defect_gauge (h : canvas.V → G) (s : State G) (v : canvas.V) :
    defect (gauge h s) v=h v*defect s v*(h v)⁻¹ := by
  fin_cases v <;> simp [defect,outgoing,gauge,canvas,mul_assoc]
lemma gauss_gauge (h : canvas.V → G) (s : State G) : Gauss (gauge h s) ↔ Gauss s := by
  simp only [Gauss,funext_iff,Pi.one_apply,defect_gauge]
  constructor
  · intro hh v
    have he := congrArg (fun z => (h v)⁻¹*z*h v) (hh v)
    simpa [mul_assoc] using he
  · intro hh v
    simp [hh v]

/-- Position in the actual signed face boundary; the loop ends at that step's target. -/
def basedLoop (f : canvas.F) (i : Fin 4) : List (canvas.E × Bool) :=
  (canvas.boundary f).rotate (i.val+1)
def holonomy (U : canvas.E → G) (f : canvas.F) (i : Fin 4) : G :=
  ((basedLoop f i).map (fun a => if a.2 then U a.1 else (U a.1)⁻¹)).reverse.prod
lemma holonomy_left (U : canvas.E → G) : holonomy U 0=
    ![U 0*U 3*U 2*U 1,U 1*U 0*U 3*U 2,
      U 2*U 1*U 0*U 3,U 3*U 2*U 1*U 0] := by
  funext i
  fin_cases i <;> simp [holonomy,basedLoop,canvas,List.rotate,mul_assoc]
lemma holonomy_right (U : canvas.E → G) : holonomy U 1=
    ![U 4*(U 1)⁻¹*U 6*U 5,U 5*U 4*(U 1)⁻¹*U 6,
      U 6*U 5*U 4*(U 1)⁻¹,(U 1)⁻¹*U 6*U 5*U 4] := by
  funext i
  fin_cases i <;> simp [holonomy,basedLoop,canvas,List.rotate,mul_assoc]
def stepTarget (f : canvas.F) : Fin 4 → canvas.V :=
  if f=0 then ![1,4,3,0] else ![2,5,4,1]
lemma holonomy_gauge (h : canvas.V → G) (s : State G) (f : canvas.F) (i : Fin 4) :
    holonomy (gauge h s).U f i=
      h (stepTarget f i)*holonomy s.U f i*(h (stepTarget f i))⁻¹ := by
  fin_cases f <;> fin_cases i <;>
    simp [holonomy,basedLoop,canvas,List.rotate,gauge,stepTarget,mul_assoc]

/-! ## Non-vacuity -/
example (U : canvas.E → G) : Gauss (State.mk U 1) := by
  unfold Gauss
  funext v
  fin_cases v <;> simp [defect,outgoing]
end Artform.Scores.NonabelianGravity
