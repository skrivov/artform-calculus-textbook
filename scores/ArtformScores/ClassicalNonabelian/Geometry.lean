import Mathlib
import ArtformTextbook.Ch03.Defs.Canvas

/-! # A plaquette with a spectator edge and an ordered group-valued Gauss defect -/
set_option autoImplicit false
namespace Artform.Scores.ClassicalNonabelian
open Artform

/-- The running square, with an extra edge from vertex0 to vertex2. -/
abbrev canvas : Canvas where
  V := Fin 4
  E := Fin 5
  F := Fin 1
  src := ![0,1,2,3,0]
  tgt := ![1,2,3,0,2]
  boundary _ := [(0,true),(1,true),(2,true),(3,true)]
  closed _ := by unfold IsClosedWalk; decide

@[ext] structure State (G : Type) where
  U : canvas.E → G
  P : canvas.E → G

variable {G : Type} [Group G]

/-- Every impulse is based at its stored edge's target vertex. -/
def gauge (h : canvas.V → G) (s : State G) : State G :=
  ⟨fun e => h (canvas.tgt e)*s.U e*(h (canvas.src e))⁻¹,
    fun e => h (canvas.tgt e)*s.P e*(h (canvas.tgt e))⁻¹⟩
lemma gauge_one (s : State G) : gauge 1 s=s := by
  apply State.ext <;> funext e <;> simp [gauge]
lemma gauge_mul (h k : canvas.V → G) (s : State G) :
    gauge (h*k) s=gauge h (gauge k s) := by
  apply State.ext <;> funext e <;> simp [gauge,mul_assoc]

/-- Source-based outgoing flux; target-based incoming flux is `P e`. -/
def outgoing (s : State G) (e : canvas.E) : G := (s.U e)⁻¹*(s.P e)⁻¹*s.U e

/-- The displayed star order is extra local data; multiplication is not commuted. -/
def defect (s : State G) : canvas.V → G :=
  ![outgoing s 0*s.P 3*outgoing s 4,
    outgoing s 1*s.P 0,
    outgoing s 2*s.P 1*s.P 4,
    outgoing s 3*s.P 2]
/-- Every incident half-edge occurs once; its cyclic order is a declared convention. -/
def star : canvas.V → List (canvas.E × Bool) :=
  ![[(0,false),(3,true),(4,false)],[(1,false),(0,true)],
    [(2,false),(1,true),(4,true)],[(3,false),(2,true)]]
def endpoint (a : canvas.E × Bool) : canvas.V :=
  if a.2 then canvas.tgt a.1 else canvas.src a.1
lemma star_complete : ∀ v a, a ∈ star v ↔ endpoint a=v := by decide +kernel
lemma star_nodup : ∀ v, (star v).Nodup := by decide +kernel
lemma defect_star (s : State G) (v : canvas.V) : defect s v=
    ((star v).map (fun a => if a.2 then s.P a.1 else outgoing s a.1)).prod := by
  fin_cases v <;> simp [defect,star,mul_assoc]
def Gauss (s : State G) : Prop := defect s=1
lemma outgoing_gauge (h : canvas.V → G) (s : State G) (e : canvas.E) :
    outgoing (gauge h s) e=h (canvas.src e)*outgoing s e*(h (canvas.src e))⁻¹ := by
  simp only [outgoing,gauge]
  group
lemma defect_gauge (h : canvas.V → G) (s : State G) (v : canvas.V) :
    defect (gauge h s) v=h v*defect s v*(h v)⁻¹ := by
  fin_cases v <;> simp [defect,outgoing,gauge,canvas,mul_assoc]
lemma gauss_gauge (h : canvas.V → G) (s : State G) : Gauss (gauge h s) ↔ Gauss s := by
  simp only [Gauss,funext_iff,Pi.one_apply,defect_gauge]
  constructor
  · intro hh v
    have hv := hh v
    have he := congrArg (fun z => (h v)⁻¹*z*h v) hv
    simpa [mul_assoc] using he
  · intro hh v
    simp [hh v]

/-- Rotate the actual boundary to start and end at the target of edge e.
The spectator edge has no face kick and is assigned the empty word. -/
def basedLoop (e : canvas.E) : List (canvas.E × Bool) :=
  if e=4 then [] else (canvas.boundary 0).rotate (e.val+1)
def holonomy (U : canvas.E → G) (e : canvas.E) : G :=
  ((basedLoop e).map (fun st => if st.2 then U st.1 else (U st.1)⁻¹)).reverse.prod
lemma holonomy_word (U : canvas.E → G) : holonomy U=
    ![U 0*U 3*U 2*U 1,U 1*U 0*U 3*U 2,
      U 2*U 1*U 0*U 3,U 3*U 2*U 1*U 0,1] := by
  funext e
  fin_cases e <;> simp [holonomy,basedLoop,canvas,List.rotate,mul_assoc]
lemma holonomy_spectator (U : canvas.E → G) : holonomy U 4=1 := by rw [holonomy_word]; rfl

def previous : canvas.E → canvas.E := ![3,0,1,2,4]
lemma holonomy_transport (U : canvas.E → G) (e : canvas.E) :
    (U e)⁻¹*holonomy U e*U e=holonomy U (previous e) := by
  rw [holonomy_word]
  fin_cases e <;> simp [previous] <;> group
lemma holonomy_gauge (h : canvas.V → G) (s : State G) (e : canvas.E) :
    holonomy (gauge h s).U e=h (canvas.tgt e)*holonomy s.U e*(h (canvas.tgt e))⁻¹ := by
  rw [holonomy_word,holonomy_word]
  fin_cases e <;> simp [gauge,canvas,mul_assoc]

lemma cyclic_gauss (l : List G) (n : ℕ) : (l.rotate n).prod=1 ↔ l.prod=1 := by
  cases l with
  | nil => simp
  | cons a l =>
    have hn : n % (a::l).length ≤ (a::l).length :=
      le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.rotate_mod,List.rotate_eq_drop_append_take hn,List.prod_append]
    have hprod : (a::l).prod=((a::l).take (n%(a::l).length)).prod*
        ((a::l).drop (n%(a::l).length)).prod := by rw [← List.prod_append,List.take_append_drop]
    rw [hprod]
    exact mul_eq_one_comm

/-! ## Non-vacuity -/
example : canvas.src 4=0 ∧ canvas.tgt 4=2 := ⟨rfl,rfl⟩
example : (canvas.boundary 0).length=4 := rfl
end Artform.Scores.ClassicalNonabelian
