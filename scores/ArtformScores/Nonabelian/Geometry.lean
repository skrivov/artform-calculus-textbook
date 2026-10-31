import Mathlib
import ArtformTextbook.Ch03.Defs.Canvas
import ArtformTextbook.Ch05.Defs.Steps

/-! # The S3 connection on the one-vertex commutator torus -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
open Artform
abbrev G := Equiv.Perm (Fin 3)
abbrev Raw := G × G

def elements : Fin 6 → G :=
  ![1,Equiv.swap 0 1,Equiv.swap 0 2,Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2,Equiv.swap 1 2 * Equiv.swap 0 1]
def elementIndex (g : G) : Fin 6 :=
  if g=elements 0 then 0 else if g=elements 1 then 1 else if g=elements 2 then 2 else
    if g=elements 3 then 3 else if g=elements 4 then 4 else 5
lemma element_left : ∀ i, elementIndex (elements i)=i := by decide +kernel
lemma element_right : ∀ g, elements (elementIndex g)=g := by decide +kernel
def elementEquiv : Fin 6 ≃ G := ⟨elements,elementIndex,element_left,element_right⟩
def rawEquiv : Fin 36 ≃ Raw :=
  (finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin 36).symm.trans (elementEquiv.prodCongr elementEquiv)

abbrev torus : Canvas where
  V := Unit
  E := Fin 2
  F := Unit
  src _ := ()
  tgt _ := ()
  boundary _ := [(0,true),(1,true),(0,false),(1,false)]
  closed _ := by unfold IsClosedWalk; decide
abbrev frame : Presentation := ⟨torus.E,fun _ => G⟩
def table (x : Raw) : frame.Table := ![x.1,x.2]
def pair (x : frame.Table) : Raw := (x 0,x 1)
@[simp] lemma pair_table (x : Raw) : pair (table x)=x := rfl
@[simp] lemma table_pair (x : frame.Table) : table (pair x)=x := by
  funext i; fin_cases i <;> rfl

def conjugate (h g : G) : G := h*g*h⁻¹
def gauge (h : G) (x : Raw) : Raw := (conjugate h x.1,conjugate h x.2)
lemma gauge_one (x : Raw) : gauge 1 x=x := by simp [gauge,conjugate]
lemma gauge_mul (g h : G) (x : Raw) : gauge (g*h) x=gauge g (gauge h x) := by
  apply Prod.ext <;> simp [gauge,conjugate,mul_assoc]
def gaugeEquiv (h : G) : Raw ≃ Raw where
  toFun := gauge h
  invFun := gauge h⁻¹
  left_inv x := by rw [← gauge_mul]; simp [gauge_one]
  right_inv x := by rw [← gauge_mul]; simp [gauge_one]

/-- Ordered product of the actual signed attaching-word occurrences. -/
def boundaryProduct (x : frame.Table) : G :=
  ((torus.boundary ()).map (fun st => if st.2 then x st.1 else (x st.1)⁻¹)).prod
def curvature (x : Raw) : G := boundaryProduct (table x)
lemma curvature_word (x : Raw) : curvature x=x.1*x.2*x.1⁻¹*x.2⁻¹ := by
  simp [curvature,boundaryProduct,table,mul_assoc]
lemma curvature_gauge (h : G) (x : Raw) : curvature (gauge h x)=conjugate h (curvature x) := by
  simp only [curvature_word,gauge,conjugate,mul_inv_rev,inv_inv]
  group
lemma curvature_flat (x : Raw) : curvature x=1 ↔ x.1*x.2=x.2*x.1 := by
  rw [curvature_word]
  constructor
  · intro h
    have he := congrArg (fun z => z*x.2*x.1) h
    simpa [mul_assoc] using he
  · intro h
    rw [h]
    group
lemma raw_card : Fintype.card Raw=36 := by decide +kernel
lemma group_card : Fintype.card G=6 := by decide +kernel
lemma nonflat_count : (Finset.univ.filter (fun x : Raw => curvature x ≠ 1)).card=18 := by
  decide +kernel

/-! ## Non-vacuity -/
example : curvature (elements 1,elements 2) ≠ 1 := by decide +kernel
example : ∀ e : torus.E, torus.inc e ()=0 := by decide +kernel
end Artform.Scores.Nonabelian
