import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! # Finite geometric data for the spherical orthant

Vertices are the four coordinate unit vectors. The ambient matrices below
are quarter-circle transports on the unit sphere: rotate the source/target
plane and fix its orthogonal complement. Their interpretation as actual
Levi-Civita transports is explained analytically in DIPOLE-RESULTS.md;
this file checks the finite matrices, simple paths and transported Gram.
The tangent frame at vertex4 is `(-e1,-e2,-e3)`.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Orthant

abbrev V4 := Fin 4 → ℚ
abbrev V3 := Fin 3 → ℚ
def vertex (v : Fin 4) : V4 := fun i => if i=v then 1 else 0
def dot4 (x y : V4) : ℚ := ∑ i, x i*y i
def vertexGram : Matrix (Fin 4) (Fin 4) ℚ := fun i j => dot4 (vertex i) (vertex j)
lemma vertexGram_identity : vertexGram=1 := by decide +kernel
lemma vertexGram_nondegenerate : vertexGram.det=1 := by rw [vertexGram_identity,Matrix.det_one]
def interior : V4 := fun _ => 1/2
lemma interior_admitted : dot4 interior interior=1 ∧ ∀ i, 0 < interior i := by decide +kernel

/-- `edge t s` transports from vertex s to vertex t. -/
def edge (t s : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  if i=t ∧ j=s then 1 else if i=s ∧ j=t then -1
  else if i=j ∧ i≠s ∧ i≠t then 1 else 0
lemma edge_inverse : ∀ s t, s≠t → edge s t*edge t s=1 := by decide +kernel
lemma edge_endpoint : ∀ s t, s≠t → (edge t s).mulVec (vertex s)=vertex t := by decide +kernel

/-- HHR equation12, with zero-based labels and special edge(24). -/
def loop : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![edge 3 2*edge 2 1*edge 1 3,
    edge 3 0*edge 0 2*edge 2 3,
    edge 3 1*edge 1 0*edge 0 3,
    edge 3 1*edge 1 2*edge 2 0*edge 0 1*edge 1 3]
def rotation : Fin 4 → Matrix (Fin 3) (Fin 3) ℚ :=
  ![!![1,0,0;0,0,-1;0,1,0],!![0,0,1;0,1,0;-1,0,0],
    !![0,-1,0;1,0,0;0,0,1],!![0,0,-1;0,1,0;1,0,0]]
lemma loop_restriction : ∀ (f : Fin 4) (i j : Fin 3),
    loop f i.castSucc j.castSucc=rotation f i j := by
  intro f i j
  fin_cases f <;> fin_cases i <;> fin_cases j <;> decide +kernel
lemma loop_base : ∀ f, (loop f).mulVec (vertex 3)=vertex 3 := by decide +kernel
lemma loop_closure : loop 3*loop 2*loop 1*loop 0=1 := by decide +kernel
lemma rotation_special_orthogonal : ∀ f,
    (rotation f).transpose*rotation f=1 ∧ (rotation f).det=1 := by decide +kernel

def normal : Fin 4 → V3 := ![![1,0,0],![0,1,0],![0,0,1],![0,-1,0]]
def dot3 (x y : V3) : ℚ := ∑ i, x i*y i
def cross (x y : V3) : V3 :=
  ![x 1*y 2-x 2*y 1,x 2*y 0-x 0*y 2,x 0*y 1-x 1*y 0]
/-- The exceptional pair24 must be compared after the face1 transport. -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  if (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) then
    dot3 (normal 1) ((rotation 0).mulVec (normal 3))
  else dot3 (normal i) (normal j)
def convexity : Fin 4 → ℚ :=
  ![dot3 (cross (normal 0) (normal 1)) (normal 2),
    dot3 (cross (normal 0) (normal 2)) (normal 3),
    dot3 (cross (normal 1) (normal 0)) ((rotation 0).mulVec (normal 3)),
    dot3 (cross (normal 2) (normal 1)) ((rotation 2).transpose.mulVec (normal 3))]
lemma gram_identity : gram=1 := by decide +kernel
lemma gram_nondegenerate : gram.det=1 := by rw [gram_identity,Matrix.det_one]
lemma convexity_positive : ∀ i, convexity i=1 := by decide +kernel
lemma untransported_gram_singular :
    Matrix.det (fun i j => dot3 (normal i) (normal j))=0 := by
  decide +kernel

/-! ## Non-vacuity -/
example : vertexGram.det ≠ 0 ∧ gram.det ≠ 0 := by
  rw [vertexGram_nondegenerate,gram_nondegenerate]
  norm_num
end Artform.Scores.NonabelianGravity.Orthant
