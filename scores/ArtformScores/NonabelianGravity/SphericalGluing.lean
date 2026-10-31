import ArtformScores.NonabelianGravity.SphericalOrthant

/-! # Two orthants with complete face metrics and sector seam matrices

The source has opposite orientation and labels (3,2,1,4). The seam fixes
physical face tangents and reverses the transverse normal. Base/stem
transports use specified one-sided cell sectors, not a global smooth
connection at the singular edges or vertices of the doubled complex.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Orthant.Gluing
def sourceLabel : Fin 4 → Fin 4 := ![2,1,0,3]
lemma sourceLabel_inverse : ∀ v, sourceLabel (sourceLabel v)=v := by decide +kernel
def sourceVertex (v : Fin 4) : V4 := vertex (sourceLabel v)
lemma paired_vertices : ∀ v, sourceVertex (sourceLabel v)=vertex v := by decide +kernel
lemma face_pairing : ∀ f v, v≠f → sourceLabel v ≠ sourceLabel f := by decide +kernel
def targetFaceGram (f : Fin 4) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => dot4 (vertex (f.succAbove i)) (vertex (f.succAbove j))
def sourceFaceGram (f : Fin 4) : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  dot4 (sourceVertex (sourceLabel (f.succAbove i)))
    (sourceVertex (sourceLabel (f.succAbove j)))
lemma face_metrics : ∀ f, targetFaceGram f=1 ∧ sourceFaceGram f=targetFaceGram f := by
  decide +kernel

/-- Coordinate reflection across the whole totally geodesic face. -/
def seam (f : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal (fun i => if i=f then -1 else 1)
lemma seam_tangents (f : Fin 4) (x : V4) (hx : x f = 0) : (seam f).mulVec x=x := by
  funext i
  by_cases hi : i=f
  · subst i
    simp [seam,hx,Matrix.mulVec,dotProduct,Matrix.diagonal]
  · simp [seam,hi,Matrix.mulVec,dotProduct,Matrix.diagonal]
lemma seam_normal : ∀ f, (seam f).mulVec (vertex f)= -vertex f := by decide +kernel

/-- Source equation12 paths, after the odd vertex-label permutation. -/
def sourceEdge (t s : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  edge (sourceLabel t) (sourceLabel s)
def sourceLoop : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![sourceEdge 3 2*sourceEdge 2 1*sourceEdge 1 3,
    sourceEdge 3 0*sourceEdge 0 2*sourceEdge 2 3,
    sourceEdge 3 1*sourceEdge 1 0*sourceEdge 0 3,
    sourceEdge 3 1*sourceEdge 1 2*sourceEdge 2 0*sourceEdge 0 1*sourceEdge 1 3]
lemma source_loop_inverse : ∀ f, sourceLoop f=(loop (sourceLabel f)).transpose := by
  decide +kernel

/-- The fourth face uses the same specified edge24 stem in both cells. -/
def basedSeam (f : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  if f=3 then edge 3 1*seam 3*edge 1 3 else seam f
def linkRotation : Fin 4 → Matrix (Fin 3) (Fin 3) ℚ :=
  ![!![1,0,0;0,-1,0;0,0,-1],!![-1,0,0;0,1,0;0,0,-1],
    !![-1,0,0;0,-1,0;0,0,1],!![-1,0,0;0,1,0;0,0,-1]]
lemma based_seam_frame : ∀ (f : Fin 4) (i j : Fin 3),
    -(basedSeam f i.castSucc j.castSucc)=linkRotation f i j := by
  intro f i j
  fin_cases f <;> fin_cases i <;> fin_cases j <;> decide +kernel
lemma based_seam_base : ∀ f, (basedSeam f).mulVec (vertex 3)=vertex 3 := by decide +kernel
lemma link_rotation_orthogonal : ∀ f,
    (linkRotation f).transpose*linkRotation f=1 ∧ (linkRotation f).det=1 := by decide +kernel

/-! ## Non-vacuity -/
example : targetFaceGram 0=sourceFaceGram 0 := (face_metrics 0).2.symm
end Artform.Scores.NonabelianGravity.Orthant.Gluing
