import ArtformScores.NonabelianGravity.QuantumSliceData

/-! # The fixed native slice represents all original admitted histories -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination Legendre BoundaryHistory
open Artform.Scores.GravityBridge.Native.Full40

abbrev Whole := Vector 2
abbrev Reduced := SliceIndex → ℚ

def restrict (q : Whole) : Reduced := fun i => q (nativeCoordinate i)
def embed (y : Reduced) : Whole := fun k => ∑ i, if nativeCoordinate i = k then y i else 0

def gaugeParameter (q : Whole) : Biv ℚ :=
  ![q (1, 1), q (1, 2), q (1, 3), q (1, 11), -q (1, 7), q (1, 6)]
def gauge (w : Biv ℚ) : Whole := fun k => if k.1 = 0 then gaugeFirst w k.2 else gaugeSecond w k.2

def project (q : Whole) : Whole := fun k => activeProjector.mulVec (row q k.1) k.2

def normalize (q : Whole) : Whole := project (q - gauge (gaugeParameter q))

lemma project_entry (q : Whole) (k : Index 2) : project q k =
    if k.2 ≠ 0 ∧ k.2 ≠ 4 ∧ k.2 ≠ 8 ∧ k.2 ≠ 12 then q k else 0 := by
  rcases k with ⟨t, i⟩
  fin_cases i <;> norm_num [project, activeProjector, row, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

def selected (k : Index 2) : Prop :=
  k.2 ≠ 0 ∧ k.2 ≠ 4 ∧ k.2 ≠ 8 ∧ k.2 ≠ 12 ∧
    (k.1 = 0 ∨ (k.2 ≠ 1 ∧ k.2 ≠ 2 ∧ k.2 ≠ 3 ∧ k.2 ≠ 6 ∧ k.2 ≠ 7 ∧ k.2 ≠ 11))

instance (k : Index 2) : Decidable (selected k) := by unfold selected; infer_instance

end Artform.Scores.NonabelianGravity.QuantumComposition
