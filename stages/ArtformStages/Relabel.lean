import ArtformStages.Pair

/-!
# Pair under a relabeling of cells

A table `P` with `Pᵀ P = 1`, from the cells `n` to the cells `m`, relabels the cells: a
bijection of cells with a sign on each cell is one such table. Pair commutes with it, and it keeps
the alternating pairing and the staggered energy. This is the step that identifies the cells of a
read board with the cells of a run, as astra's wave 39 in the research ledger on a layered
universe asks next, proved once for every such identification.

* `pair_conj` (RS1), `omega_conj` (RS2), `qstar_conj` (RS3).
-/

open Matrix

namespace Artform.Stages

section Relabel

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- A relabeling, applied to both parts of a state. -/
def relabel (P : Matrix m n R) (x : LightState R n) : LightState R m := (P *ᵥ x.1, P *ᵥ x.2)

theorem relabel_mulVec (P : Matrix m n R) (hP : Pᵀ * P = 1) (M : Matrix n n R) (v : n → R) :
    (P * M * Pᵀ) *ᵥ (P *ᵥ v) = P *ᵥ (M *ᵥ v) := by
  rw [mulVec_mulVec, Matrix.mul_assoc (P * M), hP, Matrix.mul_one, ← mulVec_mulVec]

theorem relabel_dotProduct (P : Matrix m n R) (hP : Pᵀ * P = 1) (v w : n → R) :
    (P *ᵥ v) ⬝ᵥ (P *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hP, one_mulVec]

/-- RS1. Pair commutes with a relabeling of cells. -/
theorem pair_conj (P : Matrix m n R) (hP : Pᵀ * P = 1) (S L : Matrix n n R)
    (x : LightState R n) :
    pair (P * S * Pᵀ) (P * L * Pᵀ) (relabel P x) = relabel P (pair S L x) := by
  obtain ⟨A, E⟩ := x
  simp only [relabel, pair]
  rw [relabel_mulVec P hP, ← mulVec_add, relabel_mulVec P hP, ← mulVec_sub]

/-- RS2. A relabeling of cells keeps the alternating pairing. -/
theorem omega_conj (P : Matrix m n R) (hP : Pᵀ * P = 1) (x y : LightState R n) :
    omega (relabel P x) (relabel P y) = omega x y := by
  simp only [omega, relabel, relabel_dotProduct P hP]

/-- RS3. A relabeling of cells keeps the staggered energy. -/
theorem qstar_conj (P : Matrix m n R) (hP : Pᵀ * P = 1) (S L : Matrix n n R)
    (x : LightState R n) :
    qstar (P * S * Pᵀ) (P * L * Pᵀ) (relabel P x) = qstar S L x := by
  obtain ⟨A, E⟩ := x
  simp only [qstar, relabel, relabel_mulVec P hP, relabel_dotProduct P hP]

end Relabel

end Artform.Stages
