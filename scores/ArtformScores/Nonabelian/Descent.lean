import ArtformScores.Nonabelian.Kernels
/-! # Exact descent to all eleven weighted orbit coordinates -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
open Finset

def rawInclusion : Matrix Raw (Fin 11) ℚ := fun x i => if orbitIndex x=i then 1 else 0
def orbitMatrix : Gate → Matrix (Fin 11) (Fin 11) ℚ
  | .electric e => fun i j => (electricNumerator e i j : ℚ)/3
  | .curvature active => Matrix.diagonal (fun i => if active then (orbitSign i : ℚ) else 1)

lemma gate_intertwiner : ∀ g : Gate, gateMatrix g*rawInclusion=rawInclusion*orbitMatrix g := by
  intro g
  cases g <;> rename_i b <;> cases b <;> decide +kernel

def compileOrbit : List Gate → Matrix (Fin 11) (Fin 11) ℚ
  | [] => 1
  | g::w => compileOrbit w*orbitMatrix g
lemma compile_intertwiner (w : List Gate) : compile w*rawInclusion=rawInclusion*compileOrbit w := by
  induction w with
  | nil => simp [compile,compileOrbit]
  | cons g w ih =>
    simp only [compile,compileOrbit]
    rw [Matrix.mul_assoc,gate_intertwiner,← Matrix.mul_assoc,ih,Matrix.mul_assoc]

lemma inclusion_gram : rawInclusion.transpose*rawInclusion=
    Matrix.diagonal (fun i => (orbitWeight i : ℚ)) := by decide +kernel

lemma compileOrbit_weighted (w : List Gate) :
    (compileOrbit w).transpose * Matrix.diagonal (fun i => (orbitWeight i : ℚ)) * compileOrbit w=
      Matrix.diagonal (fun i => (orbitWeight i : ℚ)) := by
  rw [← inclusion_gram]
  calc
    _ = (rawInclusion*compileOrbit w).transpose*(rawInclusion*compileOrbit w) := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = (compile w*rawInclusion).transpose*(compile w*rawInclusion) := by rw [compile_intertwiner]
    _ = rawInclusion.transpose*rawInclusion := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (compile w).transpose,compile_orthogonal,Matrix.one_mul]

end Artform.Scores.Nonabelian
