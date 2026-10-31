import ArtformScores.GravityBridge.SourceStatements
import ArtformScores.GravityBridge.Memory

/-! # Finite source responses and a same-spectrum separating experiment -/

namespace Artform.Scores.GravityBridge

open Finset Polynomial
variable {K X Y J : Type*} [Semiring K] [AddCommMonoid X] [AddCommMonoid Y]
  [AddCommMonoid J] [Module K X] [Module K Y] [Module K J]

lemma source_amplitude_of_recurrence (O : X →ₗ[K] Y) (T : X →ₗ[K] X) (B : J →ₗ[K] X)
    (x : ℕ → X) (u : ℕ → J) (h0 : x 0 = 0)
    (hx : ∀ n, x (n + 1) = T (x n) + B (u n)) (n : ℕ) :
    O (x n) = sourceAmplitude O T B n u := by
  have hz : ∀ n, x (n + 1) = B (u n) + T (x n) := by intro n; rw [hx, add_comm]
  rw [forced_memory T (fun j => B (u j)) x hz n, h0]
  simp [sourceAmplitude, impulseResponse]

lemma source_amplitude_impulse (O : X →ₗ[K] Y) (T : X →ₗ[K] X) (B : J →ₗ[K] X)
    (n : ℕ) (j : J) :
    sourceAmplitude O T B (n + 1) (fun m => if m = 0 then j else 0) =
      impulseResponse O T B n j := by
  simp [sourceAmplitude, impulseResponse, apply_ite]

lemma source_response_iff {X' : Type*} [AddCommMonoid X'] [Module K X']
    (O1 : X →ₗ[K] Y) (O2 : X' →ₗ[K] Y) (T1 : X →ₗ[K] X) (T2 : X' →ₗ[K] X')
    (B1 : J →ₗ[K] X) (B2 : J →ₗ[K] X') :
    (∀ n j, impulseResponse O1 T1 B1 n j = impulseResponse O2 T2 B2 n j) ↔
      ∀ n u, sourceAmplitude O1 T1 B1 n u = sourceAmplitude O2 T2 B2 n u := by
  constructor
  · intro h n u
    apply sum_congr rfl
    intro j hj
    exact h _ _
  · intro h n j
    have he := h (n + 1) (fun m => if m = 0 then j else 0)
    simpa only [source_amplitude_impulse] using he

lemma source_shear_prepared (n : ℕ) (x : ℚ) : (sourceShear ^ n) (x, 0) = (x, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [sourceShear]

lemma source_shear_charpoly :
    (Step.move (1 : ℚ)).mat.charpoly = (1 : Matrix (Fin 2) (Fin 2) ℚ).charpoly := by
  norm_num [Matrix.charpoly_fin_two, Step.mat, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.det_fin_two, Polynomial.C_ofNat]

lemma source_shear_separates :
    impulseResponse visibleOutput sourceShear auxiliaryInput 1 1 = 1 ∧
    impulseResponse visibleOutput LinearMap.id auxiliaryInput 1 1 = 0 := by
  norm_num [impulseResponse, visibleOutput, sourceShear, auxiliaryInput]

/-- **GAC:source-response** (retain the permitted input and output channels). -/
@[ledger "GAC:source-response"]
theorem sourceResponse : Statement.sourceResponse := by
  refine ⟨?_, ?_, source_shear_charpoly, source_shear_prepared,
    source_shear_separates.1, source_shear_separates.2⟩
  · intro K X Y J _ _ _ _ _ _ _ O T B x u h0 hx n
    exact source_amplitude_of_recurrence O T B x u h0 hx n
  · intro K X X' Y J _ _ _ _ _ _ _ _ _ O1 O2 T1 T2 B1 B2
    exact source_response_iff O1 O2 T1 T2 B1 B2

/-! ## Non-vacuity -/

example (p : ℚ × ℚ) :
    Matrix.mulVec ((realize [Step.move (1 : ℚ)]) : Matrix (Fin 2) (Fin 2) ℚ) ![p.1, p.2] =
      ![(sourceShear p).1, (sourceShear p).2] := by
  ext i
  fin_cases i <;> simp [realize, Step.mat, sourceShear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example :
    sourceAmplitude visibleOutput sourceShear auxiliaryInput 2
      (fun m => if m = 0 then 1 else 0) = 1 ∧
    sourceAmplitude visibleOutput LinearMap.id auxiliaryInput 2
      (fun m => if m = 0 then 1 else 0) = 0 := by
  simpa only [source_amplitude_impulse] using source_shear_separates

end Artform.Scores.GravityBridge
