import ArtformScores.GravityBridge.Phase

/-! # Algebraic positive states and explicit unital star pullback -/

namespace Artform.Scores.GravityBridge

noncomputable section

structure AlgebraicPositiveState (A : Type*) [Semiring A] [StarRing A] [Algebra ℂ A] where
  functional : A →ₗ[ℂ] ℂ
  normalized : functional 1 = 1
  positive : ∀ a, (functional (star a * a)).im = 0 ∧ 0 ≤ (functional (star a * a)).re

def AlgebraicPositiveState.pullback {A B : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] (s : AlgebraicPositiveState A) (f : B →⋆ₐ[ℂ] A) :
    AlgebraicPositiveState B where
  functional := s.functional.comp f.toAlgHom.toLinearMap
  normalized := by simpa using s.normalized
  positive b := by
    change (s.functional (f (star b * b))).im = 0 ∧ 0 ≤ (s.functional (f (star b * b))).re
    rw [map_mul, map_star]
    exact s.positive (f b)

def zeroVectorState : AlgebraicPositiveState (Matrix (Fin 2) (Fin 2) ℂ) where
  functional :=
    { toFun := fun A => A 0 0
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  normalized := rfl
  positive A := by
    change ((A.conjTranspose * A) 0 0).im = 0 ∧ 0 ≤ ((A.conjTranspose * A) 0 0).re
    constructor
    · norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.mul_re,
        Complex.mul_im, Complex.star_def]
      ring
    · norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.mul_re,
        Complex.mul_im, Complex.star_def]
      nlinarith [sq_nonneg (A 0 0).re, sq_nonneg (A 0 0).im,
        sq_nonneg (A 1 0).re, sq_nonneg (A 1 0).im]

def binarySwapUnitary : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨binaryX, by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [binaryX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]⟩

def binarySwapAut : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Unitary.conjStarAlgAut ℂ _ binarySwapUnitary).toStarAlgHom

end

end Artform.Scores.GravityBridge
