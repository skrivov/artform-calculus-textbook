import ArtformScores.NonabelianGravity.BoundaryHistoryKernel
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Exact rational symmetric-congruence certificates, including singular forms -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Certificate (H : Matrix ι ι ℚ) where
  forward : Matrix ι ι ℚ
  backward : Matrix ι ι ℚ
  diagonal : ι → ℚ
  left_inverse : backward * forward = 1
  right_inverse : forward * backward = 1
  congruence : forward.transpose * H * forward = Matrix.diagonal diagonal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
-- Reindex the orthogonal basis and bind its full congruence and both inverse matrices.
lemma certificate_exists (H : Matrix ι ι ℚ) (hH : H.IsSymm) : Nonempty (Certificate H) := by
  classical
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hB : H.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hH
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hB)
  let std := Pi.basisFun ℚ ι
  let e := v.indexEquiv std
  let b : Module.Basis ι ℚ (ι → ℚ) := v.reindex e
  have hb : ∀ i j, i ≠ j → H.toBilin' (b i) (b j) = 0 := by
    intro i j hij
    rw [show b i = v (e.symm i) from v.reindex_apply e i,
      show b j = v (e.symm j) from v.reindex_apply e j]
    exact @hv (e.symm i) (e.symm j) (e.symm.injective.ne hij)
  refine ⟨⟨std.toMatrix b, b.toMatrix std, fun i => H.toBilin' (b i) (b i),
    b.toMatrix_mul_toMatrix_flip std, std.toMatrix_mul_toMatrix_flip b, ?_⟩⟩
  have hm : (std.toMatrix b).transpose * H * std.toMatrix b = H.toBilin'.toMatrix b := by
    simpa [std, LinearMap.BilinForm.toMatrix_basisFun] using
      (H.toBilin').toMatrix_mul_basis_toMatrix std b
  rw [hm]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [LinearMap.BilinForm.toMatrix_apply, hij, hb i j hij]

end Artform.Scores.NonabelianGravity.HistoryElimination
