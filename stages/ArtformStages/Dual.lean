import Mathlib

/-!
# The window of Pair, read on the squares

Finding 427 of the research ledger on a layered universe reads the window of Pair on the lines:
every orbit off the level 0 is bounded exactly when `4 Λ⁻¹ - Cᵀ K C` is positive definite. The
two Schur complements of one block table show that the same window can be read on the squares,
as `4 K⁻¹ - C Λ Cᵀ`, a table of half the size: with `A = 2 K⁻¹`, `D = 2 Λ⁻¹` and `B = C` the
theorem below is that statement for the closed window, and the window is symmetric under the
exchange of the squares and `K` with the lines and `Λ`.

* `window_dual` (WD1), from Mathlib's `Matrix.PosDef.fromBlocks₁₁` and `fromBlocks₂₂`.
-/

open Matrix

namespace Artform.Stages

section Dual

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- WD1. For positive definite `A` and `D`, `D - Bᴴ A⁻¹ B` is positive semidefinite exactly when
`A - B D⁻¹ Bᴴ` is: both say that the block table `[[A, B], [Bᴴ, D]]` is. -/
theorem window_dual {A : Matrix m m R} {D : Matrix n n R} (B : Matrix m n R) (hA : A.PosDef)
    (hD : D.PosDef) [Invertible A] [Invertible D] :
    (D - Bᴴ * A⁻¹ * B).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef :=
  (PosDef.fromBlocks₁₁ B D hA).symm.trans (PosDef.fromBlocks₂₂ A B hD)

end Dual

end Artform.Stages
