import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import ArtformTextbook.Ch05.Defs.Gauge

/-!
# Class functions and Wilson loops (*Holonomy, and what survives a gauge change*)

Definition 5.24: a class function depends only on the conjugacy class; the
character `χ_ρ(g) = Tr ρ(g)` of a representation `ρ`, a homomorphism into the
invertible complex matrices, is one (`character_isClassFunction`). On a loop
`γ`, `χ_ρ(Hol_U(γ))` is a Wilson loop; on an open path, `ρ(Hol_U(γ))` is a
Wilson line.
-/

namespace Artform

variable {G : Type*} [Group G]

/-- **Definition 5.24** (class function): `f(h U h⁻¹) = f(U)` for all `h` and
`U`, so `f` depends only on the conjugacy class of `U`. Chapter 11 uses the same
notion for its convolutions. -/
@[book "def:wilson"]
def IsClassFunction {A : Type*} (f : G → A) : Prop := ∀ h U, f (h * U * h⁻¹) = f U

/-- **Definition 5.24** (character): `χ_ρ(g) = Tr ρ(g)`, for a representation
`ρ` of `G`, a homomorphism into the invertible `n × n` complex matrices. -/
@[book "def:wilson"]
def character {n : ℕ} (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) (g : G) : ℂ :=
  Matrix.trace (ρ g : Matrix (Fin n) (Fin n) ℂ)

/-- A character is a class function. -/
theorem character_isClassFunction {n : ℕ} (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) :
    IsClassFunction (character ρ) := by
  intro a g
  unfold character
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle,
    Units.inv_mul, one_mul]

namespace Skeleton

variable {X : Skeleton} {n : ℕ}

/-- **Definition 5.24** (Wilson loop): `χ_ρ(Hol_U(γ))` on a loop `γ`. -/
@[book "def:wilson"]
def wilsonLoop (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) (U : X.LinkTable G) {v : X.V}
    (γ : X.Path v v) : ℂ :=
  character ρ (hol U γ)

/-- **Definition 5.24** (Wilson line): `ρ(Hol_U(γ))` on a path `γ`, open when
its ends differ. -/
@[book "def:wilson"]
def wilsonLine (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) (U : X.LinkTable G) {u v : X.V}
    (γ : X.Path u v) : Matrix.GeneralLinearGroup (Fin n) ℂ :=
  ρ (hol U γ)

end Skeleton

/-! ## Non-vacuity -/

/-- For the trivial representation of dimension one, every Wilson loop is
`1`. -/
example {X : Skeleton} (U : X.LinkTable G) {v : X.V} (γ : X.Path v v) :
    Skeleton.wilsonLoop (1 : G →* Matrix.GeneralLinearGroup (Fin 1) ℂ) U γ = 1 := by
  simp [Skeleton.wilsonLoop, character]

end Artform
