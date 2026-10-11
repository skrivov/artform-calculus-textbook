import Mathlib.Algebra.Star.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import ArtformTextbook.Meta.Book

/-!
# Tables on a group, writes and blocks (Sections 11.1 and 11.2)

A coherent state of a link with values in a group `G` is a coefficient table `ψ : G → R₈`, one
coefficient at every group element. The writes act on tables with values in any type `A`; the
book's coefficients are those of `R₈`, and its blocks and convolutions are complex-valued
tables `G → ℂ`.

An operator on the table space is a matrix `B : Matrix G G ℂ`, `B(V, U)` being the coefficient
carried from the cell `U` to the cell `V`; it acts on a table `ψ` by `B *ᵥ ψ`, that is
`(B ψ)(V) = Σ_U B(V, U) ψ(U)`.
-/

namespace Artform

open scoped ComplexConjugate

section Writes

variable {G : Type*} [Group G] {A : Type*}

/-- **Definition 11.1** (left and right writes). For `h ∈ G` the left write acts on a table by
`(L_h ψ)(U) = ψ(h⁻¹ U)`: it moves the coefficient at `U` to the cell `h U`. -/
@[book "def:mt-writes"]
def leftWrite (h : G) (ψ : G → A) : G → A := fun U => ψ (h⁻¹ * U)

/-- **Definition 11.1** (left and right writes). For `h ∈ G` the right write acts on a table by
`(R_h ψ)(U) = ψ(U h)`: it moves the coefficient at `U` to the cell `U h⁻¹`. -/
@[book "def:mt-writes"]
def rightWrite (h : G) (ψ : G → A) : G → A := fun U => ψ (U * h)

end Writes

/-- The pairing of coefficient tables over a finite set of labels `B`, the pairing of
`qr:hilbert` (Section 7.2, "Conjugation and the pairing"):
`⟨φ, ψ⟩ = Σ_{z ∈ B} conj(φ_z) ψ_z`. -/
def coeffPairing {B : Type*} [Fintype B] (φ ψ : B → ℂ) : ℂ := ∑ z, conj (φ z) * ψ z

section Blocks

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The table `U ↦ Tr(A ρ(U))` of the block of `ρ`, for an endomorphism `A` of the space of
`ρ`. -/
noncomputable def blockTable (ρ : Representation ℂ G V) (A : Module.End ℂ V) : G → ℂ :=
  fun U => LinearMap.trace ℂ V (A * ρ U)

/-- `A ↦ (U ↦ Tr(A ρ(U)))` as a linear map. -/
noncomputable def blockMap (ρ : Representation ℂ G V) : Module.End ℂ V →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi fun U => LinearMap.trace ℂ V ∘ₗ LinearMap.mulRight ℂ (ρ U)

/-- **Definition 11.3** (block of an irreducible representation). The block of `ρ` in the table
space is `B_ρ = {U ↦ Tr(A ρ(U)) : A ∈ Mat_{d_ρ}(ℂ)}`, the matrices `A` being the
endomorphisms of the space of `ρ`. The book takes `ρ` irreducible; the definition is the same
for any representation. -/
@[book "def:mt-block"]
noncomputable def block (ρ : Representation ℂ G V) : Submodule ℂ (G → ℂ) :=
  LinearMap.range (blockMap ρ)

end Blocks

section Convolution

variable {G : Type*} [Group G]

/-- A class function: `f(h U h⁻¹) = f(U)` for all `h` and `U`. -/
def IsClassFunction {A : Type*} (f : G → A) : Prop := ∀ h U, f (h * U * h⁻¹) = f U

/-- Convolution by `f` as a matrix on the table space: `(f * ψ)(V) = Σ_U f(V U⁻¹) ψ(U)`. -/
def convolution (f : G → ℂ) : Matrix G G ℂ := Matrix.of fun V U => f (V * U⁻¹)

end Convolution

end Artform
