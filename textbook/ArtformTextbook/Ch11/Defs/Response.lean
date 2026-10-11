import Mathlib.RepresentationTheory.Character
import ArtformTextbook.Ch11.Defs.Tables

/-!
# Electric responses and electric reads (Definition 11.7)

The irreducible representations of a finite group `G` are those of a complete family of distinct
irreducible representations `σ i : G → GL(d_i, ℂ)`, `i ∈ ι`, as in Theorems 11.4 and 11.6: each
`σ i` is irreducible, no two are isomorphic, and every irreducible representation is isomorphic
to one of them (`IsCompleteFamily`). The trivial representation `1` is the member on which every
element acts as the identity (Mathlib's `Representation.IsTrivial`).

The kernel of a response `r` is the class function `(1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ`
(`responseKernel`, for any characters `χ` and dimensions `d`; `electricKernel` for the
characters of the family). Convolution by a kernel acts on tables with values in any complex
vector space `A`, `(k * ψ)(V) = Σ_h k(h) (L_h ψ)(V) = Σ_U k(V U⁻¹) ψ(U)` (`tableConv`): on
complex-valued tables it is the convolution of Theorem 11.6, and on the states of an edge, whose
values are coefficient tables over the occupations, it acts on the link and not on the matter.
-/

namespace Artform

open scoped ComplexConjugate

variable {G : Type*} [Group G]

/-- A complete family of distinct irreducible representations `σ i : G → GL(d_i, ℂ)`: each is
irreducible, no two are isomorphic, and every irreducible representation of `G` on some `ℂ^{d'}`
is isomorphic to one of them (the hypotheses of Theorems 11.4 and 11.6). -/
def IsCompleteFamily {ι : Type*} {d : ι → ℕ} (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) :
    Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i j, Nonempty ((σ i).Equiv (σ j)) → i = j) ∧
    ∀ (d' : ℕ) (τ : Representation ℂ G (Fin d' → ℂ)), τ.IsIrreducible →
      ∃ i, Nonempty (τ.Equiv (σ i))

/-- The kernel `(1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ` of a response `r`, for blocks `ρ ∈ ι` with characters
`χ_ρ` and dimensions `d_ρ`. -/
noncomputable def responseKernel {ι : Type*} [Fintype ι] (χ : ι → G → ℂ) (d r : ι → ℂ) :
    G → ℂ :=
  fun U => (Nat.card G : ℂ)⁻¹ * ∑ i, r i * d i * χ i U

/-- Convolution by a kernel `k` on tables with values in a complex vector space `A`:
`(k * ψ)(V) = Σ_h k(h) (L_h ψ)(V) = Σ_h k(h) ψ(h⁻¹ V)`. -/
noncomputable def tableConv [Fintype G] {A : Type*} [AddCommGroup A] [Module ℂ A] (k : G → ℂ)
    (ψ : G → A) : G → A :=
  ∑ h, k h • leftWrite h ψ

/-- A sign response, given by the set `D` of blocks on which it is `-1`: `r(ρ) = -1` for
`ρ ∈ D` and `r(ρ) = 1` otherwise. -/
def signResponse {ι : Type*} [DecidableEq ι] (D : Finset ι) : ι → ℂ :=
  fun i => if i ∈ D then -1 else 1

variable [Fintype G] {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- **Definition 11.7** (electric response). An electric response is a unit phase `r(ρ)` for
every irreducible representation `ρ`, with `r(1) = 1`. The irreducible representations are the
members of a complete family `σ` of distinct irreducible representations, and `1` is a member on
which every element acts as the identity (`Representation.IsTrivial`). -/
@[book "def:mt-response"]
def IsElectricResponse (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) : Prop :=
  (∀ i, ‖r i‖ = 1) ∧ ∀ i, (σ i).IsTrivial → r i = 1

/-- **Definition 11.7** (the kernel of the electric read):
`k = (1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ`, over the members of a complete family `σ`. -/
@[book "def:mt-response"]
noncomputable def electricKernel (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) :
    G → ℂ :=
  responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ)) r

/-- **Definition 11.7** (electric read). The electric read of a response `r` is convolution by
its kernel, `𝒦ψ = k * ψ = Σ_{h ∈ G} k(h) L_h ψ`, here on tables with values in any complex vector
space (on the states of an edge it acts on the link). That it is the unique operator that
multiplies each block by its response and commutes with the gauge action is Theorem 11.6. -/
@[book "def:mt-response"]
noncomputable def electricRead {A : Type*} [AddCommGroup A] [Module ℂ A]
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) (ψ : G → A) : G → A :=
  tableConv (electricKernel σ r) ψ

end Artform
