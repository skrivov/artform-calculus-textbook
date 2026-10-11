import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.ClassEquation
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import ArtformTextbook.Ch11.Defs.Colourless

/-!
# Statements of Chapter 11: colourless states, and how to count them

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.

The setting is that of `Ch11/Defs/Colourless.lean`: one edge `x → y` over a finite group `G`,
whose triplet is a homomorphism `ρ : G →* Matrix C C ℂ`, with `d = |S|` slots at each end and
the `2|C||S|` modes of the edge in any order.
-/

namespace Artform.Statement

open scoped Matrix ComplexConjugate TensorProduct

/-- **Proposition 11.14** (colourless states are the invariants of one vertex). A colourless
state is determined by its value at the identity link, `ψ(1)`, and `ψ(1)` can be any vector fixed
by the diagonal action `Γ_x(h) Γ_y(h)`. Hence the colourless states of one edge with `d` slots
correspond to the invariant occupation tables of one vertex with `2d` slots. The zero-flux space
is the tensor product of the invariant spaces at `x` and `y`.

The group `G` is finite, the triplet is any homomorphism `ρ : G →* Matrix C C ℂ` (the book: three
colours, `G ≤ SU(3)`), and the modes of the edge are in any order `ord`. The vertex with `2d`
slots has the slots `S ⊕ S`, those of `x` and those of `y`; "correspond" is a linear isomorphism
of the colourless states with its invariant tables, in any order `ordv` of its modes. "Is the
tensor product" is a linear isomorphism of the zero-flux space with the tensor product of the
invariant spaces at `x` and at `y`, each that of one vertex with the slots `S`, in any orders. -/
@[book "prop:mt-gauge-fix"]
def mtGaugeFix : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S)),
    (∀ ψ ∈ Edge.colourless ρ ord, ∀ φ ∈ Edge.colourless ρ ord, ψ 1 = φ 1 → ψ = φ) ∧
    (∀ ψ ∈ Edge.colourless ρ ord, ∀ h : G,
      (Edge.gammaX ord (ρ h) * Edge.gammaY ord (ρ h)) *ᵥ ψ 1 = ψ 1) ∧
    (∀ φ : Finset (Edge.Mode C S) → ℂ,
      (∀ h : G, (Edge.gammaX ord (ρ h) * Edge.gammaY ord (ρ h)) *ᵥ φ = φ) →
        ∃ ψ ∈ Edge.colourless ρ ord, ψ 1 = φ) ∧
    (∀ ordv : LinearOrder (C × (S ⊕ S)),
      Nonempty (Edge.colourless ρ ord ≃ₗ[ℂ] Edge.vertexInvariants ρ ordv)) ∧
    ∀ ordx ordy : LinearOrder (C × S),
      Nonempty (Edge.zeroFlux ρ ord ≃ₗ[ℂ]
        (Edge.vertexInvariants ρ ordx ⊗[ℂ] Edge.vertexInvariants ρ ordy))

open Polynomial Classical in
/-- **Theorem 11.15** (census of colourless states). On one edge with `d` slots, the number of
colourless states with `k` quarks is the coefficient of `z^k` in
`(1/|G|) Σ_{g ∈ G} (1 + χ(g) z + conj(χ(g)) z² + z³)^{2d}`,
a sum over conjugacy classes weighted by their sizes. The zero-flux states with `k_x` quarks at
`x` and `k_y` at `y` number the product of the coefficients of `z^{k_x}` and `z^{k_y}` in the same
average with exponent `d`.

The colour group is a finite group `G` with a triplet `ρ : G → SU(3)`, and `χ(g) = Tr ρ(g)`; the
`6d` modes are in any order. "The number of colourless states with `k` quarks" is the dimension of
the space of colourless states whose every coefficient table `ψ(U)` has `k` quarks, and likewise
for the zero-flux states with `k_x` quarks at `x` and `k_y` at `y`. The average is a polynomial in
`z`; the sum over the conjugacy classes takes the value of the summand at a representative of
each class. -/
@[book "thm:mt-census"]
def mtCensus : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (S : Type) [Fintype S] [DecidableEq S]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ), (∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) →
    ∀ ord : LinearOrder (Edge.Mode (Fin 3) S),
    let χ : G → ℂ := fun g => (ρ g).trace
    let term : ℕ → G → ℂ[X] := fun e g =>
      (1 + C (χ g) * X + C (conj (χ g)) * X ^ 2 + X ^ 3) ^ e
    let avg : ℕ → ℂ[X] := fun e => (Fintype.card G : ℂ)⁻¹ • ∑ g, term e g
    (∀ k : ℕ, (Module.finrank ℂ ↥(Edge.colourless ρ ord ⊓
        Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) k)) : ℂ) =
      (avg (2 * Fintype.card S)).coeff k) ∧
    (∀ e : ℕ, avg e = (Fintype.card G : ℂ)⁻¹ •
      ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) • term e (Quotient.out c)) ∧
    ∀ kx ky : ℕ, (Module.finrank ℂ ↥(Edge.zeroFlux ρ ord ⊓
        Edge.stateSector G (Edge.endSector (Fin 3) S kx ky)) : ℂ) =
      (avg (Fintype.card S)).coeff kx * (avg (Fintype.card S)).coeff ky

end Artform.Statement
