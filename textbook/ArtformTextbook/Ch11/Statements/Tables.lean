import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.Character
import ArtformTextbook.Ch11.Defs.Tables

/-!
# Statements of Chapter 11: tables on a group, writes, blocks and convolutions

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.

An irreducible representation `ρ : G → GL(d_ρ, ℂ)` of the book is a representation of `G` on
`ℂ^{d_ρ} = Fin d_ρ → ℂ`. "The distinct irreducible representations" are a family `ρ i` of
irreducible representations, no two of them isomorphic, such that every irreducible
representation is isomorphic to one of them.
-/

namespace Artform.Statement

open scoped ComplexConjugate Matrix

/-- **Proposition 11.2** (the two write families). Left and right writes commute with each
other, `L_h R_k = R_k L_h` for all `h, k`. A gauge change `(h_x, h_y)` acts on the link's
coefficient table by one write of each kind, `ψ ↦ L_{h_y} R_{h_x} ψ`,
`(L_{h_y} R_{h_x} ψ)(U) = ψ(h_y⁻¹ U h_x)`, the table that assigns to the moved link
`h_y U h_x⁻¹` the coefficient the old table assigned to `U`. Tables take values in any type
`A` (the book's are `R₈`). -/
@[book "prop:mt-writes"]
def mtWrites : Prop :=
  ∀ (G : Type) [Group G] (A : Type),
    (∀ (h k : G) (ψ : G → A), leftWrite h (rightWrite k ψ) = rightWrite k (leftWrite h ψ)) ∧
    (∀ (hx hy : G) (ψ : G → A) (U : G),
      leftWrite hy (rightWrite hx ψ) U = ψ (hy⁻¹ * U * hx)) ∧
    (∀ (hx hy : G) (ψ φ : G → A),
      (∀ U, φ (hy * U * hx⁻¹) = ψ U) ↔ φ = leftWrite hy (rightWrite hx ψ))

/-- **Theorem 11.4** (blocks fill the table space). The blocks of the distinct irreducible
representations are independent, orthogonal for the pairing of `qr:hilbert`, and together span
the complex-valued tables: `Σ_ρ d_ρ² = |G|`. Every left and right write carries each block into
itself.

The first conjunct says that the distinct irreducible representations exist, finitely many;
the second states the theorem for any choice `ρ i : G → GL(d_i, ℂ)` of them. -/
@[book "thm:mt-blocks"]
def mtBlocks : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    (∃ (n : ℕ) (d : Fin n → ℕ) (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) ∧
      ∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
        ∃ i, Nonempty (σ.Equiv (ρ i))) ∧
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) → (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) →
      (∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
        ∃ i, Nonempty (σ.Equiv (ρ i))) →
        iSupIndep (fun i => block (ρ i)) ∧
        (∀ i j, i ≠ j → ∀ φ ∈ block (ρ i), ∀ ψ ∈ block (ρ j), coeffPairing φ ψ = 0) ∧
        ⨆ i, block (ρ i) = ⊤ ∧
        ∑ i, d i ^ 2 = Fintype.card G ∧
        ∀ i (h : G), ∀ ψ ∈ block (ρ i),
          leftWrite h ψ ∈ block (ρ i) ∧ rightWrite h ψ ∈ block (ρ i)

/-- **Theorem 11.6** (one-edge operators). A matrix on the table space commutes with all left
and right writes if and only if it is convolution by a class function `f`,
`(f * ψ)(V) = Σ_{U ∈ G} f(V U⁻¹) ψ(U) = Σ_{h ∈ G} f(h) (L_h ψ)(V)`. Convolution by `f` acts on
the block `B_ρ` as the scalar `f̂(ρ) = (1/d_ρ) Σ_U f(U) conj(χ_ρ(U))`. Writing
`f = (1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ`, the scalar on `B_ρ` is `r(ρ)`, so the operator is unitary
exactly when every `r(ρ)` is a unit phase.

Here `ρ` in the third conjunct is any irreducible representation, and the last conjunct is
stated for any choice `ρ i` of the distinct irreducible representations; it includes that every
class function can be so written. -/
@[book "thm:mt-convolution"]
def mtConvolution : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G],
    (∀ B : Matrix G G ℂ,
      ((∀ (h : G) (ψ : G → ℂ), B *ᵥ leftWrite h ψ = leftWrite h (B *ᵥ ψ)) ∧
        (∀ (h : G) (ψ : G → ℂ), B *ᵥ rightWrite h ψ = rightWrite h (B *ᵥ ψ))) ↔
      ∃ f : G → ℂ, IsClassFunction f ∧ B = convolution f) ∧
    (∀ (f ψ : G → ℂ) (V : G),
      (convolution f *ᵥ ψ) V = ∑ U, f (V * U⁻¹) * ψ U ∧
      ∑ U, f (V * U⁻¹) * ψ U = ∑ h, f h * leftWrite h ψ V) ∧
    (∀ (d : ℕ) (ρ : Representation ℂ G (Fin d → ℂ)), ρ.IsIrreducible →
      ∀ f : G → ℂ, IsClassFunction f → ∀ ψ ∈ block ρ,
        convolution f *ᵥ ψ = ((d : ℂ)⁻¹ * ∑ U, f U * conj (ρ.character U)) • ψ) ∧
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (ρ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      (∀ i, (ρ i).IsIrreducible) → (∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) →
      (∀ (d' : ℕ) (σ : Representation ℂ G (Fin d' → ℂ)), σ.IsIrreducible →
        ∃ i, Nonempty (σ.Equiv (ρ i))) →
        (∀ f : G → ℂ, IsClassFunction f → ∃ r : ι → ℂ,
          f = fun U => (Fintype.card G : ℂ)⁻¹ * ∑ i, r i * d i * (ρ i).character U) ∧
        ∀ r : ι → ℂ,
          let f : G → ℂ := fun U => (Fintype.card G : ℂ)⁻¹ * ∑ i, r i * d i * (ρ i).character U
          (∀ i, ∀ ψ ∈ block (ρ i), convolution f *ᵥ ψ = r i • ψ) ∧
          (convolution f ∈ Matrix.unitaryGroup G ℂ ↔ ∀ i, ‖r i‖ = 1)

end Artform.Statement
