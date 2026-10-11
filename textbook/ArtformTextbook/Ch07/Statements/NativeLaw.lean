import ArtformTextbook.Ch07.Defs.NativeLaw

/-!
# Statements of Chapter 7: the selected native probability law

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open Artform.Exact Artform.NativeLaw

/-- **Theorem 7.4** (the selected native probability law). Under V, Z, AE, D₂, N₁, O and the
stated finite resource schema, the unique probability law on admitted complete columns is
`π_ψ(z) = |ψ_z|²`. For different independent preparations the joint law is consequently the
product of their laws.

Partial. Lean proves the algebraic core of the theorem and of its proof in outline, items 1-4
below; not formalized: the operational assumptions V, Z, AE, D₂, N₁ and O, the finite resource
schema, the book's derivation in outline that every admitted complete column has the law
`π_ψ(z) = M(ψ_z)` for one content `M` with the identities of item 1, and the operational half
of existence, that the squared law satisfies the six assumptions. They need a model of native
preparations, their tensor products and resource schemas, which the book gives in prose.

The items concern a real-valued content `M` on the formal coefficients `R₈` (Definition 7.1).
1. `M` has the identities `IsNativeContent`: splitting `2 M(x/√2) = M(x)`, the mixer identity
   `M((x + y)/√2) + M((x − y)/√2) = M(x) + M(y)`, the quarter turn `M(ix) = M(x)`,
   calibration `M(1) = 1` and nonnegativity, exactly when `M = M_λ` for one `λ ∈ [0, 1]`, where
   `M_λ(a) = λ|a|² + (1 − λ)|σ(a)|²` (`eq:qr-content-family`) and `σ` is the automorphism with
   `σ(√2) = −√2`, `σ(i) = i`.
2. For such `M`, duplication on the zero coefficient `a = (1 + ζ)/2` of `H, T, H`
   (Figure `fig:qr-hth`), `M(a · a) = M(a) M(a)`, holds exactly when `λ = 0` or `λ = 1`.
3. The contents with the identities, duplication on `a` and oriented retention `M(a) > 1/2` are
   exactly one, `M(z) = |z|²`: it has them all, and no other content does.
4. Such a content multiplies: `M(xy) = M(x) M(y)` for all `x, y` in `R₈`.

The hypotheses on `M` are interfaces. `IsNativeContent M` stands for what Section 7.6 derives in
outline from V, Z, AE, D₂ and N₁. Duplication is D₂ for two independent copies of `H, T, H` at
the report zero-zero, whose coefficient is `a · a`; oriented retention is O, the report zero of
`H, T, H` having probability `M(a) > 1/2`. Item 4 gives the product of the laws because the
coefficient of a joint report of independent preparations is the product of their
coefficients. -/
@[book "qr:selected-law"]
def selectedLaw : Prop :=
  -- 1. The identities, calibration and nonnegativity leave `M_λ`, for one `λ ∈ [0, 1]`.
  (∀ M : R8 → ℝ, IsNativeContent M ↔
      ∃! lam : ℝ, lam ∈ Set.Icc (0 : ℝ) 1 ∧ M = contentFamily lam) ∧
  -- 2. Duplication on the zero coefficient of `H, T, H` leaves `λ = 0` and `λ = 1`.
  (∀ M : R8 → ℝ, IsNativeContent M →
      (M (hthZero * hthZero) = M hthZero * M hthZero ↔
        M = contentFamily 0 ∨ M = contentFamily 1)) ∧
  -- 3. With oriented retention, the content is `|z|²`, and `|z|²` has every property.
  (∀ M : R8 → ℝ,
      (IsNativeContent M ∧ M (hthZero * hthZero) = M hthZero * M hthZero ∧
          1 / 2 < M hthZero) ↔
        ∀ z : R8, M z = Complex.normSq (Q4.toComplex z)) ∧
  -- 4. The selected content multiplies.
  (∀ M : R8 → ℝ, IsNativeContent M →
      M (hthZero * hthZero) = M hthZero * M hthZero → 1 / 2 < M hthZero →
        ∀ x y : R8, M (x * y) = M x * M y)

end Artform.Statement
