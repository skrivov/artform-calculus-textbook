import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import ArtformTextbook.Meta.Book

/-!
# Occupation tables, creations and second quantization (Section 11.4)

The modes form a finite type `M` (for one vertex, the pairs `(c, s)` of a colour and a slot).
An occupation table is a complete assignment of a bit to every mode; it is recorded here by the
finite set of its occupied modes, so that `n_m = 1` exactly when `m ∈ n`, `n + 1_m` is
`insert m n` and `n - 1_m` is `n.erase m`. Coefficient tables over the occupation tables are the
functions `Finset M → ℂ`; an operator on them is a matrix indexed by occupation tables, entry
`(n', n)` being the coefficient of `|n'⟩` in the image of `|n⟩`, and it acts by `*ᵥ`.

The order of the modes is a `LinearOrder M`, passed explicitly, because Proposition 11.11
compares two orders of the same modes.
-/

namespace Artform

namespace Fock

open scoped Matrix

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The basis table `|n⟩`: coefficient one at the occupation table `n`, zero elsewhere. The
empty table `|0⟩` is `ket ∅`. -/
def ket (n : Finset M) : Finset M → ℂ := Pi.single n 1

/-- `p(n, m)`: the number of occupied modes that precede `m` in the chosen order. -/
def precCount (ord : LinearOrder M) (n : Finset M) (m : M) : ℕ :=
  letI := ord
  (n.filter (· < m)).card

/-- **Definition 11.10** (sign rule): the creation `a†_m`, with
`a†_m |n⟩ = (-1)^{p(n,m)} |n + 1_m⟩` if `n_m = 0`, and the zero table otherwise. -/
@[book "def:mt-sign-rule"]
def creation (ord : LinearOrder M) (m : M) : Matrix (Finset M) (Finset M) ℂ :=
  Matrix.of fun n' n => if m ∉ n ∧ n' = insert m n then (-1) ^ precCount ord n m else 0

/-- **Definition 11.10** (sign rule): the annihilation `a_m`, with
`a_m |n⟩ = (-1)^{p(n,m)} |n - 1_m⟩` if `n_m = 1`, and the zero table otherwise. -/
@[book "def:mt-sign-rule"]
def annihilation (ord : LinearOrder M) (m : M) : Matrix (Finset M) (Finset M) ℂ :=
  Matrix.of fun n' n => if m ∈ n ∧ n' = n.erase m then (-1) ^ precCount ord n m else 0

/-- The operators built from the creations and annihilations: a noncommutative polynomial in
the letters `inl m` (for `a†_m`) and `inr m` (for `a_m`), evaluated in the chosen order. -/
noncomputable def build (ord : LinearOrder M) :
    FreeAlgebra ℂ (M ⊕ M) →ₐ[ℂ] Matrix (Finset M) (Finset M) ℂ :=
  FreeAlgebra.lift ℂ (Sum.elim (creation ord) (annihilation ord))

/-- The creation of the transformed mode `W e_m = Σ_{m'} W_{m'm} e_{m'}`:
`Σ_{m'} W_{m'm} a†_{m'}`. -/
def transformedCreation (ord : LinearOrder M) (W : Matrix M M ℂ) (m : M) :
    Matrix (Finset M) (Finset M) ℂ :=
  ∑ m', W m' m • creation ord m'

/-- Second quantization `Γ(W)` of a matrix `W` on the modes. Write the basis table as the
product of creations of its occupied modes in ascending order,
`|n⟩ = a†_{m₁} a†_{m₂} ⋯ a†_{m_k} |0⟩` with `m₁ < m₂ < ⋯ < m_k`; then `Γ(W)` transforms every
creation in the product, the transformed factors applied in the same order:
`Γ(W) |n⟩ = (Σ_{m'} W_{m'm₁} a†_{m'}) ⋯ (Σ_{m'} W_{m'm_k} a†_{m'}) |0⟩`. -/
noncomputable def secondQuant (ord : LinearOrder M) (W : Matrix M M ℂ) :
    Matrix (Finset M) (Finset M) ℂ :=
  Matrix.of fun n' n =>
    (((letI := ord; n.sort).map (transformedCreation ord W)).prod *ᵥ ket ∅) n'

/-- The colour rotation `Γ(g)` of one vertex, whose modes are the pairs `(c, s)` of a colour and
a slot: the second quantization of `g ⊗ 1`, which acts on one quark by
`e_{(c,s)} ↦ Σ_{c'} g_{c'c} e_{(c',s)}`. -/
noncomputable def vertexGamma {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (ord : LinearOrder (C × S)) (g : Matrix C C ℂ) :
    Matrix (Finset (C × S)) (Finset (C × S)) ℂ :=
  secondQuant ord (Matrix.kroneckerMap (· * ·) g (1 : Matrix S S ℂ))

end Fock

end Artform
