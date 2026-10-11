import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RepresentationTheory.Character
import ArtformTextbook.Ch03.Defs.Canvas
import ArtformTextbook.Ch12.Defs.ColourGroups

/-!
# Statements of Chapter 12: the colour groups and their characters

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The four colour groups are those of `Ch12/Defs/ColourGroups.lean`: the cube group, the
icosahedral group, `C₃ × A₅` (Definition 12.11) and Valentiner's group `S(1080)`. A
decomposition of a representation is read, as the book's proofs read it, through characters:
the character of `3 ⊗ 3` is `χ²`, that of `3 ⊗ 3̄` is `χ χ̄`, those of `Λ²3` and `Sym²3` are
`altSqChar χ` and `symSqChar χ`; a block occurs in a representation as many times as the
pairing of its character with the representation's character says (Proposition 11.5), and a
character `ψ` of a representation is irreducible exactly when `⟨ψ, ψ⟩ = 1`.
-/

namespace Artform.Statement

open Matrix Polynomial

/-- **Proposition 12.9** (the tensor square of the icosahedral triplet). For the icosahedral
group, `3 ⊗ 3 = 1 ⊕ 3 ⊕ 5`, with `Λ²3 = 3` and `Sym²3 = 1 ⊕ 5`, and `⟨χ⁴⟩ = 3`. For the cube
group, `Sym²3_r = 1 ⊕ 2 ⊕ 3_s` and `⟨χ⁴⟩ = 4`.

Each decomposition is an identity of characters, as in the book's proof: the character of
`3 ⊗ 3` is `χ(g)²`, that of `Λ²3` is `(χ(g)² - χ(g²))/2` and that of `Sym²3` is
`(χ(g)² + χ(g²))/2`, and each equals, at every element, the sum of the named columns of the
group's character table (Figures `fig:mm-a5-characters` and `fig:mt-s4-characters`). The
blocks named are irreducible and distinct: their columns are orthonormal for the pairing
`⟨ψ, ψ'⟩ = (1/|G|) Σ_g ψ(g) conj(ψ'(g))`. `⟨χ⁴⟩` is the average `(1/|G|) Σ_g χ(g)⁴`. -/
@[book "prop:mm-a5-tensor"]
def a5Tensor : Prop :=
  (∀ g : icoGroup, colourChar icoGroup g ^ 2 =
    a5Char .one g + a5Char .three g + a5Char .five g) ∧
  (∀ g : icoGroup, altSqChar (colourChar icoGroup) g = a5Char .three g) ∧
  (∀ g : icoGroup, symSqChar (colourChar icoGroup) g = a5Char .one g + a5Char .five g) ∧
  (∀ ρ ∈ [A5Block.one, .three, .five], ∀ σ ∈ [A5Block.one, .three, .five],
    classPairing icoGroup (a5Char ρ) (a5Char σ) = if ρ = σ then 1 else 0) ∧
  groupAvg icoGroup (fun g => colourChar icoGroup g ^ 4) = 3 ∧
  (∀ g : cubeGroup, symSqChar (colourChar cubeGroup) g =
    cubeChar .one g + cubeChar .two g + cubeChar .threeS g) ∧
  (∀ ρ ∈ [CubeBlock.one, .two, .threeS], ∀ σ ∈ [CubeBlock.one, .two, .threeS],
    classPairing cubeGroup (cubeChar ρ) (cubeChar σ) = if ρ = σ then 1 else 0) ∧
  groupAvg cubeGroup (fun g => colourChar cubeGroup g ^ 4) = 4

/-- **Proposition 12.13** (orders from traces). A unitary `3 × 3` matrix of determinant one
with a real trace `t` has the eigenvalues `1`, `e^{iθ}` and `e^{-iθ}` with `1 + 2 cos θ = t`;
with the trace `ω^j t`, `t` real, its eigenvalues are `ω^j` times these. Every trace in the
class table of `S(1080)` (Figure `fig:mm-s1080-classes`) has this form, and the orders in the
table follow: `1`, `2`, `3` (four classes), `4`, `5` (two), `6` (two), `12` (two) and `15`
(four). The exponent of the group, the least `e` with `g^e = 1` for every `g`, is `60`.

The eigenvalues of a matrix, with their multiplicities, are the roots of its characteristic
polynomial, and `ω = e^{2πi/3}`. The table is the class table of the group: its seventeen rows
correspond one to one to the conjugacy classes, and the class of a row has as many elements as
the row says, each of the order and with the trace of the triplet that the row gives. The
orders follow from the traces: two elements with the same trace have the same order. The
sixth conjunct counts the classes whose elements have order `n`. -/
@[book "prop:mm-s1080-orders"]
def s1080Orders : Prop :=
  (∀ M ∈ specialUnitaryGroup (Fin 3) ℂ, ∀ t : ℝ, M.trace = t →
    ∃ θ : ℝ, M.charpoly.roots =
        {1, Complex.exp (θ * Complex.I), Complex.exp (-θ * Complex.I)} ∧
      1 + 2 * Real.cos θ = t) ∧
  (∀ M ∈ specialUnitaryGroup (Fin 3) ℂ, ∀ (j : ℕ) (t : ℝ), M.trace = Exact.omega ^ j * t →
    ∃ θ : ℝ, M.charpoly.roots =
        {Exact.omega ^ j, Exact.omega ^ j * Complex.exp (θ * Complex.I),
          Exact.omega ^ j * Complex.exp (-θ * Complex.I)} ∧
      1 + 2 * Real.cos θ = t) ∧
  (∀ i, ∃ (j : ℕ) (t : ℝ), (s1080ClassTable i).trace = Exact.omega ^ j * t) ∧
  (∃ e : ConjClasses valentiner ≃ Fin 17, ∀ c : ConjClasses valentiner,
    c.carrier.ncard = (s1080ClassTable (e c)).size ∧
    ∀ g ∈ c.carrier, colourChar valentiner g = (s1080ClassTable (e c)).trace ∧
      orderOf g = (s1080ClassTable (e c)).order) ∧
  (∀ g h : valentiner, colourChar valentiner g = colourChar valentiner h →
    orderOf g = orderOf h) ∧
  (∀ n : ℕ, {c : ConjClasses valentiner | ∃ g ∈ c.carrier, orderOf g = n}.ncard =
    if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 4 else if n = 4 then 1
    else if n = 5 then 2 else if n = 6 then 2 else if n = 12 then 2 else if n = 15 then 4
    else 0) ∧
  Monoid.exponent valentiner = 60

/-- **Proposition 12.14** (the tensor squares of the Valentiner triplet). For `S(1080)`,
`⟨χχ̄⟩ = 1` and `⟨χ²χ̄²⟩ = 2`. Hence `3 ⊗ 3̄ = 1 ⊕ 8` with the eight irreducible, and
`3 ⊗ 3 = 3̄ ⊕ 6` with the six irreducible: the shapes of `SU(3)`. For `C₃ × A₅` the second
average is `3`, and the eight splits as `3 ⊕ 5`.

Read through characters, as in the book's proof. The character of `3 ⊗ 3̄` is `χ χ̄`: it
contains the trivial block once, `⟨χ χ̄, 1⟩ = 1`, and the rest, the eight, has the character
`χ χ̄ - 1`, of degree `8` and irreducible. The character of `3 ⊗ 3` is `χ²`, the sum of the
character `χ̄` of the conjugate triplet, irreducible, which is the antisymmetric part, and the
character of the symmetric part, the six, of degree `6` and irreducible. For `C₃ × A₅`, with
its character `χ(ω^j, g) = ω^j χ₃(g)`, the eight's character `χ χ̄ - 1` is the sum of the
characters of the blocks `3` and `5` of the icosahedral group read through the projection
`(ω^j, g) ↦ g`, which are irreducible and distinct. -/
@[book "prop:mm-s1080-tensor"]
def s1080Tensor : Prop :=
  groupAvg valentiner (fun g =>
    colourChar valentiner g * (starRingEnd ℂ) (colourChar valentiner g)) = 1 ∧
  groupAvg valentiner (fun g =>
    colourChar valentiner g ^ 2 * (starRingEnd ℂ) (colourChar valentiner g) ^ 2) = 2 ∧
  classPairing valentiner
    (fun g => colourChar valentiner g * (starRingEnd ℂ) (colourChar valentiner g))
    (fun _ => 1) = 1 ∧
  colourChar valentiner 1 * (starRingEnd ℂ) (colourChar valentiner 1) - 1 = 8 ∧
  classPairing valentiner
    (fun g => colourChar valentiner g * (starRingEnd ℂ) (colourChar valentiner g) - 1)
    (fun g => colourChar valentiner g * (starRingEnd ℂ) (colourChar valentiner g) - 1) = 1 ∧
  (∀ g : valentiner, colourChar valentiner g ^ 2 =
    (starRingEnd ℂ) (colourChar valentiner g) + symSqChar (colourChar valentiner) g) ∧
  (∀ g : valentiner,
    altSqChar (colourChar valentiner) g = (starRingEnd ℂ) (colourChar valentiner g)) ∧
  classPairing valentiner (fun g => (starRingEnd ℂ) (colourChar valentiner g))
    (fun g => (starRingEnd ℂ) (colourChar valentiner g)) = 1 ∧
  symSqChar (colourChar valentiner) 1 = 6 ∧
  classPairing valentiner (symSqChar (colourChar valentiner))
    (symSqChar (colourChar valentiner)) = 1 ∧
  groupAvg C3A5 (fun x => C3A5.char x ^ 2 * (starRingEnd ℂ) (C3A5.char x) ^ 2) = 3 ∧
  (∀ x : C3A5, C3A5.char x * (starRingEnd ℂ) (C3A5.char x) - 1 =
    a5Char .three x.2 + a5Char .five x.2) ∧
  (∀ ρ ∈ [A5Block.three, .five], ∀ σ ∈ [A5Block.three, .five],
    classPairing C3A5 (fun x => a5Char ρ x.2) (fun x => a5Char σ x.2) =
      if ρ = σ then 1 else 0)

/-- **Theorem 12.16** (every loop closes). Let `G` be a finite colour group with exponent `e`.
For every connection `U` on every canvas and every loop `γ`, `Hol_U(γ)^e = 1`: a quark
transported `e` times around any loop returns with its colour unchanged, and the Wilson loop of
the `e`-fold loop is `3`. For the four models `e = 12`, `30`, `30` and `60`. No `e` does this
for `SU(3)`.

A finite colour group is read as any finite group `G` with a triplet `ρ`, a representation on
the colour space `ℂ³`; its exponent `e` is `Monoid.exponent G`, the least `e > 0` with `g^e = 1`
for every `g`. A connection on a canvas `K` is a link table `U` on its transport skeleton
(Definition 5.19), and `Hol_U(γ)` is `Skeleton.hol`. The `e`-fold loop is `γ.loopPow e`; a
quark of colour `c ∈ ℂ³` transported along it has the colour `ρ(Hol_U(γᵉ)) c`, and the Wilson
loop of `γᵉ` is the character of the triplet at its holonomy (Definition 5.24),
`χ_ρ(Hol_U(γᵉ)) = Tr ρ(Hol_U(γᵉ))`. The four models are the cube group, the icosahedral
group, `C₃ × A₅` and `S(1080)`. "No `e` does this for `SU(3)`": for every `e > 0` there are a
canvas, a connection on it with values in `SU(3)` and a loop with `Hol_U(γ)^e ≠ 1`. -/
@[book "thm:mm-loop"]
def mmLoop : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (ρ : Representation ℂ G (Fin 3 → ℂ)) (K : Canvas)
      (U : (Skeleton.ofGraph K.src K.tgt).LinkTable G) (v : K.V)
      (γ : (Skeleton.ofGraph K.src K.tgt).Path v v),
      Skeleton.hol U γ ^ Monoid.exponent G = 1 ∧
      (∀ c : Fin 3 → ℂ, ρ (Skeleton.hol U (γ.loopPow (Monoid.exponent G))) c = c) ∧
      ρ.character (Skeleton.hol U (γ.loopPow (Monoid.exponent G))) = 3) ∧
  Monoid.exponent cubeGroup = 12 ∧ Monoid.exponent icoGroup = 30 ∧
  Monoid.exponent C3A5 = 30 ∧ Monoid.exponent valentiner = 60 ∧
  ∀ e : ℕ, 0 < e → ∃ (K : Canvas)
    (U : (Skeleton.ofGraph K.src K.tgt).LinkTable (specialUnitaryGroup (Fin 3) ℂ)) (v : K.V)
    (γ : (Skeleton.ofGraph K.src K.tgt).Path v v), Skeleton.hol U γ ^ e ≠ 1

end Artform.Statement
