import Mathlib.RepresentationTheory.Intertwining
import ArtformTextbook.Ch11.Defs.Response
import ArtformTextbook.Ch12.Groups
import ArtformTextbook.Ch13.Defs.Census
import ArtformTextbook.Ch13.Defs.String

/-!
# The empty square (Section 13.2)

The canvas is the square of Chapter 12 (`ColourGroups.squareCanvas`): four vertices
`x₀, …, x₃`, the four edges `x_j → x_{j+1}` and one face. The book's link `U_{j+1}` is the value
on the stored edge `j`, and the holonomy of the face read from `x₀` (Definition 5.25 at its first
corner, `Canvas.curvature`) is `F = U₄U₃U₂U₁` (`EmptySquare.face`).

With no matter (`d = 0`) a state is a coefficient table over the link tables, and it is
colourless when every gauge change fixes it (`Canvas.gaugeInvariants`).

* **Two bases.** The class indicators `1_C(F)` (`EmptySquare.classState`) and the characters
  `χ_ρ(F)` (`EmptySquare.charState`), both states of the square.
* **The energy law** `H = κ Σ_j H_{E,j} + β(3 - Re χ(F))` with no hop (`EmptySquare.energy`): the
  electric energy of the four links (`EmptySquare.electric`, an operator on the tables of one
  link applied to each link in turn, `Canvas.onLink`) and the magnetic term `B_U`
  (`eq:ml-magnetic`, `EmptySquare.magnetic`), with `χ` the character of the triplet.
* **The tensor matrix** `N_ρσ`, the multiplicity of `ρ` in `3 ⊗ σ` (`EmptySquare.tensorMult`):
  the dimension of the equivariant maps from `ρ` to `3 ⊗ σ`, as Proposition 11.5 counts it. For
  the cube group it is the table of `fig:ml-square-table` (`EmptySquare.cubeN`).
-/

namespace Artform

namespace EmptySquare

open ColourGroups

variable {G : Type*} [Group G]

/-- The holonomy of the face of the square read from `x₀`, `F = U₄U₃U₂U₁`: the curvature of the
face at its first corner (Definition 5.25). -/
def face (U : squareCanvas.skeleton.LinkTable G) : G :=
  squareCanvas.curvature U () 0

variable (G) in
/-- The class functions on `G`, `f(h g h⁻¹) = f(g)`. -/
def classFunctions : Submodule ℂ (G → ℂ) where
  carrier := {f | IsClassFunction f}
  add_mem' {f f'} hf hf' h U := by
    simp only [Set.mem_ofPred_eq] at hf hf'
    simp only [Pi.add_apply, hf h U, hf' h U]
  zero_mem' _ _ := rfl
  smul_mem' c f hf h U := by
    simp only [Set.mem_ofPred_eq] at hf
    simp only [Pi.smul_apply, hf h U]

open Classical in
/-- **The magnetic basis** vector of a class `C`: the indicator of the class, as the state
`U ↦ 1_C(F)` of the square. -/
noncomputable def classState (c : ConjClasses G) : squareCanvas.skeleton.LinkTable G → ℂ :=
  fun U => if ConjClasses.mk (face U) = c then 1 else 0

/-- **The electric basis** vector of a representation `ρ`: its character of the holonomy, the
state `U ↦ χ_ρ(F)` of the square. -/
noncomputable def charState {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) : squareCanvas.skeleton.LinkTable G → ℂ :=
  fun U => σ.character (face U)

/-- **The magnetic term** `B_U = β(3 - Re χ₃(F))` (`eq:ml-magnetic`), with `χ₃` the character of
the triplet `ρ`, as the operator on states that multiplies the coefficient of `U` by it. -/
noncomputable def magnetic (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (β : ℝ)
    (ψ : squareCanvas.skeleton.LinkTable G → ℂ) : squareCanvas.skeleton.LinkTable G → ℂ :=
  fun U => ((β * (3 - (ρ (face U)).trace.re) : ℝ) : ℂ) * ψ U

/-- The electric energy of the square, `Σ_{j=1}^4 H_{E,j}`, for an operator `X` on the complex
tables of one link: `X` acts on the table of each link in turn. -/
def electric (X : (G → ℂ) → (G → ℂ)) (ψ : squareCanvas.skeleton.LinkTable G → ℂ) :
    squareCanvas.skeleton.LinkTable G → ℂ :=
  ∑ j : Fin 4, squareCanvas.onLink X j ψ

/-- **The energy law of the empty square**, `H = κ Σ_j H_{E,j} + β(3 - Re χ(F))`: with no matter
there is no hop. -/
noncomputable def energy (X : (G → ℂ) → (G → ℂ)) (κ : ℝ) (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (β : ℝ) (ψ : squareCanvas.skeleton.LinkTable G → ℂ) : squareCanvas.skeleton.LinkTable G → ℂ :=
  (κ : ℂ) • electric X ψ + magnetic ρ β ψ

/-- `N_ρσ`, **the multiplicity of `ρ` in `3 ⊗ σ`**: the dimension of the equivariant maps from
`ρ` to the tensor product of the triplet with `σ`, the number of times `ρ` occurs in `3 ⊗ σ` as
Proposition 11.5 reads it. -/
noncomputable def tensorMult (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) {V V' : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (τ : Representation ℂ G V)
    (τ' : Representation ℂ G V') : ℕ :=
  Module.finrank ℂ (τ.IntertwiningMap ((Edge.tripletRep ρ).tprod τ'))

/-- The tensor matrix `N` of the cube group (`fig:ml-square-table`): the number of times the block
of the row appears in `3_r ⊗ σ` for the block `σ` of the column. -/
def cubeN : CubeBlock → CubeBlock → ℕ
  | .one, .threeR => 1
  | .one, _ => 0
  | .sign, .threeS => 1
  | .sign, _ => 0
  | .two, .threeS => 1
  | .two, .threeR => 1
  | .two, _ => 0
  | .threeS, .one => 0
  | .threeS, _ => 1
  | .threeR, .sign => 0
  | .threeR, _ => 1

end EmptySquare

end Artform
