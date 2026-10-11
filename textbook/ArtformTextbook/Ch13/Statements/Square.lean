import ArtformTextbook.Ch13.Defs.Square

/-!
# Statements of Chapter 13: the empty square

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of `Ch13/Defs/Square.lean`: the square of four links around one face, with
no matter, its holonomy `F = U₄U₃U₂U₁` read from `x₀` (`EmptySquare.face`), and a colour group
`G` with a triplet `ρ : G →* Matrix (Fin 3) (Fin 3) ℂ`, `χ(g) = Tr ρ(g)`. The four models are the
cube group, the icosahedral group, `C₃ × A₅` and Valentiner's group (Chapter 12); the book's
electric energy (Definition 11.9) and its blocks need a finite group.
-/

namespace Artform.Statement

open scoped ComplexConjugate

open ColourGroups

open Classical in
/-- **Proposition 13.5** (colourless states of the empty square). With no matter, a colourless
state of the square is a class function of `F`, and there are as many independent ones as the
group has classes: `5`, `5`, `15` and `17` for the four models. Two bases are natural. The magnetic
basis is the indicator functions of the classes, on which `B_U` is diagonal with the values
`β(3 - Re χ(C))`. The electric basis is the characters `χ_ρ(F)`, on which the electric energy is
diagonal with the values `4κE(ρ)`, every link in block `ρ`. The character table is the change of
basis between them.

"A colourless state is a class function of `F`" is read as the book's proof reads it, for any
group: `f ↦ (U ↦ f(F))` is a linear isomorphism from the class functions onto the colourless
states (`Canvas.gaugeInvariants` of the square), so every class function is reached. "As many
independent ones as classes" is the dimension, for a finite group; the four models are the cube
group, the icosahedral group, `C₃ × A₅` and Valentiner's group. "The magnetic basis" is a basis of
the colourless states whose vectors are the states `1_C(F)` (`EmptySquare.classState`), and
`B_U = β(3 - Re χ(F))` (`EmptySquare.magnetic`) multiplies each by `β(3 - Re χ(g))` for `g` in
`C`; the triplet is any `ρ` and `β` any real number. "The characters `χ_ρ(F)`" are those of the
blocks, the members of a complete family `σ` of distinct irreducible representations
(Theorem 11.4); the electric basis is a basis whose vectors are the states `χ_{σ i}(F)`
(`EmptySquare.charState`). The electric energy is `κ Σ_j H_{E,j}` with `H_{E,j}` the operator of
Definition 11.9 (`electricEnergy σ E`, for any table `E` of levels) on the link `j`
(`EmptySquare.electric`); "every link in block `ρ`": with the other links fixed, the state is a
table over the value of each link that lies in the block of `σ i` (Definition 11.3). "The
character table is the change of basis": `χ_{σ i}(F) = Σ_C χ_{σ i}(g_C) 1_C(F)`, for any choice of
an element `g_C` in each class. -/
@[book "prop:ml-square-states"]
def mlSquareStates : Prop :=
  (∀ (G : Type) [Group G],
    ∃ e : ↥(EmptySquare.classFunctions G) ≃ₗ[ℂ] ↥(squareCanvas.gaugeInvariants G),
      ∀ (f : ↥(EmptySquare.classFunctions G)) (U : squareCanvas.skeleton.LinkTable G),
        (e f : squareCanvas.skeleton.LinkTable G → ℂ) U = (f : G → ℂ) (EmptySquare.face U)) ∧
  (∀ (G : Type) [Group G] [Finite G],
    Module.finrank ℂ ↥(squareCanvas.gaugeInvariants G) = Nat.card (ConjClasses G)) ∧
  Module.finrank ℂ ↥(squareCanvas.gaugeInvariants cubeGroup) = 5 ∧
  Module.finrank ℂ ↥(squareCanvas.gaugeInvariants icoGroup) = 5 ∧
  Module.finrank ℂ ↥(squareCanvas.gaugeInvariants C3A5) = 15 ∧
  Module.finrank ℂ ↥(squareCanvas.gaugeInvariants valentiner) = 17 ∧
  (∀ (G : Type) [Group G] [Finite G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ),
    (∃ b : Module.Basis (ConjClasses G) ℂ ↥(squareCanvas.gaugeInvariants G),
      ∀ c, (b c : squareCanvas.skeleton.LinkTable G → ℂ) = EmptySquare.classState c) ∧
    ∀ (β : ℝ) (c : ConjClasses G) (g : G), ConjClasses.mk g = c →
      EmptySquare.magnetic ρ β (EmptySquare.classState c) =
        ((β * (3 - (ρ g).trace.re) : ℝ) : ℂ) • EmptySquare.classState c) ∧
  ∀ (G : Type) [Group G] [Fintype G] (ι : Type) [Fintype ι] (d : ι → ℕ)
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)), IsCompleteFamily σ →
    (∃ b : Module.Basis ι ℂ ↥(squareCanvas.gaugeInvariants G),
      ∀ i, (b i : squareCanvas.skeleton.LinkTable G → ℂ) = EmptySquare.charState (σ i)) ∧
    (∀ (E : ι → ℚ) (κ : ℝ) (i : ι),
      (κ : ℂ) • EmptySquare.electric (electricEnergy σ E) (EmptySquare.charState (σ i)) =
        ((4 * κ * (E i : ℝ) : ℝ) : ℂ) • EmptySquare.charState (σ i)) ∧
    (∀ (i : ι) (U : squareCanvas.skeleton.LinkTable G) (j : Fin 4),
      (fun g => EmptySquare.charState (σ i) (squareCanvas.setLink U j g)) ∈ block (σ i)) ∧
    ∀ g : ConjClasses G → G, (∀ c, ConjClasses.mk (g c) = c) → ∀ i,
      EmptySquare.charState (σ i) =
        ∑ c : ConjClasses G, (σ i).character (g c) • EmptySquare.classState c

open Classical in
/-- **Theorem 13.6** (the magnetic term in the electric basis). In the electric basis the magnetic
term is `B_{ρσ} = β(3 δ_{ρσ} - (N_{ρσ} + N_{σρ})/2)`, `N_{ρσ}` the multiplicity of `ρ` in
`3 ⊗ σ`, and for a real triplet `N` is symmetric and `B = β(3 - N)`. The columns of the
character table are the eigenvectors of `(N + Nᵀ)/2`, with the class values `Re χ(C)` as
eigenvalues. For the cube group `N` is the table of `fig:ml-square-table`, and the energy law of
the empty square is the `5 × 5` matrix `4κ diag(E) + β(3 - N)`.

The setting is that of Proposition 13.5: a finite group with a triplet `ρ` and a complete family
`σ` of distinct irreducible representations, the blocks, whose characters `χ_{σ i}(F)` are the
electric basis. "In the electric basis the magnetic term is `B_{ρσ}`": `B_U` carries the vector
of `σ` to `Σ_ρ B_{ρσ}` times the vector of `ρ`. `N_{ρσ}` is the dimension of the equivariant
maps from `ρ` to the tensor product of the triplet with `σ` (`EmptySquare.tensorMult`, the number
of times of Proposition 11.5). A triplet is real when its matrices are. "The columns of the
character table are eigenvectors": for every class, with `g` in it, the column `(χ_σ(g))_σ` is
not zero and `Σ_σ ((N + Nᵀ)/2)_{ρσ} χ_σ(g) = Re χ(g) χ_ρ(g)`. "The energy law is the matrix
`4κ diag(E) + B`": `H = κ Σ_j H_{E,j} + B_U` (`EmptySquare.energy`, with `H_{E,j}` the electric
energy of Definition 11.9 for any table `E` of levels) carries the vector of `σ` to
`Σ_ρ (4κ E(σ) δ_{ρσ} + B_{ρσ})` times the vector of `ρ`. For the cube group with its triplet
the blocks are named by the character table (`fig:mt-s4-characters`, `cubeChar`): read through
characters, as Chapter 12 reads the cube's blocks, the number of times the block `b` appears in
`3_r ⊗ b'` is the pairing `⟨χ χ_{b'}, χ_b⟩` (Proposition 11.5), and this is the table
(`EmptySquare.cubeN`); a complete family of the cube group has five members, which can be named
by the five blocks so that each carries its block's character, and when they are so named, `N` is
the table and the energy law is the stated matrix. -/
@[book "thm:ml-square-matrix"]
def mlSquareMatrix : Prop :=
  (∀ (G : Type) [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (ι : Type)
      [Fintype ι] (d : ι → ℕ) (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)),
      IsCompleteFamily σ →
    let N : ι → ι → ℂ := fun r s => (EmptySquare.tensorMult ρ (σ r) (σ s) : ℂ)
    let δ : ι → ι → ℂ := fun r s => if r = s then 1 else 0
    (∀ (β : ℝ) (s : ι), EmptySquare.magnetic ρ β (EmptySquare.charState (σ s)) =
      ∑ r, ((β : ℂ) * (3 * δ r s - (N r s + N s r) / 2)) • EmptySquare.charState (σ r)) ∧
    ((∀ g i j, conj (ρ g i j) = ρ g i j) →
      (∀ r s, EmptySquare.tensorMult ρ (σ r) (σ s) = EmptySquare.tensorMult ρ (σ s) (σ r)) ∧
      ∀ (β : ℝ) (s : ι), EmptySquare.magnetic ρ β (EmptySquare.charState (σ s)) =
        ∑ r, ((β : ℂ) * (3 * δ r s - N r s)) • EmptySquare.charState (σ r)) ∧
    (∀ g : G, (fun s => (σ s).character g) ≠ 0 ∧
      ∀ r, ∑ s, (N r s + N s r) / 2 * (σ s).character g =
        ((ρ g).trace.re : ℂ) * (σ r).character g) ∧
    ∀ (E : ι → ℚ) (κ β : ℝ) (s : ι),
      EmptySquare.energy (electricEnergy σ E) κ ρ β (EmptySquare.charState (σ s)) =
        ∑ r, (4 * (κ : ℂ) * (E s : ℂ) * δ r s + (β : ℂ) * (3 * δ r s - (N r s + N s r) / 2)) •
          EmptySquare.charState (σ r)) ∧
  (∀ b b' : CubeBlock,
    classPairing cubeGroup (fun g => colourChar cubeGroup g * cubeChar b' g) (cubeChar b) =
      (EmptySquare.cubeN b b' : ℂ)) ∧
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ)),
    IsCompleteFamily σ → Fintype.card ι = 5 ∧
    (∃ lab : ι → CubeBlock, ∀ i, (σ i).character = cubeChar (lab i)) ∧
    ∀ lab : ι → CubeBlock, (∀ i, (σ i).character = cubeChar (lab i)) →
      (∀ r s, EmptySquare.tensorMult cubeTriplet (σ r) (σ s) =
        EmptySquare.cubeN (lab r) (lab s)) ∧
      ∀ (E : ι → ℚ) (κ β : ℝ) (s : ι),
        EmptySquare.energy (electricEnergy σ E) κ cubeTriplet β (EmptySquare.charState (σ s)) =
          ∑ r, (4 * (κ : ℂ) * (E s : ℂ) * (if r = s then 1 else 0) +
            (β : ℂ) * (3 * (if r = s then 1 else 0) - (EmptySquare.cubeN (lab r) (lab s) : ℂ))) •
            EmptySquare.charState (σ r)

end Artform.Statement
