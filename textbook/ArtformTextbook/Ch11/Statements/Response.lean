import ArtformTextbook.Ch11.Defs.Response
import ArtformTextbook.Ch12.Defs.ColourGroups
import ArtformTextbook.Exact.R8

/-!
# Statements of Chapter 11: which electric reads stay in `R₈`

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.

The cube group is Model I of Chapter 12 (`cubeGroup`), with its five blocks `1`, `sgn`, `2`,
`3_s`, `3_r` (`CubeBlock`), and the character of each block is read off the character table of
the cube group (Figure `fig:mt-s4-characters`, `cubeCharTable`) at the class of each rotation
(`cubeClassOf`), as the book's proof reads it (`cubeChar`); the dimension `d_ρ` of a block is its
character at the identity. A sign response is given by the set `D` of blocks on which it is
`-1` (`signResponse`), and its kernel is that of Definition 11.7,
`k = (1/|G|) Σ_ρ r(ρ) d_ρ χ_ρ` (`responseKernel`). A kernel "lies in `R₈`" when each of its values
does (`Exact.R8C`).
-/

namespace Artform

/-- The five blocks of the cube group form a finite type. -/
instance CubeBlock.fintype : Fintype CubeBlock where
  elems := {.one, .sign, .two, .threeS, .threeR}
  complete x := by cases x <;> simp

namespace Statement

/-- **Proposition 11.8** (six native sign reads on the cube group). Allowing either sign on the
trivial block, of the thirty nonconstant sign assignments on `S₄`, exactly six have kernels in
`R₈`: `D = {3_r}`, `{3_s}`, `{3_r, 3_s}` and their complements. Complementing `D` negates the whole
kernel. Thus exactly three nonidentity responses obey the normalization `r(1) = 1` of
Definition 11.7: the three displayed sets. For `D = {3_r, 3_s}` the kernel is `-1/2` at the
identity, `+1/2` at each of the three half-turns about face axes, and zero elsewhere. For a single
triplet it is `±1/4` on the sixteen elements that are not third-turns.

A sign assignment is the set `D` of blocks with `r = -1`; it is nonconstant when `D` is neither
empty nor all five blocks, and the identity response is `D = ∅`. The last conjunct also records
that the kernel of a single triplet vanishes on the third-turns, as the book's proof computes. -/
@[book "prop:mt-native-reads"]
def mtNativeReads : Prop :=
  let k : Finset CubeBlock → cubeGroup → ℂ := fun D =>
    responseKernel cubeChar (fun ρ => cubeCharTable ρ .identity) (signResponse D)
  let native : Finset CubeBlock → Prop := fun D => ∀ g, k D g ∈ Exact.R8C
  let six : Finset (Finset CubeBlock) :=
    {{.threeR}, {.threeS}, {.threeR, .threeS}, {.threeR}ᶜ, {.threeS}ᶜ, {.threeR, .threeS}ᶜ}
  (Finset.univ.filter fun D : Finset CubeBlock => D ≠ ∅ ∧ D ≠ Finset.univ).card = 30 ∧
  (∀ D : Finset CubeBlock, D ≠ ∅ → D ≠ Finset.univ → (native D ↔ D ∈ six)) ∧
  six.card = 6 ∧
  (∀ (D : Finset CubeBlock) (g : cubeGroup), k Dᶜ g = -k D g) ∧
  (∀ D : Finset CubeBlock, (D ≠ ∅ ∧ CubeBlock.one ∉ D ∧ native D) ↔
    D ∈ ({{.threeR}, {.threeS}, {.threeR, .threeS}} : Finset (Finset CubeBlock))) ∧
  (∀ g : cubeGroup, k {.threeR, .threeS} g =
    if g = 1 then -1 / 2 else if cubeClassOf g = .faceHalfTurn then 1 / 2 else 0) ∧
  Nat.card {g : cubeGroup // cubeClassOf g = .faceHalfTurn} = 3 ∧
  (∀ D ∈ ({{.threeR}, {.threeS}} : Finset (Finset CubeBlock)), ∀ g : cubeGroup,
    (cubeClassOf g ≠ .vertexThirdTurn → k D g = 1 / 4 ∨ k D g = -1 / 4) ∧
    (cubeClassOf g = .vertexThirdTurn → k D g = 0)) ∧
  Nat.card {g : cubeGroup // cubeClassOf g ≠ .vertexThirdTurn} = 16

end Statement

end Artform
