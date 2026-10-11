import ArtformTextbook.Ch03.Defs.Cube

/-!
# Statements of Chapter 3: the cube

Each statement of the book is a proposition here, tagged with the book's label. Its proof, in
`Ch03/Cube.lean`, is a theorem whose type is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 3.4** (cube boundary assembled from squares). Six square instances with the
coordinate-face gluing data assemble to an instance of `CubeBoundary`. Adding the declared cubical
three-cell along its whole boundary gives an instance of `Cube` with cell counts `(8, 12, 6, 1)`.

The gluing data are, for each of the six coordinate faces `f`, a chart: a structural bijection
`χ_f` naming the cells of the square `S_f` by the triple addresses of the closure of `f`. The
squares are joined by identifying cells with the same triple (`CubeAssembly.assemble`), and the
three-cell is attached with the six cells of dimension two as its immediate faces
(`IncidenceCanvas.attachTop`). The counts are the numbers of cells of dimensions `0`, `1`, `2`
and `3`. -/
@[book "prop:cube-assembly-book"]
def cubeAssembly : Prop :=
  ∀ (S : CoordFace → IncidenceCanvas), (∀ f, (S f).IsInstance squareCanvas) →
    ∀ χ : ∀ f, (S f).Iso (faceClosure f),
      (CubeAssembly.assemble S χ).IsInstance cubeBoundaryCanvas ∧
      ((CubeAssembly.assemble S χ).attachTop 2).IsInstance cubeCanvas ∧
      ((CubeAssembly.assemble S χ).attachTop 2).cellCount 0 = 8 ∧
      ((CubeAssembly.assemble S χ).attachTop 2).cellCount 1 = 12 ∧
      ((CubeAssembly.assemble S χ).attachTop 2).cellCount 2 = 6 ∧
      ((CubeAssembly.assemble S χ).attachTop 2).cellCount 3 = 1

end Artform.Statement
