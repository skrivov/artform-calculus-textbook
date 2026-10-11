import ArtformTextbook.Ch12.Defs.Icosahedron

/-!
# The statements of Chapter 12

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open Real Matrix

/-- **Proposition 12.8** (the sixty rotations). Every vertex `v` of the
icosahedron has `v·v = φ + 2`, and with respect to `v` the twelve vertices are
`v` itself, five neighbours with `v·w = φ`, five vertices with `v·w = −φ`, and
the antipode `−v`. A rotation of the icosahedron is determined by the images
of one vertex and one of its neighbours, so there are at most `12·5 = 60`. For
each pair of neighbours `(w₁, w₂)` the matrix that carries the frame
`(v₁, v₂, v₁ × v₂)` to `(w₁, w₂, w₁ × w₂)` is a rotation with entries in
`½ℤ[φ]`, and all sixty carry the vertex set to itself. Their traces are `3`
once, `−1` fifteen times, `0` twenty times, `φ` twelve times and `1 − φ` twelve
times. -/
@[book "prop:mm-icosahedron"]
def sixtyRotations : Prop :=
  icoVertices.ncard = 12 ∧
  (∀ v ∈ icoVertices,
    v ⬝ᵥ v = goldenRatio + 2 ∧
    (∀ w ∈ icoVertices, w = v ∨ v ⬝ᵥ w = goldenRatio ∨ v ⬝ᵥ w = -goldenRatio ∨ w = -v) ∧
    {w | w ∈ icoVertices ∧ v ⬝ᵥ w = goldenRatio}.ncard = 5 ∧
    {w | w ∈ icoVertices ∧ v ⬝ᵥ w = -goldenRatio}.ncard = 5 ∧
    -v ∈ icoVertices) ∧
  (∀ v₁ ∈ icoVertices, ∀ v₂ ∈ icoVertices, v₁ ⬝ᵥ v₂ = goldenRatio →
    ∀ M ∈ icoRotations, ∀ N ∈ icoRotations,
      M.mulVec v₁ = N.mulVec v₁ → M.mulVec v₂ = N.mulVec v₂ → M = N) ∧
  (∀ v₁ ∈ icoVertices, ∀ v₂ ∈ icoVertices, v₁ ⬝ᵥ v₂ = goldenRatio →
    ∀ w₁ ∈ icoVertices, ∀ w₂ ∈ icoVertices, w₁ ⬝ᵥ w₂ = goldenRatio →
      (∃! M : Matrix (Fin 3) (Fin 3) ℝ,
        M.mulVec v₁ = w₁ ∧ M.mulVec v₂ = w₂ ∧ M.mulVec (v₁ ⨯₃ v₂) = w₁ ⨯₃ w₂) ∧
      ∀ M : Matrix (Fin 3) (Fin 3) ℝ,
        M.mulVec v₁ = w₁ → M.mulVec v₂ = w₂ → M.mulVec (v₁ ⨯₃ v₂) = w₁ ⨯₃ w₂ →
          M ∈ icoRotations ∧ ∀ i j, ∃ a b : ℤ, M i j = (a + b * goldenRatio) / 2) ∧
  icoRotations.ncard = 60 ∧
  ∀ t : ℝ, {M | M ∈ icoRotations ∧ M.trace = t}.ncard =
    if t = 3 then 1 else if t = -1 then 15 else if t = 0 then 20
    else if t = goldenRatio then 12 else if t = 1 - goldenRatio then 12 else 0

end Artform.Statement
