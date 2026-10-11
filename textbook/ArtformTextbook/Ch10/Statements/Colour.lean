import ArtformTextbook.Ch10.Defs.Colour

/-!
# Statements of Chapter 10: colour and triality

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open scoped TensorProduct

/-- **Proposition 10.1** (the colourless three-quark state). Let `g ∈ GL(3, ℂ)` act on
`V ⊗ V ⊗ V` by `g ⊗ g ⊗ g`. Then `(g ⊗ g ⊗ g) ε = det(g) ε`. Hence `ε` is fixed by `g` if and
only if `det g = 1`, and contraction with `ε` is an intertwiner in the sense of
Definition 5.31 for a group `G ≤ GL(3, ℂ)` exactly when `G ≤ SL(3, ℂ)`. Here `G` acts on each
of the three arguments by its triplet, and `SL(3, ℂ)` is the image of the special linear group
in `GL(3, ℂ)`. -/
@[book "prop:mp-epsilon"]
def mpEpsilon : Prop :=
  (∀ g : GL (Fin 3) ℂ,
    Colour.tensorCube g Colour.epsilon = (g : Matrix (Fin 3) (Fin 3) ℂ).det • Colour.epsilon) ∧
  (∀ g : GL (Fin 3) ℂ,
    Colour.tensorCube g Colour.epsilon = Colour.epsilon ↔ (g : Matrix (Fin 3) (Fin 3) ℂ).det = 1) ∧
  (∀ G : Subgroup (GL (Fin 3) ℂ),
    IsIntertwiner (fun _ : Fin 3 => Colour.triplet G) Colour.contraction ↔
      G ≤ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) ℂ →* GL (Fin 3) ℂ).range)

/-- **Proposition 10.2** (triality). The centre of `SU(3)` is `{I, ωI, ω²I}` with
`ω = e^{2πi/3}`. On a state of `q` quarks and `q̄` antiquarks the element `ωI` acts as
multiplication by `ω^{q - q̄}`. A colourless state therefore has `q - q̄ ≡ 0 (mod 3)`. Here a
state of `q` quarks and `q̄` antiquarks is a vector of `V^{⊗q} ⊗ V̄^{⊗q̄}`, on which a matrix acts
by itself on each quark and by its complex conjugate on each antiquark, and a colourless state
is a nonzero such vector fixed by every element of `SU(3)`. -/
@[book "prop:mp-triality"]
def mpTriality : Prop :=
  (∀ M : Matrix (Fin 3) (Fin 3) ℂ,
    (∃ g ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin 3) ℂ),
        (g : Matrix (Fin 3) (Fin 3) ℂ) = M) ↔
      M = 1 ∨ M = Colour.omega • 1 ∨ M = Colour.omega ^ 2 • 1) ∧
  (∀ (q qbar : ℕ) (x : Colour.QuarkStates q qbar),
    Colour.act q qbar (Colour.omega • 1) x = Colour.omega ^ ((q : ℤ) - qbar) • x) ∧
  (∀ (q qbar : ℕ) (x : Colour.QuarkStates q qbar), x ≠ 0 →
    (∀ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ, Colour.act q qbar g x = x) →
      (q : ℤ) - qbar ≡ 0 [ZMOD 3])

end Artform.Statement
