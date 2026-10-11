import ArtformTextbook.Ch07.Defs.Woven

/-!
# Statements of Chapter 7: a kept count is woven

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Corollary 7.3** (a kept count is woven: coherent laws). Let a script keep a count: every
step `x → x'` with `U[x', x] ≠ 0` keeps it. Then each such step has a weave along every
no-signalling halo of the script.

The script is given by its table `U` on the basis labels of finitely many binary cells, its
coefficients read as complex numbers. The count and the weave are those of Definition 5.43, on
the frame of the binary cells, and a no-signalling halo of the script is that of Section 7.4:
for every set `V` of cells, the weights of the report of `V` depend only on the input label on
`H(V)`. -/
@[book "cor:qr-woven"]
def qrWoven : Prop :=
  ∀ (Cell : Type) [Fintype Cell] (U : ScriptTable Cell) (c : Count (binaryCells Cell)),
    (∀ x x' : BasisLabel Cell, U.coeff x' x ≠ 0 → c.N x' = c.N x) →
    ∀ H : Cell → Set Cell, U.NoSignalling H →
      ∀ x x' : BasisLabel Cell, U.coeff x' x ≠ 0 → Nonempty (Weave H c x x')

end Artform.Statement
