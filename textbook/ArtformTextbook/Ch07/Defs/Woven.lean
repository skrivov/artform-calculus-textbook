import Mathlib.Basic.Complex.Basic
import ArtformTextbook.Ch05.Defs.Patterns

/-!
# Scripts and their no-signalling halos (Sections 7.3 and 7.4)

Chapter 7 fixes a finite inventory of named binary cells; a basis label is a complete
assignment of `0` or `1` to every cell (Section 7.3). A script's legal applications, each with
its coefficient, are summed into its table: `U[y, x]` is the sum of the coefficients of the
applications from the input label `x` that reach the output label `y` (Section 7.4). A script
is taken here by its table, the coefficients read as complex numbers, the numerical reading of
the ring `R₈` (Definition 7.1); Corollary 7.3 uses nothing else of a script.

What a script may show on a set `V` of cells, from a basis label `x`, is the report of `V`,
with the weights of the report rule: the weight of a table `τ` on `V` is `Σ |U[z, x]|²` over the
complete labels `z` that show `τ` on `V`. A no-signalling halo of a script is a halo for which
those weights depend only on the values of `x` on `H(V)` (Section 7.4, after Definition 5.41).
Counts and weaves are those of Definition 5.43, on the frame of the binary cells.
-/

namespace Artform

/-- The frame of a finite inventory of named binary cells (Section 7.3): the value `0` or `1`
at every cell. -/
abbrev binaryCells (Cell : Type) : Presentation := uniformFrame Cell (Fin 2)

/-- A basis label: a complete assignment of `0` or `1` to every cell (Section 7.3). -/
abbrev BasisLabel (Cell : Type) : Type := (binaryCells Cell).Table

/-- The table of a script (Section 7.4): for each input label `x` and output label `y`, the
coefficient `U[y, x]`, the sum of the coefficients of the legal applications from `x` that
reach `y`; outputs are rows and inputs columns. The coefficients are read as complex numbers,
the numerical reading of `R₈`. -/
structure ScriptTable (Cell : Type) where
  /-- The coefficient `U[y, x]` from the input label `x` to the output label `y`. -/
  coeff : BasisLabel Cell → BasisLabel Cell → ℂ

namespace ScriptTable

variable {Cell : Type} [Fintype Cell]

open Classical in
/-- What a script may show on a set `V` of cells from the basis label `x` (Section 7.4): the
report of `V`, with the weights of the report rule; the weight of a table `τ` on `V` is
`Σ |U[z, x]|²` over the complete labels `z` that show `τ` on `V`. -/
noncomputable def showWeight (U : ScriptTable Cell) (x : BasisLabel Cell) (V : Set Cell)
    (τ : (p : V) → Fin 2) : ℝ :=
  ∑ z : BasisLabel Cell, if restrictTo V z = τ then Complex.normSq (U.coeff z x) else 0

/-- **Definition 5.41** (no-signalling halo), for a script (Section 7.4): `H` is a
no-signalling halo of the script when, for every set `V` of cells, the weights with which it
shows tables on `V` depend only on the values of the input label on the cells `H(V)`. -/
@[book "def:no-signalling"]
def NoSignalling (U : ScriptTable Cell) (H : Cell → Set Cell) : Prop :=
  ∀ (V : Set Cell) (x z : BasisLabel Cell), (∀ p ∈ haloOf H V, x p = z p) →
    U.showWeight x V = U.showWeight z V

end ScriptTable

end Artform
