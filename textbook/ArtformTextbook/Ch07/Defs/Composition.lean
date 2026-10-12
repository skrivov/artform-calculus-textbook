import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import ArtformTextbook.Meta.Book

/-!
# Coherent composition (*From applications to a coherent law*)

Definition 7.2: two consecutive finite phases `U` and `V`, matrices with
outputs as rows and inputs as columns, compose to `(VU)[z, x] = Σ_y V[z, y]
U[y, x]`; a finite history `h = (x₀, …, x_n)` has the coefficient
`Π_{t=1}^n U_t[x_t, x_{t-1}]`; and the coefficient at a complete final endpoint
`z` is the sum of these products over the histories ending at `z`, a row over
the clock with its last entry fixed.

The coefficients lie in any commutative semiring; the book's are in the native
coefficient ring of Definition 7.1.
-/

namespace Artform

variable {X K : Type*} [Fintype X] [CommSemiring K]

/-- **Definition 7.2** (coherent composition of two phases):
`(VU)[z, x] = Σ_y V[z, y] U[y, x]`. -/
@[book "qr:coherent-composition"]
def composePhases (V U : Matrix X X K) : Matrix X X K := V * U

theorem composePhases_apply (V U : Matrix X X K) (z x : X) :
    composePhases V U z x = ∑ y, V z y * U y x :=
  Matrix.mul_apply

/-- **Definition 7.2** (coefficient of a history): `Π_{t=1}^n U_t[x_t, x_{t-1}]`
for the history `h = (x₀, …, x_n)` through the phases `U₁, …, U_n`. -/
@[book "qr:coherent-composition"]
def historyCoeff {n : ℕ} (U : Fin n → Matrix X X K) (h : Fin (n + 1) → X) : K :=
  ∏ t : Fin n, U t (h t.succ) (h t.castSucc)

/-- **Definition 7.2** (coefficient at a complete final endpoint): the sum of
the coefficients of the histories ending at `z`. -/
@[book "qr:coherent-composition"]
def endpointCoeff [DecidableEq X] {n : ℕ} (U : Fin n → Matrix X X K) (z : X) : K :=
  ∑ h : {h : Fin (n + 1) → X // h (Fin.last n) = z}, historyCoeff U h

/-! ## Non-vacuity -/

/-- Through one phase, the coefficient of the history `(x, z)` is `U[z, x]`. -/
example (U : Matrix X X K) (x z : X) :
    historyCoeff (fun _ : Fin 1 => U) ![x, z] = U z x := by
  simp [historyCoeff]

end Artform
