import ArtformTextbook.Exact.R8

/-!
# Contents on the native coefficient ring (Section 7.6)

Section 7.6 (`qr:probability`) asks which probability law a complete prepared column carries.
Its comparisons, given in outline, reduce the law to one real function `M` on the formal
coefficients `R₈` (Definition 7.1), a *content*: the probability of a complete label is the
content of its coefficient. The content is grade-compatible, `2 M(x/√2) = M(x)`, and the native
operations confined to a retained pair give the mixer identity and the quarter turn. With
calibration and nonnegativity these leave the family `M_λ(a) = λ|a|² + (1 − λ)|σ(a)|²`
(`eq:qr-content-family`), where `σ` is the arithmetic automorphism with `σ(√2) = −√2` and
`σ(i) = i`.

Here a content is a function `R8 → ℝ` on the exact ring of `Exact/R8.lean`, `|a|²` is
`Complex.normSq` of the numerical reading `Q4.toComplex a`, and the identities are bundled as
`IsNativeContent`. The coefficient `(1 + ζ)/2`, with `ζ = (1 + i)/√2`, is the zero coefficient
of the preparation `H, T, H` from `|0⟩` (Figure `fig:qr-hth`); duplication and oriented
retention are read on it.
-/

namespace Artform.NativeLaw

open Artform.Exact

/-- `√2`, as a coefficient of `R₈`: the coordinates `(a, b, c, d) = (0, 1, 0, 0)`. -/
def sqrtTwo : R8 := ⟨⟨0, 1, 0, 0⟩, isDyadic_zero, isDyadic_one, isDyadic_zero, isDyadic_zero⟩

/-- `1/√2 = √2/2`, as a coefficient of `R₈`. Dividing a coefficient by `√2` is multiplying it
by `invSqrtTwo`. -/
def invSqrtTwo : R8 :=
  ⟨⟨0, 1 / 2, 0, 0⟩, isDyadic_zero, isDyadic_half, isDyadic_zero, isDyadic_zero⟩

/-- The quarter-turn `i`, as a coefficient of `R₈`. -/
def I : R8 := ⟨⟨0, 0, 1, 0⟩, isDyadic_zero, isDyadic_zero, isDyadic_one, isDyadic_zero⟩

/-- `1/2`, as a coefficient of `R₈`. -/
def half : R8 := ⟨⟨1 / 2, 0, 0, 0⟩, isDyadic_half, isDyadic_zero, isDyadic_zero, isDyadic_zero⟩

/-- The phase mark `ζ = (1 + i)/√2`, the eighth root of unity of Chapter 7. -/
def zeta : R8 := (1 + I) * invSqrtTwo

/-- The zero coefficient `a = (1 + ζ)/2` of the preparation `H, T, H` from `|0⟩`
(Figure `fig:qr-hth`): the tally of the two histories that end at zero. -/
def hthZero : R8 := (1 + zeta) * half

/-- The arithmetic automorphism `σ` of `ℚ(√2, i)` (Section 7.6), with `σ(√2) = −√2` and
`σ(i) = i` (`sigma_sqrtTwo`, `sigma_I`). On coordinates it takes `a + b√2 + i(c + d√2)` to
`a − b√2 + i(c − d√2)`. It differs from conjugation, which keeps `√2` and reverses `i`. It keeps
`R₈` (`sigma_mem_R8`). -/
def sigma : Q4 ≃+* Q4 where
  toFun x := ⟨x.a, -x.b, x.c, -x.d⟩
  invFun x := ⟨x.a, -x.b, x.c, -x.d⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> ring

@[simp] theorem sigma_a (x : Q4) : (sigma x).a = x.a := rfl
@[simp] theorem sigma_b (x : Q4) : (sigma x).b = -x.b := rfl
@[simp] theorem sigma_c (x : Q4) : (sigma x).c = x.c := rfl
@[simp] theorem sigma_d (x : Q4) : (sigma x).d = -x.d := rfl

/-- `σ(√2) = −√2`. -/
theorem sigma_sqrtTwo : sigma (sqrtTwo : Q4) = -(sqrtTwo : Q4) := by
  ext <;> simp [sqrtTwo]

/-- `σ(i) = i`. -/
theorem sigma_I : sigma (I : Q4) = (I : Q4) := by
  ext <;> simp [I]

/-- `σ` keeps `R₈`. -/
theorem sigma_mem_R8 {x : Q4} (hx : x ∈ R8) : sigma x ∈ R8 := by
  obtain ⟨ha, hb, hc, hd⟩ := hx
  exact ⟨ha, hb.neg, hc, hd.neg⟩

/-- The family of contents `M_λ(a) = λ|a|² + (1 − λ)|σ(a)|²` (`eq:qr-content-family`). Here
`|a|²` is the squared modulus of the numerical reading of `a`, and `σ` is the arithmetic
automorphism `sigma`. `M_1(a) = |a|²` is the usual squared law, and `M_0(a) = |σ(a)|²` is the
other arithmetic reading. -/
noncomputable def contentFamily (lam : ℝ) (x : R8) : ℝ :=
  lam * Complex.normSq (Q4.toComplex x) + (1 - lam) * Complex.normSq (Q4.toComplex (sigma x))

/-- The identities of a native content `M` on the formal coefficients `R₈` (Section 7.6):
splitting, `2 M(x/√2) = M(x)`; the mixer identity,
`M((x + y)/√2) + M((x − y)/√2) = M(x) + M(y)`; the quarter turn, `M(ix) = M(x)`; calibration,
`M(1) = 1`; and nonnegativity.

The book derives them, in outline, from the operational assumptions: calibration is "Certainty
is already constrained" (from V, Z, AE, D₂ and N₁), and splitting, the mixer identity and the
quarter turn are "From complete laws to coefficient content" (from AE, Z and calibration),
which also shows that the probability of a complete label is `M` of its coefficient.
Nonnegativity holds because `M` is built from probabilities. Here the identities are hypotheses,
the interface to that derivation. `M(0) = 0` and `M(−x) = M(x)` are not assumed: they follow. -/
structure IsNativeContent (M : R8 → ℝ) : Prop where
  /-- Splitting fixes the scale: `2 M(x/√2) = M(x)`. -/
  splitting : ∀ x : R8, 2 * M (x * invSqrtTwo) = M x
  /-- The mixer identity: `M((x + y)/√2) + M((x − y)/√2) = M(x) + M(y)`. -/
  mixer : ∀ x y : R8, M ((x + y) * invSqrtTwo) + M ((x - y) * invSqrtTwo) = M x + M y
  /-- The quarter turn: `M(ix) = M(x)`. -/
  quarterTurn : ∀ x : R8, M (I * x) = M x
  /-- Calibration: the coefficient `1` has content `1`. -/
  calibration : M 1 = 1
  /-- Nonnegativity. -/
  nonneg : ∀ x : R8, 0 ≤ M x

end Artform.NativeLaw
