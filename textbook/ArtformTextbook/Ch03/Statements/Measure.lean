import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import ArtformTextbook.Ch03.Defs.Measure

/-!
# Statements of Chapter 3: measures

Each statement of the book is a proposition here, tagged with the book's label. Its proof, in
`Ch03/Measure.lean`, is a theorem whose type is exactly this proposition.
-/

namespace Artform.Statement

open scoped ENNReal Pointwise

/-- **Proposition 3.37** (finite Fubini–Tonelli). For a nonnegative function
`h : X × Y → [0, ∞]` on finite spaces with atomic weights `w_x` and `v_y`,
`Σ_{x,y} h(x,y) w_x v_y = Σ_x w_x (Σ_y h(x,y) v_y) = Σ_y v_y (Σ_x h(x,y) w_x)`.
For real-valued `h`, the same holds whenever the finite weighted sum of `|h|` is finite.

The weights of the first part are taken in `[0, ∞]` and those of the second in `ℝ`. For finitely
many real values the weighted sum of `|h|` is always finite, so the second part has no
hypothesis. -/
@[book "prop:finite-fubini-tonelli"]
def finiteFubiniTonelli : Prop :=
  (∀ (X Y : Type) [Fintype X] [Fintype Y] (w : X → ℝ≥0∞) (v : Y → ℝ≥0∞) (h : X × Y → ℝ≥0∞),
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ x, w x * ∑ y, h (x, y) * v y ∧
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ y, v y * ∑ x, h (x, y) * w x) ∧
  (∀ (X Y : Type) [Fintype X] [Fintype Y] (w : X → ℝ) (v : Y → ℝ) (h : X × Y → ℝ),
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ x, w x * ∑ y, h (x, y) * v y ∧
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ y, v y * ∑ x, h (x, y) * w x)

/-- **Theorem 3.39** (monotone convergence). If `0 ≤ f₁ ≤ f₂ ≤ ⋯` are measurable and
`f_n(x) → f(x)`, then `lim_{n → ∞} ∫ f_n dμ = ∫ f dμ`.

The functions are real-valued and measurable in the sense of Definition 3.38; the integral of a
nonnegative function is the supremum of the integrals of simple functions below it, Mathlib's
`∫⁻`, applied to the function read in `[0, ∞]`. The sequence is indexed from `0`. -/
@[book "thm:monotone-convergence"]
def monotoneConvergence : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (f : ℕ → Ω → ℝ) (F : Ω → ℝ),
    0 ≤ f 0 → (∀ n, f n ≤ f (n + 1)) → (∀ n, Measurable (f n)) →
    (∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (F x))) →
    Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) Filter.atTop
      (nhds (∫⁻ x, ENNReal.ofReal (F x) ∂μ))

/-- **Proposition 3.40**. An invariant atomic measure is constant on each `G`-orbit: if a group
`G` acts on the measurable space and `μ(gA) = μ(A)` for every `g` and every measurable `A`, then
the weight `μ({y})` of every point `y` of the orbit of `x` is `μ({x})`.

Points are measurable, as on the power set where atomic measures live. The book's group is
finite; Lean states it for every group and every measure. -/
@[book "prop:invariant-measure-orbits"]
def invariantMeasureOrbits : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (G : Type) [Group G]
    [MulAction G Ω] (μ : MeasureTheory.Measure Ω),
    (∀ (g : G) (A : Set Ω), MeasurableSet A → μ (g • A) = μ A) →
    ∀ x, ∀ y ∈ MulAction.orbit G x, μ {y} = μ {x}

end Artform.Statement
