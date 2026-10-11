import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Dirac.Def
import ArtformTextbook.Ch03.Statements.Measure

/-!
# Measures on finite patterns (Propositions 3.37 and 3.40, Theorem 3.39)

Finite Fubini–Tonelli is the reassociation of a finite double sum; monotone convergence is
Mathlib's `lintegral_tendsto_of_tendsto_of_monotone`, applied to the functions read in `[0, ∞]`;
and an invariant measure gives `μ({g x}) = μ(g {x}) = μ({x})`.
-/

namespace Artform

open scoped ENNReal Pointwise
open MeasureTheory Filter Topology

/-- Reassociating a finite double sum with product weights, in any commutative semiring. -/
private theorem sum_prod_weights {R : Type*} [CommSemiring R] {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → R) (v : Y → R) (h : X × Y → R) :
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ x, w x * ∑ y, h (x, y) * v y ∧
    ∑ p : X × Y, h p * w p.1 * v p.2 = ∑ y, v y * ∑ x, h (x, y) * w x := by
  constructor
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

/-- **Proposition 3.37** (finite Fubini–Tonelli): row-first and column-first evaluation of a
finite weighted double sum agree. -/
@[book "nolabel:03-pattern-geometry:finite-fubini-tonelli"]
theorem finiteFubiniTonelli : Statement.finiteFubiniTonelli :=
  ⟨fun _ _ _ _ w v h => sum_prod_weights w v h, fun _ _ _ _ w v h => sum_prod_weights w v h⟩

/-- **Theorem 3.39** (monotone convergence). -/
@[book "nolabel:03-pattern-geometry:monotone-convergence"]
theorem monotoneConvergence : Statement.monotoneConvergence := by
  intro Ω _ μ f F _ hmono hmeas hlim
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hmeas n).ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun x =>
      monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n x))
    (Eventually.of_forall fun x => (ENNReal.continuous_ofReal.tendsto (F x)).comp (hlim x))

/-- **Proposition 3.40**. An invariant atomic measure is constant on each `G`-orbit. -/
@[book "prop:invariant-measure-orbits"]
theorem invariantMeasureOrbits : Statement.invariantMeasureOrbits := by
  intro Ω _ _ G _ _ μ hinv x y hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  rw [← Set.smul_set_singleton, hinv g {x} (MeasurableSet.singleton x)]

/-! ## Non-vacuity -/

/-- The atomic measure with weight `w x` at each point `x`: `μ(A) = Σ_{x ∈ A} w_x`. -/
private noncomputable def atomicMeasure {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] (w : Ω → ℝ≥0∞) :
    Measure Ω :=
  ∑ i, w i • Measure.dirac i

/-- Weights constant on orbits give an invariant atomic measure (the converse that the book
states after Proposition 3.40). -/
private theorem atomicMeasure_smul_set {Ω G : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Group G] [MulAction G Ω] (w : Ω → ℝ≥0∞)
    (hw : ∀ (g : G) x, w (g • x) = w x) (g : G) (A : Set Ω) :
    atomicMeasure w (g • A) = atomicMeasure w A := by
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hgA : MeasurableSet (g • A) := (g • A).toFinite.measurableSet
  rw [atomicMeasure, Measure.finsetSum_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hgA,
    smul_eq_mul]
  refine (Equiv.sum_comp (MulAction.toPerm g) _).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  change w (g • j) * (g • A).indicator 1 (g • j) = w j * A.indicator 1 j
  rw [hw]
  by_cases hj : j ∈ A
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem (Set.smul_mem_smul_set hj)]
    rfl
  · rw [Set.indicator_of_notMem hj,
      Set.indicator_of_notMem fun h => hj (Set.smul_mem_smul_set_iff.mp h)]

/-- Proposition 3.37 on the two-by-three grid of the book's product-measure figure: row weights
`(1, 2)`, column weights `(1, 3, 2)` and `h = 1`; the weighted sum is `(1 + 2)(1 + 3 + 2)`. -/
example : ∑ p : Fin 2 × Fin 3, (1 : ℝ) * ![1, 2] p.1 * ![1, 3, 2] p.2 = 18 :=
  (finiteFubiniTonelli.2 (Fin 2) (Fin 3) ![1, 2] ![1, 3, 2] fun _ => 1).1.trans (by
    simp [Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num)

/-- The values `f = (1, 3, 2, 4)` on the four triangles `a, b, c, d` of the tetrakis square,
approached from below by `f_n = (1 - 1/(n+1)) f`. -/
private noncomputable def approxValues (n : ℕ) (x : Fin 4) : ℝ :=
  (1 - 1 / ((n : ℝ) + 1)) * ![1, 3, 2, 4] x

/-- Theorem 3.39 on the four triangles of the tetrakis square, with the weights `(2, 1, 4, 1)`
of total `8`: the sequence `f_n` meets the hypotheses. -/
example : 0 ≤ approxValues 0 ∧ (∀ n, approxValues n ≤ approxValues (n + 1)) ∧
    (∀ n, Measurable (approxValues n)) ∧
    (∀ x, Tendsto (fun n => approxValues n x) atTop (𝓝 (![1, 3, 2, 4] x))) ∧
    atomicMeasure (![2, 1, 4, 1] : Fin 4 → ℝ≥0∞) Set.univ = 8 := by
  have hf : ∀ x : Fin 4, (0 : ℝ) ≤ ![1, 3, 2, 4] x := by
    intro x
    fin_cases x <;> norm_num
  refine ⟨fun x => by simp [approxValues], fun n x => ?_, fun n => measurable_of_countable _,
    fun x => ?_, ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ (hf x)
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : 1 / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h1 (by linarith)
    push_cast
    linarith
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [approxValues] using h.mul_const (![1, 3, 2, 4] x)
  · rw [atomicMeasure, Measure.finsetSum_apply]
    simp [Fin.sum_univ_four]
    norm_num

/-- `k` quarter turns of the tetrakis square's four triangles `a, b, c, d` (positions `0` to `3`)
about its centre `z` (position `4`), as in the book's figure of invariant measures. -/
private def quarterTurns (k : ZMod 4) (i : Fin 5) : Fin 5 :=
  if h : (i : ℕ) < 4 then ⟨((i : ℕ) + k.val) % 4, by omega⟩ else i

/-- The rotation group `C₄` acting on `a, b, c, d, z`. -/
@[instance_reducible] private def quarterTurnAction :
    MulAction (Multiplicative (ZMod 4)) (Fin 5) where
  smul g i := quarterTurns (Multiplicative.toAdd g) i
  one_smul i := by
    revert i
    decide
  mul_smul g h i := by
    change quarterTurns (Multiplicative.toAdd (g * h)) i =
      quarterTurns (Multiplicative.toAdd g) (quarterTurns (Multiplicative.toAdd h) i)
    rw [toAdd_mul]
    generalize Multiplicative.toAdd g = a
    generalize Multiplicative.toAdd h = b
    revert a b i
    decide

attribute [local instance] quarterTurnAction

/-- Weight `2` on the orbit `{a, b, c, d}` and `5` on the fixed centre `z`. -/
private def orbitWeights (i : Fin 5) : ℝ≥0∞ := if (i : ℕ) < 4 then 2 else 5

/-- Proposition 3.40: the weights `2` on `{a, b, c, d}` and `5` on `z` give a measure invariant
under the quarter turns. -/
example : ∀ (g : Multiplicative (ZMod 4)) (A : Set (Fin 5)), MeasurableSet A →
    atomicMeasure orbitWeights (g • A) = atomicMeasure orbitWeights A := by
  intro g A _
  refine atomicMeasure_smul_set orbitWeights (fun g x => ?_) g A
  have h : ((g • x : Fin 5) : ℕ) < 4 ↔ (x : ℕ) < 4 := by
    change ((quarterTurns (Multiplicative.toAdd g) x : Fin 5) : ℕ) < 4 ↔ (x : ℕ) < 4
    generalize Multiplicative.toAdd g = a
    revert a x
    decide
  simp only [orbitWeights, h]

end Artform
