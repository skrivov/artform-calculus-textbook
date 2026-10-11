import ArtformTextbook.Ch04.Statements

/-!
# Counting becomes a probability law (Section 4.4)

The proof of Proposition 4.2. Both sets carry the σ-algebra `⊤` of all their
subsets, so the report map is measurable and every event is measurable. The
push-forward of normalized counting then gives each event `C` the mass of its
inverse image, `|f⁻¹(C)| / |Ω|`, and the event `Y` gets `|Ω| / |Ω| = 1`.
-/

namespace Artform

open MeasureTheory
open scoped ENNReal

/-- **Proposition 4.2** (Counting retained alternatives). For a finite
nonempty set `Ω` of equal-weight retained alternatives, a finite set `Y`, and a
report map `f : Ω → Y`, normalized counting pushes forward to
`P_Y(C) = |f⁻¹(C)| / |Ω|`, `C ⊆ Y`. This is a probability measure on the finite
power set of `Y`. -/
@[book "probbook:count-law"]
theorem countLaw : Statement.countLaw := by
  intro Ω Y _ _ _ f P
  let mΩ : MeasurableSpace Ω := ⊤
  let mY : MeasurableSpace Y := ⊤
  -- Every map and every set is measurable, so `P(C)` counts the inverse image of `C`.
  have hP : ∀ C : Set Y, P C = (Nat.card (f ⁻¹' C) : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞) := by
    intro C
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
      Measure.smul_apply, smul_eq_mul, Measure.count_apply MeasurableSpace.measurableSet_top,
      ENNReal.div_eq_inv_mul, Nat.card_coe_set_eq, ← (Set.toFinite _).cast_ncard_eq,
      ENat.toENNReal_coe]
  refine ⟨⟨?_⟩, hP⟩
  rw [hP, Set.preimage_univ, Nat.card_univ, Nat.card_eq_fintype_card]
  exact ENNReal.div_self (by simp) (by simp)

/-! ## Non-vacuity -/

/-- The book's example (Section 4.4). Fix the old exit `x`. The four complete
assignments `ab` of the two response cells each get one unit of mass, and the
next-exit report is `f_x(a, b) = x ⊕ ab`. The words `00`, `01`, `10` report `x`
and the word `11` reports `1 - x`: fibres of sizes `3` and `1`, which give the
probabilities `3/4` and `1/4`. -/
example (x : Fin 2) :
    letI : MeasurableSpace (Fin 2 × Fin 2) := ⊤
    letI : MeasurableSpace (Fin 2) := ⊤
    let P : Measure (Fin 2) := Measure.map (fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2)
      ((Fintype.card (Fin 2 × Fin 2) : ℝ≥0∞)⁻¹ • Measure.count)
    IsProbabilityMeasure P ∧ P {x} = 3 / 4 ∧ P {1 - x} = 1 / 4 := by
  -- The fibre over `y` is the set of words `ab` with `x ⊕ ab = y`.
  have hfib : ∀ y : Fin 2, Nat.card ((fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2) ⁻¹' {y}) =
      (Finset.univ.filter fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = y).card := by
    intro y
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext ab
    simp
  have h3 : ∀ x : Fin 2,
      (Finset.univ.filter fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = x).card = 3 := by
    decide
  have h1 : ∀ x : Fin 2,
      (Finset.univ.filter fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = 1 - x).card = 1 := by
    decide
  obtain ⟨hP, hC⟩ := countLaw (Fin 2 × Fin 2) (Fin 2) fun ab => x + ab.1 * ab.2
  refine ⟨hP, ?_, ?_⟩
  · rw [hC, hfib, h3]
    simp
  · rw [hC, hfib, h1]
    simp

end Artform
