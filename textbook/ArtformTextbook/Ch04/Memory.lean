import Mathlib.Probability.UniformOn
import ArtformTextbook.Ch04.Statements.Memory

/-!
# Why records and fresh preparations matter (Section 4.8)

The proof of Proposition 4.4, along the book's proof. Fix a recorded exit
history `X_0 … X_t = h` of positive probability, ending in `x`. Since the
records survive, the history event is a union of complete pasts. On each
complete past in it the next pair is uniform, so the exit rule gives three
stay patterns and one flip pattern of mass `1/4` each: the past contributes
`K(y | x)` times its own mass to the event `X_{t+1} = y`. Adding over the
countably many complete pasts gives `P(E ∩ {X_{t+1} = y}) = K(y | x) P(E)`.
-/

namespace Artform

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExitClosure

section Levels

variable {Ω S : Type*} [MeasurableSpace Ω] [Countable S] {f : Ω → S}

/-- If every level set of a countably-valued map is an event, then so is the
preimage of every set of its values. -/
lemma measurableSet_preimage_of_countable (hf : ∀ σ, MeasurableSet (f ⁻¹' {σ}))
    (U : Set S) : MeasurableSet (f ⁻¹' U) := by
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion U.to_countable fun σ _ => hf σ

/-- A measure splits over the level sets of a countably-valued map. -/
lemma measure_eq_tsum_levels (hf : ∀ σ, MeasurableSet (f ⁻¹' {σ})) (P : Measure Ω)
    (E : Set Ω) : P E = ∑' σ, P (f ⁻¹' {σ} ∩ E) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun σ => f ⁻¹' {σ}) := by
    intro σ τ hστ
    refine Set.disjoint_left.2 fun ω h1 h2 => hστ ?_
    simp only [mem_preimage, mem_singleton_iff] at h1 h2
    rw [← h1, ← h2]
  have h := measure_iUnion (μ := P.restrict E) hdisj hf
  rw [show (⋃ σ, f ⁻¹' {σ}) = univ by ext ω; simp, Measure.restrict_apply_univ] at h
  rw [h]
  exact tsum_congr fun σ => Measure.restrict_apply (hf σ)

end Levels

/-- `K(y | x)` counts the pairs `ab` with `x ⊕ ab = y`, each with weight `1/4`
(Section 4.6, "derive the matrix from the four rows"). -/
lemma exitTransition_eq_sum (y x : Fin 2) :
    exitTransition y x =
      ∑ _ab ∈ Finset.univ.filter (fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = y),
        (1 / 4 : ℝ≥0∞) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ∀ x y : Fin 2,
      (Finset.univ.filter (fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = y)).card =
        if y = x then 3 else 1 := by decide
  rw [hc, exitTransition]
  split_ifs <;> simp [div_eq_mul_inv]

end ExitClosure

open ExitClosure

/-- **Proposition 4.4** (exit-level closure). Suppose that, conditional on every
positive-probability complete past, the next response pair is uniform on
`B × B`. Suppose the next exit is `x ⊕ ab`, with no further dependence on that
past, and later updates preserve the previous exit records. Then the recorded
exit process has conditional transition law `K(y | x)` of Section 4.6. Its
next-exit law given its recorded history depends only on its current exit. -/
@[book "prob:markov"]
theorem exitLevelClosure : Statement.exitLevelClosure := by
  intro Ω _ P _ N S _ past pair exit hpast hpair hunif hexit hrec
  have key : ∀ t < N, ∀ h : Fin (t + 1) → Fin 2, P (historyEvent exit t h) ≠ 0 →
      ∀ y, P[exit (t + 1) ⁻¹' {y} | historyEvent exit t h] =
        exitTransition y (h (Fin.last t)) := by
    intro t ht h hE y
    set E := historyEvent exit t h with hEdef
    set A := exit (t + 1) ⁻¹' {y} with hAdef
    set x := h (Fin.last t) with hxdef
    -- Record preservation: the recorded history is a union of complete pasts.
    have hsat : ∀ ω ω', past t ω = past t ω' → ω ∈ E → ω' ∈ E := by
      intro ω ω' hω hωE i
      rw [← hωE i]
      exact (hrec t ht i (Nat.lt_succ_iff.1 i.2) ω ω' hω).symm
    have hEmeas : MeasurableSet E := by
      have hEq : E = past t ⁻¹' (past t '' E) := by
        refine Subset.antisymm (subset_preimage_image _ _) ?_
        rintro ω ⟨ω', hω', heq⟩
        exact hsat ω' ω heq hω'
      rw [hEq]
      exact measurableSet_preimage_of_countable (hpast t ht) _
    -- Every complete past in the history contributes `K(y | x)` times its mass.
    have hσ : ∀ σ, P (past t ⁻¹' {σ} ∩ (E ∩ A)) =
        exitTransition y x * P (past t ⁻¹' {σ} ∩ E) := by
      intro σ
      by_cases hne : (past t ⁻¹' {σ} ∩ E).Nonempty
      · obtain ⟨ω₀, hω₀σ, hω₀E⟩ := hne
        have hsub : past t ⁻¹' {σ} ⊆ E := fun ω hω =>
          hsat ω₀ ω
            (by simp only [mem_preimage, mem_singleton_iff] at hω₀σ hω ⊢; rw [hω₀σ, hω]) hω₀E
        set T := Finset.univ.filter (fun ab : Fin 2 × Fin 2 => x + ab.1 * ab.2 = y) with hT
        -- On this past the exit is `x`, so the new exit is `y` exactly when `ab ∈ T`.
        have hA : past t ⁻¹' {σ} ∩ (E ∩ A) = past t ⁻¹' {σ} ∩ pair t ⁻¹' (T : Set _) := by
          ext ω
          simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hT, Finset.coe_filter,
            Finset.mem_univ, true_and, mem_ofPred_eq]
          constructor
          · rintro ⟨hω, -, hωA⟩
            refine ⟨hω, ?_⟩
            have hxω : exit t ω = x := hsub hω (Fin.last t)
            rw [hAdef, mem_preimage, mem_singleton_iff, hexit t ht ω, hxω] at hωA
            exact hωA
          · rintro ⟨hω, hωT⟩
            refine ⟨hω, hsub hω, ?_⟩
            have hxω : exit t ω = x := hsub hω (Fin.last t)
            rw [hAdef, mem_preimage, mem_singleton_iff, hexit t ht ω, hxω]
            exact hωT
        rw [hA, Set.inter_eq_left.2 hsub, ← cond_mul_eq_inter (hpast t ht σ) _ P]
        by_cases h0 : P (past t ⁻¹' {σ}) = 0
        · rw [h0, mul_zero, mul_zero]
        · congr 1
          rw [← sum_measure_preimage_singleton T fun ab _ =>
              hpair t ht (measurableSet_singleton ab),
            exitTransition_eq_sum]
          exact Finset.sum_congr rfl fun ab _ => hunif t ht σ h0 ab
      · rw [not_nonempty_iff_eq_empty] at hne
        have h0 : past t ⁻¹' {σ} ∩ (E ∩ A) = ∅ :=
          subset_empty_iff.1 (hne ▸ inter_subset_inter_right _ inter_subset_left)
        rw [h0, hne, measure_empty, mul_zero]
    -- Add over the complete pasts and divide by `P(E)`.
    rw [cond_apply hEmeas, measure_eq_tsum_levels (hpast t ht) P (E ∩ A), tsum_congr hσ,
      ENNReal.tsum_mul_left, ← measure_eq_tsum_levels (hpast t ht) P E, mul_comm, mul_assoc,
      ENNReal.mul_inv_cancel hE (measure_ne_top P E), mul_one]
  refine ⟨key, ?_⟩
  intro t ht t' ht' h h' hE hE' hlast y
  rw [key t ht h hE y, key t' ht' h' hE' y, hlast]

/-! ## Non-vacuity -/

namespace ExitClosure

namespace TwoPhrases

/-- A fine history of the two-phrase dance (Section 4.7): a complete assignment
of a response pair `(a_t, b_t)` to each of the two phrases. -/
abbrev History := Fin 2 → Fin 2 × Fin 2

/-- The response pair prepared for phrase `t + 1`. -/
def pair (t : ℕ) (ω : History) : Fin 2 × Fin 2 := if ht : t < 2 then ω ⟨t, ht⟩ else 0

/-- The exit after `t` phrases: `x_0 = 0` and `x_{t+1} = x_t ⊕ a b`. -/
def exit : ℕ → History → Fin 2
  | 0, _ => 0
  | t + 1, ω => exit t ω + (pair t ω).1 * (pair t ω).2

/-- The complete past before phrase `t + 1`: the pairs of the phrases already
danced, the later entries left blank. It fixes every exit so far, and so every
record. -/
def past (t : ℕ) (ω : History) : History := fun i => if (i : ℕ) < t then ω i else 0

end TwoPhrases

/-- Conditioning the uniform law on a set gives the uniform law on that set. -/
lemma cond_uniformOn_univ {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Finite Ω] (B A : Set Ω) : (uniformOn (univ : Set Ω))[A | B] = uniformOn B A := by
  rw [uniformOn, cond_cond_eq_cond_inter' MeasurableSet.univ (Set.toFinite B).measurableSet
    (Measure.count_apply_lt_top.2 Set.finite_univ).ne, univ_inter, uniformOn]

end ExitClosure

/-- The book's two-phrase dance (Sections 4.7 and 4.8) meets the hypotheses of
Proposition 4.4: equally likely fine histories, so fresh uniform pairs given
every complete past; the exit rule `x_{t+1} = x_t ⊕ a b` from `x_0 = 0`; and
complete pasts that keep every pair, so every record. The proposition then gives
the book's value `P(X_2 = 1 | X_1 = 1) = 3/4`. -/
example :
    (uniformOn univ : Measure TwoPhrases.History)[TwoPhrases.exit 2 ⁻¹' {1} |
      historyEvent TwoPhrases.exit 1 ![0, 1]] = 3 / 4 := by
  open TwoPhrases in
  have hcount : ∀ t < 2, ∀ σ : History, ∀ ab : Fin 2 × Fin 2,
      (Finset.univ.filter fun ω => past t ω = σ).Nonempty →
      (Finset.univ.filter fun ω => past t ω = σ).card =
        4 * ((Finset.univ.filter fun ω => past t ω = σ) ∩
          Finset.univ.filter fun ω => pair t ω = ab).card := by
    decide
  have hunif : ∀ t < 2, ∀ σ, (uniformOn univ : Measure History) (past t ⁻¹' {σ}) ≠ 0 →
      ∀ ab, (uniformOn univ : Measure History)[pair t ⁻¹' {ab} | past t ⁻¹' {σ}] = 1 / 4 := by
    intro t ht σ hσ ab
    have hB : past t ⁻¹' {σ} = ↑(Finset.univ.filter fun ω => past t ω = σ) := by
      ext ω; simp
    have hA : pair t ⁻¹' {ab} = ↑(Finset.univ.filter fun ω => pair t ω = ab) := by
      ext ω; simp
    have hne : (Finset.univ.filter fun ω => past t ω = σ).Nonempty := by
      rw [← Finset.coe_nonempty, ← hB]
      exact nonempty_of_measure_ne_zero hσ
    have hc := hcount t ht σ ab hne
    rw [cond_uniformOn_univ, hB, hA, uniformOn_apply_finset, hc]
    set c := ((Finset.univ.filter fun ω => past t ω = σ) ∩
      Finset.univ.filter fun ω => pair t ω = ab).card
    have hc0 : (c : ℝ≥0∞) ≠ 0 := by
      have : (Finset.univ.filter fun ω => past t ω = σ).card ≠ 0 := hne.card_pos.ne'
      rw [hc] at this
      exact_mod_cast right_ne_zero_of_mul this
    push_cast
    nth_rw 1 [← one_mul (c : ℝ≥0∞)]
    rw [ENNReal.mul_div_mul_right _ _ hc0 (ENNReal.natCast_ne_top c)]
  have hrec : ∀ t < 2, ∀ s ≤ t, ∀ ω ω' : History,
      past t ω = past t ω' → exit s ω = exit s ω' := by
    intro t ht s hs ω ω' hω
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · rfl
    · obtain rfl : t = 1 := by omega
      have h0 : ω 0 = ω' 0 := by simpa [past] using congrFun hω 0
      simp [exit, pair, h0]
  have hpos : (uniformOn univ : Measure History) (historyEvent exit 1 ![0, 1]) ≠ 0 := by
    rw [Ne, uniformOn_eq_zero_iff Set.finite_univ, univ_inter, ← Ne, ← nonempty_iff_ne_empty]
    refine ⟨fun _ => (1, 1), fun i => ?_⟩
    fin_cases i <;> rfl
  obtain ⟨key, -⟩ := exitLevelClosure History (uniformOn univ) 2 (fun _ => History) past pair
    exit (fun _ _ _ => (Set.toFinite _).measurableSet) (fun _ _ => Measurable.of_discrete)
    hunif (fun _ _ _ => rfl) hrec
  rw [key 1 (by norm_num) ![0, 1] hpos 1]
  simp [exitTransition]

end Artform
