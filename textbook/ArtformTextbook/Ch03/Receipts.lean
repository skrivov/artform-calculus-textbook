import Mathlib.Tactic.Linarith
import ArtformTextbook.Ch03.Statements.Receipts

/-!
# Receipts and margins (Proposition 3.43)

A comparison whose slack moves by less than its absolute value keeps its sign, so it keeps its
truth value, strict or not (`Receipts.holds_iff_of_withinMargin`); a receipt's verdict is a
function of the truth values of its comparisons and of its data, so it is kept
(`Receipts.eval_eq_of_withinMargin`), and so is the table of verdicts of an observation.
-/

namespace Artform

namespace Receipts

/-- A comparison with nonzero slack holds exactly when its slack is positive. -/
theorem holds_iff_slack_pos {c : Cmp} (h : c.slack ≠ 0) : c.Holds ↔ 0 < c.slack := by
  unfold Cmp.Holds
  unfold Cmp.slack at h ⊢
  split
  · constructor <;> intro h' <;> linarith
  · constructor
    · intro h'
      rcases lt_or_eq_of_le h' with h'' | h''
      · linarith
      · exact absurd (by linarith) h
    · intro h'
      linarith

/-- A comparison changed by less than its recorded margin keeps its truth value. -/
theorem holds_iff_of_withinMargin {c c' : Cmp} (h : c.WithinMargin c') : c'.Holds ↔ c.Holds := by
  obtain ⟨hs, hm⟩ := h
  have hne : c.slack ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hm
    exact absurd hm (not_lt.mpr (abs_nonneg _))
  have key : 0 < c'.slack ↔ 0 < c.slack := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [abs_of_neg hneg] at hm
      have := abs_lt.mp hm
      constructor <;> intro <;> linarith [this.1, this.2]
    · rw [abs_of_pos hpos] at hm
      have := abs_lt.mp hm
      constructor <;> intro <;> linarith [this.1, this.2]
  have hne' : c'.slack ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hm
    exact lt_irrefl _ hm
  have e : c'.strict = c.strict := hs
  rw [holds_iff_slack_pos hne', holds_iff_slack_pos hne, key]

/-- Margins protect a receipt: its verdict is kept. -/
theorem eval_eq_of_withinMargin {D V : Type} (R : Receipt D V) (d : D) (c c' : R.I → Cmp)
    (h : ∀ i, (c i).WithinMargin (c' i)) : R.eval d c' = R.eval d c := by
  unfold Receipt.eval
  congr 1
  funext i
  exact decide_eq_decide.mpr (holds_iff_of_withinMargin (h i))

end Receipts

open Receipts in
/-- **Proposition 3.43** (receipts decide, and margins protect). Each receipt is decided by
finitely many comparisons of rational numbers; if every inequality of every receipt changes by
less than its recorded margin, under a bijection of the parts that preserves the data the receipts
read, every verdict is preserved and the two observations produce the same feature state. -/
@[book "prop:metric-feature-receipts-book"]
theorem metricFeatureReceipts : Statement.metricFeatureReceipts := by
  refine ⟨fun Ax _ m n A T conn ends => ?_, fun m n rMinus rPlus conn bdry => ?_,
    fun dq delta2 bU bV => ?_, fun dq delta2 bU bV ports => ?_,
    fun a b qu qv p nonzero => ?_, fun lMinus lPlus qu qv => ?_,
    fun D V R d c c' h => eval_eq_of_withinMargin R d c c' h,
    fun D V π o₁ o₂ e hd hc r t => ?_⟩
  · simp [Receipt.eval, elongatedR, elongatedCmps, Cmp.Holds]
  · simp [Receipt.eval, roundR, roundCmps, Cmp.Holds, Bool.and_assoc]
  · simp [Receipt.eval, connectedR, connectedCmps, Cmp.Holds, Bool.and_assoc]
  · simp [Receipt.eval, jointR, connectedCmps, Cmp.Holds, Bool.and_assoc]
  · simp [Receipt.eval, angleR, angleCmps, Cmp.Holds, Bool.and_assoc]
  · simp [Receipt.eval, proportionR, proportionCmps, Cmp.Holds]
  · unfold Observation.featureState
    rw [hd r t]
    exact eval_eq_of_withinMargin _ _ _ _ (hc r t)

/-! ## Non-vacuity -/

open Receipts in
/-- An elongated region read in two pictures: along the axis the spread is `5` and then `4`,
across it `1` both times, with the squared aspect `2/1`. The slack `n A - m T` moves from `3` to
`2`, by less than its margin `3`, and the verdict, positive, is kept. -/
example : (elongatedCmps (Ax := Unit) 2 1 (fun _ => 5) (fun _ => 1) (.inl ())).WithinMargin
      (elongatedCmps (Ax := Unit) 2 1 (fun _ => 4) (fun _ => 1) (.inl ())) ∧
    (elongatedR Unit).eval (true, fun _ => true) (elongatedCmps 2 1 (fun _ => 4) (fun _ => 1)) =
      some true := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [elongatedCmps, Cmp.slack]
    norm_num [abs_of_pos]
  · simp [Receipt.eval, elongatedR, elongatedCmps, Cmp.Holds]
    norm_num

end Artform
