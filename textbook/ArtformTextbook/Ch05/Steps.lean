import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch05.Statements.Steps

/-!
# Finite well-posedness (Section 5.5)

The proof of Theorem 5.13, by induction along the stretch of the score, as in
the book: the realizer selects one batch in each slot, the batch gives one
state in every order, and the realizer's evidence gives the invariants
checked at the boundary that closes the slot.

The non-vacuity example is the law of two squares that turn, with a score
that opens the left square in the even slots and the right square in the odd
ones. It declares the invariant of the number at `v₁`, which holds at the
ticks but not inside them: the left turn lifts it to `v₂`, and the right turn
brings it back. So that invariant is checked at the even boundaries, the
ticks, and its companion, the same number at `v₂`, at the odd ones.
-/

namespace Artform

variable {A : Presentation}

namespace LawInSteps

variable {L : LawInSteps A}

/-- The states that a realizer reaches from `x₀`, starting in slot `s`. -/
noncomputable def DetRealizer.trajectory (R : L.DetRealizer) (s : ℕ) (x₀ : A.Table) :
    ℕ → A.Table
  | 0 => x₀
  | k + 1 => (R.select (s + k) (R.trajectory s x₀ k)).apply

/-- The run of `n` steps that a realizer makes from `x₀`, starting in slot `s`. -/
noncomputable def DetRealizer.run (R : L.DetRealizer) (s : ℕ) (x₀ : A.Table) (n : ℕ) :
    Run A n where
  state i := R.trajectory s x₀ i
  batch i := R.select (s + i) (R.trajectory s x₀ i)
  step _ := rfl

end LawInSteps

namespace Run

variable {L : LawInSteps A} {R : L.DetRealizer} {s n : ℕ}

/-- Along a run that follows the realizer from a state legal at boundary `s`,
every state is legal at its boundary. -/
theorem legalAt_of_follows {r : Run A n} (h0 : L.LegalAt s (r.state 0)) (hf : r.Follows R s) :
    ∀ i : Fin (n + 1), L.LegalAt (s + i) (r.state i) := by
  intro i
  induction i using Fin.induction with
  | zero => simpa using h0
  | succ i ih =>
    rw [r.step i, hf i, Fin.val_succ, ← add_assoc]
    exact R.keeps (s + i) _ ih

/-- Two runs that follow the realizer from the same start pass through the
same states. -/
theorem state_eq_of_follows {r₁ r₂ : Run A n} (h0 : r₁.state 0 = r₂.state 0)
    (hf₁ : r₁.Follows R s) (hf₂ : r₂.Follows R s) : ∀ i, r₁.state i = r₂.state i := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    rw [r₁.step i, r₂.step i, hf₁ i, hf₂ i]
    exact congrArg (fun y => (R.select (s + i) y).apply) ih

/-- Two runs that follow the realizer from the same start are the same run. -/
theorem eq_of_follows {r₁ r₂ : Run A n} (h0 : r₁.state 0 = r₂.state 0)
    (hf₁ : r₁.Follows R s) (hf₂ : r₂.Follows R s) : r₁ = r₂ := by
  have hst := state_eq_of_follows h0 hf₁ hf₂
  obtain ⟨st₁, b₁, step₁⟩ := r₁
  obtain ⟨st₂, b₂, step₂⟩ := r₂
  obtain rfl : st₁ = st₂ := funext hst
  obtain rfl : b₁ = b₂ := funext fun i => (hf₁ i).trans (hf₂ i).symm
  rfl

end Run

/-- **Theorem 5.13** (finite well-posedness). Let a law in steps have a
well-posed deterministic realizer. From every legal start, over every finite
stretch of the score, the realizer has exactly one run. The order in which
the moves of each batch are applied does not change its states, and every
invariant holds at each of its checkpoints. -/
@[book "thm:well-posed"]
theorem finiteWellPosedness : Statement.finiteWellPosedness := by
  intro A L R hR s n x₀ hx₀
  refine ⟨⟨R.run s x₀ n, ⟨rfl, fun _ => rfl⟩, fun r ⟨h0, hf⟩ =>
    Run.eq_of_follows (r₂ := R.run s x₀ n) h0 hf fun _ => rfl⟩, fun r h0 hf => ?_⟩
  have hlegal := Run.legalAt_of_follows (R := R) (h0 ▸ hx₀) hf
  refine ⟨fun i l hl => ?_, fun i J hJ ht => hlegal i J hJ ht⟩
  rw [hf i] at hl
  rw [r.step i, hf i]
  exact hR.orderFree (s + i) _ (hlegal i.castSucc) l hl

/-! ## Non-vacuity -/

namespace TwoSquaresExample

/-- The frame of two squares: six corners `v₀, …, v₅`, each holding a number
modulo `3`. -/
abbrev frame : Presentation := ⟨Fin 6, fun _ => ZMod 3⟩

/-- A turn of one square: every corner of the square takes the number of the
corner behind it in that square, and every other corner keeps its own. -/
def turn (sq : Set (Fin 6)) (behind : Fin 6 → Fin 6) (h : ∀ v ∈ sq, behind v ∈ sq) :
    ProcessProfile frame where
  guard _ := True
  reads := sq
  writes := sq
  update x v := x (behind v)
  guard_reads _ _ _ := Iff.rfl
  update_reads _ _ hxy v hv := hxy _ (h v hv)

/-- The left turn: `p'(v₁) = p(v₀)`, `p'(v₂) = p(v₁)`, `p'(v₃) = p(v₂)`,
`p'(v₀) = p(v₃)`. -/
def leftTurn : ProcessProfile frame :=
  turn {0, 1, 2, 3} ![3, 0, 1, 2, 4, 5] (by decide)

/-- The right turn: `p'(v₄) = p(v₁)`, `p'(v₅) = p(v₄)`, `p'(v₂) = p(v₅)`,
`p'(v₁) = p(v₂)`. -/
def rightTurn : ProcessProfile frame :=
  turn {1, 4, 5, 2} ![0, 2, 5, 3, 1, 4] (by decide)

/-- The turn of the square that a step opens: `false` the left, `true` the
right. -/
def turnOf : Bool → ProcessProfile frame
  | false => leftTurn
  | true => rightTurn

/-- The score: the left square in the even slots and the right square in the
odd ones, so that a tick is two slots, left then right; no slot may be
empty. -/
def score : Score Bool where
  opens t := decide (t % 2 = 1)
  allowsEmpty _ := False
  period := 2
  period_pos := by decide
  repeats t := ⟨by simp [Nat.add_mod_right], Iff.rfl⟩

/-- The number `b` at `v₁` at every tick, the even boundaries. -/
def atV₁ (b : ZMod 3) : CheckedInvariant frame := ⟨fun x => x 1 = b, {t | t % 2 = 0}⟩

/-- The number `b` at `v₂` inside every tick, the odd boundaries. -/
def atV₂ (b : ZMod 3) : CheckedInvariant frame := ⟨fun x => x 2 = b, {t | t % 2 = 1}⟩

theorem turnOf_guard (σ : Bool) (x : frame.Table) : (turnOf σ).guard x := by
  cases σ <;> trivial

theorem leftTurn_apply_two (x : frame.Table) : leftTurn.apply x 2 = x 1 := by
  simp [leftTurn, turn, ProcessProfile.apply]

theorem rightTurn_apply_one (x : frame.Table) : rightTurn.apply x 1 = x 2 := by
  simp [rightTurn, turn, ProcessProfile.apply]

/-- In each slot, the turn of the open square leads from a state legal at the
slot's opening boundary to one legal at its closing boundary. -/
theorem turnOf_legal (b : ZMod 3) (t : ℕ) (x : frame.Table)
    (hx : ∀ J ∈ [atV₁ b, atV₂ b], t ∈ J.checkpoints → J.holds x) :
    ∀ J ∈ [atV₁ b, atV₂ b], t + 1 ∈ J.checkpoints →
      J.holds ((turnOf (score.opens t)).apply x) := by
  intro J hJ ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl
  · have ht' : t % 2 = 1 := by change (t + 1) % 2 = 0 at ht; omega
    have h2 := hx (atV₂ b) (by simp) ht'
    simp only [atV₁, score, ht', decide_true, turnOf, rightTurn_apply_one]
    exact h2
  · have ht' : t % 2 = 0 := by change (t + 1) % 2 = 1 at ht; omega
    have h1 := hx (atV₁ b) (by simp) ht'
    simp only [atV₂, score, ht', zero_ne_one, decide_false, turnOf, leftTurn_apply_two]
    exact h1

/-- The law of two squares, in two steps, with the number `b` at `v₁` at the
ticks and at `v₂` inside them. -/
def law (b : ZMod 3) : LawInSteps frame where
  Step := Bool
  moves σ := [turnOf σ]
  invariants := [atV₁ b, atV₂ b]
  score := score
  moves_legal t x hx u hu _ := by
    rw [List.mem_singleton] at hu
    subst hu
    exact turnOf_legal b t x hx

/-- The realizer of two squares: it takes the one move of the open step. -/
def realizer (b : ZMod 3) : (law b).DetRealizer where
  select t x := ⟨[⟨turnOf (score.opens t), turnOf_guard _ x⟩], List.pairwise_singleton _ _⟩
  allows _ _ _ _ ha := by
    rw [List.mem_singleton] at ha
    subst ha
    exact List.mem_singleton_self _
  keeps t x hx := turnOf_legal b t x hx

/-- The realizer of two squares is well posed: it is total, and its batches,
of one move each, are order-free. -/
theorem realizer_wellPosed (b : ZMod 3) : (realizer b).WellPosed where
  total _ _ _ _ := List.cons_ne_nil _ _
  orderFree t x _ l hl := by
    have happs : ((realizer b).select t x).apps = [⟨turnOf (score.opens t), turnOf_guard _ x⟩] :=
      rfl
    rw [happs, List.perm_singleton] at hl
    rw [hl]
    rfl

/-- The start of the examples: the numbers `0, 1, 2, 0, 0, 0` at `v₀, …, v₅`. -/
def start : frame.Table := ![0, 1, 2, 0, 0, 0]

end TwoSquaresExample

open TwoSquaresExample in
/-- The hypotheses of Theorem 5.13 are met: the realizer of two squares is well
posed, and a state with the number `1` at `v₁` is a legal start at
boundary `0`. -/
example : (realizer 1).WellPosed ∧ (law 1).LegalAt 0 start := by
  refine ⟨realizer_wellPosed 1, fun J hJ ht => ?_⟩
  simp only [law, List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl
  · rfl
  · simp [atV₂] at ht

open TwoSquaresExample in
/-- The invariant of the number at `v₁` is checked only at its checkpoints:
after the first slot, inside the tick, `v₁` holds the number that was at `v₀`. -/
example : ((realizer 1).select 0 start).apply 1 ≠ 1 := by
  have h : ((realizer 1).select 0 start).apply 1 = 0 := by
    simp only [Batch.apply, Fin.isValue, realizer, turnOf, score, leftTurn, turn, start,
      Nat.zero_mod, zero_ne_one, decide_false, applyAll, ProcessProfile.apply,
      Set.mem_insert_iff, one_ne_zero, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false,
      or_true, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
    rfl
  rw [h]
  exact (by decide : (0 : ZMod 3) ≠ 1)

end Artform
