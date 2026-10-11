import ArtformTextbook.Ch05.Defs.Patterns

/-!
# Statements of Chapter 5: laws as patterns on the temporal prism (Section 5.21)

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 5.42** (what a strung run fixes). Among deterministic laws that read a
declared halo and act alike at every cell, a run fixes the law exactly on the windows it shows:
the tables on a halo that occur in the run, each with the value it leads to. If `u` windows
never occur, `|A|^u` laws agree with the run, for `A` the values of a cell.

A law of the family is a table `f` from windows to values: every cell reads its halo in the
shape `K` that all halos share, and `f` gives its new value from that window (`haloLaw`). The
run is the run of such a law from `x₀`, strung over `n` ticks; a window it shows occurs at a
tick before the last, and leads to the value at the next tick. A law `g` of the family agrees
with the run when its own run from `x₀` passes through the same states. It does exactly when
`g` gives every window shown the value it leads to; and if `u` windows never occur so, the laws
that agree with the run, counted as tables from windows to values, number `|A|^u`. -/
@[book "prop:run-fixes"]
def runFixes : Prop :=
  ∀ (Cell K Val : Type) [Finite K] [Finite Val] (halo : Cell → K → Cell)
    (f : (K → Val) → Val) (x₀ : Cell → Val) (n : ℕ),
    (∀ g : (K → Val) → Val,
      (∀ t ≤ n, (haloLaw halo g).run x₀ t = (haloLaw halo f).run x₀ t) ↔
        ∀ t < n, ∀ y, g (haloWindow halo ((haloLaw halo f).run x₀ t) y) =
          (haloLaw halo f).run x₀ (t + 1) y) ∧
    ∀ u : ℕ,
      Nat.card {w : K → Val // ¬ ∃ t < n, ∃ y, haloWindow halo ((haloLaw halo f).run x₀ t) y = w}
        = u →
      Nat.card {g : (K → Val) → Val //
          ∀ t ≤ n, (haloLaw halo g).run x₀ t = (haloLaw halo f).run x₀ t} =
        Nat.card Val ^ u

/-- **Theorem 5.45** (a kept count is woven). Let every table obtained from a legal table by
emptying cells, setting their values to `0`, be legal. Let `H` be a no-signalling halo of a
realizer, and let the law keep a count. Then every step `x → x'` the realizer allows has a
weave along `H`. Conversely, a step that has a weave keeps the count.

The realizer is deterministic, relational or stochastic, and the theorem is stated for each
kind; the law keeps the count when every step its realizer allows keeps `N`. The frame has
finitely many cells, each with a value `0`. The converse holds for every step `x → x'`, with no
hypothesis. -/
@[book "thm:woven"]
def woven : Prop :=
  ∀ (A : Presentation) [Fintype A.P] [∀ p, Zero (A.V p)] (L : Law A) (c : Count A)
    (H : A.P → Set A.P),
    ((∀ x, L.Legal x → ∀ U : Set A.P, L.Legal (emptyCells U x)) →
      (∀ R : DetRealizer L, R.NoSignalling H →
        (∀ x x', R.AllowsStep x x' → c.N x' = c.N x) →
        ∀ x x', R.AllowsStep x x' → Nonempty (Weave H c x x')) ∧
      (∀ R : RelRealizer L, R.NoSignalling H →
        (∀ x x', R.AllowsStep x x' → c.N x' = c.N x) →
        ∀ x x', R.AllowsStep x x' → Nonempty (Weave H c x x')) ∧
      (∀ R : StochRealizer L, R.NoSignalling H →
        (∀ x x', R.AllowsStep x x' → c.N x' = c.N x) →
        ∀ x x', R.AllowsStep x x' → Nonempty (Weave H c x x'))) ∧
    ∀ x x' : A.Table, Nonempty (Weave H c x x') → c.N x' = c.N x

/-- **Proposition 5.46** (symmetries of a slot tapestry). Applying `h` at every slot and
shifting by `j` carries every run of the slots to a run if and only if
`h ∘ S_{(s+j) mod k} ∘ h⁻¹ = S_s` for every `s`; then `h ∘ P_j` commutes with the tick.
Applying `h`, reversing time and shifting by `j` does so if and only if
`h ∘ S_{(j-1-s) mod k}⁻¹ ∘ h⁻¹ = S_s` for every `s`; then `h ∘ P_j` reverses the tick:
`(h ∘ P_j) ∘ F ∘ (h ∘ P_j)⁻¹ = F⁻¹`.

The steps `S_0, …, S_{k-1}` are bijections of the states, indexed by `ZMod k`; the tick is
`F = S_{k-1} ∘ ⋯ ∘ S_0 = P_k` and `P_j = S_{j-1} ∘ ⋯ ∘ S_0` (`firstSteps`). A run of the slots
has a state `y_s` at every slot boundary `s ∈ ℤ`, with `y_{s+1} = S_{s mod k}(y_s)`. The moved
run is `z_s = h(y_{s+j})`, and the reversed one `z_s = h(y_{j-s})`. In `Equiv.Perm`, `f * g`
is `f ∘ g`. -/
@[book "prop:slot-symmetry"]
def slotSymmetry : Prop :=
  ∀ (X : Type) (k : ℕ) (S : ZMod k → Equiv.Perm X) (h : Equiv.Perm X) (j : ℕ),
    ((∀ y : ℤ → X, IsSlotRun S y → IsSlotRun S fun s => h (y (s + j))) ↔
        ∀ s : ZMod k, h * S (s + j) * h⁻¹ = S s) ∧
    ((∀ s : ZMod k, h * S (s + j) * h⁻¹ = S s) →
        h * firstSteps S j * firstSteps S k = firstSteps S k * (h * firstSteps S j)) ∧
    ((∀ y : ℤ → X, IsSlotRun S y → IsSlotRun S fun s => h (y ((j : ℤ) - s))) ↔
        ∀ s : ZMod k, h * (S ((j : ZMod k) - 1 - s))⁻¹ * h⁻¹ = S s) ∧
    ((∀ s : ZMod k, h * (S ((j : ZMod k) - 1 - s))⁻¹ * h⁻¹ = S s) →
        h * firstSteps S j * firstSteps S k * (h * firstSteps S j)⁻¹ = (firstSteps S k)⁻¹)

/-- **Theorem 5.47** (symmetry of what may happen). Let every motion of a group `G` be a
symmetry of a law, and let the motions of a subgroup `S` fix the start `x₀`. Then every motion
of `S` carries the runs from `x₀` to runs from `x₀`, so the set of states reachable at each tick
is carried to itself by `S`. If a stochastic realizer commutes with `G`, the weight of each state
at each tick is the weight of its image under `S`.

A group of motions acts on the states and on the batches at the states (`Motions`); a motion
is a symmetry of a law with a choice when it carries legal states to legal states and the
batches the law allows at `x` to batches it allows at the image of `x`. A run of the law has
legal states, each step applying a batch the law allows; a motion carries it to the run of the
moved states and batches. A stochastic realizer commutes with `G` when every motion carries
each batch at a legal state to a batch of the same weight; the weight of a state at tick `n` is
the total weight of the runs of positive weight from `x₀` that end there. -/
@[book "thm:curie"]
def curie : Prop :=
  ∀ (A : Presentation) (L : Law A) (G : Type) [Group G] (M : Motions G A),
    (∀ g : G, L.IsSymmetryUnder M g) →
    ∀ (S : Subgroup G) (x₀ : A.Table), (∀ s ∈ S, M.onState s x₀ = x₀) →
      (∀ s ∈ S, ∀ (n : ℕ) (r : Run A n), r.state 0 = x₀ → r.OfLaw L →
        (M.moveRun s r).state 0 = x₀ ∧ (M.moveRun s r).OfLaw L) ∧
      (∀ s ∈ S, ∀ n : ℕ, M.onState s '' L.reachableAt x₀ n = L.reachableAt x₀ n) ∧
      ∀ R : StochRealizer L, R.CommutesWith M →
        ∀ s ∈ S, ∀ (n : ℕ) (y : A.Table), R.weightAt x₀ n (M.onState s y) = R.weightAt x₀ n y

/-- **Proposition 5.48** (breaking needs a choice). Under the hypotheses of Theorem 5.47:
1. a run keeps the symmetry `S` at every tick if and only if it stays among the states that
   `S` fixes;
2. a deterministic realizer that commutes with `G` exists if and only if at every legal state
   some allowed batch is fixed by every motion that fixes the state;
3. averaging any realizer over the motions of `G` gives a stochastic realizer that commutes
   with `G`.

In (1) a run keeps the symmetry `S` at a tick when every motion of `S` carries it to a run with
the same state there. In (2) a deterministic realizer commutes with `G` when every motion
carries the batch it selects at a legal state `x` to the batch it selects at the image of `x`;
an allowed batch is one that a realizer may select: the law allows it and it keeps the
invariants. In (3) the group is finite; a deterministic realizer is read as the stochastic one
with weight `1` on the batch it selects, a relational one as weight `1` on each batch it
allows, and the average gives a batch `b` at `x` the mean over `g ∈ G` of the weight of the
batch that `g` carries to `b`. -/
@[book "prop:breaking"]
def breaking : Prop :=
  ∀ (A : Presentation) (L : Law A) (G : Type) [Group G] (M : Motions G A),
    (∀ g : G, L.IsSymmetryUnder M g) →
    ∀ (S : Subgroup G) (x₀ : A.Table), (∀ s ∈ S, M.onState s x₀ = x₀) →
      (∀ (n : ℕ) (r : Run A n),
        (∀ i, r.KeepsSymmetryAt M S i) ↔ ∀ i, r.state i ∈ M.fixedStates S) ∧
      ((∃ R : DetRealizer L, R.CommutesWith M) ↔
        ∀ x, L.Legal x → ∃ b : Batch A x, L.Allows b ∧ L.Legal b.apply ∧
          ∀ g : G, M.onState g x = x → M.onBatch g ⟨x, b⟩ = ⟨x, b⟩) ∧
      ∀ [Fintype G],
        (∀ R : StochRealizer L, ∃ R' : StochRealizer L,
          R'.weight = R.averageWeight M ∧ R'.CommutesWith M) ∧
        (∀ R : DetRealizer L, ∃ R' : StochRealizer L,
          R'.weight = R.toStoch.averageWeight M ∧ R'.CommutesWith M) ∧
        (∀ R : RelRealizer L, ∃ R' : StochRealizer L,
          R'.weight = R.toStoch.averageWeight M ∧ R'.CommutesWith M)

end Artform.Statement
