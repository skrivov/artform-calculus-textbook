import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Bounds.Defs
import ArtformTextbook.Ch02.Defs.Process
import ArtformTextbook.Ch03.Defs.Growth

/-!
# Statements of Chapter 3: growth

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 3.27** (commuting compatible changes). If two enabled
applications are compatible, making one and then the other gives the same
state in either order. -/
@[book "prop:commuting-proposals"]
def commutingProposals : Prop :=
  ∀ (A : Presentation) (x : A.Table) (a b : EnabledApp A x), a.Compatible b →
    b.profile.apply (a.profile.apply x) = a.profile.apply (b.profile.apply x)

/-- **Theorem 3.29** (stabilization). If the window `W` has finitely many cells
and `F_W` is extensive, then the increasing sequence `X₀ ⊆ X₁ ⊆ ⋯`,
`X_{t+1} = F_W(X_t)`, stabilizes after finitely many strict growth steps: it
is constant from some step `N ≤ |cells(W) \ cells(X₀)|` on. Here `F_W` is any
map of patches that attaches only cells of `W`, as the `F_W` of Section 3.9
does, attaching the cells required by enabled rules whose outputs lie in
`W`. -/
@[book "thm:growth-stabilization"]
def growthStabilization : Prop :=
  ∀ (Cell : Type) (W : Set Cell), W.Finite →
    ∀ F : Set Cell → Set Cell, (∀ X, F X ⊆ X ∪ W) → (∀ X, X ⊆ F X) →
      ∀ X₀ : Set Cell, (∀ t, F^[t] X₀ ⊆ F^[t + 1] X₀) ∧
        ∃ N ≤ (W \ X₀).ncard, ∀ t ≥ N, F^[t] X₀ = F^[N] X₀

/-- **Proposition 3.32** (fair closure). In a fixed finite window of possible
cells, every run that meets these three hypotheses reaches the least closed
patch above its seed and stays there:
1. triggers are persistent and positive, so an enabled placement stays
   enabled;
2. the control cadence keeps offering applicable phases, which is cadence
   fairness; and
3. the policy is application-fair, so a persistently enabled placement is
   eventually selected.

The rules are attachments whose outputs lie in the finite window `W`, and the
run is a continuing execution under their control; its seed is its state at
boundary `0`. -/
@[book "prop:fair-closure"]
def fairClosure : Prop :=
  ∀ (Cell : Type) (W : Set Cell), W.Finite →
    ∀ C : Control (patchFrame Cell), (∀ u ∈ C.rules, u.Attaches ∧ u.writes ⊆ W) →
      (∀ u ∈ C.rules, u.Persistent) →
      ∀ r : Execution (patchFrame Cell), r.Under C → r.CadenceFair C → r.ApplicationFair C →
        ∃ T, ∀ t ≥ T, IsLeast {Y | Closed C.rules Y ∧ r.state 0 ≤ Y} (r.state t)

/-- **Proposition 3.33** (symmetry of growth). Let a positive attachment rule be
carried to itself by a group `G` of motions of the canvas, and let the
motions of a subgroup `S` fix the seed `X₀`.
1. For every `n`, the set of patches that some run reaches in `n` steps is
   carried to itself by every motion of `S`.
2. The policy that makes every enabled attachment at once keeps the symmetry
   `S` at every step.
3. At a patch that `S` fixes, a policy that makes one attachment keeps `S` only
   if the attached face is fixed by every motion of `S`.

The rule is the set of its located attachments. In (3) the policy makes one
enabled attachment of the rule, which attaches one face `c`, fresh as
Section 3.8 requires. -/
@[book "prop:growth-symmetry"]
def growthSymmetry : Prop :=
  ∀ (Cell : Type) (R : Set (ProcessProfile (patchFrame Cell))),
    (∀ u ∈ R, u.Attaches ∧ u.Persistent) →
    ∀ G S : Subgroup (Equiv.Perm Cell), S ≤ G → (∀ g ∈ G, ∀ u ∈ R, moveProfile g u ∈ R) →
    ∀ X₀ : (patchFrame Cell).Table, (∀ s ∈ S, movePatch s X₀ = X₀) →
      (∀ n, ∀ s ∈ S, movePatch s '' reachable R X₀ n = reachable R X₀ n) ∧
      (∀ s ∈ S, ∀ t, movePatch s ((attachAll R)^[t] X₀) = (attachAll R)^[t] X₀) ∧
      (∀ X : (patchFrame Cell).Table, (∀ s ∈ S, movePatch s X = X) →
        ∀ a : EnabledApp (patchFrame Cell) X, a.profile ∈ R →
        ∀ c, a.profile.writes = {c} → ¬ X c →
        (∀ s ∈ S, movePatch s (a.profile.apply X) = a.profile.apply X) → ∀ s ∈ S, s c = c)

end Artform.Statement
