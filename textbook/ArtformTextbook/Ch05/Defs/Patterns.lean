import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import ArtformTextbook.Ch05.Defs.Laws
import ArtformTextbook.Ch05.Defs.Realizers

/-!
# Laws as patterns on the temporal prism (Section 5.21)

The notions of Section 5.21, read on the laws and realizers of Section 5.4
(`Law`, `DetRealizer`, `RelRealizer`, `StochRealizer`, `Run`).

* **Halos and what a tick shows.** A halo `H` gives every cell `y` a set
  `H(y)` of cells, and `H(V)` is the union of the halos of the cells of `V`.
  What the next tick may show on `V` from a legal state `x` is read from the
  steps the realizer allows there: the one table for a deterministic
  realizer, the set of tables for a relational one, and the weight of each
  table for a stochastic one (Definition 5.41). A realizer acts at legal
  states only, so no-signalling compares legal states.
* **Counts and weaves** (Definition 5.43). The frame's values have a `0` at
  every cell; a count puts `c_y(a)` tokens on the value `a` of the cell `y`,
  none on `0`. The tokens of a table are numbered at each cell, and a weave
  pairs them one to one, each token moving only from a cell of the halo.
* **Laws that read a declared halo** (Proposition 5.42). Every cell reads its
  halo in one shape `K`, and the law applies one table `f` from windows
  `K → A` to values at every cell.
* **Slot runs** (Proposition 5.46). The steps `S_0, …, S_{k-1}` of a law in
  steps are bijections of the states, indexed by `ZMod k`, and a run of the
  slots is a state at every slot boundary `s ∈ ℤ`; runs extend backwards,
  since the steps are bijections, so that time can be reversed.
* **Motions** (Theorem 5.47, Proposition 5.48). A motion acts on the states,
  as a permutation, and on the batches at the states, carrying a batch at
  `x` to a batch at the image of `x` that leads to the image of where the
  batch leads. A group `G` of motions is a group with two actions, written as
  homomorphisms into the permutations of the states and of the pairs of a
  state and a batch there. A motion of the canvas, a permutation of the cells,
  gives such an action by moving every move (`Motions.ofCells`). A motion
  carries a run to the run of the moved states and batches, and a stochastic
  realizer commutes with it when it carries each batch to a batch of the
  same weight.
-/

namespace Artform

open scoped BigOperators ENNReal NNReal

/-! ## Halos and what a tick shows -/

/-- The cells in the halos of the cells of a set `V`: `H(V) = ⋃_{y ∈ V} H(y)`
(Definition 5.41). -/
def haloOf {P : Type*} (H : P → Set P) (V : Set P) : Set P := ⋃ y ∈ V, H y

/-- The table that a table `x` shows on a set `V` of cells: its values there. -/
def restrictTo {P : Type*} {W : P → Type*} (V : Set P) (x : (p : P) → W p) : (p : V) → W p :=
  fun p => x p

variable {A : Presentation}

namespace DetRealizer

variable {L : Law A}

/-- A step `x → x'` that a deterministic realizer allows: `x` is legal, and `x'` is the
state that the batch it selects at `x` leads to. -/
def AllowsStep (R : DetRealizer L) (x x' : A.Table) : Prop :=
  L.Legal x ∧ (R.select x).apply = x'

/-- **Definition 5.41** (no-signalling halo), for a deterministic realizer: for every set `V`
of cells, the table that the next tick shows on `V` depends only on the table on `H(V)`. The
states compared are legal, where the realizer acts. -/
@[book "def:no-signalling"]
def NoSignalling (R : DetRealizer L) (H : A.P → Set A.P) : Prop :=
  ∀ (V : Set A.P) (x z : A.Table), L.Legal x → L.Legal z → (∀ p ∈ haloOf H V, x p = z p) →
    restrictTo V (R.select x).apply = restrictTo V (R.select z).apply

end DetRealizer

namespace RelRealizer

variable {L : Law A}

/-- A step `x → x'` that a relational realizer allows: `x` is legal, and `x'` is the state
that some batch it allows at `x` leads to. -/
def AllowsStep (R : RelRealizer L) (x x' : A.Table) : Prop :=
  L.Legal x ∧ ∃ b : Batch A x, R.allowed x b ∧ b.apply = x'

/-- The tables on `V` that some step the relational realizer allows from `x` shows. -/
def shows (R : RelRealizer L) (x : A.Table) (V : Set A.P) : Set ((p : V) → A.V p) :=
  {τ | ∃ b : Batch A x, R.allowed x b ∧ restrictTo V b.apply = τ}

/-- **Definition 5.41** (no-signalling halo), for a relational realizer: for every set `V` of
cells, the tables on `V` that some allowed step shows depend only on the table on `H(V)`.
The states compared are legal, where the realizer acts. -/
@[book "def:no-signalling"]
def NoSignalling (R : RelRealizer L) (H : A.P → Set A.P) : Prop :=
  ∀ (V : Set A.P) (x z : A.Table), L.Legal x → L.Legal z → (∀ p ∈ haloOf H V, x p = z p) →
    R.shows x V = R.shows z V

end RelRealizer

namespace StochRealizer

variable {L : Law A}

/-- A step `x → x'` that a stochastic realizer allows: `x` is legal, and `x'` is the state
that some batch of positive weight at `x` leads to. -/
def AllowsStep (R : StochRealizer L) (x x' : A.Table) : Prop :=
  L.Legal x ∧ ∃ b : Batch A x, R.weight x b ≠ 0 ∧ b.apply = x'

open Classical in
/-- The weight with which the next tick from `x` shows the table `τ` on `V`: the total weight
of the batches at `x` whose result shows `τ` there. -/
noncomputable def showWeight (R : StochRealizer L) (x : A.Table) (V : Set A.P)
    (τ : (p : V) → A.V p) : ℝ≥0∞ :=
  ∑' b : Batch A x, if restrictTo V b.apply = τ then (R.weight x b : ℝ≥0∞) else 0

/-- **Definition 5.41** (no-signalling halo), for a stochastic realizer: for every set `V` of
cells, the weights of the tables that the next tick shows on `V` depend only on the table on
`H(V)`; the tables shown are those of positive weight. The states compared are legal, where
the realizer acts. -/
@[book "def:no-signalling"]
def NoSignalling (R : StochRealizer L) (H : A.P → Set A.P) : Prop :=
  ∀ (V : Set A.P) (x z : A.Table), L.Legal x → L.Legal z → (∀ p ∈ haloOf H V, x p = z p) →
    R.showWeight x V = R.showWeight z V

end StochRealizer

/-! ## Counts and weaves -/

/-- **Definition 5.43** (count). A count gives each value `a` of a cell `y` a number `c_y(a)`
of tokens, with no tokens on the value `0`. -/
@[book "def:weave"]
structure Count (A : Presentation) [∀ p, Zero (A.V p)] where
  /-- The number `c_y(a)` of tokens on the value `a` of the cell `y`. -/
  tokens : (y : A.P) → A.V y → ℕ
  /-- No tokens on the value `0`. -/
  tokens_zero : ∀ y, tokens y 0 = 0

namespace Count

variable [∀ p, Zero (A.V p)] (c : Count A)

/-- **Definition 5.43** (the count of a table): `N(x) = Σ_y c_y(x(y))`. -/
@[book "def:weave"]
def N [Fintype A.P] (x : A.Table) : ℕ := ∑ y, c.tokens y (x y)

/-- The tokens of a table `x`: `c_y(x(y))` of them at each cell `y`, numbered from `0`. A
token is a cell with the number of one of its tokens. -/
abbrev Tokens (x : A.Table) : Type := Σ y : A.P, Fin (c.tokens y (x y))

end Count

/-- **Definition 5.43** (weave). A weave of a step `x → x'` along a halo `H` pairs the tokens
of `x` one to one with the tokens of `x'`, each token moving from a cell `u` to a cell `y`
only when `u` lies in `H(y)`. -/
@[book "def:weave"]
structure Weave [∀ p, Zero (A.V p)] (H : A.P → Set A.P) (c : Count A) (x x' : A.Table) where
  /-- The pairing of the tokens of `x` with the tokens of `x'`. -/
  pair : c.Tokens x ≃ c.Tokens x'
  /-- Each token moves from a cell `u` to a cell `y` only when `u` lies in `H(y)`. -/
  along : ∀ t : c.Tokens x, t.1 ∈ H (pair t).1

open Classical in
/-- Emptying the cells of a set `U` in a table: their values are set to `0`, and every other
cell keeps its value (Theorem 5.45). -/
noncomputable def emptyCells [∀ p, Zero (A.V p)] (U : Set A.P) (x : A.Table) : A.Table :=
  fun p => if p ∈ U then 0 else x p

/-! ## Laws that read a declared halo -/

section HaloLaw

variable {Cell K Val : Type*}

/-- The window of a table at a cell `y`, for a declared halo: the values on the halo of `y`,
read in the shape `K` that every halo shares (for the square, the corner behind and the
corner itself). -/
def haloWindow (halo : Cell → K → Cell) (x : Cell → Val) (y : Cell) : K → Val :=
  fun j => x (halo y j)

/-- The deterministic law that reads a declared halo and acts alike at every cell
(Proposition 5.42): one table `f` from windows to values gives the new value at every cell
from its window. -/
def haloLaw (halo : Cell → K → Cell) (f : (K → Val) → Val) : DetLaw (Cell → Val) where
  tick x y := f (haloWindow halo x y)

end HaloLaw

/-! ## Slot runs -/

section Slots

variable {X : Type*} {k : ℕ}

/-- A run of the slots of a law in steps whose steps `S_0, …, S_{k-1}` are bijections of the
states (Proposition 5.46): a state `y_s` at every slot boundary `s ∈ ℤ`, with
`y_{s+1} = S_{s mod k}(y_s)`. The steps are indexed by `ZMod k`. -/
def IsSlotRun (S : ZMod k → Equiv.Perm X) (y : ℤ → X) : Prop :=
  ∀ s : ℤ, y (s + 1) = S s (y s)

/-- The first `j` steps, `P_j = S_{j-1} ∘ ⋯ ∘ S_0`, step indices read modulo `k`; `P_0` is the
identity and `P_k` is the tick `F = S_{k-1} ∘ ⋯ ∘ S_0`. In `Equiv.Perm`, `f * g` is `f ∘ g`. -/
def firstSteps (S : ZMod k → Equiv.Perm X) : ℕ → Equiv.Perm X
  | 0 => 1
  | j + 1 => S j * firstSteps S j

end Slots

/-! ## Motions -/

/-- Motions of a frame (Sections 5.4 and 5.21): a group `G` acting on the states, by
permutations, and on the batches at the states, compatibly: a motion carries a batch at a
state `x` to a batch at the image of `x`, which leads to the image of the state the batch
leads to. A batch is taken together with its state, as a pair `⟨x, b⟩`. -/
structure Motions (G : Type*) [Group G] (A : Presentation) where
  /-- The action on the states. -/
  onState : G →* Equiv.Perm A.Table
  /-- The action on the batches, each taken with its state. -/
  onBatch : G →* Equiv.Perm (Σ x : A.Table, Batch A x)
  /-- A motion carries a batch at `x` to a batch at the image of `x`. -/
  onBatch_fst : ∀ (g : G) (p : Σ x : A.Table, Batch A x), (onBatch g p).1 = onState g p.1
  /-- The moved batch leads to the image of the state the batch leads to. -/
  onBatch_apply : ∀ (g : G) (p : Σ x : A.Table, Batch A x),
    (onBatch g p).2.apply = onState g p.2.apply

namespace Motions

variable {G : Type*} [Group G] (M : Motions G A)

/-- The motions of a group `G'` that acts through a homomorphism `φ : G' → G`. -/
def comp {G' : Type*} [Group G'] (φ : G' →* G) : Motions G' A where
  onState := M.onState.comp φ
  onBatch := M.onBatch.comp φ
  onBatch_fst g p := M.onBatch_fst (φ g) p
  onBatch_apply g p := M.onBatch_apply (φ g) p

/-- A batch at `y`, read off a pair whose state is `y`. -/
theorem sigma_eqRec {y : A.Table} (q : Σ x : A.Table, Batch A x) (h : q.1 = y) :
    (⟨y, h ▸ q.2⟩ : Σ x : A.Table, Batch A x) = q := by
  subst h
  rfl

/-- The batch at the image of `x` to which a motion carries a batch at `x`. -/
def moveBatch (g : G) {x : A.Table} (b : Batch A x) : Batch A (M.onState g x) :=
  M.onBatch_fst g ⟨x, b⟩ ▸ (M.onBatch g ⟨x, b⟩).2

theorem sigma_moveBatch (g : G) {x : A.Table} (b : Batch A x) :
    (⟨M.onState g x, M.moveBatch g b⟩ : Σ y : A.Table, Batch A y) = M.onBatch g ⟨x, b⟩ :=
  sigma_eqRec _ _

theorem apply_moveBatch (g : G) {x : A.Table} (b : Batch A x) :
    (M.moveBatch g b).apply = M.onState g b.apply :=
  (congrArg (fun p : Σ y : A.Table, Batch A y => p.2.apply) (M.sigma_moveBatch g b)).trans
    (M.onBatch_apply g ⟨x, b⟩)

/-- The image of a run under a motion: every state and every batch carried by it. -/
def moveRun (g : G) {n : ℕ} (r : Run A n) : Run A n where
  state i := M.onState g (r.state i)
  batch i := M.moveBatch g (r.batch i)
  step i := by rw [r.step i, M.apply_moveBatch]

/-- The states fixed by every motion of a subgroup `S`. -/
def fixedStates (S : Subgroup G) : Set A.Table := {x | ∀ s ∈ S, M.onState s x = x}

end Motions

/-! ## Motions of the canvas

A motion of the canvas, a permutation `σ` of its cells, acts on a frame with one value type at
every cell: it carries a table `x` to `σ(x)`, whose value at `c` is the value of `x` at
`σ⁻¹(c)`, and every move to the move that does the same at the moved cells, as Section 3.8
moves attachments (`moveProfile`). -/

section CellMotions

variable {Cell V : Type}

/-- The frame with one value type `V` at every cell. -/
abbrev uniformFrame (Cell V : Type) : Presentation := ⟨Cell, fun _ => V⟩

/-- A motion `σ` of the canvas carries a table `x` to `σ(x)`: the value at `c` is the value of
`x` at `σ⁻¹(c)`. -/
def cellMoveTable (σ : Equiv.Perm Cell) (x : (uniformFrame Cell V).Table) :
    (uniformFrame Cell V).Table :=
  fun c => x (σ.symm c)

/-- A motion `σ` carries a process profile to the profile that does the same at the moved
cells: its guard holds at `x` when the original holds at `σ⁻¹(x)`, and its footprints are the
images of the original's. -/
def cellMoveProfile (σ : Equiv.Perm Cell) (u : ProcessProfile (uniformFrame Cell V)) :
    ProcessProfile (uniformFrame Cell V) where
  guard x := u.guard fun c => x (σ c)
  reads := σ.symm ⁻¹' u.reads
  writes := σ.symm ⁻¹' u.writes
  update x c := u.update (fun d => x (σ d)) (σ.symm c)
  guard_reads x y h := u.guard_reads _ _ fun p hp => h (σ p) (by simpa using hp)
  update_reads x y h c hc := u.update_reads _ _ (fun p hp => h (σ p) (by simpa using hp)) _ hc

theorem cellMoveProfile_guard (σ : Equiv.Perm Cell) (u : ProcessProfile (uniformFrame Cell V))
    (x : (uniformFrame Cell V).Table) :
    (cellMoveProfile σ u).guard (cellMoveTable σ x) ↔ u.guard x := by
  have : (fun c => cellMoveTable σ x (σ c)) = x :=
    funext fun c => congrArg x (σ.symm_apply_apply c)
  change u.guard (fun c => cellMoveTable σ x (σ c)) ↔ u.guard x
  rw [this]

theorem cellMoveProfile_apply (σ : Equiv.Perm Cell) (u : ProcessProfile (uniformFrame Cell V))
    (x : (uniformFrame Cell V).Table) :
    (cellMoveProfile σ u).apply (cellMoveTable σ x) = cellMoveTable σ (u.apply x) := by
  have hx : (fun d => cellMoveTable σ x (σ d)) = x :=
    funext fun d => congrArg x (σ.symm_apply_apply d)
  funext c
  by_cases h : σ.symm c ∈ u.writes
  · have h' : c ∈ (cellMoveProfile σ u).writes := h
    calc (cellMoveProfile σ u).apply (cellMoveTable σ x) c
        = u.update (fun d => cellMoveTable σ x (σ d)) (σ.symm c) := ite_eq_left h'
      _ = u.update x (σ.symm c) := by rw [hx]
      _ = u.apply x (σ.symm c) := (ite_eq_left h).symm
  · have h' : c ∉ (cellMoveProfile σ u).writes := h
    calc (cellMoveProfile σ u).apply (cellMoveTable σ x) c = x (σ.symm c) := ite_eq_right h'
      _ = u.apply x (σ.symm c) := (ite_eq_right h).symm

/-- A motion carries an enabled application to an enabled application. -/
def cellMoveApp (σ : Equiv.Perm Cell) {x : (uniformFrame Cell V).Table}
    (a : EnabledApp (uniformFrame Cell V) x) :
    EnabledApp (uniformFrame Cell V) (cellMoveTable σ x) :=
  ⟨cellMoveProfile σ a.profile, (cellMoveProfile_guard σ a.profile x).2 a.enabled⟩

theorem cellMoveApp_compatible (σ : Equiv.Perm Cell) {x : (uniformFrame Cell V).Table}
    {a b : EnabledApp (uniformFrame Cell V) x} (h : a.Compatible b) :
    (cellMoveApp σ a).Compatible (cellMoveApp σ b) := by
  obtain ⟨hW, hba, hab⟩ := h
  refine ⟨hW.preimage _, fun p hp => ?_, fun p hp => ?_⟩
  · change (cellMoveProfile σ a.profile).apply (cellMoveTable σ x) p = cellMoveTable σ x p
    rw [cellMoveProfile_apply]
    exact hba _ hp
  · change (cellMoveProfile σ b.profile).apply (cellMoveTable σ x) p = cellMoveTable σ x p
    rw [cellMoveProfile_apply]
    exact hab _ hp

theorem applyAll_map_cellMoveApp (σ : Equiv.Perm Cell) {x : (uniformFrame Cell V).Table}
    (l : List (EnabledApp (uniformFrame Cell V) x)) (y : (uniformFrame Cell V).Table) :
    applyAll (l.map (cellMoveApp σ)) (cellMoveTable σ y) = cellMoveTable σ (applyAll l y) := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, applyAll]
    rw [← ih]
    exact congrArg _ (cellMoveProfile_apply σ a.profile y)

/-- A motion carries a batch to a batch, moving each of its moves. -/
def cellMoveBatch (σ : Equiv.Perm Cell) {x : (uniformFrame Cell V).Table}
    (b : Batch (uniformFrame Cell V) x) : Batch (uniformFrame Cell V) (cellMoveTable σ x) :=
  ⟨b.apps.map (cellMoveApp σ), List.pairwise_map.2 (b.compatible.imp (cellMoveApp_compatible σ))⟩

/-- A motion carries a state with a batch there to the moved state with the moved batch. -/
def cellMoveStep (σ : Equiv.Perm Cell)
    (p : Σ x : (uniformFrame Cell V).Table, Batch (uniformFrame Cell V) x) :
    Σ x : (uniformFrame Cell V).Table, Batch (uniformFrame Cell V) x :=
  ⟨cellMoveTable σ p.1, cellMoveBatch σ p.2⟩

theorem cellMoveStep_one
    (p : Σ x : (uniformFrame Cell V).Table, Batch (uniformFrame Cell V) x) :
    cellMoveStep 1 p = p := by
  obtain ⟨x, apps, hc⟩ := p
  have h : ∀ l : List (EnabledApp (uniformFrame Cell V) x), l.map (cellMoveApp 1) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  unfold cellMoveStep cellMoveBatch
  congr 2
  exact h apps

theorem cellMoveStep_mul (σ τ : Equiv.Perm Cell)
    (p : Σ x : (uniformFrame Cell V).Table, Batch (uniformFrame Cell V) x) :
    cellMoveStep (σ * τ) p = cellMoveStep σ (cellMoveStep τ p) := by
  obtain ⟨x, apps, hc⟩ := p
  simp only [cellMoveStep, cellMoveBatch, List.map_map]
  rfl

/-- The motions of the canvas: the permutations of the cells, acting on the tables of a frame
with one value type and on its batches by moving every move. -/
def Motions.ofCells (Cell V : Type) : Motions (Equiv.Perm Cell) (uniformFrame Cell V) where
  onState :=
    { toFun := fun σ =>
        { toFun := cellMoveTable σ
          invFun := cellMoveTable σ⁻¹
          left_inv := fun x => funext fun c => congrArg x (σ.symm_apply_apply c)
          right_inv := fun x => funext fun c => congrArg x (σ.apply_symm_apply c) }
      map_one' := Equiv.ext fun _ => rfl
      map_mul' := fun _ _ => Equiv.ext fun _ => rfl }
  onBatch :=
    { toFun := fun σ =>
        { toFun := cellMoveStep σ
          invFun := cellMoveStep σ⁻¹
          left_inv := fun p => by rw [← cellMoveStep_mul, inv_mul_cancel, cellMoveStep_one]
          right_inv := fun p => by rw [← cellMoveStep_mul, mul_inv_cancel, cellMoveStep_one] }
      map_one' := Equiv.ext cellMoveStep_one
      map_mul' := fun σ τ => Equiv.ext (cellMoveStep_mul σ τ) }
  onBatch_fst _ _ := rfl
  onBatch_apply σ p := applyAll_map_cellMoveApp σ p.2.apps p.1

end CellMotions

namespace Law

variable {G : Type*} [Group G]

/-- A motion `g` is a symmetry of a law with a choice (Sections 5.2 and 5.4): it carries legal
states to legal states, and the batches the law allows at a legal state `x` to batches it
allows at `g(x)`. Applied to `g⁻¹` in a group of symmetries, this gives the converse. -/
def IsSymmetryUnder (L : Law A) (M : Motions G A) (g : G) : Prop :=
  (∀ x, L.Legal x → L.Legal (M.onState g x)) ∧
  ∀ p : Σ x : A.Table, Batch A x, L.Legal p.1 → L.Allows p.2 → L.Allows (M.onBatch g p).2

end Law

/-- A run of a law (Theorem 5.47): its states are legal, and each step applies a batch the
law allows. These are the runs that a relational realizer allowing every such batch allows. -/
def Run.OfLaw {n : ℕ} (L : Law A) (r : Run A n) : Prop :=
  (∀ i, L.Legal (r.state i)) ∧ ∀ i, L.Allows (r.batch i)

/-- The states reachable at tick `n` from `x₀`: the last states of the runs of the law of `n`
ticks from `x₀`. -/
def Law.reachableAt (L : Law A) (x₀ : A.Table) (n : ℕ) : Set A.Table :=
  {y | ∃ r : Run A n, r.state 0 = x₀ ∧ r.OfLaw L ∧ r.state (Fin.last n) = y}

/-- A run keeps the symmetry `S` at a tick when every motion of `S` carries the run to a run
with the same state at that tick (Proposition 5.48). -/
def Run.KeepsSymmetryAt {G : Type*} [Group G] {n : ℕ} (M : Motions G A) (S : Subgroup G)
    (r : Run A n) (i : Fin (n + 1)) : Prop :=
  ∀ s ∈ S, (M.moveRun s r).state i = r.state i

section Commuting

variable {L : Law A} {G : Type*} [Group G]

/-- A deterministic realizer commutes with the motions (Section 5.4): at every legal state
`x`, each motion `g` carries the batch it selects at `x` to the batch it selects at
`g(x)`. -/
def DetRealizer.CommutesWith (R : DetRealizer L) (M : Motions G A) : Prop :=
  ∀ (g : G) (x : A.Table), L.Legal x →
    M.onBatch g ⟨x, R.select x⟩ = ⟨M.onState g x, R.select (M.onState g x)⟩

/-- A stochastic realizer commutes with the motions (Section 5.4): each motion carries every
batch at a legal state to a batch of the same weight. -/
def StochRealizer.CommutesWith (R : StochRealizer L) (M : Motions G A) : Prop :=
  ∀ (g : G) (p : Σ x : A.Table, Batch A x), L.Legal p.1 →
    R.weight (M.onBatch g p).1 (M.onBatch g p).2 = R.weight p.1 p.2

/-- The weight of a state `y` at tick `n` from `x₀` under a stochastic realizer
(Theorem 5.47): the total weight of the runs of positive weight of `n` ticks from `x₀` that
end at `y`, the weight of a run being the product of the weights of its batches. -/
noncomputable def StochRealizer.weightAt (R : StochRealizer L) (x₀ : A.Table) (n : ℕ)
    (y : A.Table) : ℝ≥0∞ :=
  ∑' r : {r : Run A n // r.state 0 = x₀ ∧ r.OfStoch R ∧ r.state (Fin.last n) = y},
    ∏ i, (R.weight _ (r.1.batch i) : ℝ≥0∞)

open Classical in
/-- A deterministic realizer as a stochastic one: weight `1` on the batch it selects, and `0`
on every other batch. -/
noncomputable def DetRealizer.toStoch (R : DetRealizer L) : StochRealizer L where
  weight x b := if b = R.select x then 1 else 0
  allows x hx b hb := by
    by_cases h : b = R.select x
    · subst h
      exact R.allows x hx
    · simp [h] at hb
  keeps x hx b hb := by
    by_cases h : b = R.select x
    · subst h
      exact R.keeps x hx
    · simp [h] at hb

open Classical in
/-- A relational realizer as a stochastic one: weight `1` on each batch it allows, and `0` on
every other batch. -/
noncomputable def RelRealizer.toStoch (R : RelRealizer L) : StochRealizer L where
  weight x b := if R.allowed x b then 1 else 0
  allows x hx b hb := by
    by_cases h : R.allowed x b
    · exact R.allows x hx b h
    · simp [h] at hb
  keeps x hx b hb := by
    by_cases h : R.allowed x b
    · exact R.keeps x hx b h
    · simp [h] at hb

/-- The average of the weights of a stochastic realizer over the motions of a finite group
(Proposition 5.48): the weight of a batch `b` at `x` is the mean, over `g ∈ G`, of the weight
of the batch that `g` carries to it, the image of `⟨x, b⟩` under `g⁻¹`. -/
noncomputable def StochRealizer.averageWeight [Fintype G] (R : StochRealizer L)
    (M : Motions G A) (x : A.Table) (b : Batch A x) : ℝ≥0 :=
  (Fintype.card G : ℝ≥0)⁻¹ *
    ∑ g : G, R.weight (M.onBatch g⁻¹ ⟨x, b⟩).1 (M.onBatch g⁻¹ ⟨x, b⟩).2

end Commuting

end Artform
