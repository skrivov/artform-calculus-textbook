import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ArtformTextbook.Ch05.Laws
import ArtformTextbook.Ch05.Statements
import ArtformTextbook.Ch05.Statements.Patterns
import ArtformTextbook.Ch05.Hall

/-!
# Laws as patterns on the temporal prism (Section 5.21)

The proofs of Propositions 5.42, 5.46 and 5.48 and Theorems 5.45 and 5.47.

* **5.42.** A law of the family is a table from windows to values: the run gives its entry
  at every window that occurs, and says nothing about the others.
* **5.45.** The book's proof: if Hall's condition failed for a set `U` of cells, empty the
  cells of `U` and compare, by no-signalling, what the next tick shows on the cells whose
  halos miss `U`; the count would grow. Hall's theorem (Theorem 5.44, `Artform.hall`) then
  gives whole numbers of tokens sent along allowed pairs, and numbering the tokens turns them
  into a one-to-one pairing. The core, `weave_of_steps`, is stated for any relation of steps,
  so that the three kinds of realizer, and the scripts of Corollary 7.3, share it.
* **5.46.** The moved run `z_s = h(y_{s+j})` is a run exactly under the condition, since the
  steps are bijections and runs pass through every table at every slot; comparing `z_k`
  with `z_0`, written as products of steps, gives the commuting and reversing identities.
* **5.47.** A motion carries a run to a run, step by step; moving by `s⁻¹` undoes moving by
  `s`, so the runs ending at `y` and at `s(y)` correspond, with the same weights.
* **5.48.** (i) holds by definition. (ii) A realizer that commutes with `G` selects at `x` a
  batch fixed by every motion fixing `x`; conversely such batches, chosen at one state of
  each orbit, extend along the orbit by `G`. (iii) Averaging commutes with every motion.
-/

namespace Artform

open scoped BigOperators ENNReal NNReal

open Finset

/-! ## Proposition 5.42 -/

/-- **Proposition 5.42** (what a strung run fixes). Among deterministic laws that read a
declared halo and act alike at every cell, a run fixes the law exactly on the windows it shows,
each with the value it leads to; if `u` windows never occur, `|A|^u` laws agree with the run.
A law of the family is a table from windows to values: the run gives its entry at every window
that occurs, and says nothing about the others, each of which may take any of the `|A|`
values. -/
@[book "prop:run-fixes"]
theorem runFixes : Statement.runFixes := by
  intro Cell K Val _ _ halo f x₀ n
  -- One tick of a law of the family.
  have hrun : ∀ (g : (K → Val) → Val) (t : ℕ), (haloLaw halo g).run x₀ (t + 1) =
      fun y => g (haloWindow halo ((haloLaw halo g).run x₀ t) y) := by
    intro g t
    simp only [DetLaw.run, Function.iterate_succ_apply']
    rfl
  have key : ∀ g : (K → Val) → Val,
      (∀ t ≤ n, (haloLaw halo g).run x₀ t = (haloLaw halo f).run x₀ t) ↔
        ∀ t < n, ∀ y, g (haloWindow halo ((haloLaw halo f).run x₀ t) y) =
          (haloLaw halo f).run x₀ (t + 1) y := by
    intro g
    constructor
    · intro h t ht y
      have h1 := congrFun (h (t + 1) ht) y
      rw [hrun g t, h t ht.le] at h1
      exact h1
    · intro h t ht
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [hrun g t, ih (Nat.le_of_succ_le ht)]
        funext y
        exact h t ht y
  refine ⟨key, fun u hu => ?_⟩
  classical
  -- The windows shown, and the laws that agree with `f` on them.
  set shown : (K → Val) → Prop :=
    fun w => ∃ t < n, ∃ y, haloWindow halo ((haloLaw halo f).run x₀ t) y = w
  have hagree : ∀ g : (K → Val) → Val,
      (∀ t ≤ n, (haloLaw halo g).run x₀ t = (haloLaw halo f).run x₀ t) ↔
        ∀ w, shown w → g w = f w := by
    intro g
    rw [key g]
    constructor
    · rintro h w ⟨t, ht, y, rfl⟩
      rw [h t ht y, hrun f t]
    · intro h t ht y
      rw [h _ ⟨t, ht, y, rfl⟩, hrun f t]
  -- Such a law is any choice of values on the windows not shown.
  let e : {g : (K → Val) → Val // ∀ w, shown w → g w = f w} ≃ ({w : K → Val // ¬ shown w} → Val) :=
    { toFun := fun g w => g.1 w.1
      invFun := fun φ => ⟨fun w => if hw : shown w then f w else φ ⟨w, hw⟩,
        fun w hw => dite_eq_left hw⟩
      left_inv := fun g => Subtype.ext <| funext fun w => by
        by_cases hw : shown w
        · exact (dite_eq_left hw).trans (g.2 w hw).symm
        · exact dite_eq_right hw
      right_inv := fun φ => funext fun w => dite_eq_right w.2 }
  calc Nat.card {g : (K → Val) → Val //
          ∀ t ≤ n, (haloLaw halo g).run x₀ t = (haloLaw halo f).run x₀ t}
      = Nat.card {g : (K → Val) → Val // ∀ w, shown w → g w = f w} :=
        Nat.card_congr (Equiv.subtypeEquivRight hagree)
    _ = Nat.card ({w : K → Val // ¬ shown w} → Val) := Nat.card_congr e
    _ = Nat.card Val ^ u := by rw [Nat.card_fun, hu]

/-! ## Theorem 5.45 -/

namespace Patterns

/-- Exchanging the two indices of a double sum of types. -/
def sigmaSwap {α β : Type*} (γ : α → β → Type*) : (Σ a, Σ b, γ a b) ≃ Σ b, Σ a, γ a b where
  toFun p := ⟨p.2.1, p.1, p.2.2⟩
  invFun q := ⟨q.2.1, q.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {A : Presentation} [Fintype A.P] [∀ p, Zero (A.V p)]

/-- The count of a table is the number of its tokens. -/
theorem card_tokens (c : Count A) (x : A.Table) : Fintype.card (c.Tokens x) = c.N x := by
  simp [Count.Tokens, Count.N, Fintype.card_sigma]

/-- Whole numbers `w(u, y)` of tokens sent from the cells `u` of `x` to the cells `y` of `x'`,
`c_u(x(u))` from each `u` and `c_y(x'(y))` to each `y`, only along allowed pairs, give a
weave: number the tokens sent along each pair. -/
theorem weave_of_transport (c : Count A) (H : A.P → Set A.P) (x x' : A.Table)
    (w : A.P → A.P → ℕ) (hw : ∀ u y, w u y ≠ 0 → u ∈ H y)
    (hrow : ∀ u, ∑ y, w u y = c.tokens u (x u)) (hcol : ∀ y, ∑ u, w u y = c.tokens y (x' y)) :
    Nonempty (Weave H c x x') := by
  classical
  have h1 : ∀ u, Fintype.card (Σ y, Fin (w u y)) = c.tokens u (x u) := fun u => by
    simp [Fintype.card_sigma, hrow u]
  have h2 : ∀ y, Fintype.card (Σ u, Fin (w u y)) = c.tokens y (x' y) := fun y => by
    simp [Fintype.card_sigma, hcol y]
  let e1 : c.Tokens x ≃ Σ u, Σ y, Fin (w u y) :=
    Equiv.sigmaCongrRight fun u => (Fintype.equivFinOfCardEq (h1 u)).symm
  let e3 : (Σ y, Σ u, Fin (w u y)) ≃ c.Tokens x' :=
    Equiv.sigmaCongrRight fun y => Fintype.equivFinOfCardEq (h2 y)
  refine ⟨⟨e1.trans ((sigmaSwap fun u y => Fin (w u y)).trans e3), fun t => ?_⟩⟩
  obtain ⟨u, i⟩ := t
  -- The token `i` at `u` travels along the pair `(u, q.1)`, which carries a token.
  set q := (Fintype.equivFinOfCardEq (h1 u)).symm i
  change u ∈ H q.1
  exact hw u q.1 (Fin.pos q.2).ne'

/-- **The core of Theorem 5.45**, for any relation of steps `x → x'` from legal states: if
emptying cells keeps tables legal, every step keeps the count, and what a step may show on a
set `V` of cells depends only on the table on `H(V)` (for legal tables `x` and `z` that agree
on `H(V)`, each step from `x` has a step from `z` that shows the same on `V`), then every step
has a weave along `H`. -/
theorem weave_of_steps {Legal : A.Table → Prop} {Step : A.Table → A.Table → Prop}
    {c : Count A} {H : A.P → Set A.P}
    (hE : ∀ x, Legal x → ∀ U : Set A.P, Legal (emptyCells U x))
    (hNS : ∀ (V : Set A.P) (x z x' : A.Table), Legal x → Legal z →
      (∀ p ∈ haloOf H V, x p = z p) → Step x x' → ∃ z', Step z z' ∧ ∀ p ∈ V, z' p = x' p)
    (hK : ∀ x x', Legal x → Step x x' → c.N x' = c.N x)
    {x x' : A.Table} (hx : Legal x) (hxx' : Step x x') : Nonempty (Weave H c x x') := by
  classical
  have hN : c.N x' = c.N x := hK x x' hx hxx'
  -- Hall's condition: every set `U` of cells holds at most as many tokens of `x` as the cells
  -- whose halos meet `U` hold tokens of `x'`.
  have hHall : ∀ U : Finset A.P, ∑ u ∈ U, c.tokens u (x u) ≤
      ∑ y ∈ univ.filter (fun y => ∃ u ∈ U, u ∈ H y), c.tokens y (x' y) := by
    intro U
    by_contra hle
    have hlt := not_le.1 hle
    -- `V`: the cells whose halos miss `U`; `z`: the table `x` with the cells of `U` emptied.
    set V : Set A.P := {y | ¬ ∃ u ∈ U, u ∈ H y} with hV
    set z := emptyCells (↑U : Set A.P) x with hz
    have hzL : Legal z := hE x hx _
    have hag : ∀ p ∈ haloOf H V, x p = z p := by
      intro p hp
      simp only [haloOf, Set.mem_iUnion] at hp
      obtain ⟨y, hy, hpy⟩ := hp
      have hpU : p ∉ U := fun hpU => hy ⟨p, hpU, hpy⟩
      simp [hz, emptyCells, hpU]
    -- By no-signalling, a step from `z` shows on `V` what `x'` shows there.
    obtain ⟨z', hzz', hz'V⟩ := hNS V x z x' hx hzL hag hxx'
    have hNz : c.N z' = c.N z := hK z z' hzL hzz'
    -- `N(z) = N(x) - N_U(x)`.
    have h1 : c.N z + ∑ u ∈ U, c.tokens u (x u) = c.N x := by
      have hzU : ∑ u ∈ univ.filter (· ∈ U), c.tokens u (z u) = 0 :=
        sum_eq_zero fun u hu => by
          have hu' : u ∈ U := (mem_filter.1 hu).2
          simp [hz, emptyCells, hu', c.tokens_zero]
      have hzn : ∑ u ∈ univ.filter (· ∉ U), c.tokens u (z u) =
          ∑ u ∈ univ.filter (· ∉ U), c.tokens u (x u) :=
        sum_congr rfl fun u hu => by
          have hu' : u ∉ U := (mem_filter.1 hu).2
          simp [hz, emptyCells, hu']
      have hU : univ.filter (· ∈ U) = U := by
        ext u
        simp
      have ez := sum_filter_add_sum_filter_not univ (· ∈ U) fun u => c.tokens u (z u)
      have ex := sum_filter_add_sum_filter_not univ (· ∈ U) fun u => c.tokens u (x u)
      rw [hzU, hzn, zero_add] at ez
      rw [hU] at ex
      change ∑ u, c.tokens u (z u) + ∑ u ∈ U, c.tokens u (x u) = ∑ u, c.tokens u (x u)
      rw [← ez, ← ex, add_comm]
    -- `N(x') = N_{A(U)}(x') + N_V(x')`.
    have h2 := sum_filter_add_sum_filter_not univ (fun y => ∃ u ∈ U, u ∈ H y)
      fun y => c.tokens y (x' y)
    -- `N_V(x') = N_V(z') ≤ N(z')`.
    have h3 : ∑ y ∈ univ.filter (fun y => ¬ ∃ u ∈ U, u ∈ H y), c.tokens y (x' y) ≤ c.N z' := by
      calc ∑ y ∈ univ.filter (fun y => ¬ ∃ u ∈ U, u ∈ H y), c.tokens y (x' y)
          = ∑ y ∈ univ.filter (fun y => ¬ ∃ u ∈ U, u ∈ H y), c.tokens y (z' y) :=
            sum_congr rfl fun y hy => by rw [hz'V y (mem_filter.1 hy).2]
        _ ≤ ∑ y, c.tokens y (z' y) := sum_le_sum_of_subset (filter_subset _ _)
    change _ = ∑ y, c.tokens y (x' y) at h2
    change c.N z' = c.N z at hNz
    have hNx' : c.N x' = ∑ y, c.tokens y (x' y) := rfl
    omega
  obtain ⟨w, hw, hrow, hcol⟩ := (hall A.P A.P (fun u => c.tokens u (x u))
    (fun y => c.tokens y (x' y)) (fun u y => u ∈ H y) hN.symm).2 fun U => by
      convert hHall U
  exact weave_of_transport c H x x' w hw hrow hcol

end Patterns

/-- **Theorem 5.45** (a kept count is woven). Let every table obtained from a legal table by
emptying cells be legal, let `H` be a no-signalling halo of a realizer, and let the law keep a
count. Then every step `x → x'` the realizer allows has a weave along `H`; conversely, a step
that has a weave keeps the count. The converse holds because a weave moves tokens and makes
none; the theorem by Hall's theorem, `Patterns.weave_of_steps`. -/
@[book "thm:woven"]
theorem woven : Statement.woven := by
  intro A _ _ L c H
  refine ⟨fun hE => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro R hNS hK x x' hxx'
    refine Patterns.weave_of_steps (Legal := L.Legal) (Step := R.AllowsStep) hE
      (fun V x z x' hx hz hag hst => ?_) (fun x x' _ h => hK x x' h) hxx'.1 hxx'
    refine ⟨(R.select z).apply, ⟨hz, rfl⟩, fun p hp => ?_⟩
    have h := congrFun (hNS V x z hx hz hag) ⟨p, hp⟩
    rw [← hst.2]
    exact h.symm
  · intro R hNS hK x x' hxx'
    refine Patterns.weave_of_steps (Legal := L.Legal) (Step := R.AllowsStep) hE
      (fun V x z x' hx hz hag hst => ?_) (fun x x' _ h => hK x x' h) hxx'.1 hxx'
    obtain ⟨-, b, hb, rfl⟩ := hst
    have hmem : restrictTo V b.apply ∈ R.shows z V := by
      rw [← hNS V x z hx hz hag]
      exact ⟨b, hb, rfl⟩
    obtain ⟨b', hb', he⟩ := hmem
    exact ⟨b'.apply, ⟨hz, b', hb', rfl⟩, fun p hp => congrFun he ⟨p, hp⟩⟩
  · intro R hNS hK x x' hxx'
    refine Patterns.weave_of_steps (Legal := L.Legal) (Step := R.AllowsStep) hE
      (fun V x z x' hx hz hag hst => ?_) (fun x x' _ h => hK x x' h) hxx'.1 hxx'
    classical
    obtain ⟨-, b, hb, rfl⟩ := hst
    -- The table that `b` shows on `V` has positive weight from `x`, so also from `z`.
    have hpos : R.showWeight x V (restrictTo V b.apply) ≠ 0 := by
      intro h0
      have h := (ENNReal.tsum_eq_zero.1 h0) b
      rw [ite_eq_left rfl] at h
      exact hb (by exact_mod_cast h)
    rw [hNS V x z hx hz hag] at hpos
    obtain ⟨b', hb'⟩ := not_forall.1 (mt ENNReal.tsum_eq_zero.2 hpos)
    by_cases he : restrictTo V b'.apply = restrictTo V b.apply
    · rw [ite_eq_left he] at hb'
      exact ⟨b'.apply, ⟨hz, b', by exact_mod_cast hb', rfl⟩, fun p hp => congrFun he ⟨p, hp⟩⟩
    · exact absurd (ite_eq_right he) hb'
  · rintro x x' ⟨π⟩
    rw [← Patterns.card_tokens, ← Patterns.card_tokens]
    exact (Fintype.card_congr π.pair).symm

/-! ## Proposition 5.46 -/

namespace Patterns

variable {X : Type*} {k : ℕ} (S : ZMod k → Equiv.Perm X)

/-- The steps of the `m` slots from slot `a`: `S_{a+m-1} ∘ ⋯ ∘ S_a`. -/
def stepsFrom (a : ZMod k) : ℕ → Equiv.Perm X
  | 0 => 1
  | m + 1 => S (a + m) * stepsFrom a m

theorem firstSteps_eq_stepsFrom (m : ℕ) : firstSteps S m = stepsFrom S 0 m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [firstSteps, stepsFrom, ih]

/-- Peeling the first step off a stretch of slots. -/
theorem stepsFrom_succ' (a : ZMod k) (m : ℕ) :
    stepsFrom S a (m + 1) = stepsFrom S (a + 1) m * S a := by
  induction m with
  | zero => simp [stepsFrom]
  | succ m ih =>
    rw [stepsFrom, ih, stepsFrom, mul_assoc]
    congr 2
    push_cast
    ring

/-- The first `a + b` steps are the first `a`, then the `b` slots from slot `a`. -/
theorem firstSteps_add (a b : ℕ) :
    firstSteps S (a + b) = stepsFrom S a b * firstSteps S a := by
  induction b with
  | zero => simp [stepsFrom]
  | succ b ih =>
    rw [← add_assoc, firstSteps, ih, stepsFrom, mul_assoc]
    push_cast
    rfl

/-- `P_j ∘ F = W ∘ P_j`, for `W` the `k` slots from slot `j`. -/
theorem firstSteps_mul_tick (j : ℕ) :
    firstSteps S j * firstSteps S k = stepsFrom S j k * firstSteps S j := by
  have h1 := firstSteps_add S k j
  have h2 := firstSteps_add S j k
  rw [ZMod.natCast_self, ← firstSteps_eq_stepsFrom] at h1
  rw [← h2, add_comm, h1]

/-- The steps back from slot `0`: `Q(-1) = S_{-1}⁻¹` and `Q(-(m+2)) = S_{-(m+2)}⁻¹ ∘ Q(-(m+1))`. -/
def backSteps : ℕ → Equiv.Perm X
  | 0 => (S ((Int.negSucc 0 : ℤ) : ZMod k))⁻¹
  | m + 1 => (S ((Int.negSucc (m + 1) : ℤ) : ZMod k))⁻¹ * backSteps m

/-- The propagator of the slots: `Q 0 = 1`, and `Q (s + 1) = S s ∘ Q s` at every slot `s ∈ ℤ`. -/
def propagator : ℤ → Equiv.Perm X
  | Int.ofNat m => firstSteps S m
  | Int.negSucc m => backSteps S m

theorem propagator_succ (s : ℤ) : propagator S (s + 1) = S s * propagator S s := by
  rcases s with m | m
  · change firstSteps S (m + 1) = S ((Int.ofNat m : ℤ) : ZMod k) * firstSteps S m
    simp [firstSteps]
  · rcases m with _ | m
    · change firstSteps S 0 = S ((Int.negSucc 0 : ℤ) : ZMod k) * backSteps S 0
      simp [firstSteps, backSteps]
    · have h : Int.negSucc (m + 1) + 1 = Int.negSucc m := by omega
      rw [h]
      change backSteps S m = S ((Int.negSucc (m + 1) : ℤ) : ZMod k) * backSteps S (m + 1)
      simp [backSteps]

/-- Since the steps are bijections, a run passes through every table at every slot. -/
theorem exists_slotRun (σ : ℤ) (v : X) : ∃ y : ℤ → X, IsSlotRun S y ∧ y σ = v := by
  refine ⟨fun t => propagator S t ((propagator S σ)⁻¹ v), fun t => ?_, ?_⟩
  · simp only [propagator_succ, Equiv.Perm.mul_apply]
  · simp

end Patterns

open Patterns in
/-- **Proposition 5.46** (symmetries of a slot tapestry). Applying `h` at every slot and
shifting by `j` carries every run of the slots to a run if and only if
`h ∘ S_{(s+j) mod k} ∘ h⁻¹ = S_s` for every `s`; then `h ∘ P_j` commutes with the tick. Applying
`h`, reversing time and shifting by `j` does so if and only if
`h ∘ S_{(j-1-s) mod k}⁻¹ ∘ h⁻¹ = S_s` for every `s`; then `h ∘ P_j` reverses the tick. The moved
run `z_s = h(y_{s+j})` satisfies `z_{s+1} = h S_{s+j} h⁻¹ (z_s)`, a run exactly under the first
condition since runs pass through every table at every slot; comparing `z_k` with `z_0` gives
`h P_j F = F h P_j`. The reversed case is the same computation with `z_s = h(y_{j-s})`. -/
@[book "prop:slot-symmetry"]
theorem slotSymmetry : Statement.slotSymmetry := by
  intro X k S h j
  refine ⟨⟨fun hrun s => ?_, fun hc y hy t => ?_⟩, fun hc => ?_,
    ⟨fun hrun s => ?_, fun hc y hy t => ?_⟩, fun hc => ?_⟩
  · -- A run through `h⁻¹ v` at slot `σ + j` is carried to a run through `v` at slot `σ`.
    obtain ⟨σ, rfl⟩ := ZMod.intCast_surjective s
    ext v
    obtain ⟨y, hy, hyv⟩ := exists_slotRun S (σ + j) (h⁻¹ v)
    have hz := hrun y hy σ
    have e1 : σ + 1 + (j : ℤ) = (σ + j) + 1 := by ring
    simp only [e1, hy (σ + j), hyv] at hz
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at hz ⊢
    push_cast at hz
    exact hz
  · have e1 : t + 1 + (j : ℤ) = (t + j) + 1 := by ring
    simp only [e1, hy (t + j)]
    rw [← hc (t : ZMod k)]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    push_cast
    rfl
  · -- `h ∘ W = F ∘ h`, for `W` the `k` slots from slot `j`, slot by slot.
    have hW : ∀ m : ℕ, h * stepsFrom S j m = stepsFrom S 0 m * h := by
      intro m
      induction m with
      | zero => simp [stepsFrom]
      | succ m ih =>
        have hm : h * S ((j : ZMod k) + m) = S m * h := by
          rw [← hc (m : ZMod k), inv_mul_cancel_right, add_comm]
        rw [stepsFrom, stepsFrom, zero_add, ← mul_assoc, hm, mul_assoc, ih, ← mul_assoc]
    rw [mul_assoc h, firstSteps_mul_tick, ← mul_assoc, hW k, ← firstSteps_eq_stepsFrom,
      mul_assoc]
  · -- A run through `h⁻¹ v` at slot `j - σ` is carried to a run through `v` at slot `σ`.
    obtain ⟨σ, rfl⟩ := ZMod.intCast_surjective s
    ext v
    obtain ⟨y, hy, hyv⟩ := exists_slotRun S ((j : ℤ) - σ) (h⁻¹ v)
    have hz := hrun y hy σ
    have hstep := hy ((j : ℤ) - σ - 1)
    have e1 : (j : ℤ) - σ - 1 + 1 = (j : ℤ) - σ := by ring
    have e2 : (j : ℤ) - (σ + 1) = (j : ℤ) - σ - 1 := by ring
    have ecast : (((j : ℤ) - σ - 1 : ℤ) : ZMod k) = (j : ZMod k) - 1 - σ := by
      push_cast
      ring
    rw [e1, hyv, ecast] at hstep
    simp only [e2, hyv] at hz
    have hback : y ((j : ℤ) - σ - 1) = (S ((j : ZMod k) - 1 - σ))⁻¹ (h⁻¹ v) := by
      rw [hstep]
      simp
    rw [hback] at hz
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at hz ⊢
    exact hz
  · have hstep := hy ((j : ℤ) - t - 1)
    have e1 : (j : ℤ) - t - 1 + 1 = (j : ℤ) - t := by ring
    have e2 : (j : ℤ) - (t + 1) = (j : ℤ) - t - 1 := by ring
    have ecast : (((j : ℤ) - t - 1 : ℤ) : ZMod k) = (j : ZMod k) - 1 - t := by
      push_cast
      ring
    rw [e1, ecast] at hstep
    simp only [e2]
    rw [← hc (t : ZMod k), hstep]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  · -- `h ∘ W⁻¹ ∘ h⁻¹ = F`, slot by slot.
    have hE : ∀ m : ℕ, h * (stepsFrom S j m)⁻¹ * h⁻¹ = stepsFrom S (-(m : ZMod k)) m := by
      intro m
      induction m with
      | zero => simp [stepsFrom]
      | succ m ih =>
        have hm : h * (S ((j : ZMod k) + m))⁻¹ * h⁻¹ = S (-1 - m) := by
          rw [← hc (-1 - m), show (j : ZMod k) - 1 - (-1 - m) = j + m by ring]
        have e3 : -((m + 1 : ℕ) : ZMod k) + 1 = -(m : ZMod k) := by
          push_cast
          ring
        have e4 : -((m + 1 : ℕ) : ZMod k) = -1 - m := by
          push_cast
          ring
        calc h * (stepsFrom S j (m + 1))⁻¹ * h⁻¹
            = (h * (stepsFrom S j m)⁻¹ * h⁻¹) * (h * (S ((j : ZMod k) + m))⁻¹ * h⁻¹) := by
              rw [stepsFrom, mul_inv_rev]
              group
          _ = stepsFrom S (-(m : ZMod k)) m * S (-1 - m) := by rw [ih, hm]
          _ = stepsFrom S (-((m + 1 : ℕ) : ZMod k)) (m + 1) := by rw [stepsFrom_succ', e3, e4]
    have hF : h * (stepsFrom S j k)⁻¹ * h⁻¹ = firstSteps S k := by
      rw [hE k, ZMod.natCast_self, neg_zero, firstSteps_eq_stepsFrom]
    calc h * firstSteps S j * firstSteps S k * (h * firstSteps S j)⁻¹
        = h * (firstSteps S j * firstSteps S k) * (firstSteps S j)⁻¹ * h⁻¹ := by group
      _ = h * stepsFrom S j k * h⁻¹ := by
        rw [firstSteps_mul_tick]
        group
      _ = (h * (stepsFrom S j k)⁻¹ * h⁻¹)⁻¹ := by group
      _ = (firstSteps S k)⁻¹ := by rw [hF]

/-! ## Theorem 5.47 -/

namespace Patterns

variable {A : Presentation}

/-- Two runs are equal when their states agree and their batches agree, each taken with its
state. -/
theorem run_ext {n : ℕ} {r₁ r₂ : Run A n} (hs : ∀ i, r₁.state i = r₂.state i)
    (hb : ∀ i : Fin n, (⟨r₁.state i.castSucc, r₁.batch i⟩ : Σ x : A.Table, Batch A x) =
      ⟨r₂.state i.castSucc, r₂.batch i⟩) : r₁ = r₂ := by
  obtain ⟨s₁, b₁, h₁⟩ := r₁
  obtain ⟨s₂, b₂, h₂⟩ := r₂
  obtain rfl : s₁ = s₂ := funext hs
  obtain rfl : b₁ = b₂ := funext fun i => eq_of_heq (Sigma.mk.inj (hb i)).2
  rfl

variable {G : Type*} [Group G] (M : Motions G A)

theorem onState_inv_mul (g : G) (x : A.Table) : M.onState g⁻¹ (M.onState g x) = x := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]

theorem onState_mul_inv (g : G) (x : A.Table) : M.onState g (M.onState g⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

theorem onBatch_mul_inv (g : G) (p : Σ x : A.Table, Batch A x) :
    M.onBatch g (M.onBatch g⁻¹ p) = p := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

theorem moveRun_mul (g h : G) {n : ℕ} (r : Run A n) :
    M.moveRun g (M.moveRun h r) = M.moveRun (g * h) r := by
  refine run_ext (fun i => ?_) (fun i => ?_)
  · change M.onState g (M.onState h (r.state i)) = M.onState (g * h) (r.state i)
    rw [map_mul, Equiv.Perm.mul_apply]
  · change (⟨M.onState g (M.onState h (r.state i.castSucc)),
        M.moveBatch g (M.moveBatch h (r.batch i))⟩ : Σ x : A.Table, Batch A x) =
      ⟨M.onState (g * h) (r.state i.castSucc), M.moveBatch (g * h) (r.batch i)⟩
    rw [M.sigma_moveBatch g, M.sigma_moveBatch h, M.sigma_moveBatch (g * h), map_mul,
      Equiv.Perm.mul_apply]

theorem moveRun_one {n : ℕ} (r : Run A n) : M.moveRun 1 r = r := by
  refine run_ext (fun i => ?_) (fun i => ?_)
  · change M.onState 1 (r.state i) = r.state i
    rw [map_one, Equiv.Perm.one_apply]
  · change (⟨M.onState 1 (r.state i.castSucc), M.moveBatch 1 (r.batch i)⟩ :
      Σ x : A.Table, Batch A x) = ⟨r.state i.castSucc, r.batch i⟩
    rw [M.sigma_moveBatch 1, map_one, Equiv.Perm.one_apply]

/-- A property of the batch in a pair, carried along an equality of pairs. -/
theorem snd_congr {p q : Σ x : A.Table, Batch A x} (h : p = q) (P : ∀ {x}, Batch A x → Prop) :
    P p.2 ↔ P q.2 := by
  subst h
  rfl

end Patterns

open Patterns in
/-- **Theorem 5.47** (symmetry of what may happen). Let every motion of a group `G` be a
symmetry of a law, and let the motions of a subgroup `S` fix the start `x₀`. Then every motion
of `S` carries the runs from `x₀` to runs from `x₀`, so the set of states reachable at each tick
is carried to itself by `S`; if a stochastic realizer commutes with `G`, the weight of each
state at each tick is the weight of its image under `S`. A motion `s` carries a run to the run
of the moved states and batches, each step allowed because `s` carries allowed batches to
allowed batches; for weights the same computation carries each run to a run of the same
weight, and moving by `s⁻¹` undoes it. -/
@[book "thm:curie"]
theorem curie : Statement.curie := by
  intro A L G _ M hG S x₀ hx₀
  -- A motion carries a run of the law to a run of the law, step by step.
  have hrun : ∀ (g : G) (n : ℕ) (r : Run A n), r.OfLaw L → (M.moveRun g r).OfLaw L := by
    intro g n r hr
    refine ⟨fun i => (hG g).1 _ (hr.1 i), fun i => ?_⟩
    have h := (hG g).2 ⟨_, r.batch i⟩ (hr.1 _) (hr.2 i)
    exact (snd_congr (M.sigma_moveBatch g (r.batch i)) L.Allows).2 h
  have hreach : ∀ s ∈ S, ∀ n, ∀ y ∈ L.reachableAt x₀ n, M.onState s y ∈ L.reachableAt x₀ n := by
    rintro s hs n y ⟨r, h0, hr, rfl⟩
    refine ⟨M.moveRun s r, ?_, hrun s n r hr, rfl⟩
    change M.onState s (r.state 0) = x₀
    rw [h0, hx₀ s hs]
  refine ⟨fun s hs n r h0 hr => ⟨?_, hrun s n r hr⟩, fun s hs n => ?_, fun R hR s hs n y => ?_⟩
  · change M.onState s (r.state 0) = x₀
    rw [h0, hx₀ s hs]
  · refine Set.Subset.antisymm ?_ fun y hy => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hreach s hs n y hy
    · exact ⟨M.onState s⁻¹ y, hreach s⁻¹ (S.inv_mem hs) n y hy, onState_mul_inv M s y⟩
  · -- A motion carries a run of positive weight to one of the same weight.
    have hmove : ∀ (g : G) (r : Run A n), r.OfStoch R →
        (M.moveRun g r).OfStoch R ∧
          ∀ i, R.weight _ ((M.moveRun g r).batch i) = R.weight _ (r.batch i) := by
      intro g r hr
      have hw : ∀ i, R.weight _ ((M.moveRun g r).batch i) = R.weight _ (r.batch i) := by
        intro i
        have h := hR g ⟨_, r.batch i⟩ (hr.1 _)
        rw [← M.sigma_moveBatch g (r.batch i)] at h
        exact h
      exact ⟨⟨fun i => (hG g).1 _ (hr.1 i), fun i => (hw i).symm ▸ hr.2 i⟩, hw⟩
    let e : {r : Run A n // r.state 0 = x₀ ∧ r.OfStoch R ∧ r.state (Fin.last n) = y} ≃
        {r : Run A n // r.state 0 = x₀ ∧ r.OfStoch R ∧
          r.state (Fin.last n) = M.onState s y} :=
      { toFun := fun r => ⟨M.moveRun s r.1, by
          refine ⟨?_, (hmove s r.1 r.2.2.1).1, ?_⟩
          · change M.onState s (r.1.state 0) = x₀
            rw [r.2.1, hx₀ s hs]
          · change M.onState s (r.1.state (Fin.last n)) = M.onState s y
            rw [r.2.2.2]⟩
        invFun := fun r => ⟨M.moveRun s⁻¹ r.1, by
          refine ⟨?_, (hmove s⁻¹ r.1 r.2.2.1).1, ?_⟩
          · change M.onState s⁻¹ (r.1.state 0) = x₀
            rw [r.2.1, hx₀ s⁻¹ (S.inv_mem hs)]
          · change M.onState s⁻¹ (r.1.state (Fin.last n)) = y
            rw [r.2.2.2, onState_inv_mul]⟩
        left_inv := fun r => Subtype.ext <| by
          change M.moveRun s⁻¹ (M.moveRun s r.1) = r.1
          rw [moveRun_mul, inv_mul_cancel, moveRun_one]
        right_inv := fun r => Subtype.ext <| by
          change M.moveRun s (M.moveRun s⁻¹ r.1) = r.1
          rw [moveRun_mul, mul_inv_cancel, moveRun_one] }
    unfold StochRealizer.weightAt
    rw [← e.tsum_eq]
    congr 1
    funext r
    exact Finset.prod_congr rfl fun i _ =>
      congrArg (fun w : ℝ≥0 => (w : ℝ≥0∞)) ((hmove s r.1 r.2.2.1).2 i)

/-! ## Proposition 5.48 -/

open Patterns in
/-- **Proposition 5.48** (breaking needs a choice). Under the hypotheses of Theorem 5.47: a
run keeps the symmetry `S` at every tick if and only if it stays among the states that `S`
fixes; a deterministic realizer that commutes with `G` exists if and only if at every legal
state some allowed batch is fixed by every motion that fixes the state; and averaging any
realizer over the motions of `G` gives a stochastic realizer that commutes with `G`. (i) holds
by definition. (ii) A realizer that commutes with `G` must choose at `x` a batch fixed by every
motion fixing `x`; conversely such batches, chosen at one state of each orbit, extend along
the orbit by `G`. (iii) Averaging commutes with every motion of `G`. -/
@[book "prop:breaking"]
theorem breaking : Statement.breaking := by
  intro A L G _ M hG S x₀ hx₀
  -- The motions keep legality, both ways.
  have hlegal : ∀ (g : G) x, L.Legal x → L.Legal (M.onState g x) := fun g => (hG g).1
  refine ⟨fun n r => Iff.rfl, ⟨?_, ?_⟩, ?_⟩
  · -- (ii), only if: the batch selected at `x` is fixed by every motion fixing `x`.
    rintro ⟨R, hR⟩ x hx
    refine ⟨R.select x, R.allows x hx, R.keeps x hx, fun g hg => ?_⟩
    rw [hR g x hx]
    exact congrArg (fun y => (⟨y, R.select y⟩ : Σ y : A.Table, Batch A y)) hg
  · -- (ii), if: choose a fixed batch at one state of each orbit, and carry it along the orbit.
    intro hfix
    classical
    let orb : Setoid A.Table :=
      { r := fun x y => ∃ g : G, M.onState g x = y
        iseqv := ⟨fun x => ⟨1, by rw [map_one, Equiv.Perm.one_apply]⟩,
          fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, onState_inv_mul]⟩,
          fun ⟨g, hg⟩ ⟨g', hg'⟩ => ⟨g' * g, by rw [map_mul, Equiv.Perm.mul_apply, hg, hg']⟩⟩ }
    -- The representative of the orbit of `x`, and a motion carrying it to `x`.
    let rep : A.Table → A.Table := fun x => (Quotient.mk orb x).out
    have hrep : ∀ x, ∃ g : G, M.onState g (rep x) = x := fun x => Quotient.mk_out (s := orb) x
    have hrep_move : ∀ (g : G) x, rep (M.onState g x) = rep x := fun g x => by
      change (Quotient.mk orb (M.onState g x)).out = (Quotient.mk orb x).out
      rw [Quotient.sound (show orb.r (M.onState g x) x from ⟨g⁻¹, onState_inv_mul M g x⟩)]
    let gAt : A.Table → G := fun x => (hrep x).choose
    have hgAt : ∀ x, M.onState (gAt x) (rep x) = x := fun x => (hrep x).choose_spec
    have hlegal_rep : ∀ x, L.Legal x → L.Legal (rep x) := by
      intro x hx
      have e : M.onState (gAt x)⁻¹ x = rep x := by
        calc M.onState (gAt x)⁻¹ x = M.onState (gAt x)⁻¹ (M.onState (gAt x) (rep x)) := by
              rw [hgAt x]
          _ = rep x := onState_inv_mul M _ _
      rw [← e]
      exact hlegal _ x hx
    -- The batch chosen at a legal representative.
    let bAt : (y : A.Table) → L.Legal y → Batch A y := fun y hy => (hfix y hy).choose
    have hbAt : ∀ y (hy : L.Legal y), L.Allows (bAt y hy) ∧ L.Legal (bAt y hy).apply ∧
        ∀ g : G, M.onState g y = y → M.onBatch g ⟨y, bAt y hy⟩ = ⟨y, bAt y hy⟩ :=
      fun y hy => (hfix y hy).choose_spec
    have hbAt_congr : ∀ y y' (hy : L.Legal y) (hy' : L.Legal y'), y = y' →
        (⟨y, bAt y hy⟩ : Σ x : A.Table, Batch A x) = ⟨y', bAt y' hy'⟩ := by
      rintro y _ hy hy' rfl
      rfl
    -- The batch at `x`, with its state: carried from the representative.
    let pairAt : A.Table → Σ y : A.Table, Batch A y := fun x =>
      if hx : L.Legal x then M.onBatch (gAt x) ⟨rep x, bAt (rep x) (hlegal_rep x hx)⟩
      else ⟨x, ⟨[], List.Pairwise.nil⟩⟩
    have hpair_legal : ∀ x (hx : L.Legal x),
        pairAt x = M.onBatch (gAt x) ⟨rep x, bAt (rep x) (hlegal_rep x hx)⟩ :=
      fun x hx => dite_eq_left hx
    have hpair_fst : ∀ x, (pairAt x).1 = x := by
      intro x
      by_cases hx : L.Legal x
      · rw [hpair_legal x hx, M.onBatch_fst]
        exact hgAt x
      · exact congrArg Sigma.fst (dite_eq_right hx : pairAt x = ⟨x, ⟨[], List.Pairwise.nil⟩⟩)
    have hpair : ∀ x (hx : L.Legal x),
        (⟨x, hpair_fst x ▸ (pairAt x).2⟩ : Σ y : A.Table, Batch A y) =
          M.onBatch (gAt x) ⟨rep x, bAt (rep x) (hlegal_rep x hx)⟩ := by
      intro x hx
      rw [Motions.sigma_eqRec]
      exact hpair_legal x hx
    let R : DetRealizer L :=
      { select := fun x => hpair_fst x ▸ (pairAt x).2
        allows := fun x hx => by
          have h := (hG (gAt x)).2 ⟨rep x, bAt (rep x) (hlegal_rep x hx)⟩ (hlegal_rep x hx)
            (hbAt _ (hlegal_rep x hx)).1
          exact (snd_congr (hpair x hx) L.Allows).2 h
        keeps := fun x hx => by
          have h : L.Legal
              (M.onBatch (gAt x) ⟨rep x, bAt (rep x) (hlegal_rep x hx)⟩).2.apply := by
            rw [M.onBatch_apply]
            exact hlegal (gAt x) _ (hbAt _ (hlegal_rep x hx)).2.1
          exact (snd_congr (hpair x hx) fun b => L.Legal b.apply).2 h }
    refine ⟨R, fun g x hx => ?_⟩
    have hgx : L.Legal (M.onState g x) := hlegal g x hx
    have hr : rep (M.onState g x) = rep x := hrep_move g x
    change M.onBatch g ⟨x, hpair_fst x ▸ (pairAt x).2⟩ =
      ⟨M.onState g x, hpair_fst (M.onState g x) ▸ (pairAt (M.onState g x)).2⟩
    rw [hpair x hx, hpair _ hgx, hbAt_congr (rep (M.onState g x)) (rep x) (hlegal_rep _ hgx)
      (hlegal_rep x hx) hr]
    -- `k = gAt(g x)⁻¹ * g * gAt x` fixes the representative, so it fixes its batch.
    have hk : M.onState ((gAt (M.onState g x))⁻¹ * g * gAt x) (rep x) = rep x := by
      have h := hgAt (M.onState g x)
      rw [hr] at h
      rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgAt x, map_inv,
        Equiv.Perm.inv_eq_iff_eq, h]
    have hfixk := (hbAt (rep x) (hlegal_rep x hx)).2.2 _ hk
    rw [← Equiv.Perm.mul_apply, ← map_mul,
      show g * gAt x = gAt (M.onState g x) * ((gAt (M.onState g x))⁻¹ * g * gAt x) by group,
      map_mul, Equiv.Perm.mul_apply, hfixk]
  · -- (iii): the average commutes with every motion.
    intro _
    have hstoch : ∀ R : StochRealizer L, ∃ R' : StochRealizer L,
        R'.weight = R.averageWeight M ∧ R'.CommutesWith M := by
      intro R
      -- The weight of a batch, taken with its state.
      let wt : (Σ x : A.Table, Batch A x) → ℝ≥0 := fun p => R.weight p.1 p.2
      have havg : ∀ x (b : Batch A x), R.averageWeight M x b =
          (Fintype.card G : ℝ≥0)⁻¹ * ∑ g : G, wt (M.onBatch g⁻¹ ⟨x, b⟩) := fun _ _ => rfl
      -- A batch of positive average weight is the image of a batch of positive weight.
      have hpos : ∀ x (b : Batch A x), R.averageWeight M x b ≠ 0 →
          ∃ g : G, wt (M.onBatch g⁻¹ ⟨x, b⟩) ≠ 0 := by
        intro x b h
        rw [havg] at h
        obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
        exact ⟨g, hg⟩
      refine ⟨{ weight := R.averageWeight M, allows := ?_, keeps := ?_ }, rfl, ?_⟩
      · intro x hx b hb
        obtain ⟨g, hg⟩ := hpos x b hb
        have hq : L.Legal (M.onBatch g⁻¹ ⟨x, b⟩).1 := by
          rw [M.onBatch_fst]
          exact hlegal _ _ hx
        have h := (hG g).2 _ hq (R.allows _ hq _ hg)
        exact (snd_congr (onBatch_mul_inv M g ⟨x, b⟩) L.Allows).1 h
      · intro x hx b hb
        obtain ⟨g, hg⟩ := hpos x b hb
        have hq : L.Legal (M.onBatch g⁻¹ ⟨x, b⟩).1 := by
          rw [M.onBatch_fst]
          exact hlegal _ _ hx
        have h : L.Legal (M.onBatch g (M.onBatch g⁻¹ ⟨x, b⟩)).2.apply := by
          rw [M.onBatch_apply]
          exact hlegal g _ (R.keeps _ hq _ hg)
        exact (snd_congr (onBatch_mul_inv M g ⟨x, b⟩) fun b => L.Legal b.apply).1 h
      · intro h p _
        change R.averageWeight M (M.onBatch h p).1 (M.onBatch h p).2 = R.averageWeight M p.1 p.2
        rw [havg, havg]
        congr 1
        -- Reindex the motions: `g ↦ h * g`.
        rw [← Equiv.sum_comp (Equiv.mulLeft h)]
        refine Finset.sum_congr rfl fun g _ => ?_
        change wt (M.onBatch (h * g)⁻¹ (M.onBatch h p)) = wt (M.onBatch g⁻¹ p)
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
    exact ⟨hstoch, fun R => hstoch R.toStoch, fun R => hstoch R.toStoch⟩

/-! ## Non-vacuity -/

namespace SquareRunFixesExample

/-- The halo of the corner `vᵢ` of the square, read in one shape at every corner: the corner
behind, then the corner itself. -/
def halo (i : Fin 4) : Fin 2 → Fin 4 := ![i - 1, i]

/-- The law of the square as a table from windows to values: the new number is the number at
the corner behind. -/
def rule (w : Fin 2 → ZMod 3) : ZMod 3 := w 0

/-- The start `(0, 1, 2, 0)`. -/
def start : Fin 4 → ZMod 3 := ![0, 1, 2, 0]

end SquareRunFixesExample

open SquareRunFixesExample in
/-- Proposition 5.42 on the square: its run from `(0, 1, 2, 0)`, strung over the four ticks
round the prism, shows four of the nine windows (corner behind, corner itself): `(0, 0)`,
`(0, 1)`, `(1, 2)` and `(2, 0)`. So `3⁵ = 243` laws that read both agree with it, the law of
the square among them. -/
example : Nat.card {g : (Fin 2 → ZMod 3) → ZMod 3 //
    ∀ t ≤ 4, (haloLaw halo g).run start t = (haloLaw halo rule).run start t} = 243 := by
  refine ((runFixes (Fin 4) (Fin 2) (ZMod 3) halo rule start 4).2 5 ?_).trans ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    rfl

namespace QueueWeaveExample

/-- The queue's frame: an empty corner `0` or a token `1` at each corner of the square. -/
abbrev frame : Presentation := ⟨Fin 4, fun _ => Fin 2⟩

/-- The queue: `p'(vᵢ) = 1` exactly when `p(vᵢ) = p(vᵢ₊₁) = 1`, or `p(vᵢ₋₁) = 1` and
`p(vᵢ) = 0`. -/
def tick (x : frame.Table) : frame.Table := fun i =>
  if (x i = 1 ∧ x (i + 1) = 1) ∨ (x (i - 1) = 1 ∧ x i = 0) then 1 else 0

/-- The queue's move, made at every tick: it writes the next table at every corner. -/
def move : ProcessProfile frame where
  guard _ := True
  reads := Set.univ
  writes := Set.univ
  update := tick
  guard_reads _ _ _ := Iff.rfl
  update_reads x y h p _ := by
    obtain rfl : x = y := funext fun q => h q (Set.mem_univ q)
    rfl

/-- The queue as a law: every table is legal. -/
def law : Law frame where
  invariants := []
  profiles := [move]
  moves_legal _ _ _ _ _ _ hJ := absurd hJ List.not_mem_nil

/-- The queue's realizer: the move at every tick. -/
def realizer : DetRealizer law where
  select _ := ⟨[⟨move, trivial⟩], List.pairwise_singleton _ _⟩
  allows _ _ a ha := by
    rw [List.mem_singleton] at ha
    rw [ha]
    exact List.mem_singleton_self _
  keeps _ _ _ hJ := absurd hJ List.not_mem_nil

theorem select_apply (x : frame.Table) : (realizer.select x).apply = tick x := by
  funext i
  simp [realizer, Batch.apply, applyAll, ProcessProfile.apply, move]

/-- The halo of each corner: the corner behind, the corner itself and the corner ahead. -/
def halo (i : Fin 4) : Set (Fin 4) := {i - 1, i, i + 1}

/-- The count of the tokens: one on each corner that holds `1`. -/
def count : Count frame := ⟨fun _ a => a.val, fun _ => rfl⟩

theorem legal (x : frame.Table) : law.Legal x := fun _ hJ => absurd hJ List.not_mem_nil

theorem noSignalling : realizer.NoSignalling halo := by
  intro V x z _ _ hag
  funext ⟨i, hi⟩
  have hsub : halo i ⊆ haloOf halo V := fun p hp => Set.mem_biUnion hi hp
  have h1 : x (i - 1) = z (i - 1) := hag _ (hsub (by simp [halo]))
  have h2 : x i = z i := hag _ (hsub (by simp [halo]))
  have h3 : x (i + 1) = z (i + 1) := hag _ (hsub (by simp [halo]))
  simp only [restrictTo, select_apply, tick, h1, h2, h3]

theorem tick_count : ∀ x : frame.Table, count.N (tick x) = count.N x := by
  unfold Count.N count tick
  decide

end QueueWeaveExample

open QueueWeaveExample in
/-- Theorem 5.45 on the queue on the square: every table is legal, so emptying cells keeps
tables legal; the halo of each corner, the corner behind, itself and the corner ahead, is
no-signalling for its realizer; and every step keeps the count of tokens. So its first tick,
from `(1, 1, 1, 0)` to `(1, 1, 0, 1)`, has a weave. -/
example : (∀ x, law.Legal x → ∀ U : Set (Fin 4), law.Legal (emptyCells U x)) ∧
    realizer.NoSignalling halo ∧
    (∀ x x', realizer.AllowsStep x x' → count.N x' = count.N x) ∧
    Nonempty (Weave halo count ![1, 1, 1, 0] ![1, 1, 0, 1]) := by
  have hE : ∀ x, law.Legal x → ∀ U : Set (Fin 4), law.Legal (emptyCells U x) :=
    fun _ _ _ => legal _
  have hK : ∀ x x', realizer.AllowsStep x x' → count.N x' = count.N x := by
    rintro x _ ⟨-, rfl⟩
    rw [select_apply]
    exact tick_count x
  refine ⟨hE, noSignalling, hK, ?_⟩
  refine ((woven frame law count halo).1 hE).1 realizer noSignalling hK _ _ ⟨legal _, ?_⟩
  rw [select_apply]
  decide

namespace TwoSquaresSlotExample

/-- The left turn on the corners `v₀, …, v₅`: the number at `v₀` goes to `v₁`, at `v₁` to `v₂`,
at `v₂` to `v₃` and at `v₃` to `v₀`. -/
def leftTurn : Equiv.Perm (Fin 6) :=
  ⟨![1, 2, 3, 0, 4, 5], ![3, 0, 1, 2, 4, 5], by decide, by decide⟩

/-- The right turn: the number at `v₁` goes to `v₄`, at `v₄` to `v₅`, at `v₅` to `v₂` and at
`v₂` to `v₁`. -/
def rightTurn : Equiv.Perm (Fin 6) :=
  ⟨![0, 4, 1, 3, 5, 2], ![0, 2, 5, 3, 1, 4], by decide, by decide⟩

/-- The half turn of the pair of squares: `v₀ ↔ v₅`, `v₁ ↔ v₂`, `v₃ ↔ v₄`. -/
def halfTurn : Equiv.Perm (Fin 6) :=
  ⟨![5, 2, 1, 4, 3, 0], ![5, 2, 1, 4, 3, 0], by decide, by decide⟩

/-- A motion of the corners, acting on the states, rows of six numbers modulo `3`. -/
abbrev act : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6 → ZMod 3) :=
  (Motions.ofCells (Fin 6) (ZMod 3)).onState

/-- The steps of the law of two squares: the left turn in slot `0`, the right turn in
slot `1`. -/
def steps (s : ZMod 2) : Equiv.Perm (Fin 6 → ZMod 3) :=
  if s = 0 then act leftTurn else act rightTurn

/-- The half turn `h` exchanges the squares: `h ∘ L ∘ h⁻¹ = R` and `h ∘ R ∘ h⁻¹ = L`. -/
theorem halfTurn_conj :
    ∀ s : ZMod 2, act halfTurn * steps (s + (1 : ℕ)) * (act halfTurn)⁻¹ = steps s := by
  have hL : halfTurn * leftTurn * halfTurn⁻¹ = rightTurn := by decide
  have hR : halfTurn * rightTurn * halfTurn⁻¹ = leftTurn := by decide
  intro s
  fin_cases s
  · change act halfTurn * act rightTurn * (act halfTurn)⁻¹ = act leftTurn
    rw [← map_inv, ← map_mul, ← map_mul, hR]
  · change act halfTurn * act leftTurn * (act halfTurn)⁻¹ = act rightTurn
    rw [← map_inv, ← map_mul, ← map_mul, hL]

end TwoSquaresSlotExample

open TwoSquaresSlotExample in
/-- Proposition 5.46 on the two squares: the half turn `h` exchanges the squares, so with a
shift of one slot it carries the slot tapestry to itself, and `h ∘ L` commutes with the tick
`R ∘ L`. -/
example : (∀ s : ZMod 2, act halfTurn * steps (s + (1 : ℕ)) * (act halfTurn)⁻¹ = steps s) ∧
    act halfTurn * firstSteps steps 1 * firstSteps steps 2 =
      firstSteps steps 2 * (act halfTurn * firstSteps steps 1) :=
  ⟨halfTurn_conj, (slotSymmetry _ 2 steps (act halfTurn) 1).2.1 halfTurn_conj⟩

namespace ShearSlotExample

/-- The kick `K(p, q) = (p + q, q)` of Section 5.18. -/
def kick : Equiv.Perm (ZMod 8 × ZMod 8) :=
  ⟨fun x => (x.1 + x.2, x.2), fun x => (x.1 - x.2, x.2), fun x => by simp, fun x => by simp⟩

/-- The move `M(p, q) = (p, q + 2p)`. -/
def move : Equiv.Perm (ZMod 8 × ZMod 8) :=
  ⟨fun x => (x.1, x.2 + 2 * x.1), fun x => (x.1, x.2 - 2 * x.1), fun x => by simp,
    fun x => by simp⟩

/-- The flip of the velocities `R(p, q) = (-p, q)`. -/
def velocityFlip : Equiv.Perm (ZMod 8 × ZMod 8) := Equiv.prodCongr (Equiv.neg _) (Equiv.refl _)

/-- The steps of the two-shear tick: the kick in slot `0`, the move in slot `1`. -/
def steps (s : ZMod 2) : Equiv.Perm (ZMod 8 × ZMod 8) := if s = 0 then kick else move

/-- The flip undoes each step, `R ∘ S_s⁻¹ ∘ R⁻¹ = S_s`; with `j = 1` and `k = 2` this is
`R ∘ S_{(j-1-s) mod 2}⁻¹ ∘ R⁻¹ = S_s`. -/
theorem flip_conj : ∀ s : ZMod 2,
    velocityFlip * (steps ((1 : ℕ) - 1 - s))⁻¹ * velocityFlip⁻¹ = steps s := by
  intro s
  fin_cases s
  · change velocityFlip * kick⁻¹ * velocityFlip⁻¹ = kick
    ext x
    · simp [velocityFlip, kick, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      ring
    · simp [velocityFlip, kick, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  · change velocityFlip * move⁻¹ * velocityFlip⁻¹ = move
    ext x
    · simp [velocityFlip, move, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    · simp [velocityFlip, move, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

end ShearSlotExample

open ShearSlotExample in
/-- Proposition 5.46, reversed, on the two-shear step of Section 5.18: the flip of the
velocities meets the reversed condition with a shift of one slot, and `I₀ = R ∘ K` reverses
the tick `M ∘ K`, the reverser of Proposition 5.39. -/
example : (∀ s : ZMod 2,
      velocityFlip * (steps ((1 : ℕ) - 1 - s))⁻¹ * velocityFlip⁻¹ = steps s) ∧
    velocityFlip * firstSteps steps 1 * firstSteps steps 2 *
        (velocityFlip * firstSteps steps 1)⁻¹ = (firstSteps steps 2)⁻¹ :=
  ⟨flip_conj, (slotSymmetry _ 2 steps velocityFlip 1).2.2.2 flip_conj⟩

namespace WalkerMirrorExample

open WalkerExample

/-- The mirror of the square in the diagonal through `v₀` and `v₂`: `vᵢ ↦ v₋ᵢ`. -/
def mirror : Equiv.Perm (Fin 4) := ⟨fun i => -i, fun i => -i, neg_neg, neg_neg⟩

theorem mirror_mul_self : mirror * mirror = 1 := by decide

/-- The group of the mirror: the identity and the mirror. -/
def mirrorGroup : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {1, mirror}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [mirror_mul_self]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl)
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_right mirror_mul_self)

/-- The mirror group acting on the walker's tables and batches, by moving every move. -/
def motions : Motions mirrorGroup frame :=
  (Motions.ofCells (Fin 4) Bool).comp mirrorGroup.subtype

/-- Two process profiles with the same guard, footprints and proposal are the same. -/
theorem profile_ext {u v : ProcessProfile frame} (hg : u.guard = v.guard)
    (hr : u.reads = v.reads) (hw : u.writes = v.writes) (hu : u.update = v.update) : u = v := by
  cases u
  cases v
  cases hg
  cases hr
  cases hw
  cases hu
  rfl

/-- A motion of the square carries the step from `i` to `j` to the step from the image of `i`
to the image of `j`. -/
theorem cellMoveProfile_step (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    cellMoveProfile σ (step i j) = step (σ i) (σ j) := by
  refine profile_ext rfl ?_ ?_ ?_
  · ext c
    simp [cellMoveProfile, step, Equiv.symm_apply_eq]
  · ext c
    simp [cellMoveProfile, step, Equiv.symm_apply_eq]
  · funext x c
    simp [cellMoveProfile, step, Equiv.symm_apply_eq]

theorem oneToken_move (σ : Equiv.Perm (Fin 4)) {x : frame.Table} (hx : oneToken x) :
    oneToken (cellMoveTable σ x) := by
  obtain ⟨v, hv, hu⟩ := hx
  refine ⟨σ v, ?_, fun w hw => ?_⟩
  · change x (σ.symm (σ v)) = true
    rw [Equiv.symm_apply_apply]
    exact hv
  · have := hu _ hw
    rw [← this, Equiv.apply_symm_apply]

/-- The walker's moves: the steps ahead and behind. -/
theorem mem_moves_iff (u : ProcessProfile frame) :
    u ∈ moves ↔ ∃ i, u = step i (i + 1) ∨ u = step i (i - 1) := by
  simp only [moves, List.mem_flatMap, List.mem_finRange, List.mem_cons, List.not_mem_nil,
    or_false, true_and]

/-- Every motion of the mirror group is a symmetry of the walker: it keeps one token, and it
carries the step ahead to the step behind and the step behind to the step ahead. -/
theorem symmetry (g : mirrorGroup) : law.IsSymmetryUnder motions g := by
  obtain ⟨σ, hσ⟩ := g
  refine ⟨fun x hx => (legal_iff _).2 (oneToken_move σ ((legal_iff x).1 hx)), ?_⟩
  rintro ⟨x, b⟩ _ hb a ha
  change a ∈ b.apps.map (cellMoveApp σ) at ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨i, hi⟩ := (mem_moves_iff _).1 (hb a' ha')
  change cellMoveProfile σ a'.profile ∈ moves
  rw [mem_moves_iff]
  rcases hσ with rfl | rfl
  · exact ⟨i, hi⟩
  · refine ⟨-i, ?_⟩
    rcases hi with hi | hi
    · right
      rw [hi, cellMoveProfile_step]
      change step (-i) (-(i + 1)) = step (-i) (-i - 1)
      rw [show ∀ i : Fin 4, -(i + 1) = -i - 1 by decide]
    · left
      rw [hi, cellMoveProfile_step]
      change step (-i) (-(i - 1)) = step (-i) (-i + 1)
      rw [show ∀ i : Fin 4, -(i - 1) = -i + 1 by decide]

/-- The mirror fixes the token at `v₀`. -/
theorem fixes_start (s : mirrorGroup) : motions.onState s start = start := by
  obtain ⟨σ, hσ⟩ := s
  rcases hσ with rfl | rfl
  · rfl
  · funext c
    change decide (-c = 0) = decide (c = 0)
    revert c
    decide

end WalkerMirrorExample

open WalkerExample WalkerMirrorExample in
/-- Theorem 5.47 on the walker: both motions of the mirror group, the identity and the mirror
through `v₀` and `v₂`, are symmetries of its law, and they fix the start, the token at `v₀`.
So the mirror carries the set of corners reachable at each tick to itself. -/
example : (∀ g : mirrorGroup, law.IsSymmetryUnder motions g) ∧
    (∀ s ∈ (⊤ : Subgroup mirrorGroup), motions.onState s start = start) ∧
    ∀ n : ℕ, motions.onState ⟨mirror, Or.inr rfl⟩ '' law.reachableAt start n =
      law.reachableAt start n :=
  ⟨symmetry, fun s _ => fixes_start s, fun n =>
    (curie frame law mirrorGroup motions symmetry ⊤ start fun s _ => fixes_start s).2.1 _
      trivial n⟩

open WalkerExample WalkerMirrorExample in
/-- Proposition 5.48 on the walker: under the same hypotheses, met by the mirror group and the
token at `v₀`, a run keeps the mirror exactly when it stays on the diagonal through `v₀` and
`v₂`, the states the mirror fixes. -/
example : (∀ g : mirrorGroup, law.IsSymmetryUnder motions g) ∧
    (∀ s ∈ (⊤ : Subgroup mirrorGroup), motions.onState s start = start) ∧
    ∀ (n : ℕ) (r : Run frame n), (∀ i, r.KeepsSymmetryAt motions ⊤ i) ↔
      ∀ i, r.state i ∈ motions.fixedStates ⊤ :=
  ⟨symmetry, fun s _ => fixes_start s,
    (breaking frame law mirrorGroup motions symmetry ⊤ start fun s _ => fixes_start s).1⟩

end Artform
