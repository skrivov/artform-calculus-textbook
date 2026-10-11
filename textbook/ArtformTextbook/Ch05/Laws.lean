import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import ArtformTextbook.Ch05.Statements.Laws

/-!
# The current of a tally; the law decides what is kept (Sections 5.3 and 5.4)

The proofs of Proposition 5.8 and Proposition 5.11.

Proposition 5.8 follows the book's proof: the tally is kept at the table `0`,
so the source terms add up to `0` and the additive part keeps the tally; at a
table with a single `1` this says that the column sums `Σ_y d(y) M_{yu}` are
`d(u)`, and the balance at a cell is then a rearrangement of
`M(p)(v) = Σ_u M_{vu} p(u)`.

Proposition 5.11 is an induction along the run.
-/

namespace Artform

open scoped BigOperators

namespace AffineLaw

variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}

/-- The additive part written cell by cell, `M(p)(v) = Σ_u M_{vu} p(u)`: every
additive `M` can be written so, since `M` is linear over `ZMod n`. -/
theorem M_apply_eq_sum (L : AffineLaw C n) (p : C → ZMod n) (v : C) :
    L.M p v = ∑ u, L.coeff v u * p u := by
  conv_lhs => rw [← Finset.univ_sum_single p]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hx : (Pi.single u (p u) : C → ZMod n) = p u • Pi.single u 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hx, ZMod.map_smul, Pi.smul_apply, smul_eq_mul, coeff, mul_comm]

end AffineLaw

/-- **Proposition 5.8** (the current of a tally). Let an affine law
`F(p) = M(p) + b` keep the tally `T(p) = Σ_v d(v) p(v)`. Then at every tick and
every cell `v` the change `d(v)(F(p)(v) − p(v))` is the current arriving at
`v`, less the current leaving it, plus the source term `d(v) b(v)`; the source
terms add up to `0`; the current runs from `u` to `v` only if the update of `v`
reads `u`, and it reads the cell `u` alone. -/
@[book "prop:tally-current"]
theorem tallyCurrent : Statement.tallyCurrent := by
  intro C _ _ n L d hT
  have hT' : ∀ p : C → ZMod n, ∑ v, d v * L.tick p v = ∑ v, d v * p v := hT
  -- The tally is kept at the table `0`: `Σ_v d(v) b(v) = T(F(0)) = T(0) = 0`.
  have hb : ∑ v, d v * L.b v = 0 := by
    have h := hT' 0
    simpa [AffineLaw.tick] using h
  -- So the additive part keeps the tally: `T(M(p)) = T(F(p)) − T(b) = T(p)`.
  have hM : ∀ p : C → ZMod n, ∑ v, d v * L.M p v = ∑ v, d v * p v := by
    intro p
    have h := hT' p
    simpa only [AffineLaw.tick, Pi.add_apply, mul_add, Finset.sum_add_distrib, hb,
      add_zero] using h
  -- At the table with a single `1` at `u`: `Σ_y d(y) M_{yu} = d(u)`.
  have hcol : ∀ u, ∑ y, d y * L.coeff y u = d u := by
    intro u
    have h := hM (Pi.single u 1)
    simpa [AffineLaw.coeff, Pi.single_apply] using h
  refine ⟨fun p v => ?_, hb, fun u v p h => ?_, fun u v p q h => ?_⟩
  · -- The current arriving at `v` and the current leaving it.
    have harr : ∑ u ∈ Finset.univ.erase v, L.current d u v p =
        d v * L.M p v - d v * L.coeff v v * p v := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ v), L.M_apply_eq_sum p v, Finset.mul_sum]
      simp only [AffineLaw.current, mul_assoc]
    have hleave : ∑ y ∈ Finset.univ.erase v, L.current d v y p =
        (d v - d v * L.coeff v v) * p v := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ v)]
      simp only [AffineLaw.current]
      rw [← Finset.sum_mul, hcol v]
      ring
    rw [harr, hleave, AffineLaw.tick, Pi.add_apply]
    ring
  · -- A current that is not `0` needs `M_{vu} ≠ 0`.
    intro hc
    apply h
    simp [AffineLaw.current, hc]
  · simp [AffineLaw.current, h]

namespace Run

variable {A : Presentation} {L : Law A} {n : ℕ}

/-- Induction along a run: if every step applies a batch the law allows from a
legal state, and every batch the law allows at a legal state keeps the
condition `J`, then a run that starts in `J` stays in `J`. -/
theorem keeps_of_allowed (r : Run A n) (J : A.Table → Prop)
    (hJ : ∀ (x : A.Table), L.Legal x → ∀ b : Batch A x, L.Allows b → J x → J b.apply)
    (hlegal : ∀ i, L.Legal (r.state i)) (hallow : ∀ i, L.Allows (r.batch i))
    (h0 : J (r.state 0)) : ∀ i, J (r.state i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    rw [r.step i]
    exact hJ _ (hlegal _) _ (hallow i) ih

end Run

/-- **Proposition 5.11** (the law decides what is kept). If every batch a law
allows carries states satisfying an invariant to states satisfying it, then
every run keeps the invariant: the run of a deterministic realizer, each run a
relational realizer allows, and each run of positive weight under a
stochastic one. Each step of each of these runs applies a batch the law
allows; induction along the run. -/
@[book "prop:law-decides"]
theorem lawDecides : Statement.lawDecides := by
  intro A L J hJ
  refine ⟨fun R n r hr h0 => ?_, fun R n r hr h0 => ?_, fun R n r hr h0 => ?_⟩
  · refine r.keeps_of_allowed J hJ hr.1 (fun i => ?_) h0
    rw [hr.2 i]
    exact R.allows _ (hr.1 _)
  · exact r.keeps_of_allowed J hJ hr.1 (fun i => R.allows _ (hr.1 _) _ (hr.2 i)) h0
  · exact r.keeps_of_allowed J hJ hr.1 (fun i => R.allows _ (hr.1 _) _ (hr.2 i)) h0

/-! ## Non-vacuity -/

/-- The law of the square keeps its total `T(p) = p(v₀) + p(v₁) + p(v₂) + p(v₃)`,
the tally with `d = 𝟏`: the hypothesis of Proposition 5.8 is met. -/
example : squareLaw.toDetLaw.Conserved (fun p => ∑ v, (fun _ => (1 : ZMod 3)) v * p v) := by
  intro p
  have h : ∀ x, squareLaw.toDetLaw.tick p x = p (x - 1) := fun x => by
    simp [AffineLaw.toDetLaw, AffineLaw.tick, squareLaw, squareShift]
  simp only [one_mul, h]
  exact Equiv.sum_comp (Equiv.subRight (1 : Fin 4)) p

/-- On the square the current on the edge `e₁` from `v₀` to `v₁` is the number
that edge carries, `J_{v₀→v₁}(p) = p(v₀)`. -/
example (p : Fin 4 → ZMod 3) :
    squareLaw.current (fun _ => 1) 0 1 p = p 0 := by
  simp [AffineLaw.current, AffineLaw.coeff, squareLaw, squareShift]

namespace WalkerExample

/-- The walker's frame: a token or none at each corner of the square. -/
abbrev frame : Presentation := ⟨Fin 4, fun _ => Bool⟩

/-- The walker's invariant: there is exactly one token. -/
def oneToken (x : frame.Table) : Prop := ∃! v, x v = true

/-- The step of the token from the corner `i` to the corner `j`: allowed when the
token is at `i`; it reads `i` and writes `i` and `j`. -/
def step (i j : Fin 4) : ProcessProfile frame where
  guard x := x i = true
  reads := {i}
  writes := {i, j}
  update _ v := decide (v = j)
  guard_reads x y h := by rw [h i (Set.mem_singleton i)]
  update_reads _ _ _ _ _ := rfl

/-- The walker's moves: from every corner, a step ahead and a step behind. -/
def moves : List (ProcessProfile frame) :=
  (List.finRange 4).flatMap fun i => [step i (i + 1), step i (i - 1)]

theorem mem_moves {u : ProcessProfile frame} (hu : u ∈ moves) : ∃ i j, i ≠ j ∧ u = step i j := by
  simp only [moves, List.mem_flatMap, List.mem_finRange, List.mem_cons, List.not_mem_nil,
    or_false, true_and] at hu
  obtain ⟨i, rfl | rfl⟩ := hu
  · exact ⟨i, i + 1, by revert i; decide, rfl⟩
  · exact ⟨i, i - 1, by revert i; decide, rfl⟩

theorem step_apply_of_ne {i j w : Fin 4} (hi : w ≠ i) (hj : w ≠ j) (x : frame.Table) :
    (step i j).apply x w = x w :=
  ite_eq_right (by simp [step, hi, hj])

theorem step_apply_target (i j : Fin 4) (x : frame.Table) : (step i j).apply x j = true :=
  (ite_eq_left (by simp [step])).trans (by simp [step])

/-- A step from the token's corner keeps exactly one token. -/
theorem step_oneToken {i j : Fin 4} (hij : i ≠ j) {x : frame.Table} (hx : oneToken x)
    (hg : x i = true) : oneToken ((step i j).apply x) := by
  refine ⟨j, step_apply_target i j x, fun w hw => ?_⟩
  change (step i j).apply x w = true at hw
  by_contra hwj
  by_cases hwi : w = i
  · subst hwi
    have h : (step w j).apply x w = decide (w = j) := ite_eq_left (by simp [step])
    rw [h] at hw
    exact hwj (of_decide_eq_true hw)
  · rw [step_apply_of_ne hwi hwj] at hw
    exact hwi (hx.unique hw hg)

/-- The walker: one token on the corners of the square, which may step to
either neighbouring corner. -/
def law : Law frame where
  invariants := [oneToken]
  profiles := moves
  moves_legal x hx u hu hg J hJ := by
    rw [List.mem_singleton] at hJ
    subst hJ
    obtain ⟨i, j, hij, rfl⟩ := mem_moves hu
    exact step_oneToken hij (hx oneToken (List.mem_singleton_self _)) hg

theorem legal_iff (x : frame.Table) : law.Legal x ↔ oneToken x :=
  ⟨fun h => h oneToken (List.mem_singleton_self _), fun h J hJ => by
    rw [show J = oneToken from List.mem_singleton.1 hJ]
    exact h⟩

/-- Every batch the walker's law allows keeps exactly one token: both moves at
the token's corner write that corner, so a batch holds at most one move. -/
theorem batch_keeps (x : frame.Table) (b : Batch frame x) (hb : law.Allows b)
    (hJ : oneToken x) : oneToken b.apply := by
  obtain ⟨apps, hcomp⟩ := b
  -- The corner a move starts from holds the token.
  have hstart : ∀ a ∈ apps, ∃ i j, i ≠ j ∧ a.profile = step i j ∧ x i = true := by
    intro a ha
    obtain ⟨i, j, hij, hu⟩ := mem_moves (hb a ha)
    exact ⟨i, j, hij, hu, by have := a.enabled; rw [hu] at this; exact this⟩
  match apps, hcomp, hstart with
  | [], _, _ => exact hJ
  | [a], _, hstart =>
    obtain ⟨i, j, hij, hu, hg⟩ := hstart a (List.mem_singleton_self _)
    change oneToken (a.profile.apply x)
    rw [hu]
    exact step_oneToken hij hJ hg
  | a :: a' :: rest, hcomp, hstart =>
    exfalso
    obtain ⟨i, j, -, hu, hg⟩ := hstart a List.mem_cons_self
    obtain ⟨i', j', -, hu', hg'⟩ := hstart a' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hii : i = i' := hJ.unique hg hg'
    have hdis := (List.pairwise_cons.1 hcomp).1 a' List.mem_cons_self
    have h1 : i ∈ a.profile.writes := by rw [hu]; exact Set.mem_insert i _
    have h2 : i ∈ a'.profile.writes := by rw [hu', hii]; exact Set.mem_insert i' _
    exact Set.disjoint_left.1 hdis.1 h1 h2

open Classical in
/-- The realizer that always steps ahead. -/
noncomputable def ahead : DetRealizer law where
  select x := if h : ∃ v, x v = true then
      ⟨[⟨step h.choose (h.choose + 1), h.choose_spec⟩], List.pairwise_singleton _ _⟩
    else ⟨[], List.Pairwise.nil⟩
  allows x _ a ha := by
    by_cases h : ∃ v, x v = true
    · rw [dite_eq_left h, List.mem_singleton] at ha
      rw [ha]
      simp only [law, moves, List.mem_flatMap, List.mem_finRange, List.mem_cons, true_and]
      exact ⟨h.choose, Or.inl rfl⟩
    · rw [dite_eq_right h] at ha
      exact absurd ha List.not_mem_nil
  keeps x hx := by
    have h1 := (legal_iff x).1 hx
    have h : ∃ v, x v = true := h1.exists
    have hsel : (if h : ∃ v, x v = true then
        (⟨[⟨step h.choose (h.choose + 1), h.choose_spec⟩], List.pairwise_singleton _ _⟩ :
          Batch frame x)
      else ⟨[], List.Pairwise.nil⟩) =
        ⟨[⟨step h.choose (h.choose + 1), h.choose_spec⟩], List.pairwise_singleton _ _⟩ :=
      dite_eq_left h
    refine (legal_iff _).2 ?_
    rw [hsel]
    exact step_oneToken ((by decide : ∀ v : Fin 4, v ≠ v + 1) h.choose) h1 h.choose_spec

/-- The states that a deterministic realizer reaches from `x₀`. -/
noncomputable def trajectory {A : Presentation} {L : Law A} (R : DetRealizer L) (x₀ : A.Table) :
    ℕ → A.Table
  | 0 => x₀
  | k + 1 => (R.select (trajectory R x₀ k)).apply

/-- The run of `n` ticks that a deterministic realizer makes from `x₀`. -/
noncomputable def run {A : Presentation} {L : Law A} (R : DetRealizer L) (x₀ : A.Table)
    (n : ℕ) : Run A n where
  state i := trajectory R x₀ i
  batch i := R.select (trajectory R x₀ i)
  step _ := rfl

theorem run_ofDet {A : Presentation} {L : Law A} (R : DetRealizer L) {x₀ : A.Table}
    (h₀ : L.Legal x₀) (n : ℕ) : (run R x₀ n).OfDet R := by
  have h : ∀ k, L.Legal (trajectory R x₀ k) := by
    intro k
    induction k with
    | zero => exact h₀
    | succ k ih => exact R.keeps _ ih
  exact ⟨fun i => h i, fun _ => rfl⟩

/-- The token at `v₀`. -/
def start : frame.Table := fun v => decide (v = 0)

theorem start_oneToken : oneToken start := ⟨0, rfl, fun _ hw => of_decide_eq_true hw⟩

end WalkerExample

open WalkerExample in
/-- The walker meets the hypotheses of Proposition 5.11: every batch its law allows
keeps exactly one token, and the realizer that always steps ahead has a run of
two ticks from the token at `v₀`, which starts with one token. -/
example : (∀ x, law.Legal x → ∀ b : Batch frame x, law.Allows b → oneToken x → oneToken b.apply) ∧
    (run ahead start 2).OfDet ahead ∧ oneToken ((run ahead start 2).state 0) :=
  ⟨fun x _ b hb hJ => batch_keeps x b hb hJ,
    run_ofDet ahead ((legal_iff start).2 start_oneToken) 2, start_oneToken⟩

end Artform
