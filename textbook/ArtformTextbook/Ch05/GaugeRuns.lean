import ArtformTextbook.Ch03.Growth
import ArtformTextbook.Ch05.Defs.PoseLaw
import ArtformTextbook.Ch05.Statements.GaugeRuns
import ArtformTextbook.Ch05.Steps

/-!
# Gauge covariance passes to runs (Proposition 5.36)

The proof is the book's. At `h · x` the realizer selects the same moves as at
`x`, perhaps listed in another order, and the order does not matter: the
applications of a batch are compatible (Definition 2.6), and compatible changes
commute (Proposition 3.27). Each move of the batch proposes at `h · x` the
image under `h` of its proposal at `x`, so each change gives `h` applied to
what it gave before, and so does the whole batch: `F(h · x) = h · F(x)`.
Induction over the ticks relates the runs, and a gauge-invariant reading
cannot tell `h · y` from `y`.

A batch lists applications that are enabled and compatible at the state `x`
where it is selected. Made one after another, each acts on the state that the
earlier ones left. Two moves compatible at `x` stay compatible after a third
that is compatible with both (`CompatibleAt.after`), and each move stays
enabled, since nothing it reads has changed. So Proposition 3.27, and each
move's gauge covariance, apply at every state along the way.

The non-vacuity section writes the pose law of the two squares (Section 5.15)
on a frame with a link at every edge and a pose at every corner, as a law of
Section 5.4 and as a law in steps, and meets the hypotheses of both parts with
the gauge change by `1` at `v₁` of `fig:covariant-law`.
-/

namespace Artform

namespace GaugeRuns

variable {A : Presentation}

/-! ## Moves made one after another -/

/-- Making a list of moves one after another, in the order listed. -/
noncomputable def applyMoves : List (ProcessProfile A) → A.Table → A.Table
  | [], y => y
  | u :: l, y => applyMoves l (u.apply y)

/-- Making a list of applications is making their moves. -/
theorem applyAll_eq {x : A.Table} (l : List (EnabledApp A x)) (y : A.Table) :
    applyAll l y = applyMoves (l.map EnabledApp.profile) y := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih => exact ih (a.profile.apply y)

/-- A batch leads where its moves lead, made in the order listed. -/
theorem batch_apply {x : A.Table} (b : Batch A x) : b.apply = applyMoves b.moves x :=
  applyAll_eq b.apps x

/-- The moves of a batch whose every application has a property have it. -/
theorem forall_moves {P : ProcessProfile A → Prop} {x : A.Table} {b : Batch A x}
    (hb : ∀ a ∈ b.apps, P a.profile) : ∀ u ∈ b.moves, P u := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  exact hb a ha

/-- A move changes its write footprint to its proposal. -/
theorem apply_of_mem {u : ProcessProfile A} {y : A.Table} {p : A.P} (hp : p ∈ u.writes) :
    u.apply y p = u.update y p := by
  simp [ProcessProfile.apply, hp]

/-- A move leaves every other position as it was. -/
theorem apply_of_not_mem {u : ProcessProfile A} {y : A.Table} {p : A.P} (hp : p ∉ u.writes) :
    u.apply y p = y p := by
  simp [ProcessProfile.apply, hp]

/-! ## Compatibility along the way -/

/-- Two moves compatible at the state `y`, as Definition 2.6 asks of two
applications enabled at `y`: their write footprints are disjoint, and making
either leaves unchanged every position that the other reads. -/
def CompatibleAt (y : A.Table) (a b : ProcessProfile A) : Prop :=
  Disjoint a.writes b.writes ∧ (∀ p ∈ b.reads, a.apply y p = y p) ∧
    ∀ p ∈ a.reads, b.apply y p = y p

/-- Compatibility is symmetric. -/
theorem CompatibleAt.symm {y : A.Table} {a b : ProcessProfile A} (h : CompatibleAt y a b) :
    CompatibleAt y b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- The moves of a batch are pairwise compatible at the state where it is
selected: the batch's evidence of compatibility. -/
theorem pairwise_moves {x : A.Table} (b : Batch A x) : b.moves.Pairwise (CompatibleAt x) :=
  List.pairwise_map.2 b.compatible

/-- A move with its guard dropped: the same footprints and the same proposal. -/
def unguarded (u : ProcessProfile A) : ProcessProfile A where
  guard _ := True
  reads := u.reads
  writes := u.writes
  update := u.update
  guard_reads _ _ _ := Iff.rfl
  update_reads := u.update_reads

/-- Proposition 3.27 at any state: two moves compatible at `y` commute there.
Proposition 3.27 speaks of applications enabled at `y`; the two moves with
their guards dropped are, and making a move does not consult its guard. -/
theorem commute {y : A.Table} {a b : ProcessProfile A} (h : CompatibleAt y a b) :
    b.apply (a.apply y) = a.apply (b.apply y) :=
  commutingProposals A y ⟨unguarded a, trivial⟩ ⟨unguarded b, trivial⟩ h

/-- After a move `c` that leaves unchanged what `a` reads and writes nowhere
`a` writes, `a` still leaves unchanged each position it left unchanged. -/
theorem apply_after {y : A.Table} {c a : ProcessProfile A} (hca : CompatibleAt y c a)
    {p : A.P} (hp : a.apply y p = y p) : a.apply (c.apply y) p = c.apply y p := by
  by_cases hpa : p ∈ a.writes
  · have hpc : p ∉ c.writes := fun h => Set.disjoint_left.1 hca.1 h hpa
    rw [apply_of_mem hpa] at hp ⊢
    rw [a.update_reads _ _ hca.2.1 p hpa, hp, apply_of_not_mem hpc]
  · rw [apply_of_not_mem hpa]

/-- Two moves compatible at `y` stay compatible after a third that is
compatible with both. -/
theorem CompatibleAt.after {y : A.Table} {c a b : ProcessProfile A} (hca : CompatibleAt y c a)
    (hcb : CompatibleAt y c b) (hab : CompatibleAt y a b) : CompatibleAt (c.apply y) a b :=
  ⟨hab.1, fun p hp => apply_after hca (hab.2.1 p hp), fun p hp => apply_after hcb (hab.2.2 p hp)⟩

/-- After the first move of a pairwise compatible list, the others are still
pairwise compatible. -/
theorem pairwise_after {y : A.Table} {c : ProcessProfile A} {l : List (ProcessProfile A)}
    (h : (c :: l).Pairwise (CompatibleAt y)) : l.Pairwise (CompatibleAt (c.apply y)) := by
  rw [List.pairwise_cons] at h
  exact h.2.imp_of_mem fun ha hb hab => CompatibleAt.after (h.1 _ ha) (h.1 _ hb) hab

/-- After the first move of a pairwise compatible list, the others are still
enabled where they were: the first leaves unchanged what they read. -/
theorem guard_after {y : A.Table} {c : ProcessProfile A} {l : List (ProcessProfile A)}
    (h : (c :: l).Pairwise (CompatibleAt y)) (hg : ∀ u ∈ l, u.guard y) :
    ∀ u ∈ l, u.guard (c.apply y) := fun u hu =>
  (u.guard_reads _ _ ((List.pairwise_cons.1 h).1 u hu).2.1).2 (hg u hu)

/-- The order does not matter: pairwise compatible moves made in two orders
lead to the same state. Each exchange of two neighbours is Proposition 3.27, at
the state reached so far. -/
theorem applyMoves_perm {l l' : List (ProcessProfile A)} (hp : l.Perm l') :
    ∀ y, l.Pairwise (CompatibleAt y) → applyMoves l y = applyMoves l' y := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | cons c _ ih => exact fun y h => ih (c.apply y) (pairwise_after h)
  | swap a b l =>
    intro y h
    exact congrArg (applyMoves l) (commute ((List.pairwise_cons.1 h).1 a List.mem_cons_self))
  | trans h₁ _ ih₁ ih₂ =>
    exact fun y h => (ih₁ y h).trans (ih₂ y ((h₁.pairwise_iff CompatibleAt.symm).1 h))

/-! ## One tick, then the runs -/

variable {𝒢 : Type*} (α : GaugeAction A 𝒢)

/-- A gauge-covariant move enabled at `y` leads from `h · y` to `h` applied to
where it leads from `y`. -/
theorem apply_smul {u : ProcessProfile A} (hu : α.CovariantMove u) (h : 𝒢) {y : A.Table}
    (hy : u.guard y) : u.apply (α.smul h y) = α.smul h (u.apply y) := by
  funext p
  simp only [GaugeAction.smul_apply]
  by_cases hp : p ∈ u.writes
  · rw [apply_of_mem hp, apply_of_mem hp]
    exact (hu h y hy).2 p hp
  · simp only [apply_of_not_mem hp, GaugeAction.smul_apply]

/-- Pairwise compatible gauge-covariant moves, enabled at `y`, lead from `h · y`
to `h` applied to where they lead from `y`: each change gives `h` applied to
what it gave before. -/
theorem applyMoves_smul (h : 𝒢) {l : List (ProcessProfile A)}
    (hcov : ∀ u ∈ l, α.CovariantMove u) :
    ∀ y, l.Pairwise (CompatibleAt y) → (∀ u ∈ l, u.guard y) →
      applyMoves l (α.smul h y) = α.smul h (applyMoves l y) := by
  induction l with
  | nil => exact fun _ _ _ => rfl
  | cons u l ih =>
    intro y hc hg
    change applyMoves l (u.apply (α.smul h y)) = α.smul h (applyMoves l (u.apply y))
    rw [apply_smul α (hcov u List.mem_cons_self) h (hg u List.mem_cons_self)]
    exact ih (fun v hv => hcov v (List.mem_cons_of_mem _ hv)) _ (pairwise_after hc)
      (guard_after hc fun v hv => hg v (List.mem_cons_of_mem _ hv))

/-- One tick: a selection that, at every state `legal` admits, selects
gauge-covariant moves, and selects at `h · x` the same moves as at `x` in any
order, commutes with `h` there: `F(h · x) = h · F(x)`. -/
theorem select_smul {legal : A.Table → Prop} {sel : (x : A.Table) → Batch A x}
    (hcov : ∀ x, legal x → ∀ u ∈ (sel x).moves, α.CovariantMove u)
    (hsame : α.SameBatch legal sel) (h : 𝒢) {x : A.Table} (hx : legal x) :
    (sel (α.smul h x)).apply = α.smul h (sel x).apply := by
  rw [batch_apply, batch_apply,
    applyMoves_perm (hsame h x hx) _ (pairwise_moves (sel (α.smul h x)))]
  exact applyMoves_smul α h (hcov x hx) x (pairwise_moves (sel x))
    (forall_moves fun a _ => a.enabled)

/-- Induction over the ticks: two runs that make the selected batches, the
first through states where each selection commutes with `h`, and that start
`h` apart, stay `h` apart. -/
theorem state_smul {n : ℕ} {sel : ℕ → (x : A.Table) → Batch A x} {s : ℕ} {h : 𝒢}
    {r r' : Run A n}
    (hF : ∀ i : Fin n, (sel (s + i) (α.smul h (r.state i.castSucc))).apply =
      α.smul h (sel (s + i) (r.state i.castSucc)).apply)
    (hr : ∀ i : Fin n, r.batch i = sel (s + i) (r.state i.castSucc))
    (hr' : ∀ i : Fin n, r'.batch i = sel (s + i) (r'.state i.castSucc))
    (h0 : r'.state 0 = α.smul h (r.state 0)) : ∀ i, r'.state i = α.smul h (r.state i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih => rw [r'.step i, hr' i, r.step i, hr i, ← hF i, ih]

end GaugeRuns

open GaugeRuns in
/-- **Proposition 5.36** (gauge covariance passes to runs). For a gauge-covariant
law with a gauge-covariant deterministic realizer, `F(h · x) = h · F(x)` for
every gauge change `h` and every legal state `x`. The runs from `x` and from
`h · x` are related tick by tick by `h`, and every gauge-invariant reading takes
the same values along both; for a law of Section 5.4, and slot by slot for a
law in steps. -/
@[book "prop:gauge-runs"]
theorem gaugeRuns : Statement.gaugeRuns := by
  refine ⟨fun A 𝒢 α L R hL hR => ?_, fun A 𝒢 α L R hL hR => ?_⟩
  · -- A law of Definition 5.9: the moves of a selected batch are moves of the law.
    have hF : ∀ (h : 𝒢) (x : A.Table), L.Legal x →
        (R.select (α.smul h x)).apply = α.smul h (R.select x).apply := fun h x hx =>
      select_smul α (fun x hx => forall_moves fun a ha => hL.moves _ (R.allows x hx a ha)) hR h hx
    refine ⟨hF, fun h n r r' hr hr' h0 => ?_⟩
    have hst : ∀ i, r'.state i = α.smul h (r.state i) :=
      state_smul α (sel := fun _ => R.select) (s := 0) (fun i => hF h _ (hr.1 _)) hr.2 hr'.2 h0
    refine ⟨hst, fun i => ?_, fun Q q hq i => by rw [hst i, hq]⟩
    rw [hr'.2 i, hr.2 i, hst i.castSucc]
    exact hR h _ (hr.1 _)
  · -- A law in steps: in each slot, the moves of the selected batch are moves of the open step.
    have hF : ∀ (t : ℕ) (h : 𝒢) (x : A.Table), L.LegalAt t x →
        (R.select t (α.smul h x)).apply = α.smul h (R.select t x).apply := fun t h x hx =>
      select_smul α (fun x hx => forall_moves fun a ha => hL.moves _ _ (R.allows t x hx a ha))
        (hR t) h hx
    refine ⟨hF, fun h s n r r' hx hr hr' h0 => ?_⟩
    have hlegal := Run.legalAt_of_follows (R := R) hx hr
    have hst : ∀ i, r'.state i = α.smul h (r.state i) :=
      state_smul α (sel := R.select) (s := s) (fun i => hF _ h _ (hlegal i.castSucc)) hr hr' h0
    refine ⟨hst, fun i => ?_, fun Q q hq i => by rw [hst i, hq]⟩
    rw [hr' i, hr i, hst i.castSucc]
    exact hR _ h _ (hlegal i.castSucc)

/-! ## Non-vacuity

The pose law of the two squares (Section 5.15). Its frame holds, in the
coordinates of a trivialization, a link `U_e` at each of the seven edges and a
pose `g_v` at each of the six corners, all in a group `G`. A gauge change `h`,
an element `h_v` at every corner, acts on a link by
`U_e ↦ h_{t(e)} U_e h_{s(e)}⁻¹` and on a pose by `g_v ↦ h_v g_v`.

Each turn is written as one move, which reads the links and poses of its
square and writes the square's four poses (`poseLeft`, `poseRight`). The book's
moves carry one pose each, but the carries of one turn are not compatible in
the sense of Definition 2.6: each writes the pose that the next one reads, so
no batch holds them all. As a law of Section 5.4 the pose law has one move, its
whole tick (`poseLaw`); as a law in steps it has two, the left turn open in the
even slots and the right turn in the odd ones. It declares no invariant, and
its realizer takes the one move of the open step.
-/

namespace GaugeRuns.PoseExample

open Skeleton Skeleton.TwoSquares Skeleton.TwoSquares.Vertex Skeleton.TwoSquares.Edge

/-- The positions of the pose frame: a link at every edge, a pose at every
corner. -/
inductive Pos
  | link (e : Edge)
  | pose (v : Vertex)

variable (G : Type)

/-- The pose frame: every position holds an element of the group `G`. -/
abbrev poseFrame : Presentation := ⟨Pos, fun _ => G⟩

variable [Group G]

/-- The gauge action of Definition 5.35 on the pose frame:
`U_e ↦ h_{t(e)} U_e h_{s(e)}⁻¹` on the link at the edge `e`, and `g_v ↦ h_v g_v`
on the pose at the corner `v`. -/
def poseAction : GaugeAction (poseFrame G) (Vertex → G) where
  act h p g := match p, g with
    | .link e, U => h e.tgt * U * (h e.src)⁻¹
    | .pose v, g => h v * g

variable {G}

/-- The link table of a state; the reversal law gives the links against the
edges' arrows. -/
def linksOf (x : (poseFrame G).Table) : skeleton.LinkTable G :=
  LinkTable.ofGraph fun e => x (.link e)

/-- The poses of a state. -/
def posesOf (x : (poseFrame G).Table) : Vertex → G := fun v => x (.pose v)

/-- The gauge action on a link along its arrow, `U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`. -/
theorem gaugeAct_along (h : Vertex → G) (U : skeleton.LinkTable G) (e : Edge) :
    gaugeAct h U (along e) = h e.tgt * U (along e) * (h e.src)⁻¹ := rfl

/-- The gauge action on a link against its arrow,
`U^h_{ē} = h_{s(e)} U_{ē} h_{t(e)}⁻¹`. -/
theorem gaugeAct_against (h : Vertex → G) (U : skeleton.LinkTable G) (e : Edge) :
    gaugeAct h U (against e) = h e.src * U (against e) * (h e.tgt)⁻¹ := rfl

/-- Two link tables with the same links are equal. -/
theorem linkTable_ext {U V : skeleton.LinkTable G} (h : ∀ e, U e = V e) : U = V := by
  obtain ⟨u, _⟩ := U
  obtain ⟨v, _⟩ := V
  obtain rfl : u = v := funext h
  rfl

/-- In link coordinates the gauge change acts on the link table as on a
connection (`eq:gauge-action`). -/
theorem linksOf_smul (h : Vertex → G) (x : (poseFrame G).Table) :
    linksOf ((poseAction G).smul h x) = gaugeAct h (linksOf x) := by
  refine linkTable_ext ?_
  rintro ⟨e, _ | _⟩
  · change (h e.tgt * x (.link e) * (h e.src)⁻¹)⁻¹ = h e.src * (x (.link e))⁻¹ * (h e.tgt)⁻¹
    group
  · rfl

/-- The gauge change on the poses of a state, `g_v ↦ h_v g_v`. -/
theorem posesOf_smul (h : Vertex → G) (x : (poseFrame G).Table) :
    posesOf ((poseAction G).smul h x) = fun v => h v * posesOf x v := rfl

/-- The book's calculation for the left turn, corner by corner:
`U^h_e h_u g_u = h_v (U_e g_u)`. -/
theorem poseLeft_gauge (h : Vertex → G) (U : skeleton.LinkTable G) (g : Vertex → G) :
    poseLeft (gaugeAct h U) (fun v => h v * g v) = fun v => h v * poseLeft U g v := by
  funext v
  cases v <;> simp only [poseLeft, gaugeAct_along, Edge.src, Edge.tgt] <;> group

/-- The book's calculation for the right turn, corner by corner; across `e₂`
against its arrow, `U^h_{ē₂} h_{v₂} g_{v₂} = h_{v₁} (U_{ē₂} g_{v₂})`. -/
theorem poseRight_gauge (h : Vertex → G) (U : skeleton.LinkTable G) (g : Vertex → G) :
    poseRight (gaugeAct h U) (fun v => h v * g v) = fun v => h v * poseRight U g v := by
  funext v
  cases v <;> simp only [poseRight, gaugeAct_along, gaugeAct_against, Edge.src, Edge.tgt] <;>
    group

/-- The left turn as one move (`poseLeft`). It reads the links at `e₁, …, e₄`
and the poses of the left square, and writes those four poses:
`g'_{v₁} = U_{e₁} g_{v₀}`, `g'_{v₂} = U_{e₂} g_{v₁}`, `g'_{v₃} = U_{e₃} g_{v₂}`
and `g'_{v₀} = U_{e₄} g_{v₃}`. -/
def leftTurnMove : ProcessProfile (poseFrame G) where
  guard _ := True
  reads := {Pos.link e₁, Pos.link e₂, Pos.link e₃, Pos.link e₄,
    Pos.pose v₀, Pos.pose v₁, Pos.pose v₂, Pos.pose v₃}
  writes := {Pos.pose v₀, Pos.pose v₁, Pos.pose v₂, Pos.pose v₃}
  update x p := match p with
    | .link e => x (.link e)
    | .pose v => poseLeft (linksOf x) (posesOf x) v
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy p hp := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · change x (.link e₄) * x (.pose v₃) = y (.link e₄) * y (.pose v₃)
      rw [hxy (.link e₄) (by simp), hxy (.pose v₃) (by simp)]
    · change x (.link e₁) * x (.pose v₀) = y (.link e₁) * y (.pose v₀)
      rw [hxy (.link e₁) (by simp), hxy (.pose v₀) (by simp)]
    · change x (.link e₂) * x (.pose v₁) = y (.link e₂) * y (.pose v₁)
      rw [hxy (.link e₂) (by simp), hxy (.pose v₁) (by simp)]
    · change x (.link e₃) * x (.pose v₂) = y (.link e₃) * y (.pose v₂)
      rw [hxy (.link e₃) (by simp), hxy (.pose v₂) (by simp)]

/-- The right turn as one move (`poseRight`). It reads the links at `e₂`, `e₅`,
`e₆`, `e₇` and the poses of the right square, and writes those four poses:
`g'_{v₄} = U_{e₅} g_{v₁}`, `g'_{v₅} = U_{e₆} g_{v₄}`, `g'_{v₂} = U_{e₇} g_{v₅}`,
and `g'_{v₁} = U_{e₂}⁻¹ g_{v₂}`, across `e₂` against its arrow. -/
def rightTurnMove : ProcessProfile (poseFrame G) where
  guard _ := True
  reads := {Pos.link e₂, Pos.link e₅, Pos.link e₆, Pos.link e₇,
    Pos.pose v₁, Pos.pose v₂, Pos.pose v₄, Pos.pose v₅}
  writes := {Pos.pose v₁, Pos.pose v₂, Pos.pose v₄, Pos.pose v₅}
  update x p := match p with
    | .link e => x (.link e)
    | .pose v => poseRight (linksOf x) (posesOf x) v
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy p hp := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · change (x (.link e₂))⁻¹ * x (.pose v₂) = (y (.link e₂))⁻¹ * y (.pose v₂)
      rw [hxy (.link e₂) (by simp), hxy (.pose v₂) (by simp)]
    · change x (.link e₇) * x (.pose v₅) = y (.link e₇) * y (.pose v₅)
      rw [hxy (.link e₇) (by simp), hxy (.pose v₅) (by simp)]
    · change x (.link e₅) * x (.pose v₁) = y (.link e₅) * y (.pose v₁)
      rw [hxy (.link e₅) (by simp), hxy (.pose v₁) (by simp)]
    · change x (.link e₆) * x (.pose v₄) = y (.link e₆) * y (.pose v₄)
      rw [hxy (.link e₆) (by simp), hxy (.pose v₄) (by simp)]

/-- The whole tick of the pose law as one move (`poseLaw`): the left turn and
then the right. It reads every link and every pose, and writes every pose. -/
def tickMove : ProcessProfile (poseFrame G) where
  guard _ := True
  reads := Set.univ
  writes := Set.range Pos.pose
  update x p := match p with
    | .link e => x (.link e)
    | .pose v => (poseLaw.tick (linksOf x, posesOf x)).2 v
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy _ _ := by
    obtain rfl : x = y := funext fun p => hxy p (Set.mem_univ p)
    rfl

/-- The left turn is gauge covariant: its proposal at `h · x` is `h` applied to
its proposal at `x`. -/
theorem leftTurnMove_covariant : (poseAction G).CovariantMove (leftTurnMove (G := G)) := by
  intro h x _
  refine ⟨trivial, fun p hp => ?_⟩
  cases p with
  | link e => simp [leftTurnMove] at hp
  | pose v =>
    change poseLeft (linksOf ((poseAction G).smul h x)) (posesOf ((poseAction G).smul h x)) v =
      h v * poseLeft (linksOf x) (posesOf x) v
    rw [linksOf_smul, posesOf_smul, poseLeft_gauge]

/-- The right turn is gauge covariant. -/
theorem rightTurnMove_covariant : (poseAction G).CovariantMove (rightTurnMove (G := G)) := by
  intro h x _
  refine ⟨trivial, fun p hp => ?_⟩
  cases p with
  | link e => simp [rightTurnMove] at hp
  | pose v =>
    change poseRight (linksOf ((poseAction G).smul h x)) (posesOf ((poseAction G).smul h x)) v =
      h v * poseRight (linksOf x) (posesOf x) v
    rw [linksOf_smul, posesOf_smul, poseRight_gauge]

/-- The whole tick is gauge covariant: each of its turns is. -/
theorem tickMove_covariant : (poseAction G).CovariantMove (tickMove (G := G)) := by
  intro h x _
  refine ⟨trivial, fun p hp => ?_⟩
  obtain ⟨v, rfl⟩ := hp
  change poseRight (linksOf ((poseAction G).smul h x))
      (poseLeft (linksOf ((poseAction G).smul h x)) (posesOf ((poseAction G).smul h x))) v =
    h v * poseRight (linksOf x) (poseLeft (linksOf x) (posesOf x)) v
  rw [linksOf_smul, posesOf_smul, poseLeft_gauge, poseRight_gauge]

variable (G) in
/-- The pose law as a law of Section 5.4: its one move is the whole tick; it
declares no invariant. -/
def poseTickLaw : Law (poseFrame G) where
  invariants := []
  profiles := [tickMove]
  moves_legal _ _ _ _ _ _ hJ := absurd hJ List.not_mem_nil

/-- The realizer of the pose law: the tick at every state. -/
def poseTickRealizer : DetRealizer (poseTickLaw G) where
  select _ := ⟨[⟨tickMove, trivial⟩], List.pairwise_singleton _ _⟩
  allows _ _ a ha := by
    rw [List.mem_singleton] at ha
    subst ha
    exact List.mem_singleton_self _
  keeps _ _ _ hJ := absurd hJ List.not_mem_nil

/-- The pose law, as a law of Section 5.4, is gauge covariant (Definition 5.35). -/
theorem poseTickLaw_covariant : (poseTickLaw G).GaugeCovariant (poseAction G) :=
  ⟨fun u hu => by
    obtain rfl : u = tickMove := List.mem_singleton.1 hu
    exact tickMove_covariant,
   fun _ _ => ⟨fun _ _ hJ => absurd hJ List.not_mem_nil, fun _ _ hJ => absurd hJ List.not_mem_nil⟩⟩

/-- Its realizer is gauge covariant: it selects the tick at every state. -/
theorem poseTickRealizer_covariant :
    (poseTickRealizer (G := G)).GaugeCovariant (poseAction G) :=
  fun _ _ _ => List.Perm.refl _

/-- The turn of the square that a step opens: `false` the left, `true` the
right. -/
def turnMove : Bool → ProcessProfile (poseFrame G)
  | false => leftTurnMove
  | true => rightTurnMove

/-- Each turn is enabled at every state. -/
theorem turnMove_guard (σ : Bool) (x : (poseFrame G).Table) : (turnMove σ).guard x := by
  cases σ <;> trivial

/-- Each turn is gauge covariant. -/
theorem turnMove_covariant (σ : Bool) : (poseAction G).CovariantMove (turnMove (G := G) σ) := by
  cases σ
  · exact leftTurnMove_covariant
  · exact rightTurnMove_covariant

/-- The score of the pose law in steps: the left square turns in the even slots
and the right square in the odd ones, so that a tick is two slots, left then
right; no slot may be empty. -/
def poseScore : Score Bool where
  opens t := decide (t % 2 = 1)
  allowsEmpty _ := False
  period := 2
  period_pos := by decide
  repeats t := ⟨by simp [Nat.add_mod_right], Iff.rfl⟩

variable (G) in
/-- The pose law as a law in steps: the left turn and the right turn, each a
step of one move, opened by the score; it declares no invariant. -/
def poseStepsLaw : LawInSteps (poseFrame G) where
  Step := Bool
  moves σ := [turnMove σ]
  invariants := []
  score := poseScore
  moves_legal _ _ _ _ _ _ _ hJ := absurd hJ List.not_mem_nil

/-- The realizer of the pose law in steps: the one move of the open step. -/
def poseStepsRealizer : (poseStepsLaw G).DetRealizer where
  select t x :=
    ⟨[⟨turnMove (poseScore.opens t), turnMove_guard _ x⟩], List.pairwise_singleton _ _⟩
  allows _ _ _ a ha := by
    rw [List.mem_singleton] at ha
    subst ha
    exact List.mem_singleton_self _
  keeps _ _ _ _ hJ := absurd hJ List.not_mem_nil

/-- The pose law in steps is gauge covariant (Definition 5.35). -/
theorem poseStepsLaw_covariant : (poseStepsLaw G).GaugeCovariant (poseAction G) :=
  ⟨fun σ u hu => by
    obtain rfl : u = turnMove σ := List.mem_singleton.1 hu
    exact turnMove_covariant σ,
   fun _ _ _ =>
    ⟨fun _ _ hJ => absurd hJ List.not_mem_nil, fun _ _ hJ => absurd hJ List.not_mem_nil⟩⟩

/-- Its realizer is gauge covariant: in each slot it selects the turn of the
open step at every state. -/
theorem poseStepsRealizer_covariant :
    (poseStepsRealizer (G := G)).GaugeCovariant (poseAction G) :=
  fun _ _ _ _ => List.Perm.refl _

/-- The links `1, 0, 1, 0, 1, 0, 1` of `fig:square-gauge`(a) at `e₁, …, e₇`. -/
def startLinks : Edge → ZMod 3
  | e₁ | e₃ | e₅ | e₇ => 1
  | e₂ | e₄ | e₆ => 0

/-- The state of `fig:covariant-law`: the links `startLinks`, and the pose `0`
at every corner, in `C₃`, where the number `k` stands for `r^k`. -/
def poseStart : (poseFrame (Multiplicative (ZMod 3))).Table := fun p => match p with
  | .link e => Multiplicative.ofAdd (startLinks e)
  | .pose _ => 1

/-- The gauge change by `1` at `v₁` (`gaugeChange`) moves the start: it turns
the pose at `v₁`. -/
theorem smul_poseStart_ne : (poseAction _).smul gaugeChange poseStart ≠ poseStart :=
  fun hc => absurd (congrFun hc (Pos.pose v₁)) (by decide)

/-- The holonomy round the outside from `v₀`, read from the links. -/
def outsideHolonomy (x : (poseFrame (Multiplicative (ZMod 3))).Table) :
    Multiplicative (ZMod 3) :=
  hol (linksOf x) (outside v₀)

/-- Over `C₃`, which is commutative, the holonomy round the outside is a
gauge-invariant reading (Theorem 5.23). -/
theorem outsideHolonomy_smul (h : Vertex → Multiplicative (ZMod 3))
    (x : (poseFrame (Multiplicative (ZMod 3))).Table) :
    outsideHolonomy ((poseAction _).smul h x) = outsideHolonomy x := by
  rw [outsideHolonomy, outsideHolonomy, linksOf_smul, hol_gaugeAct, mul_inv_cancel_comm]

end GaugeRuns.PoseExample

open GaugeRuns.PoseExample Skeleton.TwoSquares in
/-- The hypotheses of the first part are met by the pose law of the two squares
as a law of Section 5.4, over `C₃`, with the gauge change by `1` at `v₁` of
`fig:covariant-law`, which moves the start: the law and its realizer are gauge
covariant, the start is legal, the realizer has runs of five ticks from the
start and from its gauge transform, and the holonomy round the outside is a
gauge-invariant reading. -/
example :
    (poseTickLaw (Multiplicative (ZMod 3))).GaugeCovariant (poseAction _) ∧
    poseTickRealizer.GaugeCovariant (poseAction (Multiplicative (ZMod 3))) ∧
    (poseTickLaw _).Legal poseStart ∧
    (poseAction _).smul gaugeChange poseStart ≠ poseStart ∧
    (poseTickRealizer.inSteps.run 0 poseStart 5).OfDet poseTickRealizer ∧
    (poseTickRealizer.inSteps.run 0 ((poseAction _).smul gaugeChange poseStart) 5).OfDet
      poseTickRealizer ∧
    (poseTickRealizer.inSteps.run 0 ((poseAction _).smul gaugeChange poseStart) 5).state 0 =
      (poseAction _).smul gaugeChange ((poseTickRealizer.inSteps.run 0 poseStart 5).state 0) ∧
    ∀ (g : Vertex → Multiplicative (ZMod 3)) (y : (poseFrame (Multiplicative (ZMod 3))).Table),
      outsideHolonomy ((poseAction _).smul g y) = outsideHolonomy y :=
  ⟨poseTickLaw_covariant, poseTickRealizer_covariant, fun _ hJ => absurd hJ List.not_mem_nil,
    smul_poseStart_ne, ⟨fun _ _ hJ => absurd hJ List.not_mem_nil, fun _ => rfl⟩,
    ⟨fun _ _ hJ => absurd hJ List.not_mem_nil, fun _ => rfl⟩, rfl, outsideHolonomy_smul⟩

open GaugeRuns.PoseExample Skeleton.TwoSquares in
/-- The hypotheses of the second part are met by the pose law of the two
squares as a law in steps, over `C₃`, with the same gauge change and start:
the law and its realizer are gauge covariant, the start is legal at boundary
`0`, and the realizer has runs of ten slots, five ticks, from the start and
from its gauge transform. -/
example :
    (poseStepsLaw (Multiplicative (ZMod 3))).GaugeCovariant (poseAction _) ∧
    poseStepsRealizer.GaugeCovariant (poseAction (Multiplicative (ZMod 3))) ∧
    (poseStepsLaw _).LegalAt 0 poseStart ∧
    (poseAction _).smul gaugeChange poseStart ≠ poseStart ∧
    (poseStepsRealizer.run 0 poseStart 10).Follows poseStepsRealizer 0 ∧
    (poseStepsRealizer.run 0 ((poseAction _).smul gaugeChange poseStart) 10).Follows
      poseStepsRealizer 0 ∧
    (poseStepsRealizer.run 0 ((poseAction _).smul gaugeChange poseStart) 10).state 0 =
      (poseAction _).smul gaugeChange ((poseStepsRealizer.run 0 poseStart 10).state 0) :=
  ⟨poseStepsLaw_covariant, poseStepsRealizer_covariant, fun _ hJ => absurd hJ List.not_mem_nil,
    smul_poseStart_ne, fun _ => rfl, fun _ => rfl, rfl⟩

open GaugeRuns.PoseExample Skeleton.TwoSquares in
/-- Proposition 5.36 on the pose law: over five ticks from the state of
`fig:covariant-law` and from its gauge transform, the two runs are related at
every tick by the gauge change, and the holonomy round the outside reads the
same along both. -/
example (i : Fin 6) :
    (poseTickRealizer.inSteps.run 0 ((poseAction _).smul gaugeChange poseStart) 5).state i =
        (poseAction _).smul gaugeChange ((poseTickRealizer.inSteps.run 0 poseStart 5).state i) ∧
      outsideHolonomy
          ((poseTickRealizer.inSteps.run 0 ((poseAction _).smul gaugeChange poseStart) 5).state i) =
        outsideHolonomy ((poseTickRealizer.inSteps.run 0 poseStart 5).state i) := by
  have hr : ∀ x, (poseTickRealizer.inSteps.run 0 x 5).OfDet
      (poseTickRealizer (G := Multiplicative (ZMod 3))) :=
    fun _ => ⟨fun _ _ hJ => absurd hJ List.not_mem_nil, fun _ => rfl⟩
  have h := (gaugeRuns.1 _ _ _ _ _ poseTickLaw_covariant poseTickRealizer_covariant).2
    gaugeChange 5 _ _ (hr poseStart) (hr _) rfl
  exact ⟨h.1 i, h.2.2 _ outsideHolonomy (outsideHolonomy_smul gaugeChange) i⟩

end Artform
