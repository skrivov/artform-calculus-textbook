import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.OrderIsoNat
import ArtformTextbook.Ch03.Statements.Growth

/-!
# Growth: commuting changes, stabilization, fair closure and symmetry (Sections 3.8–3.9)

The proofs of Proposition 3.27, Theorem 3.29 and Propositions 3.32 and 3.33.

* 3.27: each change writes only its own footprint, and neither changes what
  the other reads, so the second computes the same update after the first.
* 3.29: every strict step adds a cell of `W` that the seed lacks, so there are
  at most `|W \ X₀|` of them in a row, and the first step that adds nothing
  repeats forever.
* 3.32: the run stays below every closed patch above its seed; it only adds
  cells of a finite window, so it stops growing; and a patch where it stops
  is closed, since an attachment that could still add a cell stays enabled,
  its phase keeps opening, and the policy would select it.
* 3.33: a motion of `S` carries each placement to a placement, each batch to a
  batch, and each run to a run.
-/

namespace Artform

/-! ## Proposition 3.27 -/

/-- **Proposition 3.27** (commuting compatible changes). If two enabled
applications are compatible, making one and then the other gives the same
state in either order. -/
@[book "prop:commuting-proposals"]
theorem commutingProposals : Statement.commutingProposals := by
  intro A x a b ⟨hW, hba, hab⟩
  -- Neither changes what the other reads, so each proposes the same values after the other.
  have hub := b.profile.update_reads _ _ hba
  have hua := a.profile.update_reads _ _ hab
  funext p
  simp only [ProcessProfile.apply]
  by_cases hpb : p ∈ b.profile.writes
  · have hpa : p ∉ a.profile.writes := fun h => Set.disjoint_left.1 hW h hpb
    simp [hpb, hpa, hub p hpb]
  · by_cases hpa : p ∈ a.profile.writes
    · simp [hpb, hpa, hua p hpa]
    · simp [hpb, hpa]

/-! ## Theorem 3.29 -/

/-- **Theorem 3.29** (stabilization). If `W` has finitely many cells and `F_W` is
extensive, then the increasing sequence `X₀ ⊆ X₁ ⊆ ⋯` stabilizes after finitely
many strict growth steps, at most `|cells(W) \ cells(X₀)|`. -/
@[book "thm:growth-stabilization"]
theorem growthStabilization : Statement.growthStabilization := by
  intro Cell W hW F hFW hext X₀
  have hsucc : ∀ t, F^[t + 1] X₀ = F (F^[t] X₀) := fun t => Function.iterate_succ_apply' F t X₀
  have hmono : ∀ t, F^[t] X₀ ⊆ F^[t + 1] X₀ := fun t => by
    rw [hsucc]
    exact hext _
  refine ⟨hmono, ?_⟩
  have hbdd : ∀ t, F^[t] X₀ ⊆ X₀ ∪ W := by
    intro t
    induction t with
    | zero => exact Set.subset_union_left
    | succ t ih =>
      rw [hsucc]
      exact (hFW _).trans (Set.union_subset ih Set.subset_union_right)
  have hseed : ∀ t, X₀ ⊆ F^[t] X₀ := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hmono t)
  -- The cells gained by step `t` are cells of `W` that the seed lacks.
  have hD : ∀ t, F^[t] X₀ \ X₀ ⊆ W \ X₀ := fun t c hc =>
    ⟨((hbdd t) hc.1).resolve_left hc.2, hc.2⟩
  have hWfin : (W \ X₀).Finite := hW.sdiff
  -- If the first `N` steps are strict, at least `N` cells have been gained.
  have hcount : ∀ N, (∀ j < N, F^[j] X₀ ≠ F^[j + 1] X₀) → N ≤ (F^[N] X₀ \ X₀).ncard := by
    intro N
    induction N with
    | zero => exact fun _ => Nat.zero_le _
    | succ N ih =>
      intro h
      have h1 := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
      have hss : F^[N] X₀ \ X₀ ⊂ F^[N + 1] X₀ \ X₀ := by
        refine Set.ssubset_iff_subset_ne.2 ⟨Set.sdiff_subset_sdiff_left (hmono N), fun heq => ?_⟩
        refine h N (Nat.lt_succ_self N) (Set.Subset.antisymm (hmono N) fun c hc => ?_)
        by_cases hc0 : c ∈ X₀
        · exact hseed N hc0
        · exact (show c ∈ F^[N] X₀ \ X₀ from heq ▸ ⟨hc, hc0⟩).1
      have hlt := Set.ncard_lt_ncard hss (hWfin.subset (hD _))
      omega
  -- So some step `N ≤ |W \ X₀|` adds nothing.
  obtain ⟨N, hNle, hN⟩ : ∃ N ≤ (W \ X₀).ncard, F^[N] X₀ = F^[N + 1] X₀ := by
    by_contra hcon
    push Not at hcon
    have h1 := hcount ((W \ X₀).ncard + 1) fun j hj => hcon j (Nat.lt_succ_iff.1 hj)
    have h2 := Set.ncard_le_ncard (hD ((W \ X₀).ncard + 1)) hWfin
    omega
  -- And a step that adds nothing repeats forever.
  have hstay : ∀ k, F^[N + k] X₀ = F^[N] X₀ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, hsucc, ih, ← hsucc, ← hN]
  refine ⟨N, hNle, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hstay k

/-! ## Attachments -/

variable {Cell : Type}

namespace ProcessProfile

/-- Making an attachment adds its cells: `X ↦ X ∪ W_p`. -/
theorem Attaches.apply_iff {u : ProcessProfile (patchFrame Cell)} (hu : u.Attaches)
    (X : (patchFrame Cell).Table) (c : Cell) : u.apply X c ↔ X c ∨ c ∈ u.writes := by
  unfold ProcessProfile.apply
  by_cases hc : c ∈ u.writes
  · rw [ite_eq_left hc]
    exact ⟨fun _ => Or.inr hc, fun _ => hu X c hc⟩
  · rw [ite_eq_right hc]
    exact ⟨Or.inl, fun h => h.resolve_right hc⟩

end ProcessProfile

/-- Making a list of attachments adds the cells of each. -/
theorem applyAll_attaches_iff {X : (patchFrame Cell).Table}
    (l : List (EnabledApp (patchFrame Cell) X)) (hl : ∀ a ∈ l, a.profile.Attaches)
    (Y : (patchFrame Cell).Table) (c : Cell) :
    applyAll l Y c ↔ Y c ∨ ∃ a ∈ l, c ∈ a.profile.writes := by
  induction l generalizing Y with
  | nil => simp [applyAll]
  | cons a l ih =>
    simp only [applyAll]
    rw [ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)),
      (hl a List.mem_cons_self).apply_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-! ## Proposition 3.32 -/

/-! ### Runs of policies

A scheduler carries out a run under a policy (`Policy.execution`), and every
continuing execution is the run of a policy that remembers the slot
(`Execution.eq_replay`); so "every run" ranges over the executions. -/

section Replay

variable {A : Presentation}

open Classical in
/-- The policy that replays an execution: it remembers the slot, and at the
execution's state it chooses the execution's batch. -/
noncomputable def Execution.replay (r : Execution A) : Policy A ℕ where
  choose x t := if h : x = r.state t then h ▸ r.batch t else ⟨[], List.Pairwise.nil⟩
  remember _ t := t + 1

theorem Execution.replay_choose (r : Execution A) (t : ℕ) :
    r.replay.choose (r.state t) t = r.batch t := by
  simp [Execution.replay]

theorem Execution.replay_trajectory (r : Execution A) (t : ℕ) :
    r.replay.trajectory (r.state 0) 0 t = (r.state t, t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ((r.replay.choose (r.replay.trajectory (r.state 0) 0 t).1
      (r.replay.trajectory (r.state 0) 0 t).2).apply, (r.replay.trajectory (r.state 0) 0 t).2 + 1)
        = _
    rw [ih, r.replay_choose t, r.step t]

theorem Execution.ext_of_state {r₁ r₂ : Execution A} (h : r₁.state = r₂.state)
    (hb : ∀ t, HEq (r₁.batch t) (r₂.batch t)) : r₁ = r₂ := by
  obtain ⟨st₁, b₁, _⟩ := r₁
  obtain ⟨st₂, b₂, _⟩ := r₂
  obtain rfl : st₁ = st₂ := h
  obtain rfl : b₁ = b₂ := funext fun t => eq_of_heq (hb t)
  rfl

/-- Every continuing execution is the run of a policy (Definition 3.28): one
that remembers the slot. -/
theorem Execution.eq_replay (r : Execution A) : r.replay.execution (r.state 0) 0 = r := by
  refine Execution.ext_of_state (funext fun t => congrArg Prod.fst (r.replay_trajectory t))
    fun t => ?_
  change HEq (r.replay.choose (r.replay.trajectory (r.state 0) 0 t).1
    (r.replay.trajectory (r.state 0) 0 t).2) (r.batch t)
  rw [r.replay_trajectory t]
  exact heq_of_eq (r.replay_choose t)

end Replay

namespace Execution

variable {r : Execution (patchFrame Cell)} {C : Control (patchFrame Cell)}

/-- Under a control whose rules attach, each step adds the cells of the
attachments it makes. -/
theorem state_succ_iff (hA : ∀ u ∈ C.rules, u.Attaches) (hr : r.Under C) (t : ℕ) (c : Cell) :
    r.state (t + 1) c ↔ r.state t c ∨ ∃ a ∈ (r.batch t).apps, c ∈ a.profile.writes := by
  rw [r.step t]
  exact applyAll_attaches_iff _ (fun a ha => hA _ (hr t a ha).1) _ c

theorem state_mono (hA : ∀ u ∈ C.rules, u.Attaches) (hr : r.Under C) :
    Monotone r.state :=
  monotone_nat_of_le_succ fun t c hc => (state_succ_iff hA hr t c).2 (Or.inl hc)

/-- A rule selected in slot `t` has its cells present from boundary `t + 1` on. -/
theorem writes_of_selected (hA : ∀ u ∈ C.rules, u.Attaches) (hr : r.Under C)
    {u : ProcessProfile (patchFrame Cell)} {t : ℕ} (hs : r.Selected u t) :
    ∀ c ∈ u.writes, r.state (t + 1) c := by
  obtain ⟨a, ha, rfl⟩ := hs
  exact fun c hc => (state_succ_iff hA hr t c).2 (Or.inr ⟨a, ha, hc⟩)

/-- The run stays below every closed patch above its seed. -/
theorem state_le_closed (hA : ∀ u ∈ C.rules, u.Attaches) (hP : ∀ u ∈ C.rules, u.Persistent)
    (hr : r.Under C) {Y : (patchFrame Cell).Table} (hY : Closed C.rules Y) (h0 : r.state 0 ≤ Y) :
    ∀ t, r.state t ≤ Y := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro c hc
    rcases (state_succ_iff hA hr t c).1 hc with hc | ⟨a, ha, hcw⟩
    · exact ih c hc
    · exact hY _ (hr t a ha).1 (hP _ (hr t a ha).1 _ _ ih a.enabled) c hcw

/-- In a finite window the run stops growing. -/
theorem eventually_const (hA : ∀ u ∈ C.rules, u.Attaches) (hr : r.Under C) {W : Set Cell}
    (hW : W.Finite) (hWr : ∀ u ∈ C.rules, u.writes ⊆ W) :
    ∃ T, ∀ t ≥ T, r.state t = r.state T := by
  have hmono := state_mono hA hr
  -- Every cell gained is a cell of the window.
  have hbdd : ∀ t c, r.state t c → r.state 0 c ∨ c ∈ W := by
    intro t
    induction t with
    | zero => exact fun c hc => Or.inl hc
    | succ t ih =>
      intro c hc
      rcases (state_succ_iff hA hr t c).1 hc with hc | ⟨a, ha, hcw⟩
      · exact ih c hc
      · exact Or.inr (hWr _ (hr t a ha).1 hcw)
  have : Finite W := hW.to_subtype
  let a : ℕ →o Set W := ⟨fun t => {c | r.state t c.1}, fun t t' h c hc => hmono h c.1 hc⟩
  obtain ⟨T, hT⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨T, fun t ht => funext fun c => propext ⟨fun hc => ?_, fun hc => hmono ht c hc⟩⟩
  rcases hbdd t c hc with h0 | hcW
  · exact hmono (Nat.zero_le T) c h0
  · have : (⟨c, hcW⟩ : W) ∈ a t := hc
    rw [← hT t ht] at this
    exact this

end Execution

/-- **Proposition 3.32** (fair closure). In a fixed finite window of possible
cells, every run that meets the three hypotheses reaches the least closed
patch above its seed and stays there. -/
@[book "prop:fair-closure"]
theorem fairClosure : Statement.fairClosure := by
  intro Cell W hW C hAW hP r hr hcf haf
  have hA : ∀ u ∈ C.rules, u.Attaches := fun u hu => (hAW u hu).1
  have hmono := Execution.state_mono hA hr
  obtain ⟨T, hT⟩ := Execution.eventually_const hA hr hW fun u hu => (hAW u hu).2
  -- Where the run stops, the patch is closed.
  have hclosed : Closed C.rules (r.state T) := by
    intro u hu hg c hcw
    by_contra hc
    -- `u` stays enabled, and it is never selected: a selection would add `c`.
    have hen : ∀ t ≥ T, u.guard (r.state t) := fun t ht => by rw [hT t ht]; exact hg
    have hns : ∀ s, ¬ r.Selected u s := by
      intro s hs
      have hcs := Execution.writes_of_selected hA hr hs c hcw
      rcases le_total (s + 1) T with h | h
      · exact hc (hmono h c hcs)
      · exact hc (Eq.mp (congrFun (hT (s + 1) h) c) hcs)
    -- Its phase keeps opening, by cadence fairness.
    have hoff : ∀ t₁, ∃ t' ≥ t₁, C.Offered u t' := by
      intro t₁
      obtain ⟨t', ht', hoff⟩ :=
        hcf u hu (max t₁ T) (hen _ (le_max_right _ _)) fun s _ => hns s
      exact ⟨t', (le_max_left _ _).trans ht', hoff⟩
    -- So application fairness selects it.
    obtain ⟨t', -, hsel⟩ := haf u hu T (fun s _ => hns s) (fun t' ht' _ => hen t' ht') hoff
    exact hns t' hsel
  refine ⟨T, fun t ht => ⟨⟨hT t ht ▸ hclosed, hmono (Nat.zero_le t)⟩, fun Y ⟨hY, h0⟩ => ?_⟩⟩
  exact Execution.state_le_closed hA hP hr hY h0 t

/-! ## Proposition 3.33 -/

section Motions

theorem movePatch_movePatch_inv (s : Equiv.Perm Cell) (X : (patchFrame Cell).Table) :
    movePatch s (movePatch s⁻¹ X) = X := by
  funext c
  change X ((s⁻¹).symm (s.symm c)) = X c
  rw [Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem moveProfile_guard (s : Equiv.Perm Cell) (u : ProcessProfile (patchFrame Cell))
    (X : (patchFrame Cell).Table) : (moveProfile s u).guard (movePatch s X) ↔ u.guard X := by
  have : (fun c => movePatch s X (s c)) = X := funext fun c => congrArg X (s.symm_apply_apply c)
  change u.guard (fun c => movePatch s X (s c)) ↔ u.guard X
  rw [this]

theorem moveProfile_apply (s : Equiv.Perm Cell) (u : ProcessProfile (patchFrame Cell))
    (X : (patchFrame Cell).Table) :
    (moveProfile s u).apply (movePatch s X) = movePatch s (u.apply X) := by
  have hX : (fun d => movePatch s X (s d)) = X :=
    funext fun d => congrArg X (s.symm_apply_apply d)
  funext c
  by_cases h : s.symm c ∈ u.writes
  · have h' : c ∈ (moveProfile s u).writes := h
    calc (moveProfile s u).apply (movePatch s X) c
        = u.update (fun d => movePatch s X (s d)) (s.symm c) := ite_eq_left h'
      _ = u.update X (s.symm c) := by rw [hX]
      _ = u.apply X (s.symm c) := (ite_eq_left h).symm
  · have h' : c ∉ (moveProfile s u).writes := h
    calc (moveProfile s u).apply (movePatch s X) c = X (s.symm c) := ite_eq_right h'
      _ = u.apply X (s.symm c) := (ite_eq_right h).symm

/-- A motion carries an enabled application to an enabled application. -/
def moveApp (s : Equiv.Perm Cell) {X : (patchFrame Cell).Table}
    (a : EnabledApp (patchFrame Cell) X) : EnabledApp (patchFrame Cell) (movePatch s X) :=
  ⟨moveProfile s a.profile, (moveProfile_guard s a.profile X).2 a.enabled⟩

theorem moveApp_compatible (s : Equiv.Perm Cell) {X : (patchFrame Cell).Table}
    {a b : EnabledApp (patchFrame Cell) X} (h : a.Compatible b) :
    (moveApp s a).Compatible (moveApp s b) := by
  obtain ⟨hW, hba, hab⟩ := h
  refine ⟨hW.preimage _, fun p hp => ?_, fun p hp => ?_⟩
  · change (moveProfile s a.profile).apply (movePatch s X) p = movePatch s X p
    rw [moveProfile_apply]
    exact hba _ hp
  · change (moveProfile s b.profile).apply (movePatch s X) p = movePatch s X p
    rw [moveProfile_apply]
    exact hab _ hp

theorem applyAll_map_moveApp (s : Equiv.Perm Cell) {X : (patchFrame Cell).Table}
    (l : List (EnabledApp (patchFrame Cell) X)) (Y : (patchFrame Cell).Table) :
    applyAll (l.map (moveApp s)) (movePatch s Y) = movePatch s (applyAll l Y) := by
  induction l generalizing Y with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, applyAll]
    rw [← ih]
    exact congrArg _ (moveProfile_apply s a.profile Y)

/-- A motion carries a batch to a batch. -/
def Batch.move (s : Equiv.Perm Cell) {X : (patchFrame Cell).Table}
    (b : Batch (patchFrame Cell) X) : Batch (patchFrame Cell) (movePatch s X) :=
  ⟨b.apps.map (moveApp s), List.pairwise_map.2 (b.compatible.imp (moveApp_compatible s))⟩

/-- A motion carries a run to a run. -/
def Run.move (s : Equiv.Perm Cell) {n : ℕ} (r : Run (patchFrame Cell) n) :
    Run (patchFrame Cell) n where
  state i := movePatch s (r.state i)
  batch i := (r.batch i).move s
  step i := by
    rw [r.step i]
    exact (applyAll_map_moveApp s _ _).symm

/-- A motion that carries the rules to themselves, with its inverse, commutes with
making every enabled attachment at once. -/
theorem movePatch_attachAll {R : Set (ProcessProfile (patchFrame Cell))} {s : Equiv.Perm Cell}
    (hs : ∀ u ∈ R, moveProfile s u ∈ R) (hs' : ∀ u ∈ R, moveProfile s⁻¹ u ∈ R)
    (X : (patchFrame Cell).Table) : movePatch s (attachAll R X) = attachAll R (movePatch s X) := by
  funext c
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨u, hu, hg, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨moveProfile s u, hs u hu, (moveProfile_guard s u X).2 hg, hw⟩
  · rcases h with h | ⟨u, hu, hg, hw⟩
    · exact Or.inl h
    · refine Or.inr ⟨moveProfile s⁻¹ u, hs' u hu, hg, ?_⟩
      change (s⁻¹).symm (s.symm c) ∈ u.writes
      simpa [Equiv.Perm.inv_def] using hw

end Motions

/-- **Proposition 3.33** (symmetry of growth). Let a positive attachment rule be
carried to itself by a group `G` of motions of the canvas, and let the motions
of a subgroup `S` fix the seed. The set of patches that some run reaches in `n`
steps is carried to itself by every motion of `S`; the policy that makes every
enabled attachment at once keeps `S` at every step; and at a patch that `S`
fixes, a policy that makes one attachment keeps `S` only if the attached face
is fixed by every motion of `S`. -/
@[book "prop:growth-symmetry"]
theorem growthSymmetry : Statement.growthSymmetry := by
  intro Cell R hR G S hSG hG X₀ hX₀
  have hS : ∀ s ∈ S, ∀ u ∈ R, moveProfile s u ∈ R := fun s hs => hG s (hSG hs)
  -- A motion of `S` carries each run from the seed to a run from the seed.
  have hreach : ∀ n, ∀ s ∈ S, ∀ X ∈ reachable R X₀ n, movePatch s X ∈ reachable R X₀ n := by
    rintro n s hs X ⟨r, h0, hb, rfl⟩
    refine ⟨r.move s, ?_, fun i a ha => ?_, rfl⟩
    · change movePatch s (r.state 0) = X₀
      rw [h0, hX₀ s hs]
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      exact hS s hs _ (hb i a' ha')
  refine ⟨fun n s hs => ?_, fun s hs t => ?_, ?_⟩
  · refine Set.Subset.antisymm ?_ fun X hX => ?_
    · rintro _ ⟨X, hX, rfl⟩
      exact hreach n s hs X hX
    · exact ⟨movePatch s⁻¹ X, hreach n s⁻¹ (S.inv_mem hs) X hX, movePatch_movePatch_inv s X⟩
  · induction t with
    | zero => exact hX₀ s hs
    | succ t ih =>
      rw [Function.iterate_succ_apply', movePatch_attachAll (hS s hs) (hS s⁻¹ (S.inv_mem hs)),
        ih]
  · intro X hX a ha c hw hc hY s hs
    have hAtt := (hR _ ha).1
    have hcw : c ∈ a.profile.writes := by
      rw [hw]
      exact Set.mem_singleton c
    -- The patch after the attachment has `c`, so it has `s c`.
    have hsc : a.profile.apply X (s c) := by
      have h := congrFun (hY s hs) (s c)
      change a.profile.apply X (s.symm (s c)) = a.profile.apply X (s c) at h
      rw [Equiv.symm_apply_apply] at h
      exact Eq.mp h ((hAtt.apply_iff X c).2 (Or.inr hcw))
    rcases (hAtt.apply_iff X (s c)).1 hsc with hX' | hw'
    · -- `s c` cannot be a cell of `X`: then `c` would be one, since `s⁻¹` fixes `X`.
      exact absurd (Eq.mp (congrFun (hX s⁻¹ (S.inv_mem hs)) c) hX') hc
    · rw [hw] at hw'
      exact hw'

/-! ## Non-vacuity -/

namespace GrowthExample

/-- The faces of the canvas `Q`, five by five, numbered by column and row; the
centre face is `(2, 2)`. -/
abbrev Face := Fin 5 × Fin 5

/-- Two faces of `Q` share an edge. -/
def Adjacent (f g : Face) : Prop :=
  (f.1 = g.1 ∧ (f.2.val + 1 = g.2.val ∨ g.2.val + 1 = f.2.val)) ∨
    (f.2 = g.2 ∧ (f.1.val + 1 = g.1.val ∨ g.1.val + 1 = f.1.val))

instance : DecidableRel Adjacent := fun f g => by
  unfold Adjacent
  infer_instance

/-- The attachment of the face `g` at a placement on the face `f`: valid when `f`
is present; it reads `f` and attaches `g`. -/
def attach (f g : Face) : ProcessProfile (patchFrame Face) where
  guard X := X f
  reads := {f}
  writes := {g}
  update _ _ := True
  guard_reads X Y h := by rw [h f (Set.mem_singleton f)]
  update_reads _ _ _ _ _ := rfl

/-- The rule of the monotone growth of Section 3.9: attach a face that shares an
edge with a face already present, one located attachment for each placement. -/
def rule : Set (ProcessProfile (patchFrame Face)) := {u | ∃ f g, Adjacent f g ∧ attach f g = u}

/-- The seed: the centre face of `Q`. -/
def seed : (patchFrame Face).Table := fun c => c = (2, 2)

theorem rule_attaches : ∀ u ∈ rule, u.Attaches ∧ u.Persistent := by
  rintro _ ⟨f, g, -, rfl⟩
  exact ⟨fun _ _ _ => trivial, fun _ _ h hX => h f hX⟩

theorem ProcessProfile.ext' {A : Presentation} {u v : ProcessProfile A} (hg : u.guard = v.guard)
    (hr : u.reads = v.reads) (hw : u.writes = v.writes) (hu : u.update = v.update) : u = v := by
  cases u
  cases v
  cases hg
  cases hr
  cases hw
  cases hu
  rfl

theorem moveProfile_attach (g : Equiv.Perm Face) (f c : Face) :
    moveProfile g (attach f c) = attach (g f) (g c) := by
  refine ProcessProfile.ext' rfl ?_ ?_ rfl
  · ext d
    simp [moveProfile, attach, Equiv.symm_apply_eq]
  · ext d
    simp [moveProfile, attach, Equiv.symm_apply_eq]

/-- The motions of the canvas `Q`, acting on its faces: the permutations that keep
which faces share an edge. -/
def motions : Subgroup (Equiv.Perm Face) where
  carrier := {g | ∀ f c, Adjacent f c ↔ Adjacent (g f) (g c)}
  one_mem' _ _ := Iff.rfl
  mul_mem' {g h} hg hh f c := (hh f c).trans (hg (h f) (h c))
  inv_mem' {g} hg f c := by
    have := hg (g⁻¹ f) (g⁻¹ c)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
    exact this.symm

/-- The motions of `Q` that fix the centre face. -/
def centreMotions : Subgroup (Equiv.Perm Face) where
  carrier := {g | g ∈ motions ∧ g (2, 2) = (2, 2)}
  one_mem' := ⟨motions.one_mem, rfl⟩
  mul_mem' {g h} hg hh := ⟨motions.mul_mem hg.1 hh.1, by
    rw [Equiv.Perm.mul_apply, hh.2, hg.2]⟩
  inv_mem' {g} hg := ⟨motions.inv_mem hg.1, by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hg.2.symm⟩

/-- Making every enabled attachment of the rule at once, on the patches of `Q`. -/
def growthStep : Set Face → Set Face := attachAll rule

/-- The quarter turn of `Q`, `(i, j) ↦ (4 − j, i)`. -/
def quarterTurn : Equiv.Perm Face where
  toFun p := (p.2.rev, p.1)
  invFun p := (p.2, p.1.rev)
  left_inv p := by simp
  right_inv p := by simp

/-- The located attachments of the rule, listed. -/
noncomputable def ruleList : List (ProcessProfile (patchFrame Face)) :=
  ((Finset.univ : Finset (Face × Face)).filter fun p => Adjacent p.1 p.2).toList.map
    fun p => attach p.1 p.2

theorem mem_ruleList (u : ProcessProfile (patchFrame Face)) : u ∈ ruleList ↔ u ∈ rule := by
  simp [ruleList, rule]

end GrowthExample

/-! ### A fair execution: the round-robin policy -/

namespace GrowthExample

variable {A : Presentation}

open Classical in
/-- A round-robin policy over a list of rules: in slot `t` it makes the rule
numbered `t mod m`, if that rule is enabled. Its memory is the slot. -/
noncomputable def roundRobin (rs : List (ProcessProfile A)) : Policy A ℕ where
  choose x t := match rs[t % rs.length]? with
    | some u =>
      if h : u.guard x then ⟨[⟨u, h⟩], List.pairwise_singleton _ _⟩ else ⟨[], List.Pairwise.nil⟩
    | none => ⟨[], List.Pairwise.nil⟩
  remember _ t := t + 1

/-- The control with one phase, open in every slot. -/
def everySlot (rs : List (ProcessProfile A)) : Control A :=
  ⟨Unit, {u | u ∈ rs}, fun _ => (), fun _ => ()⟩

theorem roundRobin_memory (rs : List (ProcessProfile A)) (x₀ : A.Table) (t : ℕ) :
    ((roundRobin rs).trajectory x₀ 0 t).2 = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ((roundRobin rs).trajectory x₀ 0 t).2 + 1 = t + 1
    rw [ih]

theorem roundRobin_choose_mem (rs : List (ProcessProfile A)) (x : A.Table) (t : ℕ) :
    ∀ a ∈ ((roundRobin rs).choose x t).apps, a.profile ∈ rs := by
  intro a ha
  simp only [roundRobin] at ha
  split at ha
  · rename_i u hu
    split at ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact List.mem_of_getElem? hu
    · simp at ha
  · simp at ha

theorem roundRobin_choose_of_guard (rs : List (ProcessProfile A)) (x : A.Table) (t k : ℕ)
    (hk : k < rs.length) (hmod : t % rs.length = k) (hg : rs[k].guard x) :
    (⟨rs[k], hg⟩ : EnabledApp A x) ∈ ((roundRobin rs).choose x t).apps := by
  have h : rs[t % rs.length]? = some rs[k] := by rw [hmod, List.getElem?_eq_getElem hk]
  simp only [roundRobin, h, dite_eq_left hg]
  exact List.mem_singleton_self _

theorem roundRobin_under (rs : List (ProcessProfile A)) (x₀ : A.Table) :
    ((roundRobin rs).execution x₀ 0).Under (everySlot rs) :=
  fun _ a ha => ⟨roundRobin_choose_mem rs _ _ a ha, rfl⟩

theorem roundRobin_fair (rs : List (ProcessProfile A)) (x₀ : A.Table) :
    ((roundRobin rs).execution x₀ 0).CadenceFair (everySlot rs) ∧
      ((roundRobin rs).execution x₀ 0).ApplicationFair (everySlot rs) := by
  refine ⟨fun u _ t _ _ => ⟨t, le_rfl, rfl⟩, fun u hu t _ hen _ => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hu
  have hpos : 0 < rs.length := lt_of_le_of_lt (Nat.zero_le k) hk
  have hle : t ≤ rs.length * (t + 1) + k := by nlinarith
  have hmod : (rs.length * (t + 1) + k) % rs.length = k := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  have hg := hen _ hle rfl
  refine ⟨_, hle, ⟨rs[k], hg⟩, ?_, rfl⟩
  have hb : ((roundRobin rs).execution x₀ 0).batch (rs.length * (t + 1) + k) =
      (roundRobin rs).choose (((roundRobin rs).execution x₀ 0).state (rs.length * (t + 1) + k))
        (rs.length * (t + 1) + k) := by
    change (roundRobin rs).choose _
      ((roundRobin rs).trajectory x₀ 0 (rs.length * (t + 1) + k)).2 = _
    rw [roundRobin_memory]
    rfl
  rw [hb]
  exact roundRobin_choose_of_guard rs _ _ k hk hmod hg

end GrowthExample

open GrowthExample in
/-- The hypotheses of Proposition 3.32 hold for the growth of Section 3.9 in the
window `W₂ = Q`, from the centre face: the rule's attachments are positive and
attach cells of the window, and the round-robin policy, which offers every
attachment in turn, gives a run that is cadence fair and application fair. -/
example : ∃ (C : Control (patchFrame Face)) (r : Execution (patchFrame Face)),
    (Set.univ : Set Face).Finite ∧ (∀ u ∈ C.rules, u.Attaches ∧ u.writes ⊆ Set.univ) ∧
    (∀ u ∈ C.rules, u.Persistent) ∧ r.state 0 = seed ∧
    r.Under C ∧ r.CadenceFair C ∧ r.ApplicationFair C := by
  refine ⟨everySlot ruleList, (roundRobin ruleList).execution seed 0, Set.finite_univ,
    fun u hu => ⟨(rule_attaches u ((mem_ruleList u).1 hu)).1, Set.subset_univ _⟩,
    fun u hu => (rule_attaches u ((mem_ruleList u).1 hu)).2, rfl, roundRobin_under _ _,
    roundRobin_fair _ _⟩

open GrowthExample in
/-- The diamond of Section 3.8: at the seed, attaching its east neighbour and
attaching its north neighbour are compatible, the hypothesis of
Proposition 3.27. -/
example : ∃ a b : EnabledApp (patchFrame Face) seed,
    a.profile = attach (2, 2) (3, 2) ∧ b.profile = attach (2, 2) (2, 3) ∧ a.Compatible b := by
  refine ⟨⟨attach (2, 2) (3, 2), rfl⟩, ⟨attach (2, 2) (2, 3), rfl⟩, rfl, rfl,
    Set.disjoint_singleton.2 (by decide), fun p hp => ?_, fun p hp => ?_⟩
  · rw [Set.mem_singleton_iff.1 hp]
    exact ite_eq_right (by simp [attach])
  · rw [Set.mem_singleton_iff.1 hp]
    exact ite_eq_right (by simp [attach])

open GrowthExample in
/-- The hypotheses of Theorem 3.29 hold for the growth of Section 3.9 in the
window `W₂ = Q`: `F_W` makes every enabled attachment of the rule at once. -/
example : (Set.univ : Set Face).Finite ∧ (∀ X, growthStep X ⊆ X ∪ Set.univ) ∧
    ∀ X, X ⊆ growthStep X :=
  ⟨Set.finite_univ, fun _ _ _ => Or.inr trivial, fun _ _ h => Or.inl h⟩

open GrowthExample in
/-- The hypotheses of Proposition 3.33 hold for the growth of Section 3.9: the
rule is positive and is carried to itself by the motions of `Q`, the motions
that fix the centre face form a subgroup that fixes the seed, and the quarter
turn is one of them. -/
example : (∀ u ∈ rule, u.Attaches ∧ u.Persistent) ∧ centreMotions ≤ motions ∧
    (∀ g ∈ motions, ∀ u ∈ rule, moveProfile g u ∈ rule) ∧
    (∀ s ∈ centreMotions, movePatch s seed = seed) ∧
    quarterTurn ∈ centreMotions ∧ quarterTurn ≠ 1 := by
  refine ⟨rule_attaches, fun g hg => hg.1, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro g hg _ ⟨f, c, hfc, rfl⟩
    exact ⟨g f, g c, (hg f c).1 hfc, (moveProfile_attach g f c).symm⟩
  · intro s hs
    funext d
    change (s.symm d = (2, 2)) = (d = (2, 2))
    rw [Equiv.symm_apply_eq, hs.2]
  · change ∀ f c : Face, Adjacent f c ↔ Adjacent (quarterTurn f) (quarterTurn c)
    decide
  · decide
  · intro h
    have := congrArg (fun g : Equiv.Perm Face => g (0, 0)) h
    exact absurd this (by decide)

end Artform
