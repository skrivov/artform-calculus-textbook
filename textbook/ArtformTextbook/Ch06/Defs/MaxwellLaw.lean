import Mathlib.Data.Finset.Dedup
import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch05.Defs.Calculus
import ArtformTextbook.Ch05.Defs.GaugeLaw

/-!
# The Maxwell law in steps (Section 6.3, "Locality and parallelism")

In the terms of Definition 5.12, the frame carries `A`, `E` and the source `J`
on the links and `ρ` on the sites, and no move writes `J`. The moves are the
kick and the Faraday move at each link and the charge update `ρ' = ρ − div J`
at each site, in the kick phase; the score opens the kick step and then the
move step; and the invariant is `div E = ρ`. A kick reads the faces at its link
and their boundary links, a Faraday move its own link, and a charge update the
links at its site. The realizer takes every move of the open step.

The law is written here by its parts: its frame, its moves with their steps,
its invariant, and the batch its realizer selects in each step. It is not a
`LawInSteps` (`Ch05/Defs/Steps.lean`): that structure asks each single move of
the open step to lead from a state legal at the slot's opening boundary to one
legal at its closing boundary, and the Maxwell law keeps Gauss's law only batch
by batch (Theorem 6.4). A kick at one link alone changes `div E` at both its
ends, and a Faraday move made from a state between the kick and the move, where
nothing is checked, need not end in a legal state.
-/

namespace Artform

/-- The positions of the Maxwell frame on a canvas `K`: the potential `A`, the
electric link `E` and the source current `J` at every edge, and the charge `ρ`
at every site. -/
inductive MaxwellPos (K : Canvas)
  /-- The potential at an edge. -/
  | A (e : K.E)
  /-- The electric link at an edge. -/
  | E (e : K.E)
  /-- The source current at an edge. -/
  | J (e : K.E)
  /-- The charge at a site. -/
  | ρ (v : K.V)

/-- The Maxwell frame: every position holds a residue modulo eight. -/
abbrev maxwellFrame (K : Canvas) : Presentation := ⟨MaxwellPos K, fun _ => ZMod 8⟩

variable {K : Canvas}

/-- The potential of a table of the Maxwell frame. -/
def potentialOf (x : (maxwellFrame K).Table) : K.E → ZMod 8 := fun e => x (.A e)

/-- The electric links of a table of the Maxwell frame. -/
def electricOf (x : (maxwellFrame K).Table) : K.E → ZMod 8 := fun e => x (.E e)

/-- The source current of a table of the Maxwell frame. -/
def currentOf (x : (maxwellFrame K).Table) : K.E → ZMod 8 := fun e => x (.J e)

/-- The charges of a table of the Maxwell frame. -/
def chargeOf (x : (maxwellFrame K).Table) : K.V → ZMod 8 := fun v => x (.ρ v)

/-- An edge that the boundary of a face never runs along is read `0` by it. -/
private theorem Canvas.inc_eq_zero_of_not_mem {e : K.E} {f : K.F}
    (he : e ∉ (K.boundary f).map Prod.fst) : K.inc e f = 0 := by
  unfold Canvas.inc
  refine List.sum_eq_zero fun z hz => ?_
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hz
  have hne : st.1 ≠ e := fun h => he (List.mem_map.mpr ⟨st, hst, h⟩)
  simp [hne]

variable (K)

/-- The kick at the edge `e`: it writes `E(e) + curl*(curl A)(e) − J(e)` at
`E(e)`. It reads `E(e)`, `J(e)` and the potential on the edges of the faces at
`e`. -/
def kickMove (e : K.E) : ProcessProfile (maxwellFrame K) where
  guard _ := True
  reads := {p | (∃ f e', e ∈ (K.boundary f).map Prod.fst ∧ e' ∈ (K.boundary f).map Prod.fst ∧
    p = .A e') ∨ p = .E e ∨ p = .J e}
  writes := {.E e}
  update x _ := x (.E e) + K.curlStar (K.curl (potentialOf x)) e - x (.J e)
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy _ _ := by
    have hE : x (.E e) = y (.E e) := hxy _ (Or.inr (Or.inl rfl))
    have hJ : x (.J e) = y (.J e) := hxy _ (Or.inr (Or.inr rfl))
    have hB : K.curlStar (K.curl (potentialOf x)) e = K.curlStar (K.curl (potentialOf y)) e := by
      unfold Canvas.curlStar Canvas.curl
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases hf : e ∈ (K.boundary f).map Prod.fst
      · congr 1
        refine Finset.sum_congr rfl fun e' _ => ?_
        by_cases he' : e' ∈ (K.boundary f).map Prod.fst
        · rw [show potentialOf x e' = potentialOf y e' from
            hxy _ (Or.inl ⟨f, e', hf, he', rfl⟩)]
        · simp [Canvas.inc_eq_zero_of_not_mem he']
      · simp [Canvas.inc_eq_zero_of_not_mem hf]
    simp only [hE, hJ, hB]

/-- The Faraday move at the edge `e`: it writes `A(e) − E(e)` at `A(e)`,
reading `A(e)` and `E(e)`. Made after the kick, it reads the new `E`. -/
def faradayMove (e : K.E) : ProcessProfile (maxwellFrame K) where
  guard _ := True
  reads := {.A e, .E e}
  writes := {.A e}
  update x _ := x (.A e) - x (.E e)
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy _ _ := by
    have hA : x (.A e) = y (.A e) := hxy _ (Or.inl rfl)
    have hE : x (.E e) = y (.E e) := hxy _ (Or.inr rfl)
    simp only [hA, hE]

/-- The charge update at the site `v`, continuity: it writes
`ρ(v) − div J(v)` at `ρ(v)`, reading `ρ(v)` and the current on the edges at
`v`. -/
def chargeMove (v : K.V) : ProcessProfile (maxwellFrame K) where
  guard _ := True
  reads := {p | p = .ρ v ∨ ∃ e, (K.src e = v ∨ K.tgt e = v) ∧ p = .J e}
  writes := {.ρ v}
  update x _ := x (.ρ v) - K.div (currentOf x) v
  guard_reads _ _ _ := Iff.rfl
  update_reads x y hxy _ _ := by
    have hρ : x (.ρ v) = y (.ρ v) := hxy _ (Or.inl rfl)
    have hdiv : K.div (currentOf x) v = K.div (currentOf y) v := by
      unfold Canvas.div
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : K.src e = v ∨ K.tgt e = v
      · have hJ : x (.J e) = y (.J e) := hxy _ (Or.inr ⟨e, he, rfl⟩)
        simp only [currentOf, hJ]
      · rw [not_or] at he
        simp [he.1, he.2]
    simp only [hρ, hdiv]

/-- The two steps of the Maxwell score, opened in turn: the kick, then the
move. -/
inductive MaxwellStep
  /-- The kick step: the kicks and the charge updates. -/
  | kick
  /-- The move step: the Faraday moves. -/
  | move

/-- The moves of each step. The kick step holds the kick at every edge and the
charge update at every site; the move step holds the Faraday move at every
edge. -/
noncomputable def maxwellStepMoves : MaxwellStep → List (ProcessProfile (maxwellFrame K))
  | .kick => (Finset.univ : Finset K.E).toList.map (kickMove K) ++
      (Finset.univ : Finset K.V).toList.map (chargeMove K)
  | .move => (Finset.univ : Finset K.E).toList.map (faradayMove K)

/-- All the moves of the Maxwell law, those of the kick step and then those of
the move step. -/
noncomputable def maxwellMoves : List (ProcessProfile (maxwellFrame K)) :=
  maxwellStepMoves K .kick ++ maxwellStepMoves K .move

/-- Gauss's law, `div E = ρ`. -/
def gaussLaw (x : (maxwellFrame K).Table) : Prop := K.div (electricOf x) = chargeOf x

/-- The invariants of the Maxwell law: Gauss's law alone, checked at the
macro-tick checkpoints. -/
def maxwellInvariants : List ((maxwellFrame K).Table → Prop) := [gaussLaw K]

/-- A legal state of the Maxwell law: every invariant holds. -/
def maxwellLegal (x : (maxwellFrame K).Table) : Prop := ∀ J ∈ maxwellInvariants K, J x

/-- The gauge action on the Maxwell frame, for a site function `g`: it adds
`Dg(e) = g(t(e)) − g(s(e))` to the potential at every edge `e`
(`eq:gauge-formula`, the additive form of `eq:gauge-action`), and fixes `E`,
`J` and `ρ`. -/
def maxwellGaugeAction : GaugeAction (maxwellFrame K) (K.V → ZMod 8) where
  act g p a := match p with
    | .A e => a + K.diff g e
    | .E _ => a
    | .J _ => a
    | .ρ _ => a

variable {K}

/-- Making a change leaves every position outside its write footprint alone. -/
private theorem ProcessProfile.apply_of_not_mem {A : Presentation} (u : ProcessProfile A)
    (x : A.Table) {p : A.P} (hp : p ∉ u.writes) : u.apply x p = x p := by
  simp [ProcessProfile.apply, hp]

/-- Two enabled applications are compatible when their write footprints are
disjoint and neither writes what the other reads. -/
private theorem EnabledApp.compatible_of_disjoint {A : Presentation} {x : A.Table}
    (a b : EnabledApp A x) (hw : Disjoint a.profile.writes b.profile.writes)
    (hab : Disjoint a.profile.writes b.profile.reads)
    (hba : Disjoint b.profile.writes a.profile.reads) : a.Compatible b :=
  ⟨hw, fun _ hp => a.profile.apply_of_not_mem x fun h => Set.disjoint_left.mp hab h hp,
    fun _ hp => b.profile.apply_of_not_mem x fun h => Set.disjoint_left.mp hba h hp⟩

variable {x : (maxwellFrame K).Table}

/-- Kicks at two different edges are compatible. -/
theorem kick_compatible_kick {e e' : K.E} (hne : e ≠ e') :
    (⟨kickMove K e, trivial⟩ : EnabledApp (maxwellFrame K) x).Compatible
      ⟨kickMove K e', trivial⟩ := by
  refine EnabledApp.compatible_of_disjoint _ _ ?_ ?_ ?_
  · exact Set.disjoint_singleton.mpr fun h => hne (MaxwellPos.E.inj h)
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .E e := hp
    rcases hq with ⟨_, _, _, _, h⟩ | h | h
    · cases h
    · exact hne (MaxwellPos.E.inj h)
    · cases h
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .E e' := hp
    rcases hq with ⟨_, _, _, _, h⟩ | h | h
    · cases h
    · exact hne (MaxwellPos.E.inj h).symm
    · cases h

/-- Charge updates at two different sites are compatible. -/
theorem charge_compatible_charge {v v' : K.V} (hne : v ≠ v') :
    (⟨chargeMove K v, trivial⟩ : EnabledApp (maxwellFrame K) x).Compatible
      ⟨chargeMove K v', trivial⟩ := by
  refine EnabledApp.compatible_of_disjoint _ _ ?_ ?_ ?_
  · exact Set.disjoint_singleton.mpr fun h => hne (MaxwellPos.ρ.inj h)
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .ρ v := hp
    rcases hq with h | ⟨_, _, h⟩
    · exact hne (MaxwellPos.ρ.inj h)
    · cases h
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .ρ v' := hp
    rcases hq with h | ⟨_, _, h⟩
    · exact hne (MaxwellPos.ρ.inj h).symm
    · cases h

/-- A kick and a charge update are compatible. -/
theorem kick_compatible_charge (e : K.E) (v : K.V) :
    (⟨kickMove K e, trivial⟩ : EnabledApp (maxwellFrame K) x).Compatible
      ⟨chargeMove K v, trivial⟩ := by
  refine EnabledApp.compatible_of_disjoint _ _ ?_ ?_ ?_
  · exact Set.disjoint_singleton.mpr fun h => by cases h
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .E e := hp
    rcases hq with h | ⟨_, _, h⟩ <;> cases h
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .ρ v := hp
    rcases hq with ⟨_, _, _, _, h⟩ | h | h <;> cases h

/-- Faraday moves at two different edges are compatible. -/
theorem faraday_compatible_faraday {e e' : K.E} (hne : e ≠ e') :
    (⟨faradayMove K e, trivial⟩ : EnabledApp (maxwellFrame K) x).Compatible
      ⟨faradayMove K e', trivial⟩ := by
  refine EnabledApp.compatible_of_disjoint _ _ ?_ ?_ ?_
  · exact Set.disjoint_singleton.mpr fun h => hne (MaxwellPos.A.inj h)
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .A e := hp
    rcases hq with h | h
    · exact hne (MaxwellPos.A.inj h)
    · cases h
  · refine Set.disjoint_left.mpr fun p hp hq => ?_
    obtain rfl : p = .A e' := hp
    rcases hq with h | h
    · exact hne (MaxwellPos.A.inj h).symm
    · cases h

variable (K)

/-- The batch that the realizer of the Maxwell law selects in each step: every
move of the open step, each enabled, since no guard asks anything. The kicks
and the charge updates write different positions and read none that another
writes; so do the Faraday moves. -/
noncomputable def maxwellSelect (σ : MaxwellStep) (x : (maxwellFrame K).Table) :
    Batch (maxwellFrame K) x :=
  match σ with
  | .kick =>
    { apps := (Finset.univ : Finset K.E).toList.map (fun e => ⟨kickMove K e, trivial⟩) ++
        (Finset.univ : Finset K.V).toList.map (fun v => ⟨chargeMove K v, trivial⟩)
      compatible := List.pairwise_append.mpr
        ⟨List.pairwise_map.mpr (List.Pairwise.imp kick_compatible_kick (Finset.nodup_toList _)),
          List.pairwise_map.mpr
            (List.Pairwise.imp charge_compatible_charge (Finset.nodup_toList _)),
          fun a ha b hb => by
            obtain ⟨e, -, rfl⟩ := List.mem_map.mp ha
            obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
            exact kick_compatible_charge e v⟩ }
  | .move =>
    { apps := (Finset.univ : Finset K.E).toList.map (fun e => ⟨faradayMove K e, trivial⟩)
      compatible :=
        List.pairwise_map.mpr (List.Pairwise.imp faraday_compatible_faraday
          (Finset.nodup_toList _)) }

end Artform
