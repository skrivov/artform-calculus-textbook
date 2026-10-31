import ArtformScores.ClassicalNonabelian.Dynamics
import ArtformTextbook.Ch05.GaugeRuns

/-! # Owned classical commits and a nontrivial Gauss-checked two-phase law -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.ClassicalNonabelian
open Artform
abbrev Position := Bool × canvas.E
abbrev frame (G : Type) : Presentation := ⟨Position,fun _ => G⟩
def encode {G : Type} (s : State G) : (frame G).Table
  | (false,e) => s.U e
  | (true,e) => s.P e
def decode {G : Type} (x : (frame G).Table) : State G := ⟨fun e => x (false,e),fun e => x (true,e)⟩
@[simp] lemma decode_encode {G : Type} (s : State G) : decode (encode s)=s := rfl
@[simp] lemma encode_decode {G : Type} (x : (frame G).Table) : encode (decode x)=x := by
  funext ⟨b,e⟩
  cases b <;> rfl

variable {G : Type} [Group G]
def writes (g : Instruction) : Set Position := fun q =>
  match g with
  | .kick _ => q.1=true ∧ q.2 ≠ 4
  | .drift _ => q.1=false
  | .link _ e => q=(false,e)
def reads (g : Instruction) : Set Position := fun q =>
  match g with
  | .kick _ => q.2 ≠ 4
  | .drift _ => True
  | .link _ e => q.2=e
lemma holonomy_reads (U V : canvas.E → G) (h : ∀ e, e ≠ 4 → U e = V e) :
    holonomy U=holonomy V := by
  rw [holonomy_word,holonomy_word]
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]
lemma proposal_reads (g : Instruction) (x y : (frame G).Table)
    (h : ∀ q, reads g q → x q = y q) (q : Position) (hq : writes g q) :
    encode (execute g (decode x)) q=encode (execute g (decode y)) q := by
  cases g with
  | drift b =>
    have he : x=y := funext fun p => h p trivial
    rw [he]
  | link b e =>
    change q=(false,e) at hq
    subst q
    simp only [encode,execute,driftOne,Function.update_self,decode]
    rw [h (true,e) rfl,h (false,e) rfl]
  | kick b =>
    rcases q with ⟨a,e⟩
    cases a with
    | false => exact False.elim (Bool.false_ne_true hq.1)
    | true =>
      have hh := holonomy_reads (decode x).U (decode y).U (fun e he => h (false,e) he)
      change multiplier b (decode x).U e*x (true,e)=multiplier b (decode y).U e*y (true,e)
      rw [show multiplier b (decode x).U e=multiplier b (decode y).U e by simp only [multiplier,hh]]
      rw [h (true,e) hq.2]
lemma proposal_frame (g : Instruction) (x : (frame G).Table) (q : Position)
    (hq : ¬ writes g q) : encode (execute g (decode x)) q=x q := by
  rcases q with ⟨a,e⟩
  cases g with
  | drift b =>
    cases a with
    | false => exact False.elim (hq rfl)
    | true => rfl
  | link b f =>
    cases a with
    | false =>
      have he : e ≠ f := by simpa [writes] using hq
      simp [encode,execute,driftOne,decode,he]
    | true => rfl
  | kick b =>
    cases a with
    | false => rfl
    | true =>
      have he : e=4 := by simpa [writes] using hq
      subst e
      simp [encode,execute,kick,multiplier_spectator,decode]

def profile (g : Instruction) : ProcessProfile (frame G) where
  guard _ := True
  reads := reads g
  writes := writes g
  update x := encode (execute g (decode x))
  guard_reads _ _ _ := Iff.rfl
  update_reads := proposal_reads g
lemma profile_apply (g : Instruction) (x : (frame G).Table) :
    (profile g).apply x=encode (execute g (decode x)) := by
  classical
  funext q
  by_cases h : writes g q
  · change (if writes g q then encode (execute g (decode x)) q else x q)=_
    rw [ite_eq_left h]
  · change (if writes g q then encode (execute g (decode x)) q else x q)=_
    rw [ite_eq_right h]
    exact (proposal_frame g x q h).symm

def app (g : Instruction) (x : (frame G).Table) : EnabledApp (frame G) x := ⟨profile g,trivial⟩
lemma link_compatible (b : Bool) (e f : canvas.E) (x : (frame G).Table) (h : e ≠ f) :
    EnabledApp.Compatible (app (.link b e) x) (app (.link b f) x) := by
  classical
  refine ⟨?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro q he hf
    change q=(false,e) at he
    change q=(false,f) at hf
    exact h (Prod.mk.inj (he.symm.trans hf)).2
  · intro q hq
    change q.2=f at hq
    have hn : ¬ writes (.link b e) q := by
      intro he
      change q=(false,e) at he
      have heq := congrArg Prod.snd he
      exact h (heq.symm.trans hq)
    exact GaugeRuns.apply_of_not_mem hn
  · intro q hq
    change q.2=e at hq
    have hn : ¬ writes (.link b f) q := by
      intro he
      change q=(false,f) at he
      have heq := congrArg Prod.snd he
      exact h (hq.symm.trans heq)
    exact GaugeRuns.apply_of_not_mem hn

def kickBatch (x : (frame G).Table) : Batch (frame G) x :=
  ⟨[app (.kick false) x],by simp⟩
def linkList : List Instruction :=
  [.link false 0,.link false 1,.link false 2,.link false 3,.link false 4]
def driftBatch (x : (frame G).Table) : Batch (frame G) x where
  apps := linkList.map (fun g => app g x)
  compatible := by
    simp [linkList,link_compatible]
lemma applyAll_app (w : List Instruction) (x y : (frame G).Table) :
    applyAll (w.map (fun g => app g x)) y=encode (run w (decode y)) := by
  induction w generalizing y with
  | nil => exact (encode_decode y).symm
  | cons g w ih =>
    change applyAll (w.map (fun g => app g x)) ((profile g).apply y)=_
    rw [profile_apply,ih,decode_encode]
    rfl
lemma kickBatch_apply (x : (frame G).Table) : (kickBatch x).apply=encode (kick false (decode x)) :=
  profile_apply _ _
lemma driftBatch_apply (x : (frame G).Table) :
    (driftBatch x).apply=encode (drift false (decode x)) := by
  change applyAll (linkList.map (fun g => app g x)) x=_
  rw [applyAll_app]
  exact congrArg encode (drift_links false (decode x))

/-- No empty phases: an atomic complete-face kick, then five compatible link drifts. -/
def openingMoves (i : Fin 2) : List Instruction :=
  if i=0 then [.kick false] else linkList
def phaseBatch (i : Fin 2) (x : (frame G).Table) : Batch (frame G) x :=
  if i=0 then kickBatch x else driftBatch x
lemma phaseBatch_apply (i : Fin 2) (x : (frame G).Table) :
    (phaseBatch i x).apply=if i=0 then encode (kick false (decode x))
      else encode (drift false (decode x)) := by
  by_cases h : i=0 <;> simp [phaseBatch,h,kickBatch_apply,driftBatch_apply]
lemma phaseBatch_allows (i : Fin 2) (x : (frame G).Table) (a : EnabledApp (frame G) x)
    (ha : a ∈ (phaseBatch i x).apps) : a.profile ∈ (openingMoves i).map profile := by
  by_cases h : i=0
  · simp only [phaseBatch,ite_eq_left h,kickBatch,List.mem_singleton] at ha
    subst a
    simp [openingMoves,h,app]
  · simp only [phaseBatch,ite_eq_right h,driftBatch] at ha
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
    simp only [app,openingMoves,ite_eq_right h]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩

abbrev law (G : Type) [Group G] : LawInSteps (frame G) where
  Step := Fin 2
  moves i := (openingMoves i).map profile
  invariants := [⟨fun x => Gauss (decode x),Set.univ⟩]
  score :=
    { opens t := ⟨t%2,Nat.mod_lt _ (by decide)⟩
      allowsEmpty _ := False
      period := 2
      period_pos := by decide
      repeats t := by
        constructor
        · apply Fin.ext
          simp
        · rfl }
  moves_legal t x hx u hu _ J hJ _ := by
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hu
    simp only [List.mem_singleton] at hJ
    subst J
    have hh : Gauss (decode x) := hx _ (List.mem_singleton_self _) trivial
    simpa only [profile_apply,decode_encode,Gauss,execute_defect] using hh
lemma law_legal (t : ℕ) (x : (frame G).Table) : (law G).LegalAt t x ↔ Gauss (decode x) := by
  simp [LawInSteps.LegalAt]

def realizer (G : Type) [Group G] : (law G).DetRealizer where
  select t x := phaseBatch ((law G).score.opens t) x
  allows t x _ a ha := phaseBatch_allows _ x a ha
  keeps t x hx := by
    rw [law_legal] at hx ⊢
    rw [phaseBatch_apply]
    split_ifs <;> simpa only [decode_encode,Gauss,kick_defect,drift_defect] using hx
omit [Group G] in
lemma batch_order_free (x : (frame G).Table) (b : Batch (frame G) x)
    (l : List (EnabledApp (frame G) x)) (hl : l.Perm b.apps) : applyAll l x=b.apply := by
  change applyAll l x=applyAll b.apps x
  rw [GaugeRuns.applyAll_eq,GaugeRuns.applyAll_eq]
  exact (GaugeRuns.applyMoves_perm (hl.map EnabledApp.profile).symm x
    (GaugeRuns.pairwise_moves b)).symm
lemma realizer_wellPosed : (realizer G).WellPosed where
  total t x _ _ := by
    change (phaseBatch ((law G).score.opens t) x).apps ≠ []
    by_cases h : t%2=0 <;>
      simp [phaseBatch,Fin.ext_iff,h,kickBatch,driftBatch,linkList]
  orderFree t x _ l hl := batch_order_free x _ l hl
lemma realizer_slot (t : ℕ) (s : State G) :
    decode (((realizer G).select t (encode s)).apply)=
      if t%2=0 then kick false s else drift false s := by
  change decode (phaseBatch ((law G).score.opens t) (encode s)).apply=_
  rw [phaseBatch_apply]
  by_cases h : t%2=0 <;> simp [Fin.ext_iff,h]
lemma realizer_tick (s : State G) :
    decode (((realizer G).select 1
      (((realizer G).select 0 (encode s)).apply)).apply)=tick s := by
  simp [realizer,law,phaseBatch,kickBatch_apply,driftBatch_apply,tick_order]

def tableGauge (h : canvas.V → G) (x : (frame G).Table) : (frame G).Table :=
  encode (gauge h (decode x))
lemma profile_covariant (g : Instruction) (h : canvas.V → G) (x : (frame G).Table) :
    (profile g).apply (tableGauge h x)=tableGauge h ((profile g).apply x) := by
  simp only [profile_apply,tableGauge,decode_encode,execute_gauge]

/-! ## Non-vacuity -/
example (x : (frame G).Table) : (driftBatch x).apps.length=5 := rfl
example (x : (frame G).Table) : (kickBatch x).apps.length=1 := rfl
end Artform.Scores.ClassicalNonabelian
