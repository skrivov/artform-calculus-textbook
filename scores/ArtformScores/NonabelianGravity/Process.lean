import ArtformScores.NonabelianGravity.Dynamics
import ArtformTextbook.Ch05.GaugeRuns

/-! # NGB: overlapping face maps as honest sequential commits -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity
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
def faceMember (f : canvas.F) (e : canvas.E) : Prop :=
  if f=0 then e.val<4 else e=1 ∨ 4≤e.val
instance (f : canvas.F) (e : canvas.E) : Decidable (faceMember f e) := by
  unfold faceMember
  infer_instance
def writes (g : Instruction) : Set Position := fun q =>
  match g with
  | .face f _ => q.1=true ∧ faceMember f q.2
  | .drift _ => q.1=false
  | .link _ e => q=(false,e)
def reads (g : Instruction) : Set Position := fun q =>
  match g with
  | .face f _ => faceMember f q.2
  | .drift _ => True
  | .link _ e => q.2=e

variable {G : Type} [Group G]
lemma holonomy_reads (f : canvas.F) (U V : canvas.E → G)
    (h : ∀ e, faceMember f e → U e = V e) : holonomy U f=holonomy V f := by
  fin_cases f
  · change holonomy U 0=holonomy V 0
    rw [holonomy_left,holonomy_left,h 0 (by decide),h 1 (by decide),
      h 2 (by decide),h 3 (by decide)]
  · change holonomy U 1=holonomy V 1
    rw [holonomy_right,holonomy_right,h 1 (by decide),h 4 (by decide),
      h 5 (by decide),h 6 (by decide)]
lemma leftFactor_reads (f : canvas.F) (b : Bool) (U V : canvas.E → G)
    (h : ∀ e, faceMember f e → U e = V e) : leftFactor f b U=leftFactor f b V := by
  have hh := holonomy_reads f U V h
  simp only [leftFactor,multiplier,hh]
lemma rightFactor_reads (f : canvas.F) (b : Bool) (U V : canvas.E → G)
    (h : ∀ e, faceMember f e → U e = V e) : rightFactor f b U=rightFactor f b V := by
  have hh := holonomy_reads f U V h
  by_cases hf : f=0
  · simp [rightFactor,hf]
  · have he : faceMember f 1 := by simp [faceMember,hf]
    simp only [rightFactor,multiplier,hh,h 1 he]
lemma factors_outside (f : canvas.F) (b : Bool) (U : canvas.E → G) (e : canvas.E)
    (h : ¬ faceMember f e) : leftFactor f b U e=1 ∧ rightFactor f b U e=1 := by
  fin_cases f <;> fin_cases e <;> simp_all [faceMember,leftFactor,rightFactor]
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
  | face f b =>
    rcases q with ⟨a,e⟩
    cases a with
    | false => exact False.elim (Bool.false_ne_true hq.1)
    | true =>
      have hu : ∀ j, faceMember f j → (decode x).U j=(decode y).U j :=
        fun j hj => h (false,j) hj
      change leftFactor f b (decode x).U e*x (true,e)*rightFactor f b (decode x).U e=_
      rw [leftFactor_reads f b _ _ hu,rightFactor_reads f b _ _ hu,h (true,e) hq.2]
      rfl
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
  | face f b =>
    cases a with
    | false => rfl
    | true =>
      have he : ¬ faceMember f e := by simpa [writes] using hq
      have hh := factors_outside f b (decode x).U e he
      change leftFactor f b (decode x).U e*(decode x).P e*
        rightFactor f b (decode x).U e=(decode x).P e
      rw [hh.1,hh.2,one_mul,mul_one]
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
def tableGauge (h : canvas.V → G) (x : (frame G).Table) : (frame G).Table :=
  encode (gauge h (decode x))
lemma profile_covariant (g : Instruction) (h : canvas.V → G) (x : (frame G).Table) :
    (profile g).apply (tableGauge h x)=tableGauge h ((profile g).apply x) := by
  simp only [profile_apply,tableGauge,decode_encode,execute_gauge]
def app (g : Instruction) (x : (frame G).Table) : EnabledApp (frame G) x := ⟨profile g,trivial⟩
lemma faces_not_compatible (b c : Bool) (x : (frame G).Table) :
    ¬ EnabledApp.Compatible (app (.face 0 b) x) (app (.face 1 c) x) := by
  intro h
  exact Set.disjoint_left.mp h.1 (by simp [writes,faceMember] : writes (.face 0 b) (true,1))
    (by simp [writes,faceMember] : writes (.face 1 c) (true,1))

def phaseInstruction : Fin 3 → Instruction := ![.face 0 false,.face 1 false,.drift false]
def phaseBatch (i : Fin 3) (x : (frame G).Table) : Batch (frame G) x :=
  ⟨[app (phaseInstruction i) x],by simp⟩
lemma phaseBatch_apply (i : Fin 3) (x : (frame G).Table) :
    (phaseBatch i x).apply=encode (execute (phaseInstruction i) (decode x)) := profile_apply _ _
abbrev law (G : Type) [Group G] : LawInSteps (frame G) where
  Step := Fin 3
  moves i := [profile (phaseInstruction i)]
  invariants := [⟨fun x => Gauss (decode x),Set.univ⟩]
  score :=
    { opens t := ⟨t%3,Nat.mod_lt _ (by decide)⟩
      allowsEmpty _ := False
      period := 3
      period_pos := by decide
      repeats t := by
        constructor
        · apply Fin.ext
          simp
        · rfl }
  moves_legal t x hx u hu _ J hJ _ := by
    simp only [List.mem_singleton] at hu hJ
    subst u
    subst J
    have hh : Gauss (decode x) := hx _ (List.mem_singleton_self _) trivial
    simpa only [profile_apply,decode_encode,Gauss,execute_defect] using hh
lemma law_legal (t : ℕ) (x : (frame G).Table) : (law G).LegalAt t x ↔ Gauss (decode x) := by
  simp [LawInSteps.LegalAt]
def realizer (G : Type) [Group G] : (law G).DetRealizer where
  select t x := phaseBatch ((law G).score.opens t) x
  allows t x _ a ha := by
    simp only [phaseBatch,List.mem_singleton] at ha
    subst a
    exact List.mem_singleton_self _
  keeps t x hx := by
    rw [law_legal] at hx ⊢
    rw [phaseBatch_apply]
    simpa only [decode_encode,Gauss,execute_defect] using hx
lemma realizer_wellPosed : (realizer G).WellPosed where
  total _ _ _ _ := by simp [realizer,phaseBatch]
  orderFree _ _ _ l hl := by
    have he := List.perm_singleton.mp hl
    rw [he]
    rfl
lemma realizer_tick (s : State G) :
    decode (((realizer G).select 2 (((realizer G).select 1
      (((realizer G).select 0 (encode s)).apply)).apply)).apply)=tick s := by
  simp [realizer,law,phaseBatch_apply,phaseInstruction,tick,run,execute]

/-! ## Non-vacuity -/
example (x : (frame G).Table) : (phaseBatch 1 x).apps.length=1 := rfl
example (x : (frame G).Table) :
    ¬ EnabledApp.Compatible (app (.face 0 false) x) (app (.face 1 false) x) :=
  faces_not_compatible _ _ x
end Artform.Scores.NonabelianGravity
