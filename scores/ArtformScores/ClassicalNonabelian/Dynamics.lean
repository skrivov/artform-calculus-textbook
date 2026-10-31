import ArtformScores.ClassicalNonabelian.Geometry

/-! # Exact target-based impulse shears and fixed score words -/
set_option autoImplicit false
namespace Artform.Scores.ClassicalNonabelian
variable {G : Type} [Group G]

def multiplier (backward : Bool) (U : canvas.E → G) (e : canvas.E) : G :=
  if backward then (holonomy U e)⁻¹ else holonomy U e
def kick (backward : Bool) (s : State G) : State G :=
  ⟨s.U,fun e => multiplier backward s.U e*s.P e⟩
def driftFactor (backward : Bool) (p : G) : G := if backward then p⁻¹ else p
def drift (backward : Bool) (s : State G) : State G :=
  ⟨fun e => driftFactor backward (s.P e)*s.U e,s.P⟩
def driftOne (backward : Bool) (e : canvas.E) (s : State G) : State G :=
  ⟨Function.update s.U e (driftFactor backward (s.P e)*s.U e),s.P⟩

lemma multiplier_spectator (b : Bool) (U : canvas.E → G) : multiplier b U 4=1 := by
  simp [multiplier,holonomy_spectator]
lemma multiplier_transport (b : Bool) (U : canvas.E → G) (e : canvas.E) :
    (U e)⁻¹*multiplier b U e*U e=multiplier b U (previous e) := by
  cases b with
  | false => exact holonomy_transport U e
  | true =>
    simpa only [multiplier,Bool.true_eq,ite_true,mul_inv_rev,inv_inv,mul_assoc] using
      congrArg Inv.inv (holonomy_transport U e)
lemma kick_inverse (b : Bool) (s : State G) : kick (!b) (kick b s)=s := by
  apply State.ext
  · rfl
  · funext e
    cases b <;> simp [kick,multiplier]
lemma drift_inverse (b : Bool) (s : State G) : drift (!b) (drift b s)=s := by
  apply State.ext
  · funext e
    cases b <;> simp [drift,driftFactor]
  · rfl
lemma driftOne_inverse (b : Bool) (e : canvas.E) (s : State G) :
    driftOne (!b) e (driftOne b e s)=s := by
  apply State.ext
  · funext f
    by_cases h : f=e
    · subst f
      cases b <;> simp [driftOne,driftFactor]
    · simp [driftOne,h]
  · rfl

lemma kick_defect (b : Bool) (s : State G) : defect (kick b s)=defect s := by
  cases b <;> funext v <;> fin_cases v <;>
    simp [defect,outgoing,kick,multiplier,holonomy_word] <;> group
lemma outgoing_drift (b : Bool) (s : State G) (e : canvas.E) :
    outgoing (drift b s) e=outgoing s e := by
  cases b <;> simp [outgoing,drift,driftFactor,mul_assoc]
lemma drift_defect (b : Bool) (s : State G) : defect (drift b s)=defect s := by
  unfold defect
  simp_rw [outgoing_drift]
  rfl
lemma outgoing_driftOne (b : Bool) (e f : canvas.E) (s : State G) :
    outgoing (driftOne b e s) f=outgoing s f := by
  by_cases h : f=e
  · subst f
    cases b <;> simp [outgoing,driftOne,driftFactor,mul_assoc]
  · simp [outgoing,driftOne,h]
lemma driftOne_defect (b : Bool) (e : canvas.E) (s : State G) :
    defect (driftOne b e s)=defect s := by
  unfold defect
  simp_rw [outgoing_driftOne]
  rfl
lemma multiplier_gauge (b : Bool) (h : canvas.V → G) (s : State G) (e : canvas.E) :
    multiplier b (gauge h s).U e=
      h (canvas.tgt e)*multiplier b s.U e*(h (canvas.tgt e))⁻¹ := by
  unfold multiplier
  rw [holonomy_gauge]
  cases b <;> simp [mul_assoc]
lemma kick_gauge (b : Bool) (h : canvas.V → G) (s : State G) :
    kick b (gauge h s)=gauge h (kick b s) := by
  apply State.ext
  · rfl
  · funext e
    change multiplier b (gauge h s).U e*(gauge h s).P e=
      h (canvas.tgt e)*(multiplier b s.U e*s.P e)*(h (canvas.tgt e))⁻¹
    rw [multiplier_gauge]
    simp [gauge,mul_assoc]
lemma drift_gauge (b : Bool) (h : canvas.V → G) (s : State G) :
    drift b (gauge h s)=gauge h (drift b s) := by
  apply State.ext
  · funext e
    cases b <;> simp [drift,driftFactor,gauge,mul_assoc]
  · rfl
lemma driftOne_gauge (b : Bool) (e : canvas.E) (h : canvas.V → G) (s : State G) :
    driftOne b e (gauge h s)=gauge h (driftOne b e s) := by
  apply State.ext
  · funext f
    by_cases hf : f=e
    · subst f
      cases b <;> simp [driftOne,driftFactor,gauge,mul_assoc]
    · simp [driftOne,gauge,hf]
  · rfl

lemma driftOne_commute (b c : Bool) (e f : canvas.E) (s : State G) (h : e ≠ f) :
    driftOne b e (driftOne c f s)=driftOne c f (driftOne b e s) := by
  apply State.ext
  · funext j
    by_cases he : j=e <;> by_cases hf : j=f <;>
      simp_all [driftOne,Function.update_apply]
  · rfl

inductive Instruction
  | kick : Bool → Instruction
  | drift : Bool → Instruction
  | link : Bool → canvas.E → Instruction
  deriving DecidableEq

def execute : Instruction → State G → State G
  | .kick b,s => kick b s
  | .drift b,s => drift b s
  | .link b e,s => driftOne b e s
def inverseInstruction : Instruction → Instruction
  | .kick b => .kick (!b)
  | .drift b => .drift (!b)
  | .link b e => .link (!b) e
lemma inverseInstruction_involutive (g : Instruction) :
    inverseInstruction (inverseInstruction g)=g := by cases g <;> simp [inverseInstruction]
lemma execute_inverse (g : Instruction) (s : State G) :
    execute (inverseInstruction g) (execute g s)=s := by
  cases g with
  | kick b => exact kick_inverse b s
  | drift b => exact drift_inverse b s
  | link b e => exact driftOne_inverse b e s
lemma execute_defect (g : Instruction) (s : State G) : defect (execute g s)=defect s := by
  cases g with
  | kick b => exact kick_defect b s
  | drift b => exact drift_defect b s
  | link b e => exact driftOne_defect b e s
lemma execute_gauge (g : Instruction) (h : canvas.V → G) (s : State G) :
    execute g (gauge h s)=gauge h (execute g s) := by
  cases g with
  | kick b => exact kick_gauge b h s
  | drift b => exact drift_gauge b h s
  | link b e => exact driftOne_gauge b e h s

def run : List Instruction → State G → State G
  | [],s => s
  | g::w,s => run w (execute g s)
lemma run_append (u v : List Instruction) (s : State G) : run (u++v) s=run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons g u ih => exact ih (execute g s)
lemma run_inverse (w : List Instruction) (s : State G) :
    run (w.reverse.map inverseInstruction) (run w s)=s := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,run_append,run]
    rw [ih,execute_inverse]
lemma run_inverse_other (w : List Instruction) (s : State G) :
    run w (run (w.reverse.map inverseInstruction) s)=s := by
  have hw : (w.reverse.map inverseInstruction).reverse.map inverseInstruction=w := by
    simp [List.map_map,Function.comp_def,inverseInstruction_involutive]
  simpa only [hw] using run_inverse (w.reverse.map inverseInstruction) s
lemma run_defect (w : List Instruction) (s : State G) : defect (run w s)=defect s := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih => rw [run,ih,execute_defect]
lemma run_gauge (w : List Instruction) (h : canvas.V → G) (s : State G) :
    run w (gauge h s)=gauge h (run w s) := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih => rw [run,execute_gauge,ih,run]
lemma run_gauss (w : List Instruction) (s : State G) : Gauss (run w s) ↔ Gauss s := by
  simp only [Gauss,run_defect]

lemma drift_links (b : Bool) (s : State G) :
    run [.link b 0,.link b 1,.link b 2,.link b 3,.link b 4] s=drift b s := by
  apply State.ext
  · funext e
    fin_cases e <;> simp [run,execute,drift,driftOne]
  · rfl

def tick (s : State G) : State G := run [.kick false,.drift false] s
lemma tick_order (s : State G) : tick s=drift false (kick false s) := rfl
lemma tick_formula (s : State G) (e : canvas.E) :
    (tick s).P e=holonomy s.U e*s.P e ∧
    (tick s).U e=(tick s).P e*s.U e := by
  exact ⟨rfl,rfl⟩

/-! ## Non-vacuity -/
example (s : State G) : Gauss s → Gauss (tick s) := (run_gauss _ s).mpr
example (s : State G) : kick true (kick false s)=s := kick_inverse false s
end Artform.Scores.ClassicalNonabelian
