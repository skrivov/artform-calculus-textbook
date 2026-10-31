import ArtformScores.NonabelianGravity.Geometry

/-! # NGB: complete oriented face kicks and link drifts -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
variable {G : Type} [Group G]

def multiplier (b : Bool) (U : canvas.E → G) (f : canvas.F) (i : Fin 4) : G :=
  if b then (holonomy U f i)⁻¹ else holonomy U f i
def leftFactor (f : canvas.F) (b : Bool) (U : canvas.E → G) : canvas.E → G :=
  if f=0 then ![multiplier b U f 0,multiplier b U f 1,
    multiplier b U f 2,multiplier b U f 3,1,1,1]
  else ![1,1,1,1,multiplier b U f 0,multiplier b U f 1,multiplier b U f 2]
def rightFactor (f : canvas.F) (b : Bool) (U : canvas.E → G) : canvas.E → G :=
  if f=0 then 1 else ![1,U 1*(multiplier b U f 3)⁻¹*(U 1)⁻¹,1,1,1,1,1]
def kick (f : canvas.F) (b : Bool) (s : State G) : State G :=
  ⟨s.U,fun e => leftFactor f b s.U e*s.P e*rightFactor f b s.U e⟩

/-- The negative occurrence of edge1 is kicked in its own traversal orientation. -/
lemma reversed_shared (b : Bool) (s : State G) :
    outgoing (kick 1 b s) 1=multiplier b s.U 1 3*outgoing s 1 := by
  simp only [outgoing,kick,rightFactor,leftFactor]
  norm_num
  group
lemma kick_inverse (f : canvas.F) (b : Bool) (s : State G) :
    kick f (!b) (kick f b s)=s := by
  apply State.ext
  · rfl
  · funext e
    fin_cases f <;> cases b <;> fin_cases e <;>
      simp [kick,leftFactor,rightFactor,multiplier,mul_assoc]
lemma kick_defect (f : canvas.F) (b : Bool) (s : State G) :
    defect (kick f b s)=defect s := by
  fin_cases f <;> cases b <;> funext v <;> fin_cases v <;>
    simp [defect,outgoing,kick,leftFactor,rightFactor,multiplier,
      holonomy_left,holonomy_right] <;> group
lemma multiplier_gauge (b : Bool) (h : canvas.V → G) (s : State G)
    (f : canvas.F) (i : Fin 4) :
    multiplier b (gauge h s).U f i=
      h (stepTarget f i)*multiplier b s.U f i*(h (stepTarget f i))⁻¹ := by
  unfold multiplier
  rw [holonomy_gauge]
  cases b <;> simp [mul_assoc]
lemma leftFactor_gauge (f : canvas.F) (b : Bool) (h : canvas.V → G)
    (s : State G) (e : canvas.E) :
    leftFactor f b (gauge h s).U e=
      h (canvas.tgt e)*leftFactor f b s.U e*(h (canvas.tgt e))⁻¹ := by
  fin_cases f <;> fin_cases e <;>
    simp [leftFactor,multiplier_gauge,stepTarget,canvas,mul_assoc]
lemma rightFactor_gauge (f : canvas.F) (b : Bool) (h : canvas.V → G)
    (s : State G) (e : canvas.E) :
    rightFactor f b (gauge h s).U e=
      h (canvas.tgt e)*rightFactor f b s.U e*(h (canvas.tgt e))⁻¹ := by
  by_cases hf : f=0
  · subst f
    simp [rightFactor]
  · have hf1 : f=1 := by fin_cases f <;> simp_all
    subst f
    by_cases he : e=1
    · subst e
      change (gauge h s).U 1*(multiplier b (gauge h s).U 1 3)⁻¹*
        ((gauge h s).U 1)⁻¹=
        h 4*(s.U 1*(multiplier b s.U 1 3)⁻¹*(s.U 1)⁻¹)*(h 4)⁻¹
      rw [multiplier_gauge]
      simp [gauge,canvas,stepTarget,mul_assoc]
    · have hr : ∀ U : canvas.E → G, rightFactor 1 b U e=1 := by
        intro U
        fin_cases e <;> simp_all [rightFactor]
      simp only [hr,mul_one,mul_inv_cancel]
lemma kick_gauge (f : canvas.F) (b : Bool) (h : canvas.V → G) (s : State G) :
    kick f b (gauge h s)=gauge h (kick f b s) := by
  apply State.ext
  · rfl
  · funext e
    change leftFactor f b (gauge h s).U e*(gauge h s).P e*
      rightFactor f b (gauge h s).U e=
      h (canvas.tgt e)*(leftFactor f b s.U e*s.P e*rightFactor f b s.U e)*
        (h (canvas.tgt e))⁻¹
    rw [leftFactor_gauge,rightFactor_gauge]
    simp [gauge,mul_assoc]
lemma left_disjoint (b c : Bool) (U : canvas.E → G) (e : canvas.E) :
    leftFactor 0 b U e=1 ∨ leftFactor 1 c U e=1 := by
  fin_cases e <;> simp [leftFactor]
lemma kick_U (f : canvas.F) (b : Bool) (s : State G) : (kick f b s).U=s.U := rfl
lemma kick_P (f : canvas.F) (b : Bool) (s : State G) (e : canvas.E) :
    (kick f b s).P e=leftFactor f b s.U e*s.P e*rightFactor f b s.U e := rfl
lemma rightFactor_zero (b : Bool) (U : canvas.E → G) (e : canvas.E) :
    rightFactor 0 b U e=1 := rfl
lemma commuting_factors (a b p q : G) (h : a = 1 ∨ b = 1) : a*(b*p*q)=b*(a*p)*q := by
  rcases h with h | h <;> subst_vars <;> simp [mul_assoc]
lemma kicks_commute (b c : Bool) (s : State G) :
    kick 0 b (kick 1 c s)=kick 1 c (kick 0 b s) := by
  apply State.ext
  · rw [kick_U,kick_U,kick_U,kick_U]
  · funext e
    simp only [kick_P,kick_U,rightFactor_zero,mul_one]
    exact commuting_factors _ _ _ _ (left_disjoint b c s.U e)

/-- Opposite traversal gives the transported neighbouring curvature on the right. -/
lemma shared_pair (s : State G) :
    (kick 1 false (kick 0 false s)).P 1=
      holonomy s.U 0 1*s.P 1*(holonomy s.U 1 2)⁻¹ := by
  simp [kick,leftFactor,rightFactor,multiplier,holonomy_left,holonomy_right]
  group

def driftFactor (b : Bool) (p : G) : G := if b then p⁻¹ else p
def drift (b : Bool) (s : State G) : State G :=
  ⟨fun e => driftFactor b (s.P e)*s.U e,s.P⟩
def driftOne (b : Bool) (e : canvas.E) (s : State G) : State G :=
  ⟨Function.update s.U e (driftFactor b (s.P e)*s.U e),s.P⟩
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

inductive Instruction
  | face : canvas.F → Bool → Instruction
  | drift : Bool → Instruction
  | link : Bool → canvas.E → Instruction
  deriving DecidableEq
def execute : Instruction → State G → State G
  | .face f b,s => kick f b s
  | .drift b,s => drift b s
  | .link b e,s => driftOne b e s
def inverseInstruction : Instruction → Instruction
  | .face f b => .face f (!b)
  | .drift b => .drift (!b)
  | .link b e => .link (!b) e
lemma inverseInstruction_involutive (g : Instruction) :
    inverseInstruction (inverseInstruction g)=g := by cases g <;> simp [inverseInstruction]
lemma execute_inverse (g : Instruction) (s : State G) :
    execute (inverseInstruction g) (execute g s)=s := by
  cases g with
  | face f b => exact kick_inverse f b s
  | drift b => exact drift_inverse b s
  | link b e => exact driftOne_inverse b e s
lemma execute_defect (g : Instruction) (s : State G) : defect (execute g s)=defect s := by
  cases g with
  | face f b => exact kick_defect f b s
  | drift b => exact drift_defect b s
  | link b e => exact driftOne_defect b e s
lemma execute_gauge (g : Instruction) (h : canvas.V → G) (s : State G) :
    execute g (gauge h s)=gauge h (execute g s) := by
  cases g with
  | face f b => exact kick_gauge f b h s
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
def tick (s : State G) : State G := run [.face 0 false,.face 1 false,.drift false] s

/-! ## Non-vacuity -/
example (s : State G) : Gauss s → Gauss (tick s) := (run_gauss _ s).mpr
example (s : State G) : kick 0 true (kick 0 false s)=s := kick_inverse 0 false s
end Artform.Scores.NonabelianGravity
