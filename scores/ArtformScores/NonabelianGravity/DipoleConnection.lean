import ArtformScores.NonabelianGravity.Dipole

/-! # Independent link drift: exact intrinsic-data preservation

The underlying target twist is established AMM machinery. This module
checks its local dipole action and does not select a gravitational law.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Dipole
variable {G : Type} [Group G]
lemma gauge_one (s : State G) : gauge 1 s=s := by
  apply State.ext <;> funext e <;> simp [gauge]
lemma gauge_mul (h k : canvas.V → G) (s : State G) : gauge (h*k) s=gauge h (gauge k s) := by
  apply State.ext <;> funext e <;> simp [gauge,mul_assoc]
def driftOne (backward : Bool) (e : canvas.E) (s : State G) : State G :=
  ⟨Function.update s.U e ((if backward then (s.P e)⁻¹ else s.P e)*s.U e),s.P⟩
lemma driftOne_inverse (b : Bool) (e : canvas.E) (s : State G) :
    driftOne (!b) e (driftOne b e s)=s := by
  apply State.ext
  · funext f
    by_cases he : f=e
    · subst f
      cases b <;> simp [driftOne]
    · simp [driftOne,he]
  · rfl
lemma driftOne_outgoing (b : Bool) (e f : canvas.E) (s : State G) :
    outgoing (driftOne b e s) f=outgoing s f := by
  by_cases he : f=e
  · subst f
    cases b <;> simp [outgoing,driftOne,mul_assoc]
  · simp [outgoing,driftOne,he]
lemma driftOne_defect (b : Bool) (e : canvas.E) (s : State G) :
    defect (driftOne b e s)=defect s := by
  unfold defect
  simp_rw [driftOne_outgoing]
  rfl
lemma driftOne_gauge (b : Bool) (e : canvas.E) (h : canvas.V → G) (s : State G) :
    driftOne b e (gauge h s)=gauge h (driftOne b e s) := by
  apply State.ext
  · funext f
    by_cases he : f=e
    · subst f
      cases b <;> simp [driftOne,gauge,mul_assoc]
    · simp [driftOne,gauge,he]
  · rfl

/-! ## Non-vacuity -/
example (b : Bool) (e : canvas.E) (s : State G) : (driftOne b e s).P=s.P := rfl
end Artform.Scores.NonabelianGravity.Dipole
