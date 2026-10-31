import ArtformScores.NonabelianGravity.Descent

/-! # Exact preservation of stabilizers, including singular orbit types

This set equality uses the actual vertex gauge action. It is useful for
regular reduction, but does not itself construct a smooth quotient.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
variable {G : Type} [Group G]

def stabilizer (s : State G) : Set (canvas.V → G) := {h | gauge h s=s}

lemma run_injective (w : List Instruction) : Function.Injective (run (G:=G) w) :=
  Function.LeftInverse.injective (run_inverse w)

lemma run_stabilizer (w : List Instruction) (s : State G) :
    stabilizer (run w s)=stabilizer s := by
  ext h
  change gauge h (run w s)=run w s ↔ gauge h s=s
  rw [← run_gauge]
  exact ⟨fun he => run_injective w he,congrArg (run w)⟩

/-! ## Non-vacuity -/
example (a : G) : (fun _ => a) ∈ stabilizer (State.mk (1 : canvas.E → G) 1) := by
  change gauge (fun _ => a) (State.mk 1 1)=State.mk 1 1
  apply State.ext <;> funext e <;> simp [gauge]
example (U : canvas.E → G) :
    Gauss (State.mk U 1) ∧ stabilizer (tick (State.mk U 1))=stabilizer (State.mk U 1) := by
  refine ⟨?_,run_stabilizer _ _⟩
  unfold Gauss
  funext v
  fin_cases v <;> simp [defect,outgoing]
end Artform.Scores.NonabelianGravity
