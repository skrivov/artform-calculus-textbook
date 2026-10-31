import ArtformScores.NonabelianGravity.Dynamics

/-! # The admitted impulse carrier and its classical gauge-orbit dynamics -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
variable (G : Type) [Group G]
abbrev Admitted := {s : State G // Gauss s}
def gaugeSetoid : Setoid (Admitted G) where
  r x y := ∃ h, gauge h x.val=y.val
  iseqv :=
    { refl x := ⟨1,gauge_one x.val⟩
      symm := by
        rintro x y ⟨h,hh⟩
        refine ⟨h⁻¹,?_⟩
        rw [← hh,← gauge_mul]
        simpa only [inv_mul_cancel] using gauge_one x.val
      trans := by
        rintro x y z ⟨h,hh⟩ ⟨k,hk⟩
        exact ⟨k*h,by rw [gauge_mul,hh,hk]⟩ }
abbrev GaugeReduced := Quotient (gaugeSetoid G)
variable {G}
def runAdmitted (w : List Instruction) (s : Admitted G) : Admitted G :=
  ⟨run w s.val,(run_gauss w s.val).mpr s.property⟩
lemma admitted_inverse (w : List Instruction) (s : Admitted G) :
    runAdmitted (w.reverse.map inverseInstruction) (runAdmitted w s)=s := by
  apply Subtype.ext
  exact run_inverse w s.val
lemma admitted_inverse_other (w : List Instruction) (s : Admitted G) :
    runAdmitted w (runAdmitted (w.reverse.map inverseInstruction) s)=s := by
  apply Subtype.ext
  exact run_inverse_other w s.val
lemma runAdmitted_respects (w : List Instruction) (x y : Admitted G)
    (hxy : (gaugeSetoid G).r x y) :
    (gaugeSetoid G).r (runAdmitted w x) (runAdmitted w y) := by
  obtain ⟨h,hh⟩ := hxy
  refine ⟨h,?_⟩
  change gauge h (run w x.val)=run w y.val
  rw [← run_gauge,hh]
def runPhysical (w : List Instruction) : GaugeReduced G → GaugeReduced G :=
  Quotient.map (runAdmitted w) (runAdmitted_respects w)
lemma physical_inverse (w : List Instruction) (x : GaugeReduced G) :
    runPhysical (w.reverse.map inverseInstruction) (runPhysical w x)=x := by
  induction x using Quotient.inductionOn with
  | h s => exact congrArg (Quotient.mk (gaugeSetoid G)) (admitted_inverse w s)
lemma physical_inverse_other (w : List Instruction) (x : GaugeReduced G) :
    runPhysical w (runPhysical (w.reverse.map inverseInstruction) x)=x := by
  induction x using Quotient.inductionOn with
  | h s => exact congrArg (Quotient.mk (gaugeSetoid G)) (admitted_inverse_other w s)
def physicalEquiv (w : List Instruction) : GaugeReduced G ≃ GaugeReduced G where
  toFun := runPhysical w
  invFun := runPhysical (w.reverse.map inverseInstruction)
  left_inv := physical_inverse w
  right_inv := physical_inverse_other w

/-! ## Non-vacuity -/
example (U : canvas.E → G) : Gauss (State.mk U 1) := by
  unfold Gauss
  funext v
  fin_cases v <;> simp [defect,outgoing]
end Artform.Scores.NonabelianGravity
