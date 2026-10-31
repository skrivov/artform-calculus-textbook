import ArtformScores.NonabelianGravity.QuaternionForm
import ArtformScores.NonabelianGravity.Dynamics

/-! # Geometric preflight controls for the next conditional stage

The present canvas has no four-valent vertex. A nonzero unit-quaternion
impulse on an admitted face cycle changes conjugacy class under the actual
kick. Thus fixed-area shape-space preservation is an additional obligation.
This is not a reconstructed tetrahedron or a geometric-domain no-go theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity

lemma no_four_valent_vertex : ∀ v, (star v).length<4 := by decide +kernel

def cycleState {G : Type} [Group G] (a : G) : State G :=
  ⟨![a,1,1,1,1,1,1],![a,a,a,a,1,1,1]⟩
lemma cycleState_gauss {G : Type} [Group G] (a : G) : Gauss (cycleState a) := by
  unfold Gauss
  funext v
  fin_cases v <;> simp [defect,outgoing,cycleState,mul_assoc]
lemma cycleState_kick {G : Type} [Group G] (a : G) :
    (kick 0 false (cycleState a)).P 0=a*a := by
  simp [kick_P,leftFactor,rightFactor,multiplier,holonomy_left,cycleState]

def quaternionI : Maurer.Hˣ where
  val := Maurer.imaginaryI
  inv := -Maurer.imaginaryI
  val_inv := by ext <;> norm_num [Maurer.imaginaryI]
  inv_val := by ext <;> norm_num [Maurer.imaginaryI]

lemma impulse_class_changes :
    ((cycleState quaternionI).P 0 : Maurer.H).re=0 ∧
    ((kick 0 false (cycleState quaternionI)).P 0 : Maurer.H).re = -1 := by
  rw [cycleState_kick]
  norm_num [cycleState,quaternionI,Maurer.imaginaryI]

lemma unit_conjugate_re (h a : Maurer.Hˣ) :
    ((h*a*h⁻¹ : Maurer.Hˣ) : Maurer.H).re=(a : Maurer.H).re := by
  have ht := Maurer.trace_adjoint h (a : Maurer.H)
  change -(((h : Maurer.H)*(a : Maurer.H)*(↑h⁻¹ : Maurer.H)).re) = -(a : Maurer.H).re at ht
  simpa using neg_injective ht

lemma impulse_not_conjugate : ¬ ∃ h : Maurer.Hˣ,
    h*(cycleState quaternionI).P 0*h⁻¹=(kick 0 false (cycleState quaternionI)).P 0 := by
  rintro ⟨h,hh⟩
  have he := unit_conjugate_re h ((cycleState quaternionI).P 0)
  rw [hh,impulse_class_changes.1,impulse_class_changes.2] at he
  norm_num at he

lemma cycle_unit_norm : ∀ e,
    Quaternion.normSq ((cycleState quaternionI).U e : Maurer.H)=1 ∧
    Quaternion.normSq ((cycleState quaternionI).P e : Maurer.H)=1 := by
  intro e
  fin_cases e <;> norm_num [cycleState,quaternionI,Maurer.imaginaryI,Quaternion.normSq_def']

lemma kicked_cycle_unit_norm : ∀ e,
    Quaternion.normSq ((kick 0 false (cycleState quaternionI)).U e : Maurer.H)=1 ∧
    Quaternion.normSq ((kick 0 false (cycleState quaternionI)).P e : Maurer.H)=1 := by
  intro e
  constructor
  · exact (cycle_unit_norm e).1
  · fin_cases e <;>
      norm_num [kick_P,leftFactor,rightFactor,multiplier,holonomy_left,cycleState,
        quaternionI,Maurer.imaginaryI,Quaternion.normSq_def']

/-! ## Non-vacuity -/
example : Gauss (cycleState quaternionI) ∧ Gauss (kick 0 false (cycleState quaternionI)) :=
  ⟨cycleState_gauss quaternionI,by rw [Gauss,kick_defect]; exact cycleState_gauss quaternionI⟩
example : ((cycleState quaternionI).P 0 : Maurer.H) ≠ 1 := by
  intro he
  have hh := congrArg (fun q : Maurer.H => q.re) he
  norm_num [cycleState,quaternionI,Maurer.imaginaryI] at hh
end Artform.Scores.NonabelianGravity
