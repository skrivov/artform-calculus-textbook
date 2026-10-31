import ArtformScores.NonabelianGravity.NonlinearAmbient
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Directional source derivatives and critical products -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearDifferential
open Filter Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {x v : X} {f g : X → ℝ}

noncomputable def directional (v : X) (f : X → ℝ) (x : X) : ℝ := fderiv ℝ f x v

lemma directional_hasDerivAt (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (directional v f x) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  simpa [directional] using! hf'.comp_hasDerivAt 0 hl

lemma partial_mul (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    directional v (fun q => f q * g q) x = directional v f x * g x + f x * directional v g x := by
  have h := (directional_hasDerivAt (v := v) hf).mul (directional_hasDerivAt (v := v) hg)
  have h' := directional_hasDerivAt (v := v) (hf.fun_mul hg)
  simpa using! h'.unique h

lemma partial_zero_of_line (hf : DifferentiableAt ℝ f x)
    (h : ∀ t : ℝ, f (x + t • v) = f x) : directional v f x = 0 := by
  have hd := directional_hasDerivAt (v := v) hf
  have he : (fun t : ℝ => f (x + t • v)) = fun _ => f x := funext h
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (f x))

lemma smooth_partial {n : WithTop ℕ∞} (hf : ContDiffAt ℝ (n + 1) f x) :
    ContDiffAt ℝ n (directional v f) x := by
  have hd := hf.fderiv_right_succ
  unfold directional
  fun_prop

/-- Value and complete first derivative vanish, with no direction restriction. -/
def Critical (f : X → ℝ) (x : X) : Prop := f x = 0 ∧ HasFDerivAt f (0 : X →L[ℝ] ℝ) x

lemma critical_product (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : f x = 0) (hg0 : g x = 0) : Critical (fun q => f q * g q) x := by
  refine ⟨by change f x * g x = 0; rw [hf0, hg0]; ring, ?_⟩
  have h := hf.hasFDerivAt.fun_mul hg.hasFDerivAt
  simpa only [hf0, hg0, zero_smul, add_zero] using! h

lemma critical_mul_left (hf : DifferentiableAt ℝ f x) (hg : Critical g x) :
    Critical (fun q => f q * g q) x := by
  refine ⟨by change f x * g x = 0; rw [hg.1]; ring, ?_⟩
  simpa only [hg.1, zero_smul, smul_zero, zero_add] using! hf.hasFDerivAt.fun_mul hg.2

lemma critical_add (hf : Critical f x) (hg : Critical g x) : Critical (fun q => f q + g q) x := by
  refine ⟨?_, ?_⟩
  · change f x + g x = 0
    rw [hf.1, hg.1, add_zero]
  · simpa using! hf.2.fun_add hg.2

end Artform.Scores.NonabelianGravity.NonlinearDifferential
