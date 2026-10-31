import ArtformScores.NonabelianGravity.NonlinearSmooth
import ArtformScores.NonabelianGravity.NonlinearDifferential

/-! # Complete criticality of original spatial commutator curvature -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearDifferential
open scoped Matrix.Norms.Elementwise
open NonlinearAmbient
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {x : X}

lemma critical_sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (h : ∀ i ∈ s, Critical (f i) x) : Critical (fun q => ∑ i ∈ s, f i q) x := by
  constructor
  · exact Finset.sum_eq_zero (fun i hi => (h i hi).1)
  · simpa using! HasFDerivAt.fun_sum (fun i hi => (h i hi).2)

def MatrixCritical (A : X → Mat) (x : X) : Prop := ∀ i j, Critical (fun q => A q i j) x

lemma matrix_product_critical {A B : X → Mat}
    (hA : ∀ i j, DifferentiableAt ℝ (fun q => A q i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun q => B q i j) x)
    (ha : A x = 0) (hb : B x = 0) : MatrixCritical (fun q => A q * B q) x := by
  intro i j
  simp only [Matrix.mul_apply]
  exact critical_sum Finset.univ (fun k _ => critical_product (hA i k) (hB k j)
    (by rw [ha]; rfl) (by rw [hb]; rfl))

lemma matrix_mul_critical_left {A B : X → Mat}
    (hA : ∀ i j, DifferentiableAt ℝ (fun q => A q i j) x)
    (hB : MatrixCritical B x) : MatrixCritical (fun q => A q * B q) x := by
  intro i j
  simp only [Matrix.mul_apply]
  exact critical_sum Finset.univ (fun k _ => critical_mul_left (hA i k) (hB k j))

lemma matrix_sub_critical {A B : X → Mat} (hA : MatrixCritical A x)
    (hB : MatrixCritical B x) : MatrixCritical (fun q => A q - B q) x := by
  intro i j
  constructor
  · exact sub_eq_zero.mpr ((hA i j).1.trans (hB i j).1.symm)
  · simpa using! (hA i j).2.fun_sub (hB i j).2

lemma commutator_factor (A B : Mat) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    B⁻¹ * A⁻¹ * B * A - A⁻¹ * B⁻¹ * A * B =
      (1 + A⁻¹ * B⁻¹ * A * B) * (B⁻¹ * A⁻¹) *
        ((B - 1) * (A - 1) - (A - 1) * (B - 1)) := by
  have hAa := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have haA := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have hBb := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)
  have hbB := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)
  let H := B⁻¹ * A⁻¹ * B * A
  let J := A⁻¹ * B⁻¹ * A * B
  have hJH : J * H = 1 := by
    calc
      _ = A⁻¹ * B⁻¹ * A * (B * B⁻¹) * A⁻¹ * B * A := by dsimp [H, J]; noncomm_ring
      _ = A⁻¹ * B⁻¹ * (A * A⁻¹) * B * A := by rw [hBb]; noncomm_ring
      _ = A⁻¹ * (B⁻¹ * B) * A := by rw [hAa]; noncomm_ring
      _ = 1 := by rw [hbB, mul_one, haA]
  have hi : B⁻¹ * A⁻¹ * (A * B) = 1 := by
    calc
      _ = B⁻¹ * (A⁻¹ * A) * B := by noncomm_ring
      _ = 1 := by rw [haA, mul_one, hbB]
  have hd : B⁻¹ * A⁻¹ * ((B - 1) * (A - 1) - (A - 1) * (B - 1)) = H - 1 := by
    have hh : (B - 1) * (A - 1) - (A - 1) * (B - 1) = B * A - A * B := by noncomm_ring
    rw [hh, mul_sub, hi]
    dsimp [H]
    noncomm_ring
  calc
    _ = (1 + J) * (H - 1) := by
      change H - J = _
      noncomm_ring [hJH]
    _ = _ := by rw [← hd]; dsimp [J]; noncomm_ring

end Artform.Scores.NonabelianGravity.NonlinearDifferential
