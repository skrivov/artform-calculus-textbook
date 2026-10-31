import ArtformScores.NonabelianGravity.Double

/-! # NGB: oriented neighbour cancellation and the small-step scaling obligation -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Scaling

@[ext] structure Jet3 (R : Type*) where
  c0 : R
  c1 : R
  c2 : R
  c3 : R
  deriving DecidableEq
def times {R : Type*} [Ring R] (a b : Jet3 R) : Jet3 R :=
  ⟨a.c0*b.c0,a.c0*b.c1+a.c1*b.c0,
   a.c0*b.c2+a.c1*b.c1+a.c2*b.c0,
   a.c0*b.c3+a.c1*b.c2+a.c2*b.c1+a.c3*b.c0⟩
def field {R : Type*} [Ring R] (E J : R) : Jet3 R := ⟨1,0,E,J⟩
def link {R : Type*} [Ring R] (A B C : R) : Jet3 R := ⟨1,A,B,C⟩
def inverseField {R : Type*} [Ring R] (F K : R) : Jet3 R := ⟨1,0,-F,-K⟩
lemma paired_kick {R : Type*} [Ring R] (E J FL FR KL KR : R) :
    times (times (field FL KL) (field E J)) (inverseField FR KR)=
      field (FL+E-FR) (KL+J-KR) := by
  ext <;> simp only [times,field,inverseField,one_mul,mul_one,zero_mul,mul_zero,add_zero]
    <;> noncomm_ring
lemma common_leading_cancels {R : Type*} [Ring R] (E J F KL KR : R) :
    times (times (field F KL) (field E J)) (inverseField F KR)=field E (KL+J-KR) := by
  rw [paired_kick]
  congr 1
  noncomm_ring
lemma drift_scale {R : Type*} [Ring R] (E J A B C : R) :
    times (field E J) (link A B C)=link A (B+E) (C+E*A+J) := by
  ext <;> simp [times,field,link]

variable {R : Type*} [NormedDivisionRing R]
/-- A pointwise norm estimate, conditional on unit norms and actual neighbour matching. -/
lemma shared_error (L K P : R) (hK : ‖K‖ = 1) (hP : ‖P‖ = 1) :
    ‖L*P*K⁻¹-P‖ ≤ ‖L-K‖+2*‖K-1‖*‖P-1‖ := by
  have hne : K ≠ 0 := by
    intro he
    simp [he] at hK
  have hi : ‖K⁻¹‖=1 := by simp [norm_inv,hK]
  have hd : L*P*K⁻¹-P=((L-K)*P+(K*P-P*K))*K⁻¹ := by
    calc
      L*P*K⁻¹-P=(L*P-P*K)*K⁻¹ := by
        simp only [sub_mul,mul_assoc,mul_inv_cancel₀ hne,mul_one]
      _ = ((L-K)*P+(K*P-P*K))*K⁻¹ := by congr 1; noncomm_ring
  have hc : K*P-P*K=(K-1)*(P-1)-(P-1)*(K-1) := by noncomm_ring
  have hb : ‖K*P-P*K‖ ≤ 2*‖K-1‖*‖P-1‖ := by
    rw [hc]
    calc
      _ ≤ ‖(K-1)*(P-1)‖+‖(P-1)*(K-1)‖ := norm_sub_le _ _
      _ = 2*‖K-1‖*‖P-1‖ := by rw [norm_mul,norm_mul]; ring
  calc
    _ = ‖(L-K)*P+(K*P-P*K)‖ := by rw [hd,norm_mul,hi,mul_one]
    _ ≤ ‖(L-K)*P‖+‖K*P-P*K‖ := norm_add_le _ _
    _ ≤ ‖L-K‖+2*‖K-1‖*‖P-1‖ := by rw [norm_mul,hP,mul_one]; exact add_le_add le_rfl hb
lemma shared_budget (L K P : R) (hK : ‖K‖ = 1) (hP : ‖P‖ = 1)
    (h CF CK CP : ℝ) (_hh : 0 ≤ h) (hCK : 0 ≤ CK) (_hCP : 0 ≤ CP)
    (hf : ‖L - K‖ ≤ CF * h ^ 3) (hk : ‖K - 1‖ ≤ CK * h ^ 2) (hp : ‖P - 1‖ ≤ CP * h ^ 2) :
    ‖L*P*K⁻¹-P‖ ≤ CF*h ^ 3+2*CK*CP*h ^ 4 := by
  have hb := shared_error L K P hK hP
  have hn : ‖K-1‖*‖P-1‖ ≤ (CK*h ^ 2)*(CP*h ^ 2) :=
    mul_le_mul hk hp (norm_nonneg _) (mul_nonneg hCK (sq_nonneg h))
  nlinarith
lemma rescaled_budget (L K P : R) (hK : ‖K‖ = 1) (hP : ‖P‖ = 1)
    (h CF CK CP : ℝ) (hh : 0 < h) (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hf : ‖L - K‖ ≤ CF * h ^ 3) (hk : ‖K - 1‖ ≤ CK * h ^ 2)
    (hp : ‖P - 1‖ ≤ CP * h ^ 2) :
    ‖L*P*K⁻¹-P‖ / h ^ 2 ≤ CF*h+2*CK*CP*h ^ 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  calc
    _ ≤ CF*h ^ 3+2*CK*CP*h ^ 4 := shared_budget L K P hK hP h CF CK CP
      (le_of_lt hh) hCK hCP hf hk hp
    _ = (CF*h+2*CK*CP*h ^ 2)*h ^ 2 := by ring

/-! ## Non-vacuity -/
example : times (times (field (2:ℚ) 3) (field 5 7)) (inverseField 2 11)=field 5 (-1) := by
  decide +kernel
example : ‖(1:ℝ)*1*1⁻¹-1‖ ≤ ‖(1:ℝ)-1‖+2*‖(1:ℝ)-1‖*‖(1:ℝ)-1‖ :=
  shared_error 1 1 1 (by simp) (by simp)
end Artform.Scores.NonabelianGravity.Scaling
