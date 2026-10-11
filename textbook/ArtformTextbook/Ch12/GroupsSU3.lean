import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.DotProduct
import ArtformTextbook.Ch12.Statements.Groups

/-!
# Eigenvalues and traces in `SU(3)`

For a matrix `M` of `SU(3)`: its characteristic polynomial is
`X³ - (Tr M) X² + conj(Tr M) X - 1`, since the sum of its principal `2 × 2` minors is the trace
of its adjugate `M⁻¹ = M*`; its eigenvalues have modulus one; and when its trace is `ω^j t`
with `t` real, its eigenvalues are `ω^j`, `ω^j e^{iθ}` and `ω^j e^{-iθ}` with
`1 + 2 cos θ = t` (the first claim of Proposition 12.13). Newton's identity
`Tr M² = (Tr M)² - 2 e₂(M)` gives the character of the antisymmetric square,
`(χ(M)² - χ(M²))/2 = conj χ(M)`.
-/

namespace Artform
namespace SU3
open Matrix Polynomial
open scoped ComplexOrder

/-- The sum of the principal `2 × 2` minors of a `3 × 3` matrix. -/
def e2 (M : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0 + M 1 1 * M 2 2 - M 1 2 * M 2 1

theorem charpoly_eq (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C (e2 M) * X - C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [charmatrix_apply, Matrix.diagonal_apply, Matrix.trace_fin_three, e2,
    Matrix.det_fin_three]
  simp
  ring

theorem e2_eq_trace_adjugate (M : Matrix (Fin 3) (Fin 3) ℂ) : e2 M = (adjugate M).trace := by
  rw [adjugate_fin_three, trace_fin_three]
  simp [e2]
  ring

theorem adjugate_eq_star {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ∈ specialUnitaryGroup (Fin 3) ℂ) :
    adjugate M = star M := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff] at hM
  calc adjugate M = adjugate M * (M * star M) := by rw [hM.1, Matrix.mul_one]
    _ = adjugate M * M * star M := by rw [Matrix.mul_assoc]
    _ = star M := by rw [adjugate_mul, hM.2, one_smul, Matrix.one_mul]

/-- For `M ∈ SU(3)` the sum of the principal minors is the conjugate of the trace. -/
theorem e2_eq_conj_trace {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ∈ specialUnitaryGroup (Fin 3) ℂ) :
    e2 M = (starRingEnd ℂ) M.trace := by
  rw [e2_eq_trace_adjugate, adjugate_eq_star hM, star_eq_conjTranspose, trace_conjTranspose]
  rfl

/-- Newton's identity: `Tr M² = (Tr M)² - 2 e₂(M)`. -/
theorem trace_sq (M : Matrix (Fin 3) (Fin 3) ℂ) : (M * M).trace = M.trace ^ 2 - 2 * e2 M := by
  simp [trace_fin_three, mul_apply, Fin.sum_univ_three, e2]
  ring

/-- For `M ∈ SU(3)`: `(χ(M)² - χ(M²))/2 = conj χ(M)`. -/
theorem altSq_eq {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : M ∈ specialUnitaryGroup (Fin 3) ℂ) :
    (M.trace ^ 2 - (M * M).trace) / 2 = (starRingEnd ℂ) M.trace := by
  rw [trace_sq, ← e2_eq_conj_trace hM]
  ring

/-- A root of the characteristic polynomial of a unitary matrix has modulus one. -/
theorem norm_root {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : M ∈ unitaryGroup (Fin 3) ℂ) {z : ℂ}
    (hz : M.charpoly.IsRoot z) : z * (starRingEnd ℂ) z = 1 := by
  rw [IsRoot, eval_charpoly] at hz
  obtain ⟨v, hv, hMv⟩ := (exists_mulVec_eq_zero_iff (M := scalar (Fin 3) z - M)).mpr hz
  have hMv' : M *ᵥ v = z • v := by
    rw [sub_mulVec, sub_eq_zero] at hMv
    rw [← hMv, scalar_apply]
    ext i
    simp [mulVec_diagonal]
  have hU := (mem_unitaryGroup_iff' (A := M)).mp hM
  have h1 : star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose, hU,
      one_mulVec]
  rw [hMv', star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at h1
  have hne : star v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
  have h2 : (star z * z) * (star v ⬝ᵥ v) = 1 * (star v ⬝ᵥ v) := by
    rw [one_mul, ← smul_eq_mul, h1]
  rw [mul_comm z, ← Complex.star_def]
  exact mul_right_cancel₀ hne h2


theorem prod_X_sub_C (a b c : ℂ) :
    (X - C a) * (X - C b) * (X - C c) =
      X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + b * c + c * a) * X - C (a * b * c) := by
  simp only [map_add, map_mul]
  ring

theorem roots_prod_X_sub_C (a b c : ℂ) :
    ((X - C a) * (X - C b) * (X - C c)).roots = {a, b, c} := by
  rw [roots_mul (by simp [X_sub_C_ne_zero]), roots_mul (by simp [X_sub_C_ne_zero]),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  simp [Multiset.insert_eq_cons]

/-- A matrix of `SU(3)` with the trace `ω^j t`, `t` real, has the eigenvalues `ω^j`,
`ω^j e^{iθ}` and `ω^j e^{-iθ}`, with `1 + 2 cos θ = t`. -/
theorem roots_charpoly_of_trace {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ∈ specialUnitaryGroup (Fin 3) ℂ) (j : ℕ) (t : ℝ)
    (ht : M.trace = Exact.omega ^ j * t) :
    ∃ θ : ℝ, M.charpoly.roots =
        {Exact.omega ^ j, Exact.omega ^ j * Complex.exp (θ * Complex.I),
          Exact.omega ^ j * Complex.exp (-θ * Complex.I)} ∧
      1 + 2 * Real.cos θ = t := by
  set ω := Exact.omega with hω
  have hconj : (starRingEnd ℂ) ω = ω ^ 2 := by rw [Exact.conj_omega, Exact.omega_sq]
  have h3 : ω ^ (3 * j) = 1 := by rw [pow_mul, Exact.omega_pow_three, one_pow]
  have hωj : ω ^ j * (starRingEnd ℂ) (ω ^ j) = 1 := by
    rw [map_pow, ← mul_pow, Exact.omega_mul_conj, one_pow]
  have he2 : e2 M = ω ^ (2 * j) * t := by
    rw [e2_eq_conj_trace hM, ht, map_mul, map_pow, hconj, Complex.conj_ofReal, ← pow_mul]
  have hdet : M.det = 1 := (mem_specialUnitaryGroup_iff.mp hM).2
  have hdeg : 0 < (X ^ 2 - C ((t : ℂ) - 1) * X + 1 : ℂ[X]).degree := by
    rw [show (X ^ 2 - C ((t : ℂ) - 1) * X + 1 : ℂ[X]) =
        C 1 * X ^ 2 + C (-((t : ℂ) - 1)) * X + C 1 by
      simp only [map_neg, map_one]; ring]
    rw [degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
  have hμ' : μ ^ 2 - (t - 1) * μ + 1 = 0 := by simpa using hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ'
  have hroot : M.charpoly.IsRoot (ω ^ j * μ) := by
    rw [IsRoot, charpoly_eq, ht, he2, hdet]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    have e1 : (ω ^ j * μ) ^ 3 = ω ^ (3 * j) * μ ^ 3 := by ring
    have e2' : ω ^ j * t * (ω ^ j * μ) ^ 2 = ω ^ (3 * j) * (t * μ ^ 2) := by ring
    have e3 : ω ^ (2 * j) * t * (ω ^ j * μ) = ω ^ (3 * j) * (t * μ) := by ring
    rw [e1, e2', e3, h3]
    linear_combination (μ - 1) * hμ'
  have hn := norm_root (mem_specialUnitaryGroup_iff.mp hM).1 hroot
  have hμn : μ * (starRingEnd ℂ) μ = 1 := by
    have : (ω ^ j * (starRingEnd ℂ) (ω ^ j)) * (μ * (starRingEnd ℂ) μ) = 1 := by
      rw [← hn, map_mul]; ring
    rwa [hωj, one_mul] at this
  have hnorm : ‖μ‖ = 1 := by
    have h := Complex.mul_conj μ
    rw [hμn] at h
    have h2 : Complex.normSq μ = 1 := by exact_mod_cast h.symm
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg μ]
  set θ := Complex.arg μ
  have hμe : Complex.exp (θ * Complex.I) = μ := by
    have := Complex.norm_mul_exp_arg_mul_I μ
    rwa [hnorm, Complex.ofReal_one, one_mul] at this
  have hνe : Complex.exp (-θ * Complex.I) = μ⁻¹ := by
    rw [neg_mul, Complex.exp_neg, hμe]
  have hsum : μ + μ⁻¹ = t - 1 := by
    field_simp
    linear_combination hμ'
  have hcos : ((2 * Real.cos θ : ℝ) : ℂ) = t - 1 := by
    push_cast
    rw [Complex.two_cos, hμe, hνe, hsum]
  have hmi : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
  have hs1 : ω ^ j + ω ^ j * μ + ω ^ j * μ⁻¹ = ω ^ j * t := by
    linear_combination ω ^ j * hsum
  have hs2 : ω ^ j * (ω ^ j * μ) + ω ^ j * μ * (ω ^ j * μ⁻¹) + ω ^ j * μ⁻¹ * ω ^ j =
      ω ^ (2 * j) * t := by
    linear_combination ω ^ (2 * j) * hsum + ω ^ (2 * j) * hmi
  have hs3 : ω ^ j * (ω ^ j * μ) * (ω ^ j * μ⁻¹) = 1 := by
    linear_combination h3 + ω ^ (3 * j) * hmi
  refine ⟨θ, ?_, ?_⟩
  · rw [hμe, hνe, ← roots_prod_X_sub_C, prod_X_sub_C, charpoly_eq, ht, he2, hdet, hs1, hs2,
      hs3, map_one]
  · have := Complex.ofReal_injective (hcos.trans (by push_cast; ring) :
      ((2 * Real.cos θ : ℝ) : ℂ) = ((t - 1 : ℝ) : ℂ))
    linarith


/-- A matrix of `SU(3)` with a real trace `t` has the eigenvalues `1`, `e^{iθ}` and `e^{-iθ}`,
with `1 + 2 cos θ = t`. -/
theorem roots_charpoly_of_real_trace {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ∈ specialUnitaryGroup (Fin 3) ℂ) (t : ℝ) (ht : M.trace = t) :
    ∃ θ : ℝ, M.charpoly.roots =
        {1, Complex.exp (θ * Complex.I), Complex.exp (-θ * Complex.I)} ∧
      1 + 2 * Real.cos θ = t := by
  obtain ⟨θ, h1, h2⟩ := roots_charpoly_of_trace hM 0 t (by rw [pow_zero, one_mul, ht])
  exact ⟨θ, by simpa using h1, h2⟩

/-- The character of the antisymmetric square of a colour group `G ≤ SU(3)` is the conjugate
character: `(χ(g)² - χ(g²))/2 = conj χ(g)`. -/
theorem altSqChar_colourChar (G : Subgroup (specialUnitaryGroup (Fin 3) ℂ)) (g : G) :
    altSqChar (colourChar G) g = (starRingEnd ℂ) (colourChar G g) := by
  have h := altSq_eq (g : specialUnitaryGroup (Fin 3) ℂ).2
  simp only [altSqChar, colourChar, pow_two, Subgroup.coe_mul, Submonoid.coe_mul] at h ⊢
  exact h

/-- The character of the symmetric square of a colour group `G ≤ SU(3)`:
`(χ(g)² + χ(g²))/2 = χ(g)² - conj χ(g)`. -/
theorem symSqChar_colourChar (G : Subgroup (specialUnitaryGroup (Fin 3) ℂ)) (g : G) :
    symSqChar (colourChar G) g = colourChar G g ^ 2 - (starRingEnd ℂ) (colourChar G g) := by
  have h := altSqChar_colourChar G g
  simp only [altSqChar, symSqChar] at h ⊢
  linear_combination -h

end SU3
end Artform
