import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import ArtformTextbook.Exact.QPhi

/-!
# Exact arithmetic in `ℤ[ω, φ]`

The numbers `a + b φ + c ω + d φ ω`, with `a b c d : ℤ`, `φ` the golden ratio
(`φ² = φ + 1`) and `ω = e^{2πi/3}` (`ω² = -1 - ω`), written as quadruples of integers so
that the kernel computes with them, together with `3 × 3` matrices over them.

`ZOP.toComplex` sends a quadruple to the complex number it stands for. It respects sums and
products, and it is injective, because `ω` is not real and `φ` is irrational; so `ZOP` is a
commutative ring and `toComplex` a ring homomorphism, and an identity checked by `decide` on
the exact side holds for the complex numbers. Complex conjugation is `ZOP.conj`.
-/

namespace Artform.Exact

open Complex Real

/-- `ω = e^{2πi/3}`, a primitive cube root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * π * I / 3)

/-- `ω = -1/2 + (√3/2) i`. -/
theorem omega_eq : omega = ⟨-1 / 2, √3 / 2⟩ := by
  have h : 2 * (π : ℂ) * I / 3 = ((2 * π / 3 : ℝ) : ℂ) * I := by push_cast; ring
  have hc : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hs : Real.sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [omega, h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, hc, hs]
  apply Complex.ext <;> simp

theorem omega_re : omega.re = -1 / 2 := by rw [omega_eq]

theorem omega_im : omega.im = √3 / 2 := by rw [omega_eq]

/-- `ω² + ω + 1 = 0`. -/
theorem omega_sq_add : omega ^ 2 + omega + 1 = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [sq, omega_re, omega_im] <;> nlinarith [h3]

/-- `ω² = -1 - ω`. -/
theorem omega_sq : omega ^ 2 = -1 - omega := by linear_combination omega_sq_add

/-- `ω³ = 1`. -/
theorem omega_pow_three : omega ^ 3 = 1 := by linear_combination (omega - 1) * omega_sq_add

/-- `ω̄ = -1 - ω = ω²`. -/
theorem conj_omega : (starRingEnd ℂ) omega = -1 - omega := by
  apply Complex.ext
  · simp [omega_re]
    norm_num
  · simp [omega_im]

/-- `ω ω̄ = 1`. -/
theorem omega_mul_conj : omega * (starRingEnd ℂ) omega = 1 := by
  rw [conj_omega]; linear_combination -omega_sq_add

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have := omega_mul_conj
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- `ω^n` depends on `n` modulo three. -/
theorem omega_pow_mod (n : ℕ) : omega ^ (n % 3) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, omega_pow_three, one_pow, one_mul]

/-- The number `a + b φ + c ω + d φ ω` of `ℤ[ω, φ]`. -/
@[ext]
structure ZOP where
  /-- The coefficient of `1`. -/
  a : ℤ
  /-- The coefficient of `φ`. -/
  b : ℤ
  /-- The coefficient of `ω`. -/
  c : ℤ
  /-- The coefficient of `φ ω`. -/
  d : ℤ
  deriving DecidableEq

namespace ZOP

instance : Zero ZOP := ⟨⟨0, 0, 0, 0⟩⟩
instance : One ZOP := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add ZOP := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg ZOP := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub ZOP := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩

/-- With `x = p + q ω` and `y = r + s ω`, `p, q, r, s ∈ ℤ[φ]`:
`x y = (p r - q s) + (p s + q r - q s) ω`, since `ω² = -1 - ω`, and
`(a + b φ)(e + f φ) = (a e + b f) + (a f + b e + b f) φ`, since `φ² = φ + 1`. -/
instance : Mul ZOP :=
  ⟨fun x y =>
    ⟨x.a * y.a + x.b * y.b - x.c * y.c - x.d * y.d,
     x.a * y.b + x.b * y.a + x.b * y.b - x.c * y.d - x.d * y.c - x.d * y.d,
     x.a * y.c + x.b * y.d + x.c * y.a + x.d * y.b - x.c * y.c - x.d * y.d,
     x.a * y.d + x.b * y.c + x.b * y.d + x.c * y.b + x.d * y.a + x.d * y.b
       - x.c * y.d - x.d * y.c - x.d * y.d⟩⟩

instance : SMul ℕ ZOP := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : SMul ℤ ZOP := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : NatCast ZOP := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast ZOP := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : Pow ZOP ℕ := ⟨fun x n => npowRec n x⟩

/-- The complex number `a + b φ + c ω + d φ ω`. -/
noncomputable def toComplex (x : ZOP) : ℂ :=
  x.a + x.b * (goldenRatio : ℂ) + x.c * omega + x.d * (goldenRatio : ℂ) * omega

theorem phi_sq : (goldenRatio : ℂ) ^ 2 = goldenRatio + 1 := by
  exact_mod_cast goldenRatio_sq

theorem toComplex_zero : toComplex 0 = 0 := by
  simp [toComplex, show (0 : ZOP) = ⟨0, 0, 0, 0⟩ from rfl]

theorem toComplex_one : toComplex 1 = 1 := by
  simp [toComplex, show (1 : ZOP) = ⟨1, 0, 0, 0⟩ from rfl]

theorem toComplex_add (x y : ZOP) : toComplex (x + y) = toComplex x + toComplex y := by
  simp only [toComplex, show x + y = ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩ from rfl]
  push_cast
  ring

theorem toComplex_neg (x : ZOP) : toComplex (-x) = -toComplex x := by
  simp only [toComplex, show -x = ⟨-x.a, -x.b, -x.c, -x.d⟩ from rfl]
  push_cast
  ring

theorem toComplex_sub (x y : ZOP) : toComplex (x - y) = toComplex x - toComplex y := by
  simp only [toComplex, show x - y = ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩ from rfl]
  push_cast
  ring

theorem toComplex_mul (x y : ZOP) : toComplex (x * y) = toComplex x * toComplex y := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨e, f, g, h⟩ := y
  rw [show (⟨a, b, c, d⟩ : ZOP) * ⟨e, f, g, h⟩ =
    ⟨a * e + b * f - c * g - d * h, a * f + b * e + b * f - c * h - d * g - d * h,
     a * g + b * h + c * e + d * f - c * g - d * h,
     a * h + b * g + b * h + c * f + d * e + d * f - c * h - d * g - d * h⟩ from rfl]
  simp only [toComplex]
  have hp := phi_sq
  generalize (goldenRatio : ℂ) = p at hp ⊢
  push_cast
  linear_combination
    (-((c : ℂ) + d * p) * (g + h * p)) * omega_sq_add +
    (-((b : ℂ) * f - d * h + (b * h + d * f - d * h) * omega)) * hp

theorem toComplex_nsmul (n : ℕ) (x : ZOP) : toComplex (n • x) = n • toComplex x := by
  simp only [toComplex, show n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩ from rfl,
    nsmul_eq_mul]
  push_cast
  ring

theorem toComplex_zsmul (n : ℤ) (x : ZOP) : toComplex (n • x) = n • toComplex x := by
  simp only [toComplex, show n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩ from rfl,
    zsmul_eq_mul]
  push_cast
  ring

theorem toComplex_pow (x : ZOP) (n : ℕ) : toComplex (x ^ n) = toComplex x ^ n := by
  induction n with
  | zero => exact toComplex_one
  | succ n ih =>
    rw [show x ^ (n + 1) = x ^ n * x from rfl, toComplex_mul, ih, pow_succ]

theorem toComplex_natCast (n : ℕ) : toComplex n = n := by
  simp [toComplex, show (n : ZOP) = ⟨n, 0, 0, 0⟩ from rfl]

theorem toComplex_intCast (n : ℤ) : toComplex n = n := by
  simp [toComplex, show (n : ZOP) = ⟨n, 0, 0, 0⟩ from rfl]

theorem toComplex_im (x : ZOP) : (toComplex x).im = (x.c + x.d * goldenRatio) * (√3 / 2) := by
  simp [toComplex, omega_im, omega_re]
  ring

theorem toComplex_re (x : ZOP) :
    (toComplex x).re = x.a + x.b * goldenRatio - (x.c + x.d * goldenRatio) / 2 := by
  simp [toComplex, omega_im, omega_re]
  ring

/-- `toComplex` is injective: `ω` is not real, and `φ` is irrational. -/
theorem toComplex_injective : Function.Injective toComplex := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [toComplex_im, toComplex_im] at him
  rw [toComplex_re, toComplex_re] at hre
  have h3 : (0 : ℝ) < √3 / 2 := by positivity
  have hcd : (c : ℝ) + d * goldenRatio = c' + d' * goldenRatio :=
    mul_right_cancel₀ h3.ne' him
  have hcd' : ZPhi.mk c d = ZPhi.mk c' d' := ZPhi.toReal_injective hcd
  have hab : ZPhi.mk a b = ZPhi.mk a' b' := by
    apply ZPhi.toReal_injective
    simp only [ZPhi.toReal]
    linear_combination hre + hcd / 2
  simp only [ZPhi.mk.injEq] at hcd' hab
  obtain ⟨rfl, rfl⟩ := hcd'
  obtain ⟨rfl, rfl⟩ := hab
  rfl

theorem toComplex_inj {x y : ZOP} : toComplex x = toComplex y ↔ x = y :=
  toComplex_injective.eq_iff

/-- `ℤ[ω, φ]` is a commutative ring, as a subring of `ℂ`. -/
noncomputable instance : CommRing ZOP :=
  Function.Injective.commRing toComplex toComplex_injective toComplex_zero toComplex_one
    toComplex_add toComplex_mul toComplex_neg toComplex_sub toComplex_nsmul toComplex_zsmul
    toComplex_pow toComplex_natCast toComplex_intCast

/-- `toComplex` as a ring homomorphism. -/
noncomputable def toComplexHom : ZOP →+* ℂ where
  toFun := toComplex
  map_one' := toComplex_one
  map_mul' := toComplex_mul
  map_zero' := toComplex_zero
  map_add' := toComplex_add

@[simp] theorem toComplexHom_apply (x : ZOP) : toComplexHom x = toComplex x := rfl

/-- The complex conjugate: `ω̄ = -1 - ω`, so
`conj (a + b φ + c ω + d φ ω) = (a - c) + (b - d) φ - c ω - d φ ω`. -/
def conj (x : ZOP) : ZOP := ⟨x.a - x.c, x.b - x.d, -x.c, -x.d⟩

theorem toComplex_conj (x : ZOP) : toComplex (conj x) = (starRingEnd ℂ) (toComplex x) := by
  simp only [toComplex, conj, map_add, map_mul, map_intCast, Complex.conj_ofReal, conj_omega]
  push_cast
  ring

/-- The number `ω`. -/
def omegaZ : ZOP := ⟨0, 0, 1, 0⟩

theorem toComplex_omegaZ : toComplex omegaZ = omega := by
  simp [toComplex, omegaZ]

/-- `ω^j` for `j ∈ {0, 1, 2}`: `1`, `ω` and `ω² = -1 - ω`. -/
def omegaPow : Fin 3 → ZOP := ![⟨1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩]

theorem toComplex_omegaPow (j : Fin 3) : toComplex (omegaPow j) = omega ^ (j : ℕ) := by
  fin_cases j
  · simp [toComplex, omegaPow]
  · simp [toComplex, omegaPow]
  · simp [toComplex, omegaPow, omega_sq]
    ring

/-- The number `a + b φ` of `ℤ[φ]` in `ℤ[ω, φ]`. -/
def ofZPhi (x : ZPhi) : ZOP := ⟨x.re, x.im, 0, 0⟩

theorem toComplex_ofZPhi (x : ZPhi) : toComplex (ofZPhi x) = (x.toReal : ℂ) := by
  simp [toComplex, ofZPhi, ZPhi.toReal]

end ZOP

/-- A `3 × 3` matrix over `ℤ[ω, φ]`, given by its nine entries. -/
@[ext]
structure M3Z where
  /-- Entry `(0, 0)`. -/ e00 : ZOP
  /-- Entry `(0, 1)`. -/ e01 : ZOP
  /-- Entry `(0, 2)`. -/ e02 : ZOP
  /-- Entry `(1, 0)`. -/ e10 : ZOP
  /-- Entry `(1, 1)`. -/ e11 : ZOP
  /-- Entry `(1, 2)`. -/ e12 : ZOP
  /-- Entry `(2, 0)`. -/ e20 : ZOP
  /-- Entry `(2, 1)`. -/ e21 : ZOP
  /-- Entry `(2, 2)`. -/ e22 : ZOP
  deriving DecidableEq

namespace M3Z

open ZOP

/-- The product of two matrices. -/
def mul (A B : M3Z) : M3Z :=
  ⟨A.e00 * B.e00 + A.e01 * B.e10 + A.e02 * B.e20,
   A.e00 * B.e01 + A.e01 * B.e11 + A.e02 * B.e21,
   A.e00 * B.e02 + A.e01 * B.e12 + A.e02 * B.e22,
   A.e10 * B.e00 + A.e11 * B.e10 + A.e12 * B.e20,
   A.e10 * B.e01 + A.e11 * B.e11 + A.e12 * B.e21,
   A.e10 * B.e02 + A.e11 * B.e12 + A.e12 * B.e22,
   A.e20 * B.e00 + A.e21 * B.e10 + A.e22 * B.e20,
   A.e20 * B.e01 + A.e21 * B.e11 + A.e22 * B.e21,
   A.e20 * B.e02 + A.e21 * B.e12 + A.e22 * B.e22⟩

/-- A scalar multiple. -/
def smul (s : ZOP) (A : M3Z) : M3Z :=
  ⟨s * A.e00, s * A.e01, s * A.e02, s * A.e10, s * A.e11, s * A.e12,
   s * A.e20, s * A.e21, s * A.e22⟩

/-- The scalar matrix `s · 1`. -/
def scalar (s : ZOP) : M3Z := ⟨s, 0, 0, 0, s, 0, 0, 0, s⟩

/-- The transpose. -/
def transpose (A : M3Z) : M3Z :=
  ⟨A.e00, A.e10, A.e20, A.e01, A.e11, A.e21, A.e02, A.e12, A.e22⟩

/-- The conjugate transpose. -/
def star (A : M3Z) : M3Z :=
  ⟨conj A.e00, conj A.e10, conj A.e20, conj A.e01, conj A.e11, conj A.e21,
   conj A.e02, conj A.e12, conj A.e22⟩

/-- The trace. -/
def trace (A : M3Z) : ZOP := A.e00 + A.e11 + A.e22

/-- The determinant. -/
def det (A : M3Z) : ZOP :=
  A.e00 * A.e11 * A.e22 - A.e00 * A.e12 * A.e21 - A.e01 * A.e10 * A.e22 +
    A.e01 * A.e12 * A.e20 + A.e02 * A.e10 * A.e21 - A.e02 * A.e11 * A.e20

/-- The complex matrix that `A` stands for. -/
noncomputable def toMat (A : M3Z) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![toComplex A.e00, toComplex A.e01, toComplex A.e02;
     toComplex A.e10, toComplex A.e11, toComplex A.e12;
     toComplex A.e20, toComplex A.e21, toComplex A.e22]

theorem toMat_mul (A B : M3Z) : toMat (mul A B) = toMat A * toMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mul, Matrix.mul_apply, Fin.sum_univ_three, toComplex_add, toComplex_mul]

theorem toMat_smul (s : ZOP) (A : M3Z) : toMat (smul s A) = toComplex s • toMat A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, smul, toComplex_mul]

theorem toMat_scalar (s : ZOP) :
    toMat (scalar s) = toComplex s • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, scalar, toComplex_zero]

theorem toMat_transpose (A : M3Z) : toMat (transpose A) = (toMat A).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_star (A : M3Z) : toMat (star A) = (toMat A).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, star, toComplex_conj]

theorem toMat_trace (A : M3Z) : (toMat A).trace = toComplex (trace A) := by
  simp [toMat, trace, Matrix.trace_fin_three, toComplex_add]

theorem toMat_det (A : M3Z) : (toMat A).det = toComplex (det A) := by
  simp [toMat, det, Matrix.det_fin_three, toComplex_add, toComplex_sub, toComplex_mul]

theorem toMat_injective : Function.Injective toMat := by
  intro A B h
  have e : ∀ i j, toMat A i j = toMat B i j := fun i j => by rw [h]
  ext1
  · exact toComplex_injective (e 0 0)
  · exact toComplex_injective (e 0 1)
  · exact toComplex_injective (e 0 2)
  · exact toComplex_injective (e 1 0)
  · exact toComplex_injective (e 1 1)
  · exact toComplex_injective (e 1 2)
  · exact toComplex_injective (e 2 0)
  · exact toComplex_injective (e 2 1)
  · exact toComplex_injective (e 2 2)

/-- The `ℤ[φ]` matrix `A` of `Exact.M3` in `ℤ[ω, φ]`. -/
def ofM3 (A : M3) : M3Z :=
  ⟨ofZPhi A.r0.x, ofZPhi A.r0.y, ofZPhi A.r0.z, ofZPhi A.r1.x, ofZPhi A.r1.y, ofZPhi A.r1.z,
   ofZPhi A.r2.x, ofZPhi A.r2.y, ofZPhi A.r2.z⟩

/-- The real matrix `A / 2` of `Exact.M3`, read in `ℂ`, is half of `ofM3 A`. -/
theorem map_toRealHalf (A : M3) :
    A.toRealHalf.map (fun x : ℝ => (x : ℂ)) = (2 : ℂ)⁻¹ • toMat (ofM3 A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toRealHalf, toMat, ofM3, toComplex_ofZPhi, div_eq_inv_mul]

end M3Z

end Artform.Exact
