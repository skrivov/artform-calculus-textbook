import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Exact arithmetic in `ℤ[φ]`

The numbers `a + b φ`, with `a b : ℤ` and `φ` the golden ratio (`φ² = φ + 1`),
written as pairs of integers so that the kernel computes with them, together
with vectors of length three and `3 × 3` matrices over them. A matrix `A`
here stands for the real matrix `A / 2`, whose entries lie in `½ℤ[φ]`.

`ZPhi.toReal` sends a pair to the real number it stands for. It respects
sums and products, and it is injective because `φ` is irrational, so that an
identity checked by `decide` on the exact side holds for the real numbers.
-/

namespace Artform.Exact

open Real Matrix

/-- The number `re + im φ` of `ℤ[φ]`. -/
structure ZPhi where
  /-- The integer part. -/
  re : ℤ
  /-- The coefficient of `φ`. -/
  im : ℤ
  deriving DecidableEq

namespace ZPhi

instance : Add ZPhi := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg ZPhi := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub ZPhi := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩

/-- `(a + b φ)(c + d φ) = (a c + b d) + (a d + b c + b d) φ`, since `φ² = φ + 1`. -/
instance : Mul ZPhi :=
  ⟨fun x y => ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

@[simp] theorem add_re (x y : ZPhi) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : ZPhi) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : ZPhi) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : ZPhi) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : ZPhi) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : ZPhi) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : ZPhi) : (x * y).re = x.re * y.re + x.im * y.im := rfl
@[simp] theorem mul_im (x y : ZPhi) : (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im :=
  rfl

/-- The real number `re + im φ`. -/
noncomputable def toReal (x : ZPhi) : ℝ := x.re + x.im * goldenRatio

theorem toReal_mk (a b : ℤ) : toReal ⟨a, b⟩ = a + b * goldenRatio := rfl

@[simp] theorem toReal_add (x y : ZPhi) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, add_re, add_im, Int.cast_add]
  ring

@[simp] theorem toReal_neg (x : ZPhi) : (-x).toReal = -x.toReal := by
  simp only [toReal, neg_re, neg_im, Int.cast_neg]
  ring

@[simp] theorem toReal_sub (x y : ZPhi) : (x - y).toReal = x.toReal - y.toReal := by
  simp only [toReal, sub_re, sub_im, Int.cast_sub]
  ring

@[simp] theorem toReal_mul (x y : ZPhi) : (x * y).toReal = x.toReal * y.toReal := by
  simp only [toReal, mul_re, mul_im, Int.cast_add, Int.cast_mul]
  linear_combination (-(x.im : ℝ) * y.im) * goldenRatio_sq

/-- `toReal` is injective, since `φ` is irrational. -/
theorem toReal_injective : Function.Injective toReal := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [toReal] at h
  have hbd : b = d := by
    by_contra hne
    apply (goldenRatio_irrational.intCast_mul (sub_ne_zero.mpr hne)).ne_int (c - a)
    push_cast
    linear_combination h
  subst hbd
  have hac : (a : ℝ) = c := by linear_combination h
  simp only [mk.injEq, and_true]
  exact_mod_cast hac

theorem toReal_inj {x y : ZPhi} : x.toReal = y.toReal ↔ x = y :=
  toReal_injective.eq_iff

end ZPhi

/-- A vector of `ℤ[φ]³`. -/
structure V3 where
  /-- The first coordinate. -/
  x : ZPhi
  /-- The second coordinate. -/
  y : ZPhi
  /-- The third coordinate. -/
  z : ZPhi
  deriving DecidableEq

namespace V3

/-- The dot product. -/
def dot (u v : V3) : ZPhi := u.x * v.x + u.y * v.y + u.z * v.z

/-- The opposite vector. -/
def neg (u : V3) : V3 := ⟨-u.x, -u.y, -u.z⟩

/-- Twice the vector. -/
def double (u : V3) : V3 := ⟨u.x + u.x, u.y + u.y, u.z + u.z⟩

/-- The real vector that `u` stands for. -/
noncomputable def toReal (u : V3) : Fin 3 → ℝ := ![u.x.toReal, u.y.toReal, u.z.toReal]

theorem toReal_dot (u v : V3) : u.toReal ⬝ᵥ v.toReal = (u.dot v).toReal := by
  simp only [toReal, dot, vec3_dotProduct', ZPhi.toReal_add, ZPhi.toReal_mul]

theorem toReal_neg (u : V3) : u.neg.toReal = -u.toReal := by
  ext i
  fin_cases i <;> simp [toReal, neg]

theorem toReal_injective : Function.Injective toReal := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [toReal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [ZPhi.toReal_injective h0, ZPhi.toReal_injective h1, ZPhi.toReal_injective h2]

end V3

/-- A `3 × 3` matrix over `ℤ[φ]`, given by its rows. It stands for the real
matrix `A / 2`. -/
structure M3 where
  /-- The first row. -/
  r0 : V3
  /-- The second row. -/
  r1 : V3
  /-- The third row. -/
  r2 : V3
  deriving DecidableEq

namespace M3

/-- The product of a matrix and a vector. -/
def mulVec (A : M3) (v : V3) : V3 := ⟨A.r0.dot v, A.r1.dot v, A.r2.dot v⟩

/-- The transpose. -/
def transpose (A : M3) : M3 :=
  ⟨⟨A.r0.x, A.r1.x, A.r2.x⟩, ⟨A.r0.y, A.r1.y, A.r2.y⟩, ⟨A.r0.z, A.r1.z, A.r2.z⟩⟩

/-- The determinant. -/
def det (A : M3) : ZPhi :=
  A.r0.x * A.r1.y * A.r2.z - A.r0.x * A.r1.z * A.r2.y - A.r0.y * A.r1.x * A.r2.z +
    A.r0.y * A.r1.z * A.r2.x + A.r0.z * A.r1.x * A.r2.y - A.r0.z * A.r1.y * A.r2.x

/-- The trace. -/
def trace (A : M3) : ZPhi := A.r0.x + A.r1.y + A.r2.z

/-- `A Aᵀ = 4`, so that the rows of `A / 2` are orthonormal. -/
def Ortho4 (A : M3) : Prop :=
  A.r0.dot A.r0 = ⟨4, 0⟩ ∧ A.r1.dot A.r1 = ⟨4, 0⟩ ∧ A.r2.dot A.r2 = ⟨4, 0⟩ ∧
    A.r0.dot A.r1 = ⟨0, 0⟩ ∧ A.r0.dot A.r2 = ⟨0, 0⟩ ∧ A.r1.dot A.r2 = ⟨0, 0⟩

instance : DecidablePred Ortho4 := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The real matrix `A / 2` that `A` stands for. -/
noncomputable def toRealHalf (A : M3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A.r0.x.toReal / 2, A.r0.y.toReal / 2, A.r0.z.toReal / 2;
     A.r1.x.toReal / 2, A.r1.y.toReal / 2, A.r1.z.toReal / 2;
     A.r2.x.toReal / 2, A.r2.y.toReal / 2, A.r2.z.toReal / 2]

/-- If `A v = 2 w` exactly, then `(A / 2) v = w`. -/
theorem toRealHalf_mulVec {A : M3} {v w : V3} (h : A.mulVec v = w.double) :
    A.toRealHalf *ᵥ v.toReal = w.toReal := by
  have h0 := congrArg (fun u => u.x.toReal) h
  have h1 := congrArg (fun u => u.y.toReal) h
  have h2 := congrArg (fun u => u.z.toReal) h
  simp only [mulVec, V3.double, V3.dot, ZPhi.toReal_add, ZPhi.toReal_mul] at h0 h1 h2
  simp only [toRealHalf, V3.toReal, cons_mulVec, vec3_dotProduct', empty_mulVec]
  refine vec3_eq ?_ ?_ ?_
  · linear_combination h0 / 2
  · linear_combination h1 / 2
  · linear_combination h2 / 2

/-- If `A Aᵀ = 4` exactly, then `(A / 2)(A / 2)ᵀ = 1`. -/
theorem toRealHalf_mul_transpose {A : M3} (h : A.Ortho4) :
    A.toRealHalf * A.toRealHalfᵀ = 1 := by
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := h
  replace h00 := congrArg ZPhi.toReal h00
  replace h11 := congrArg ZPhi.toReal h11
  replace h22 := congrArg ZPhi.toReal h22
  replace h01 := congrArg ZPhi.toReal h01
  replace h02 := congrArg ZPhi.toReal h02
  replace h12 := congrArg ZPhi.toReal h12
  simp only [V3.dot, ZPhi.toReal_add, ZPhi.toReal_mul, ZPhi.toReal_mk, Int.cast_ofNat,
    Int.cast_zero, zero_mul, add_zero] at h00 h11 h22 h01 h02 h12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, toRealHalf]
  · linear_combination h00 / 4
  · linear_combination h01 / 4
  · linear_combination h02 / 4
  · linear_combination h01 / 4
  · linear_combination h11 / 4
  · linear_combination h12 / 4
  · linear_combination h02 / 4
  · linear_combination h12 / 4
  · linear_combination h22 / 4

/-- The determinant of `A / 2` is `det A / 8`. -/
theorem det_toRealHalf (A : M3) : A.toRealHalf.det = A.det.toReal / 8 := by
  simp only [toRealHalf, Matrix.det_fin_three, of_apply, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, det, ZPhi.toReal_add, ZPhi.toReal_sub, ZPhi.toReal_mul]
  ring

/-- The trace of `A / 2` is `trace A / 2`. -/
theorem trace_toRealHalf (A : M3) : A.toRealHalf.trace = A.trace.toReal / 2 := by
  simp only [toRealHalf, Matrix.trace_fin_three_of, trace, ZPhi.toReal_add]
  ring

/-- The exact transpose stands for the real transpose. -/
theorem toRealHalf_transpose (A : M3) : A.transpose.toRealHalf = A.toRealHalfᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Every entry of `A / 2` has the form `(a + b φ) / 2` with `a b : ℤ`. -/
theorem toRealHalf_entry (A : M3) (i j : Fin 3) :
    ∃ a b : ℤ, A.toRealHalf i j = (a + b * goldenRatio) / 2 := by
  fin_cases i <;> fin_cases j <;> exact ⟨_, _, rfl⟩

end M3

end Artform.Exact
