import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import ArtformTextbook.Ch05.Stokes

/-!
# The difference, curl, divergence and adjoint curl are additive

What the proofs of Chapter 6 use about the four operators of Section 5.10:
each respects sums, negatives and differences, and Proposition 5.38 gives
`curl D = 0`, `div curl* = 0` and summation by parts.
-/

namespace Artform.Canvas

open scoped BigOperators

variable (K : Canvas) {R : Type} [CommRing R]

@[simp]
theorem diff_add (a b : K.V → R) : K.diff (a + b) = K.diff a + K.diff b := by
  funext e
  simp only [diff, Pi.add_apply]
  ring

@[simp]
theorem diff_neg (a : K.V → R) : K.diff (-a) = -K.diff a := by
  funext e
  simp only [diff, Pi.neg_apply]
  ring

@[simp]
theorem diff_sub (a b : K.V → R) : K.diff (a - b) = K.diff a - K.diff b := by
  funext e
  simp only [diff, Pi.sub_apply]
  ring

@[simp]
theorem diff_zero : K.diff (0 : K.V → R) = 0 := by
  funext e
  simp [diff]

@[simp]
theorem curl_add (a b : K.E → R) : K.curl (a + b) = K.curl a + K.curl b := by
  funext f
  simp only [curl, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
theorem curl_neg (a : K.E → R) : K.curl (-a) = -K.curl a := by
  funext f
  simp only [curl, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp]
theorem curl_sub (a b : K.E → R) : K.curl (a - b) = K.curl a - K.curl b := by
  rw [sub_eq_add_neg, curl_add, curl_neg, ← sub_eq_add_neg]

@[simp]
theorem curl_zero : K.curl (0 : K.E → R) = 0 := by
  funext f
  simp [curl]

@[simp]
theorem curlStar_add (a b : K.F → R) : K.curlStar (a + b) = K.curlStar a + K.curlStar b := by
  funext e
  simp only [curlStar, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
theorem curlStar_neg (a : K.F → R) : K.curlStar (-a) = -K.curlStar a := by
  funext e
  simp only [curlStar, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp]
theorem curlStar_sub (a b : K.F → R) : K.curlStar (a - b) = K.curlStar a - K.curlStar b := by
  rw [sub_eq_add_neg, curlStar_add, curlStar_neg, ← sub_eq_add_neg]

@[simp]
theorem curlStar_zero : K.curlStar (0 : K.F → R) = 0 := by
  funext e
  simp [curlStar]

@[simp]
theorem div_add (a b : K.E → R) : K.div (a + b) = K.div a + K.div b := by
  funext v
  simp only [div, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

@[simp]
theorem div_neg (a : K.E → R) : K.div (-a) = -K.div a := by
  funext v
  simp only [div, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

@[simp]
theorem div_sub (a b : K.E → R) : K.div (a - b) = K.div a - K.div b := by
  rw [sub_eq_add_neg, div_add, div_neg, ← sub_eq_add_neg]

@[simp]
theorem div_zero : K.div (0 : K.E → R) = 0 := by
  funext v
  simp [div]

/-- `curl D = 0` (Proposition 5.38, part 1). -/
@[simp]
theorem curl_diff (φ : K.V → R) : K.curl (K.diff φ) = 0 :=
  (discreteStokes K R).1 φ

/-- `div curl* = 0` (Proposition 5.38, part 1). -/
@[simp]
theorem div_curlStar (B : K.F → R) : K.div (K.curlStar B) = 0 :=
  (discreteStokes K R).2.1 B

/-- Summation by parts, `Σ_e Dφ(e) E(e) = −Σ_v φ(v) div E(v)` (Proposition 5.38,
part 4). -/
theorem sum_diff_mul (φ : K.V → R) (E : K.E → R) :
    ∑ e, K.diff φ e * E e = -∑ v, φ v * K.div E v :=
  (discreteStokes K R).2.2.2.2.1 φ E

/-- Summation by parts, `Σ_f curl A(f) B(f) = Σ_e A(e) curl* B(e)`
(Proposition 5.38, part 4). -/
theorem sum_curl_mul (A : K.E → R) (B : K.F → R) :
    ∑ f, K.curl A f * B f = ∑ e, A e * K.curlStar B e :=
  (discreteStokes K R).2.2.2.2.2 A B

end Artform.Canvas
