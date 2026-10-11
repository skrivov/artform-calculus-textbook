import Mathlib.RingTheory.RootsOfUnity.Complex
import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# Gauge covariance of a hop (Proposition 6.10)

The book's calculation: the transformed link value is
`A'(u → v) = A(u → v) + g(v) − g(u)`, so transporting the transformed source
gives `ζ^{qA'} ζ^{qg(u)} ψ(u) = ζ^{qg(v)} ζ^{qA} ψ(u)`. It uses that `k ↦ ζ^k`
turns sums of residues into products, since `ζ⁸ = 1`.
-/

namespace Artform

/-- `ζ⁸ = 1`. -/
theorem zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  have h := (Complex.isPrimitiveRoot_exp 8 (by norm_num)).pow_eq_one
  simpa [zeta8] using h

/-- `ζ^(n mod 8) = ζ^n`. -/
theorem zeta8_pow_mod (n : ℕ) : zeta8 ^ (n % 8) = zeta8 ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 8, pow_add, pow_mul, zeta8_pow_eight, one_pow, mul_one]

/-- `ζ^(a + b) = ζ^a ζ^b` for residues `a`, `b`. -/
theorem phase8_add (a b : ZMod 8) : phase8 (a + b) = phase8 a * phase8 b := by
  rw [phase8, phase8, phase8, ZMod.val_add, zeta8_pow_mod, pow_add]

/-- The gauge change adds `g(v) − g(u)` to the potential on an oriented link
from `u` to `v`, whichever way the link runs. -/
theorem linkValue_add_diff (K : Canvas) (A : K.E → ZMod 8) (g : K.V → ZMod 8)
    (ℓ : K.E × Bool) :
    K.linkValue (A + K.diff g) ℓ =
      K.linkValue A ℓ + g (stepEnd K.src K.tgt ℓ) - g (stepStart K.src K.tgt ℓ) := by
  obtain ⟨e, b⟩ := ℓ
  cases b <;> simp only [Canvas.linkValue, stepStart, stepEnd, Pi.add_apply, Canvas.diff] <;>
    ring

/-- **Proposition 6.10** (gauge covariance of a hop). Hopping in `A + Dg` from
the amplitudes `ζ^{q g(x)} ψ(x)` gives `ζ^{q g(v)}` times the hop in `A` from
`ψ`, at the target `v` of the link. -/
@[book "prop:hop-covariance"]
theorem hopCovariance : Statement.hopCovariance := by
  intro K M _ _ q A g ψ ℓ
  have hlink : q * K.linkValue (A + K.diff g) ℓ + q * g (stepStart K.src K.tgt ℓ) =
      q * g (stepEnd K.src K.tgt ℓ) + q * K.linkValue A ℓ := by
    rw [linkValue_add_diff]
    ring
  simp only [hop, gaugeAmplitude, smul_smul]
  rw [← phase8_add, ← phase8_add, hlink]

/-! ## Non-vacuity -/

/-- The checkpoint after the proof: a walker of charge `3` hops along a link
carrying `A(ℓ) = 5`, here the link `ℓ₁` of the face of Figure 6.7, and turns by
`ζ^{15} = ζ^7`; after the gauge change with `g(u) = 1` and `g(v) = 4` the link
carries `0`, and the hop does not turn the amplitude at all. -/
example : (3 : ZMod 8) * oneFace.linkValue ![5, 0, 0, 0] (0, true) = 7 ∧
    oneFace.linkValue (![5, 0, 0, 0] + oneFace.diff ![1, 4, 0, 0]) (0, true) = 0 ∧
    hop oneFace 3 (![5, 0, 0, 0] + oneFace.diff ![1, 4, 0, 0]) (fun _ => (1 : ℂ)) (0, true) = 1 :=
  by
  refine ⟨by decide, by decide, ?_⟩
  have h : oneFace.linkValue (![5, 0, 0, 0] + oneFace.diff ![1, 4, 0, 0]) (0, true) = 0 := by
    decide
  simp only [hop, h, mul_zero, phase8, ZMod.val_zero, pow_zero, smul_eq_mul, mul_one]

end Artform
