import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch03.Defs.Canvas

/-!
# The coupled hop (Section 6.8, "Minimal coupling")

A walker of charge `q ∈ ℤ/8` carries amplitudes at the sites. A hop along an
oriented link `ℓ : u → v` multiplies the amplitude it carries from `u` by the
link phase `ζ^{q A(ℓ)}`, with `ζ = e^{2πi/8}`: the covariant transport of
Definition 5.30 in the character `k ↦ ζ^{qk}` of `C₈`. An oriented link is an
edge with a direction, `(e, true)` along its stored direction and `(e, false)`
against it, where the potential reads `A(ē) = −A(e)`. The amplitudes lie in any
complex vector space: the walker's two components, or one.
-/

namespace Artform

/-- `ζ = e^{2πi/8}`, the primitive eighth root of unity of the phase notation. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The phase `ζ^k` of a residue `k ∈ ℤ/8`, with `k` read as one of `0, …, 7`. -/
noncomputable def phase8 (k : ZMod 8) : ℂ := zeta8 ^ k.val

variable (K : Canvas)

/-- The potential on an oriented link: `A(e)` along the stored direction of
`e`, and `A(ē) = −A(e)` against it. -/
def Canvas.linkValue (A : K.E → ZMod 8) : K.E × Bool → ZMod 8
  | (e, true) => A e
  | (e, false) => -A e

/-- The coupled hop of a walker of charge `q` along the oriented link `ℓ`, from
`u = stepStart ℓ` to `v = stepEnd ℓ`: the amplitude `ψ(u)` carried to `v`,
multiplied by `ζ^{q A(ℓ)}`. -/
noncomputable def hop {M : Type*} [AddCommGroup M] [Module ℂ M] (q : ZMod 8)
    (A : K.E → ZMod 8) (ψ : K.V → M) (ℓ : K.E × Bool) : M :=
  phase8 (q * K.linkValue A ℓ) • ψ (stepStart K.src K.tgt ℓ)

variable {K}

/-- The gauge action on the amplitudes of a walker of charge `q`, for a site
function `g`: `ψ(x) ↦ ζ^{q g(x)} ψ(x)`. -/
noncomputable def gaugeAmplitude {M : Type*} [AddCommGroup M] [Module ℂ M] (q : ZMod 8)
    (g : K.V → ZMod 8) (ψ : K.V → M) : K.V → M :=
  fun x => phase8 (q * g x) • ψ x

end Artform
