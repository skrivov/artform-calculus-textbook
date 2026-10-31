import ArtformScores.GravityBridge.Native.SlowCompanion.Resolvent

/-! # Complete mixed source response and preparation contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

def mixedSymbol (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V)
    (r z : K) (x : T × V) : T × V :=
  ((z ^ 2 + r) • x.1, C0 x.1 + z • C1 x.1 + coordinatePolynomial g z x.2)

def sourceResponse (L : Module.End K V) (C0 C1 : T →ₗ[K] V)
    (r z : K) (source : T × V) : T × V :=
  let t := (z ^ 2 + r)⁻¹ • source.1
  (t, L (source.2 - C0 t - z • C1 t))

end Artform.Scores.GravityBridge.Native.SlowCompanion
