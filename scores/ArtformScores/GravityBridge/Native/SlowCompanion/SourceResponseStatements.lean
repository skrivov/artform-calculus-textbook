import ArtformScores.GravityBridge.Native.SlowCompanion.SourceResponseDefs

/-! # Complete mixed source response and preparation contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion.Statement

/-- **GAC2:mixed-source-response-contacts**
(complete mixed source response and preparation contact). -/
@[ledger "GAC2:mixed-source-response-contacts"]
def sourceResponseLaw : Prop :=
  ∀ (K V T : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T],
    (∀ (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V)
    (L : Module.End K V) (r z : K) (source : T × V)
    (_hz : z ^ 2 + r ≠ 0) (_hL : coordinatePolynomial g z * L = 1),
    mixedSymbol g C0 C1 r z (sourceResponse L C0 C1 r z source) = source) ∧
    (∀ (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V)
    (L : Module.End K V) (r z : K) (x : T × V)
    (_hz : z ^ 2 + r ≠ 0) (_hL : L * coordinatePolynomial g z = 1),
    sourceResponse L C0 C1 r z (mixedSymbol g C0 C1 r z x) = x) ∧
    (∀ (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V) (L : Module.End K V)
    (r z : K) (q v : T) (x y : Fin 4 → V),
    sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v x)-
      sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v y) =
      (0, L (coordinateCauchy g z x - coordinateCauchy g z y))) ∧
    (∀ (g : Fin 5 → Module.End K V) (C0 C1 : T →ₗ[K] V) (L : Module.End K V)
    (r z : K) (q v : T) (x : Fin 4 → V),
    sourceResponse L C0 C1 r z (mixedCauchy g C1 z q v x)-
      sourceResponse L C0 C1 r z (z • q + v, coordinateCauchy g z x) =
      (0, L (C1 q)))

end Artform.Scores.GravityBridge.Native.SlowCompanion.Statement
