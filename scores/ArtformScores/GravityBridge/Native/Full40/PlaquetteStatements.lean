import ArtformScores.GravityBridge.Native.Full40.PlaquetteDefs

/-! # Ordered native plaquette through quadratic degree -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:native-ordered-plaquette-jet**
(ordered native plaquette through quadratic degree). -/
@[ledger "GAC2:native-ordered-plaquette-jet"]
def plaquetteLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (X : Fin 4 → Matrix4 K),
    orderedFourJet X 0 = 1 ∧ orderedFourJet X 1 = firstSum X) ∧
    (∀ (X : Fin 4 → Matrix4 K),
    orderedFourJet X 2 =
      (1 / 2 : K) • (X 0 * X 0 + X 1 * X 1 + X 2 * X 2 + X 3 * X 3) +
        orderedPairs X) ∧
    (∀ (J : Jet2 K) (_hJ : J 0 = 1),
    jetProduct (inverseJetAtOne J) J = ![1, 0, 0]) ∧
    (∀ (J : Jet2 K) (_hJ : J 0 = 1),
    jetProduct J (inverseJetAtOne J) = ![1, 0, 0]) ∧
    (∀ (X : Fin 4 → Matrix4 K),
    curvatureJet (orderedFourJet X) 2 = (-1 / 2 : K) • orderedCommutators X) ∧
    (∀ (Al SlAk SkAl Ak : Matrix4 K),
    curvatureJet (orderedFourJet (plaquetteLetters Al SlAk SkAl Ak)) 1 =
      SlAk - Ak - (SkAl - Al))

end Artform.Scores.GravityBridge.Native.Full40.Statement
