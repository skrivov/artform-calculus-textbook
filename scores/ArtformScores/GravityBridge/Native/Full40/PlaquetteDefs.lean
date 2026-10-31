import ArtformScores.GravityBridge.Defs

/-! # Ordered native plaquette through quadratic degree -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

abbrev Matrix4 (K : Type*) := Matrix (Fin 4) (Fin 4) K

abbrev Jet2 (K : Type*) := Fin 3 → Matrix4 K
variable {K : Type*} [Field K] [CharZero K]

def jetProduct (p q : Jet2 K) : Jet2 K :=
  ![p 0 * q 0, p 0 * q 1 + p 1 * q 0, p 0 * q 2 + p 1 * q 1 + p 2 * q 0]

def exponentialJet (X : Matrix4 K) : Jet2 K := ![1, X, (1 / 2 : K) • (X * X)]

def orderedFourJet (X : Fin 4 → Matrix4 K) : Jet2 K :=
  jetProduct (jetProduct (jetProduct (exponentialJet (X 0)) (exponentialJet (X 1)))
    (exponentialJet (X 2))) (exponentialJet (X 3))

def firstSum (X : Fin 4 → Matrix4 K) : Matrix4 K := X 0 + X 1 + X 2 + X 3

def orderedPairs (X : Fin 4 → Matrix4 K) : Matrix4 K :=
  X 0 * X 1 + X 0 * X 2 + X 0 * X 3 + X 1 * X 2 + X 1 * X 3 + X 2 * X 3

def commutator (X Y : Matrix4 K) : Matrix4 K := X * Y - Y * X

def orderedCommutators (X : Fin 4 → Matrix4 K) : Matrix4 K :=
  commutator (X 0) (X 1) + commutator (X 0) (X 2) + commutator (X 0) (X 3) +
  commutator (X 1) (X 2) + commutator (X 1) (X 3) + commutator (X 2) (X 3)

def inverseJetAtOne (J : Jet2 K) : Jet2 K := ![1, -J 1, J 1 * J 1 - J 2]

def curvatureJet (J : Jet2 K) : Jet2 K :=
  fun i => (-1 / 2 : K) • (J i - inverseJetAtOne J i)

def plaquetteLetters (Al SlAk SkAl Ak : Matrix4 K) : Fin 4 → Matrix4 K :=
  ![-Al, -SlAk, SkAl, Ak]

end Artform.Scores.GravityBridge.Native.Full40
