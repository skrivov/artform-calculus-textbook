import ArtformScores.GravityBridge.Native.InverseJets.Signed

/-! # Ordered noncommutative inverse jets through third order -/

namespace Artform.Scores.GravityBridge.Native.InverseJets

open Matrix

variable {R : Type*} [Ring R]

def inverseJet1 (H N1 : R) : R := -(H * N1 * H)

def inverseJet2 (H N1 N2 : R) : R := H * N1 * H * N1 * H - H * N2 * H

def inverseJet3 (H N1 N2 N3 : R) : R :=
  -(H * N1 * H * N1 * H * N1 * H) + H * N1 * H * N2 * H + H * N2 * H * N1 * H - H * N3 * H

def thirdN (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (-1 / 12 : ℚ) • firstN (l ^ 3) (p ^ 3) (q ^ 3)

def thirdH (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  inverseJet3 signedH0 (firstN l p q) (secondN l p q) (thirdN l p q)

def linkCube (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  linkD l p q * linkD l p q * linkD l p q

def thirdLinkProduct (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (2 / 101 : ℚ) • (signedC * ((-1 / 3 : ℚ) • (linkCube l p q * signedBcInverse) +
    (1 / 3 : ℚ) • (signedBcInverse * linkCube l p q)) * signedC.transpose)

end Artform.Scores.GravityBridge.Native.InverseJets
