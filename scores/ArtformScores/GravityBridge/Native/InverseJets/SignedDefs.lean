import ArtformScores.GravityBridge.Native.Retrospective.Homogeneous
/-! # Original signed physical block and ordered inverse contacts -/
namespace Artform.Scores.GravityBridge.Native.InverseJets
open Matrix
open Full40
open Retrospective
def signedC : Matrix (Fin 3) (Fin 3) ℚ := !![-1, -1, 0;1, 0, -1;0, 1, -1]
def signedV : Fin 3 → ℚ := ![1, 1, -1]
def signedW : Fin 3 → ℚ := ![1, -1, -1]
def rankOne (a b : Fin 3 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ := fun i j => a i * b j
def signedBc : Matrix (Fin 3) (Fin 3) ℚ := rankOne signedV signedV - 1
def signedBcInverse : Matrix (Fin 3) (Fin 3) ℚ := -1 + (1/2 : ℚ) • rankOne signedV signedV
def physicalConnection (z : Fin 3 → ℚ) : Connection ℚ := ![
  z 0 • wedge (basisVector 1) (basisVector 2),
  z 1 • wedge (basisVector 0) (basisVector 2),
  z 2 • wedge (basisVector 0) (basisVector 1), 0]
def physicalTorsionRows (z : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let th := torsion (fun _ : Fin 4 => (0 : ℤ)) 0 (fun _ => -physicalConnection z) 0
  ![th 0 1 2, th 0 2 1, th 1 2 0]
def signedAlpha : ℚ := 103/101
def signedA : ℚ := 101/103
def signedG : ℚ := 101/97
def signedE : ℚ := 202/9991
def signedH0 : Matrix (Fin 3) (Fin 3) ℚ :=
  (-signedA) • 1 - signedE • rankOne signedW signedW
def signedN0 : Matrix (Fin 3) (Fin 3) ℚ :=
  (-signedAlpha) • 1 + (2/101 : ℚ) • rankOne signedW signedW
def linkD (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := diagonal ![l/2, p/2, q/2]
def firstN (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (2/101 : ℚ) • (signedC * (linkD l p q * signedBcInverse -
    signedBcInverse * linkD l p q) * signedC.transpose)
def secondN (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (-2/101 : ℚ) • (signedC * linkD l p q * signedBcInverse * linkD l p q * signedC.transpose)
def firstH (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  -(signedH0 * firstN l p q * signedH0)
def secondH (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  signedH0 * firstN l p q * signedH0 * firstN l p q * signedH0 -
    signedH0 * secondN l p q * signedH0
def sourceL (l p q : ℚ) : Fin 3 → ℚ := ![-l-p, l+q, p+q]
def sourceN2 (l p q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (1/202 : ℚ) • (l^2 • rankOne ![-1, 1, 0] ![-1, 1, 0] +
    p^2 • rankOne ![-1, 0, 1] ![-1, 0, 1] + q^2 • rankOne ![0, -1, -1] ![0, -1, -1]) -
    (1/404 : ℚ) • rankOne (sourceL l p q) (sourceL l p q)
end Artform.Scores.GravityBridge.Native.InverseJets
