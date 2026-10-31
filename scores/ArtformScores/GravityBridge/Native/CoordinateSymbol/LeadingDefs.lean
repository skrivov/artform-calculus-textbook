import ArtformScores.GravityBridge.Native.CoordinateSymbol.Quartic

/-! # Complete native quartic and its leading inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

def spatialRadius (k : Fin 3 → K) : K := k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2

def leadingCoordinate (k : Fin 3 → K) : Mat4 (K := K) :=
  let R := spatialRadius k
  let H : K := 9999 / 9991
  let D : K := 10201 / 10300
  !![D * R / 202, 0, 0, 0;
    0, (-H * R + (H - D) * k 0 ^ 2) / 202, ((H - D) * k 0 * k 1) / 202, ((H - D) * k 0 * k 2) / 202;
    0, ((H - D) * k 1 * k 0) / 202, (-H * R + (H - D) * k 1 ^ 2) / 202, ((H - D) * k 1 * k 2) / 202;
    0, ((H - D) * k 2 * k 0) / 202, ((H - D) * k 2 * k 1) / 202, (-H * R + (H - D) * k 2 ^ 2) / 202]

def leadingCoordinateInverse (k : Fin 3 → K) : Mat4 (K := K) :=
  let R := spatialRadius k
  let H : K := 9999 / 9991
  let D : K := 10201 / 10300
  !![202 / (D * R), 0, 0, 0;
    0, -202 / R * (H⁻¹ + (D⁻¹ - H⁻¹) * k 0 ^ 2 / R), -202 / R * ((D⁻¹ - H⁻¹) * k 0 * k 1 / R),
      -202 / R * ((D⁻¹ - H⁻¹) * k 0 * k 2 / R);
    0, -202 / R * ((D⁻¹ - H⁻¹) * k 1 * k 0 / R), -202 / R * (H⁻¹ + (D⁻¹ - H⁻¹) * k 1 ^ 2 / R),
      -202 / R * ((D⁻¹ - H⁻¹) * k 1 * k 2 / R);
    0, -202 / R * ((D⁻¹ - H⁻¹) * k 2 * k 0 / R), -202 / R * ((D⁻¹ - H⁻¹) * k 2 * k 1 / R),
      -202 / R * (H⁻¹ + (D⁻¹ - H⁻¹) * k 2 ^ 2 / R)]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
