import ArtformScores.GravityBridge.Native.CoordinateSymbol.Simple

/-! # Original coordinate symbol and guarded two-sided inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

def twoValueSymbol (C : Mat4 (K := K)) (d a b : K) : Mat4 (K := K) :=
  (a * d) • 1 + (b - a) • C

def twoValueNumerator (C : Mat4 (K := K)) (d a b : K) : Mat4 (K := K) :=
  (b * d) • 1 + (a - b) • C

def twoValueInverse (C : Mat4 (K := K)) (d a b : K) : Mat4 (K := K) :=
  (a * b * d ^ 2)⁻¹ • twoValueNumerator C d a b

def etaMatrix : Mat4 (K := K) := Matrix.diagonal signature

def nativeCoordinateInverse (p : Vec4 (K := K)) : Mat4 (K := K) :=
  (101 / 2 : K) • (twoValueInverse (raisedK (componentSquares p) p)
    (simpleDiscriminant (componentSquares p) p) (9999 / 9991) (10201 / 10300) * etaMatrix)

def nativeLowerSymbol (p : Vec4 (K := K)) : Mat4 (K := K) :=
  etaMatrix * nativeUpperSymbol p * etaMatrix

def nativeLowerInverse (p : Vec4 (K := K)) : Mat4 (K := K) :=
  etaMatrix * nativeCoordinateInverse p * etaMatrix

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
