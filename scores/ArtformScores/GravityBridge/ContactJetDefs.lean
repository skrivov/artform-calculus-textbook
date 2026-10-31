import ArtformScores.GravityBridge.KernelDefs
import ArtformScores.GravityBridge.Native.PreparationDefs

/-! # Formal polynomial source jets and prepared native input polynomials -/

namespace Artform.Scores.GravityBridge

open Polynomial

noncomputable section

def sourceJet (n : ℕ) (p : Polynomial ℚ) (z : ℚ) : ℚ :=
  ((Polynomial.derivative^[n]) p).eval z

def completeInputPolynomial : Polynomial ℚ := C (-2 / 103) * X ^ 2

def connectionInputPolynomial : Polynomial ℚ := C (4 / 10403) * X ^ 2

end

end Artform.Scores.GravityBridge
