import ArtformScores.GravityBridge.LinearDefs

/-! # A two-mode form and its declared uncertainty test -/

namespace Artform.Scores.GravityBridge

noncomputable section

def uncertaintyMatrix (y c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(y : ℂ), Complex.I * c; -Complex.I * c, (y : ℂ)]

def uncertaintyValue (y c : ℝ) (z : Fin 2 → ℂ) : ℝ :=
  (dotProduct (star z) ((uncertaintyMatrix y c).mulVec z)).re

abbrev TwoModes := (ℝ × ℝ) × (ℝ × ℝ)

def twoModeArea (x y : TwoModes) : ℝ :=
  x.1.1 * y.1.2 - x.1.2 * y.1.1 + x.2.1 * y.2.2 - x.2.2 * y.2.1

def beamSplitter (r t : ℝ) (x : TwoModes) : TwoModes :=
  ((r * x.1.1 + t * x.2.1, r * x.1.2 + t * x.2.2),
    (-t * x.1.1 + r * x.2.1, -t * x.1.2 + r * x.2.2))

end

end Artform.Scores.GravityBridge
