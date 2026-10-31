import ArtformScores.GravityBridge.LinearDefs

/-! # Two old shear schedules and their endpoint primitives -/

namespace Artform.Scores.GravityBridge

noncomputable section

def scheduleKick (a : ℚ) (x : ℚ × ℚ) : ℚ × ℚ := (x.1, x.2 + a * x.1)

def scheduleMove (b : ℚ) (x : ℚ × ℚ) : ℚ × ℚ := (x.1 + b * x.2, x.2)

def boundaryPotential (x u : ℚ × ℚ) : ℚ := x.2 * u.1

def kmPrimitive (a b : ℚ) (x : ℚ × ℚ) : ℚ :=
  a * x.1 ^ 2 / 2 + b * (x.2 + a * x.1) ^ 2 / 2

def mkPrimitive (a b : ℚ) (x : ℚ × ℚ) : ℚ :=
  b * x.2 ^ 2 / 2 + a * (x.1 + b * x.2) ^ 2 / 2

def kmDerivative (a b : ℚ) (x u : ℚ × ℚ) : ℚ :=
  a * x.1 * u.1 + b * (x.2 + a * x.1) * (u.2 + a * u.1)

def mkDerivative (a b : ℚ) (x u : ℚ × ℚ) : ℚ :=
  b * x.2 * u.2 + a * (x.1 + b * x.2) * (u.1 + b * u.2)

end

end Artform.Scores.GravityBridge
