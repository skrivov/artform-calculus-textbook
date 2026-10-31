import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverse
/-! # Verified exact arithmetic programs for the original native block -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
inductive ScalarRef where
  | input (i : Fin 3)
  | slot (i : ℕ)
  | neg (a : ScalarRef)
  deriving DecidableEq
inductive ScalarGate where
  | scale (c : ℚ) (a : ScalarRef)
  | add (a b : ScalarRef)
  deriving DecidableEq
def resolveRef (z : Fin 3 → ℚ) (registers : List ℚ) : ScalarRef → ℚ
  | .input i => z i
  | .slot i => registers.getD i 0
  | .neg a => -resolveRef z registers a
def evaluateGate (z : Fin 3 → ℚ) (registers : List ℚ) : ScalarGate → ℚ
  | .scale c a => c * resolveRef z registers a
  | .add a b => resolveRef z registers a + resolveRef z registers b
def runScalarProgram (program : List ScalarGate) (z : Fin 3 → ℚ) : List ℚ :=
  program.foldl (fun registers gate => registers ++ [evaluateGate z registers gate]) []
def programOutput (program : List ScalarGate) (outputs : Fin 3 → ℕ)
    (z : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => (runScalarProgram program z).getD (outputs i) 0
def validRef (bound : ℕ) : ScalarRef → Bool
  | .input _ => true
  | .slot i => decide (i < bound)
  | .neg a => validRef bound a
def validGate (bound : ℕ) : ScalarGate → Bool
  | .scale _ a => validRef bound a
  | .add a b => validRef bound a && validRef bound b
def validProgram : ℕ → List ScalarGate → Bool
  | _, [] => true
  | n, g :: gs => validGate n g && validProgram (n + 1) gs
def scaleCount (program : List ScalarGate) : ℕ :=
  (program.filter (fun g => match g with | .scale _ _ => true | .add _ _ => false)).length
def addCount (program : List ScalarGate) : ℕ := program.length - scaleCount program
def denseBlockProgram : List ScalarGate := [
  .scale (-9595 / 19982) (.input 0), .scale (-9999 / 19982) (.input 1),
  .add (.slot 0) (.slot 1), .scale (-9999 / 19982) (.input 2), .add (.slot 2) (.slot 3),
  .scale (-9999 / 19982) (.input 0), .scale (-9595 / 19982) (.input 1),
  .add (.slot 5) (.slot 6), .scale (9999 / 19982) (.input 2), .add (.slot 7) (.slot 8),
  .scale (-9999 / 19982) (.input 0), .scale (9999 / 19982) (.input 1),
  .add (.slot 10) (.slot 11), .scale (-9595 / 19982) (.input 2), .add (.slot 12) (.slot 13)]
def rankBlockProgram : List ScalarGate := [
  .scale (-101 / 103) (.input 0), .scale (-101 / 103) (.input 1),
  .scale (-101 / 103) (.input 2), .add (.input 0) (.neg (.input 1)),
  .add (.slot 3) (.neg (.input 2)), .scale (9999 / 19982) (.slot 4),
  .add (.slot 0) (.slot 5), .add (.slot 1) (.neg (.slot 5)),
  .add (.slot 2) (.neg (.slot 5))]
end Artform.Scores.GravityBridge.Native.Retrospective
