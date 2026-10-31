import ArtformScores.GravityBridge.Native.RetroCertificates.OddInverse

/-! # Native modal interpolation requires the fifth-degree term -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



def sixEigenvalues : Fin 6 → ℚ := ![194 / 101, -194 / 101, 103 / 101, -103 / 101, 200 / 101,
  -200 / 101]

def sixEigenvectors (i : Fin 6) : Connection ℚ := ![
  gDistinctInput 0 ![1, -1, -1], gDistinctInput 3 ![1, 1, 1],
  gDistinctInput 3 ![0, 1, -1], gDistinctInput 0 ![0, -1, 1],
  gRepeatedInput 0 ![1, 1, 1], gRepeatedInput 1 ![1, 1, 1]] i

end Artform.Scores.GravityBridge.Native.RetroCertificates
