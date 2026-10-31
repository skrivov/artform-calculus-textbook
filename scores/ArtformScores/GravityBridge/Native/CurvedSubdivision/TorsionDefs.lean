import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost

/-! # Full ordered nonlinear torsion on the inherited coframe -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40

variable {K : Type*} [Field K] [CharZero K]

def inverseLinks (c s : K) (i : Fin 4) : Frame K := if i = 1 then boost c (-s) else 1

def exactTorsion (h b c s : K) (i l : Fin 4) : Vec K :=
  let E := inheritedCoframe h b
  let ei := fun a => E a i
  let el := fun a => E a l
  inverseLinks c s i *ᵥ el - el - inverseLinks c s l *ᵥ ei + ei

def exactMetricInverse (h b : K) : Frame K :=
  Matrix.diagonal ![-(h ^ 2)⁻¹, 1, (b ^ 2)⁻¹, 1]

def exactTorsionDensity (h b c s : K) : K :=
  (inheritedCoframe h b).det / 2 *
    ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      exactMetricInverse h b i k * exactMetricInverse h b j l *
        etaPair (exactTorsion h b c s i j) (exactTorsion h b c s k l)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
