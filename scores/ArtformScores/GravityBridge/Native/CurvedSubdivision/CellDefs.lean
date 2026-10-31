import ArtformScores.GravityBridge.Native.CurvedSubdivision.Mean
import ArtformScores.GravityBridge.Native.CurvedSubdivision.Torsion
import ArtformScores.GravityBridge.Native.CurvedSubdivision.Words

/-! # Complete current cubical cell law and symmetric merge defect -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40

variable {K : Type*} [Field K] [CharZero K]

def fullCornerBivector (h b : K) (r : Fin 6) (P : Frame K) : Biv K :=
  let E := inheritedCoframe h b
  complementSign (K := K) r • wedge
    (P *ᵥ (fun a => E a (complementFirst r)))
    (P *ᵥ (fun a => E a (complementSecond r)))

def fullOriginalMean (h b c0 s0 c1 s1 : K) (r : Fin 6) : Biv K :=
  let i := faceFirst r
  let l := faceSecond r
  (1 / 4 : K) • fullCornerBivector h b r 1 +
    (1 / 4 : K) • fullCornerBivector h b r (reversedEdge c0 s0 c1 s1 false i) +
    (1 / 4 : K) • fullCornerBivector h b r (reversedEdge c0 s0 c1 s1 false l) +
    (1 / 8 : K) • fullCornerBivector h b r
      (reversedEdge c0 s0 c1 s1 false i * reversedEdge c0 s0 c1 s1 (i==0) l) +
    (1 / 8 : K) • fullCornerBivector h b r
      (reversedEdge c0 s0 c1 s1 false l * reversedEdge c0 s0 c1 s1 (l==0) i)

def fullOriginalCurvature (h b c0 s0 c1 s1 : K) : K :=
  ∑ r : Fin 6, bivPair (fullOriginalMean h b c0 s0 c1 s1 r)
    (internalStar (lieCoordinates ((-1 / 2 : K) •
      (basedPlaquette c0 s0 c1 s1 r - reversePlaquette c0 s0 c1 s1 r))))

def fullOriginalCell (h b c0 s0 c1 s1 : K) : K :=
  fullOriginalCurvature h b c0 s0 c1 s1 + (1 / 101 : K) * exactTorsionDensity h b c0 s0

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
