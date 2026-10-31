import ArtformScores.GravityBridge.Native.CurvedSubdivision.GeometryDefs

/-! # Actual sourced two-cube incidence and inherited coframes -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-two-cube-incidence**
(actual sourced two-cube incidence and inherited coframes). -/
@[ledger "GAC2:native-two-cube-incidence"]
def geometryLaw : Prop :=
    ((cubeCount 0, cubeCount 1, cubeCount 2, cubeCount 3, cubeCount 4) = (16, 32, 24, 8, 1) ∧
    (splitCount 0, splitCount 1, splitCount 2, splitCount 3, splitCount 4) = (24, 52, 42, 15, 2)) ∧
    (∀ (K : Type) [Field K] [CharZero K] (h b : K),
    inheritedCoframe h b * Matrix.diagonal ![1 / 2, 1, 1, 1] = inheritedCoframe (h / 2) b ∧
    (inheritedCoframe (h / 2) b).det + (inheritedCoframe (h / 2) b).det =
      (inheritedCoframe h b).det) ∧
    (∀ (K : Type) [Field K] [CharZero K] (h b : K) (i : Fin 3) (a : Fin 4),
    inheritedCoframe (h / 2) b a i.succ = inheritedCoframe h b a i.succ)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
