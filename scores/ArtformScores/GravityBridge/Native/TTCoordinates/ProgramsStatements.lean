import ArtformScores.GravityBridge.Native.TTCoordinates.ProgramsDefs

/-! # Matched exact programs for the original temporal forcing -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates.Statement

open Matrix

/-- **GAC2:native-tt-forcing-programs**
(matched exact programs for the original temporal forcing). -/
@[ledger "GAC2:native-tt-forcing-programs"]
def programsLaw : Prop :=
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ)
    (_hs : q.transpose = q) (_ht : trace q = 0) (_hk : q *ᵥ momentum = 0),
    temporalSymbol momentum q = (84 / 505 : ℚ) * q 1 2) ∧
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ),
    evalTTExpr q literalForcingProgram = temporalSymbol momentum q) ∧
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ)
    (_hs : q.transpose = q) (_ht : trace q = 0) (_hk : q *ᵥ momentum = 0),
    evalTTExpr q contractedForcingProgram = temporalSymbol momentum q) ∧
    ((ttScales literalForcingProgram, ttAdds literalForcingProgram) = (3, 2) ∧
    (ttScales contractedForcingProgram, ttAdds contractedForcingProgram) = (1, 0)) ∧
    (∀ (i j : Fin 3) (sign : ℚ) (_hsgn : sign = 1 ∨ sign = -1),
    ¬∀ (x y : ℚ), temporalSymbol momentum (parametricTT x y) = sign * parametricTT x y i j) ∧
    (∀ (c : ℚ),
    ¬∀ (x y : ℚ), temporalSymbol momentum (parametricTT x y) = c)

end Artform.Scores.GravityBridge.Native.TTCoordinates.Statement
