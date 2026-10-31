import ArtformScores.GravityBridge.Defs

/-! # A singular quadratic action and its boundary momenta -/

namespace Artform.Scores.GravityBridge

abbrev SingularConfig := ℚ × ℚ
abbrev SingularPhase := SingularConfig × SingularConfig

def singularAction (x y : SingularConfig) : ℚ := (y.1 - x.1) ^ 2 / 2

def preMomentum (x y : SingularConfig) : SingularConfig := (y.1 - x.1, 0)

def postMomentum (x y : SingularConfig) : SingularConfig := (y.1 - x.1, 0)

def boundaryPair (p v : SingularConfig) : ℚ := p.1 * v.1 + p.2 * v.2

def singularRelation : Evolution SingularPhase SingularPhase :=
  fun a b => a.2 = preMomentum a.1 b.1 ∧ b.2 = postMomentum a.1 b.1

def cornerStationary (x y z : SingularConfig) : Prop :=
  ∀ d : SingularConfig,
    boundaryPair (postMomentum x y) d = boundaryPair (preMomentum y z) d

end Artform.Scores.GravityBridge
