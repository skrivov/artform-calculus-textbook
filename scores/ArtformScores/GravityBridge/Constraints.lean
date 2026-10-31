import ArtformScores.GravityBridge.ConstraintStatements

/-! # A singular quadratic action gives constrained multivalued evolution -/

namespace Artform.Scores.GravityBridge

lemma singular_first_variation (x y dx dy : SingularConfig) (e : ℚ) :
    singularAction (x + e • dx) (y + e • dy) = singularAction x y +
      e * (-boundaryPair (preMomentum x y) dx + boundaryPair (postMomentum x y) dy) +
        e ^ 2 * (dy.1 - dx.1) ^ 2 / 2 := by
  dsimp [singularAction, boundaryPair, preMomentum, postMomentum]
  ring

lemma singular_relation_iff (x p y q : SingularConfig) :
    singularRelation (x, p) (y, q) ↔
      p.2 = 0 ∧ q.2 = 0 ∧ q.1 = p.1 ∧ y.1 = x.1 + p.1 := by
  constructor
  · rintro ⟨hp, hq⟩
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    have hq1 := congrArg Prod.fst hq
    have hq2 := congrArg Prod.snd hq
    dsimp [preMomentum, postMomentum] at hp1 hp2 hq1 hq2
    exact ⟨hp2, hq2, hq1.trans hp1.symm, by linarith⟩
  · rintro ⟨hp2, hq2, hqp, hy⟩
    constructor
    · apply Prod.ext
      · change p.1 = y.1 - x.1
        linarith
      · exact hp2
    · apply Prod.ext
      · change q.1 = y.1 - x.1
        linarith
      · exact hq2

lemma corner_stationary_iff (x y z : SingularConfig) :
    cornerStationary x y z ↔ x.1 - 2 * y.1 + z.1 = 0 := by
  constructor
  · intro h
    have hd := h (1, 0)
    dsimp [boundaryPair, preMomentum, postMomentum] at hd
    linarith
  · intro h d
    dsimp [boundaryPair, preMomentum, postMomentum]
    have hh : y.1 - x.1 = z.1 - y.1 := by linarith
    rw [hh]

lemma two_step_variation (x y z d : SingularConfig) (e : ℚ) :
    singularAction x (y + e • d) + singularAction (y + e • d) z =
      singularAction x y + singularAction y z +
        e * (2 * y.1 - x.1 - z.1) * d.1 + e ^ 2 * d.1 ^ 2 := by
  dsimp [singularAction]
  ring

lemma relation_gluing (x y z : SingularConfig) :
    (∃ px py pz, singularRelation (x, px) (y, py) ∧
      singularRelation (y, py) (z, pz)) ↔ cornerStationary x y z := by
  constructor
  · rintro ⟨px, py, pz, hxy, hyz⟩
    rw [corner_stationary_iff]
    have hp : postMomentum x y = preMomentum y z := hxy.2.symm.trans hyz.1
    have h1 := congrArg Prod.fst hp
    dsimp [postMomentum, preMomentum] at h1
    linarith
  · intro h
    refine ⟨preMomentum x y, postMomentum x y, postMomentum y z, ⟨rfl, rfl⟩, ?_, rfl⟩
    apply Prod.ext
    · have hs := (corner_stationary_iff x y z).mp h
      dsimp [preMomentum, postMomentum]
      linarith
    · rfl

/-- **GAC:singular-action** (variation, momentum constraints and relational gluing). -/
@[ledger "GAC:singular-action"]
theorem singularActionLaw : Statement.singularActionLaw := by
  exact ⟨singular_first_variation, singular_relation_iff, corner_stationary_iff,
    two_step_variation, relation_gluing⟩

/-! ## Non-vacuity -/

example : singularRelation ((0, 7), (1, 0)) ((1, 11), (1, 0)) := by
  norm_num [singularRelation, preMomentum, postMomentum]

example : singularRelation ((0, 0), (1, 0)) ((1, 0), (1, 0)) ∧
    singularRelation ((0, 0), (1, 0)) ((1, 1), (1, 0)) ∧
    (((1, 0), (1, 0)) : SingularPhase) ≠ ((1, 1), (1, 0)) := by
  norm_num [singularRelation, preMomentum, postMomentum]

example : cornerStationary (0, 2) (1, 99) (2, -3) := by
  rw [corner_stationary_iff]
  norm_num

end Artform.Scores.GravityBridge
