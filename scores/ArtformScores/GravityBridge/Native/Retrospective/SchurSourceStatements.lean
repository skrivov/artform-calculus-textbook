import ArtformScores.GravityBridge.Native.Retrospective.SchurSourceDefs

/-! # Full source Schur reduction with exact reconstruction -/

namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement

open Matrix

/-- **GAC2:guarded-schur-source-reconstruction**
(full source schur reduction with exact reconstruction). -/
@[ledger "GAC2:guarded-schur-source-reconstruction"]
def schurSourceLaw : Prop :=
  ∀ (R V W : Type) [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W],
    (∀ (A : V →ₗ[R] V) (B : W →ₗ[R] V)
    (C : V →ₗ[R] W) (D E : W →ₗ[R] W)
    (_hDE : ∀ w, D (E w) = w) (_hED : ∀ w, E (D w) = w)
    (u f : V) (v a : W),
    (A f + B a = u ∧ C f + D a = v) ↔
      (schurMap A B C E f = schurRightHandSide B E u v ∧
        a = reconstructAuxiliary C E v f))

end Artform.Scores.GravityBridge.Native.Retrospective.Statement
