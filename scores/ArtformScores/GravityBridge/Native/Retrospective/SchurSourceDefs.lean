import ArtformScores.GravityBridge.Defs

/-! # Full source Schur reduction with exact reconstruction -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix

variable {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

def schurMap (A : V →ₗ[R] V) (B : W →ₗ[R] V) (C : V →ₗ[R] W)
    (E : W →ₗ[R] W) : V →ₗ[R] V := A - B.comp (E.comp C)

def schurRightHandSide (B : W →ₗ[R] V) (E : W →ₗ[R] W) (u : V) (v : W) : V :=
  u - B (E v)

def reconstructAuxiliary (C : V →ₗ[R] W) (E : W →ₗ[R] W) (v : W) (f : V) : W :=
  E (v - C f)

end Artform.Scores.GravityBridge.Native.Retrospective
