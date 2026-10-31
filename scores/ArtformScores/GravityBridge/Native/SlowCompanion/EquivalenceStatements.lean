import ArtformScores.GravityBridge.Native.SlowCompanion.EquivalenceDefs

/-! # Admitted source and observation agreement -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion.Statement

/-- **GAC2:source-observation-preparation-equivalence**
(admitted source and observation agreement). -/
@[ledger "GAC2:source-observation-preparation-equivalence"]
def equivalenceLaw : Prop :=
  ∀ (K H S O F : Type) [Field K] [AddCommGroup H] [Module K H] [AddCommGroup S] [Module K S]
    [AddCommGroup O] [Module K O] [AddCommGroup F] [Module K F],
    (∀ (W : Submodule K H) (J : H →ₗ[K] F)
    (read : H →ₗ[K] O) (U V : S →ₗ[K] H) (_hU : ∀ s, U s ∈ W),
    (∀ s, V s ∈ W ∧ J (V s) = J (U s) ∧ read (V s) = read (U s)) ↔
      ∀ s, (V - U) s ∈ compatibleChanges W J read) ∧
    (∀ (W : Submodule K H) (trace : H →ₗ[K] S)
    (recover : S →ₗ[K] H) (_hrec : ∀ w ∈ W, recover (trace w) = w)
    (U V : O →ₗ[K] H) (_hU : ∀ s, U s ∈ W) (_hV : ∀ s, V s ∈ W)
    (_htrace : trace.comp U = trace.comp V),
    U = V) ∧
    ((LinearMap.fst ℚ ℚ ℚ) (0, 1) = 0 ∧
    (LinearMap.snd ℚ ℚ ℚ) (0, 1) ≠ 0)

end Artform.Scores.GravityBridge.Native.SlowCompanion.Statement
