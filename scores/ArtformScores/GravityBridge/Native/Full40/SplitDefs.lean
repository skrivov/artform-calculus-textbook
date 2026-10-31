import ArtformScores.GravityBridge.Native.Full40.Projector
/-! # The exact metric and coframe Lorentz isomorphism -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
def symmetricFrames : Submodule K (Frame K) where
  carrier := {m | ∀ i j, m i j = m j i}
  zero_mem' := by intro i j; rfl
  add_mem' := by intro a b ha hb i j; simp only [Matrix.add_apply, ha i j, hb i j]
  smul_mem' := by intro c m hm i j; simp only [Matrix.smul_apply, hm i j]
def metricReadout (F : Frame K) : symmetricFrames (K := K) :=
  ⟨metricVariation F, by intro i j; simp only [metricVariation]; ring⟩
def coframeReconstruct (m : Frame K) (w : Biv K) : Frame K :=
  (1 / 2 : K) • frameGram m + lie w
end Artform.Scores.GravityBridge.Native.Full40
