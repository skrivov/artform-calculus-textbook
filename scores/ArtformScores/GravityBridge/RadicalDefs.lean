import ArtformScores.GravityBridge.Quotients
import ArtformScores.GravityBridge.CanonicalDefs

/-! # The singular model constraint quotient and induced drift -/

namespace Artform.Scores.GravityBridge

noncomputable section

def constraintEmbedding (x : GaugeSpace) : SingularPhase := ((x.1, x.2.2), (x.2.1, 0))

def reducedDrift : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) where
  toFun x := (x.1 + x.2, x.2)
  map_add' x y := by
    ext <;> simp
    all_goals ring
  map_smul' c x := by
    ext <;> simp
    all_goals ring

lemma gauge_kernel : LinearMap.ker gaugeRead = gaugeNull := by
  ext x
  simp [LinearMap.mem_ker, gaugeRead, gaugeNull, Prod.ext_iff]

lemma gauge_read_surjective : Function.Surjective gaugeRead := by
  rintro ⟨q, p⟩
  exact ⟨(q, p, 0), rfl⟩

def gaugeQuotientEquiv : (GaugeSpace ⧸ gaugeNull) ≃ₗ[ℚ] (ℚ × ℚ) :=
  (Submodule.quotEquivOfEq gaugeNull (LinearMap.ker gaugeRead) gauge_kernel.symm).trans
    (gaugeRead.quotKerEquivOfSurjective gauge_read_surjective)

lemma gauge_step_preserves : gaugeNull ≤ gaugeNull.comap gaugeStep := by
  intro x hx
  change x.1 = 0 ∧ x.2.1 = 0 at hx
  change x.1 + x.2.1 = 0 ∧ x.2.1 = 0
  simp [hx.1, hx.2]

def gaugeQuotientStep : (GaugeSpace ⧸ gaugeNull) →ₗ[ℚ] (GaugeSpace ⧸ gaugeNull) :=
  gaugeNull.mapQ gaugeNull gaugeStep gauge_step_preserves

def hiddenSource : GaugeSpace →ₗ[ℚ] ℚ where
  toFun x := x.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end Artform.Scores.GravityBridge
