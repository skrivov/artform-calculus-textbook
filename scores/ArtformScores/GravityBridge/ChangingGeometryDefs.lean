import ArtformScores.GravityBridge.Defs

/-! # Coarse and subdivided incidence maps with retained detail -/

namespace Artform.Scores.GravityBridge

noncomputable section

def coarseGradient : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun u := u 1 - u 0
  map_add' u v := by simp; ring
  map_smul' c u := by simp; ring

def fineGradient : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 1 - u 0, u 2 - u 1]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp <;> ring

def vertexRestriction : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 0, u 2]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c u := by ext i; fin_cases i <;> simp

def edgeAggregation : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun e := e 0 + e 1
  map_add' u v := by simp; ring
  map_smul' c u := by simp; ring

def midpointRefinement : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun u := ![u 0, (u 0 + u 1) / 2, u 1]
  map_add' u v := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp
    all_goals ring

def edgeDetailEquiv : (Fin 2 → ℚ) ≃ₗ[ℚ] (ℚ × ℚ) where
  toFun e := (e 0 + e 1, e 0 - e 1)
  invFun p := ![(p.1 + p.2) / 2, (p.1 - p.2) / 2]
  left_inv e := by ext i; fin_cases i <;> simp
  right_inv p := by ext <;> simp <;> ring
  map_add' e f := by ext <;> simp <;> ring
  map_smul' c e := by ext <;> simp <;> ring

end

end Artform.Scores.GravityBridge
