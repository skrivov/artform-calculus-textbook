import ArtformScores.GravityBridge.CompanionStatements
import ArtformScores.GravityBridge.Memory

/-! # Companion readout and the scope of the native leading split -/

namespace Artform.Scores.GravityBridge

variable {K Y Z : Type*} [CommRing K] [AddCommGroup Y] [AddCommGroup Z]
  [Module K Y] [Module K Z]

lemma triangular_readout_iterate (r : K) (F : (Y × Y) →ₗ[K] Z) (D : (Fin 4 → Z) →ₗ[K] Z)
    (n : ℕ) (y : Y × Y) (z : Fin 4 → Z) :
    (((triangularJet r F D)^[n]) (y, z)).1 = ((oscillator r)^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change oscillator r (((triangularJet r F D)^[n]) (y, z)).1 = _
    rw [ih]

lemma triangular_zero_graph (r : K) (F : (Y × Y) →ₗ[K] Z) (D : (Fin 4 → Z) →ₗ[K] Z)
    :
    (∀ y, triangularJet r F D (y, 0) = (oscillator r y, 0)) ↔ ∀ y, F y = 0 := by
  constructor
  · intro h y
    have he := congrArg (fun p => p.2 3) (h y)
    simpa [triangularJet, map_zero] using he
  · intro h y
    simp [triangularJet, h y, map_zero]

/-- **GAC:companion-readout** (closed head readings with a forced auxiliary tail). -/
@[ledger "GAC:companion-readout"]
theorem companionReadout : Statement.companionReadout := by
  intro K Y Z _ _ _ _ _ r F D
  exact ⟨triangular_readout_iterate r F D, triangular_zero_graph r F D⟩

/-! ## Non-vacuity -/

example : (((triangularJet (14 : ℚ) ((36 / 505 : ℚ) • LinearMap.fst ℚ ℚ ℚ)
    (0 : (Fin 4 → ℚ) →ₗ[ℚ] ℚ)) ((1, 0), 0)).2) 3 = 36 / 505 := by
  norm_num [triangularJet]

example (n : ℕ) (y : ℚ × ℚ) (z : Fin 4 → ℚ) :
    (((triangularJet (14 : ℚ) ((36 / 505 : ℚ) • LinearMap.fst ℚ ℚ ℚ)
      (0 : (Fin 4 → ℚ) →ₗ[ℚ] ℚ))^[n]) (y, z)).1 = ((oscillator (14 : ℚ))^[n]) y :=
  triangular_readout_iterate _ _ _ _ _ _

example : oscillator (1 : ℚ) = quarterTurn := by
  funext p
  simp [oscillator, quarterTurn]

example (p : ℚ × ℚ) :
    Matrix.mulVec (realize (whitehead (1 : ℚˣ)) : Matrix (Fin 2) (Fin 2) ℚ) ![p.1, p.2] =
      ![(oscillator (1 : ℚ) p).1, (oscillator (1 : ℚ) p).2] := by
  rw [whitehead_mat]
  ext i
  fin_cases i <;> simp [oscillator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Artform.Scores.GravityBridge
