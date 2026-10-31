import ArtformScores.GravityBridge.ForcedGraphStatements

/-! # Nonzero auxiliary jets can be determined by the visible pair -/

namespace Artform.Scores.GravityBridge

noncomputable section

variable {K Y Z : Type*} [Field K] [AddCommGroup Y] [AddCommGroup Z] [Module K Y] [Module K Z]

lemma forced_jet_invariant (r : K) (F : Y →ₗ[K] Z) (hr : r ≠ 0) (y : Y × Y) :
    triangularJet r (F.comp (LinearMap.fst K Y Y)) 0 (y, forcedJetGraph r F y) =
      (oscillator r y, forcedJetGraph r F (oscillator r y)) := by
  apply Prod.ext
  · rfl
  · funext i
    have h1 : (r ^ 2)⁻¹ * r = r⁻¹ := by field_simp
    have h2 : r⁻¹ * r = 1 := inv_mul_cancel₀ hr
    fin_cases i <;>
      simp [triangularJet, forcedJetGraph, oscillator, map_smul, smul_smul, h1, h2,
      neg_mul]

lemma forced_jet_powers (r : K) (F : Y →ₗ[K] Z) (hr : r ≠ 0)
    (n : ℕ) (y : Y × Y) :
    (triangularJet r (F.comp (LinearMap.fst K Y Y)) 0)^[n] (y, forcedJetGraph r F y) =
      ((oscillator r)^[n] y, forcedJetGraph r F ((oscillator r)^[n] y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact forced_jet_invariant r F hr _

lemma forced_graph_zero_iff (r : K) (F : Y →ₗ[K] Z) (hr : r ≠ 0) (y : Y × Y) :
    forcedJetGraph r F y = 0 ↔ F y.1 = 0 ∧ F y.2 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have hi : (r⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hr)
    have hp0 : (r⁻¹) ^ 2 • F y.1 = 0 := h0
    have hp1 : (r⁻¹) ^ 2 • F y.2 = 0 := h1
    exact ⟨(smul_eq_zero.mp hp0).resolve_left hi, (smul_eq_zero.mp hp1).resolve_left hi⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [forcedJetGraph, h0, h1]

/-- **GAC:forced-jet-graph** (operator powers on a specified leading graph). -/
@[ledger "GAC:forced-jet-graph"]
theorem forcedGraphLaw : Statement.forcedGraphLaw := by
  intro K Y Z _ _ _ _ _ r F hr
  exact ⟨forced_jet_invariant r F hr, forced_jet_powers r F hr, forced_graph_zero_iff r F hr⟩

/-! ## Non-vacuity -/

example : forcedJetGraph (14 : ℂ)
    (((Complex.I * (36 / 505 : ℂ))) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (1, 0) =
      ![Complex.I * (9 / 24745 : ℂ), 0, -Complex.I * (18 / 3535 : ℂ), 0] := by
  ext i
  fin_cases i <;> norm_num [forcedJetGraph] <;> ring

example : forcedJetGraph (14 : ℚ) ((36 / 505 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (1, 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [forcedJetGraph] at h0

end

end Artform.Scores.GravityBridge
