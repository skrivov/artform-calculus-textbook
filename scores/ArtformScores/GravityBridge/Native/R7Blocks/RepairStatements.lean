import ArtformScores.GravityBridge.Native.R7Blocks.RepairDefs

/-! # The graph gap and whole-trace head normalization -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:whole-trace-repair-gap**
(the graph gap and whole-trace head normalization). -/
@[ledger "GAC2:whole-trace-repair-gap"]
def repairLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (a : ℝ)
    (_h11 : ‖A11‖ ≤ a) (_h12 : ‖A12‖ ≤ a) (_h22 : ‖A22‖ ≤ a)
    (_hRic : blockDefect A11 A12 A21 A22 K = 0),
    ‖A21‖ ≤ 2 * a * ‖K‖ + a * ‖K‖ ^ 2) ∧
    (∀ (a d : ℝ) (_ha : 0 < a) (_hd : 0 < d),
    0 < graphGap a d) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (a d : ℝ)
    (_ha : 0 < a) (_hd : 0 < d) (_h21 : d / 2 ≤ ‖A21‖)
    (_h11 : ‖A11‖ ≤ a) (_h12 : ‖A12‖ ≤ a) (_h22 : ‖A22‖ ≤ a)
    (_hRic : blockDefect A11 A12 A21 A22 K = 0),
    graphGap a d ≤ ‖K‖) ∧
    (∀ (K K₀ : Y →L[ℝ] Z) (c : ℝ)
    (_hK : c ≤ ‖K‖) (_h₀ : ‖K₀‖ ≤ c / 2),
    c / 2 ≤ ‖K - K₀‖) ∧
    (∀ [CompleteSpace Y] [Nontrivial Y]
    (D : Y →L[ℝ] Y) (δ : ℝ) (_hD : ‖D‖ ≤ δ) (_hδ : δ < 1),
    ∃ J : Y →L[ℝ] Y,
      (ContinuousLinearMap.id ℝ Y + D).comp J = ContinuousLinearMap.id ℝ Y ∧
      J.comp (ContinuousLinearMap.id ℝ Y + D) = ContinuousLinearMap.id ℝ Y ∧
      ‖J‖ ≤ 1 / (1 - δ)) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E Δ : Y →L[ℝ] H) (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z)
    (K : Y →L[ℝ] Z) (J : Y →L[ℝ] Y)
    (_hQE : Q.comp E = ContinuousLinearMap.id ℝ Y) (_hRE : R.comp E = K)
    (_hhead : (ContinuousLinearMap.id ℝ Y + Q.comp Δ).comp J = ContinuousLinearMap.id ℝ Y)
    (_hhead' : J.comp (ContinuousLinearMap.id ℝ Y + Q.comp Δ) = ContinuousLinearMap.id ℝ Y),
    Q.comp ((E + Δ).comp J) = ContinuousLinearMap.id ℝ Y ∧
    R.comp ((E + Δ).comp J) = (K + R.comp Δ).comp J ∧
    Set.range ((E + Δ).comp J) = Set.range (E + Δ)) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Y →L[ℝ] Z) (Δ : Y →L[ℝ] H) (R : H →L[ℝ] Z) (J : Y →L[ℝ] Y)
    (δ : ℝ) (_hR : ‖R‖ ≤ 1) (_hΔ : ‖Δ‖ ≤ δ) (_hδ : δ < 1)
    (_hJ : ‖J‖ ≤ 1 / (1 - δ)),
    ‖(K + R.comp Δ).comp J‖ ≤ (‖K‖ + δ) / (1 - δ)) ∧
    (∀ (c k δ : ℝ) (_hc : 0 ≤ c) (_hk : 0 ≤ k) (_hd : 0 ≤ δ)
    (_hsmall : δ < 1 → c ≤ (k + δ) / (1 - δ)),
    (c - k) / (1 + c) ≤ δ) ∧
    (∀ [CompleteSpace Y] [Nontrivial Y]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Y →L[ℝ] Z) (Δ : Y →L[ℝ] H) (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z)
    (c : ℝ) (_hc : 0 ≤ c) (_hQ : ‖Q‖ ≤ 1) (_hR : ‖R‖ ≤ 1)
    (_hgap : ∀ J : Y →L[ℝ] Y,
      (ContinuousLinearMap.id ℝ Y + Q.comp Δ).comp J = ContinuousLinearMap.id ℝ Y →
      J.comp (ContinuousLinearMap.id ℝ Y + Q.comp Δ) = ContinuousLinearMap.id ℝ Y →
      c ≤ ‖(K + R.comp Δ).comp J‖),
    (c-‖K‖) / (1 + c) ≤ ‖Δ‖) ∧
    (∀ (c k δ : ℝ) (_hc : 0 < c) (_hk : k ≤ c / 2)
    (_hgap : (c - k) / (1 + c) ≤ δ),
    c / (2 * (1 + c)) ≤ δ)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
