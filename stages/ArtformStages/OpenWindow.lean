import ArtformStages.ForcedComplex
import ArtformStages.EulerCount

/-!
# The window

The book runs its light on the torus and on windows with open edges (finding 453 of the research
ledger on a layered universe). Here the window of `a` by `b` squares is a complex of squares
(finding 452), on which the law of light is forced, and it has no harmonic field (finding 463 of
the ledger):

* `windowComplex`, `window_incidence_mul_gauge` (WN1): the window, whose maps close up;
* `window_wide`, `window_kick_forced` (WN2): it is wide, so the askings leave `Cᵀ diag K C`;
* `window_gauge_ker`, `window_transpose_ker` (WN3): `G φ = 0` only for constants, and `Cᵀ ψ = 0`
  only for `ψ = 0`;
* `window_harmonic_finrank`, `window_no_harmonic` (WN4): so it has no harmonic field;
* `window_hodge`, `window_divergence_sum` (WN5): every field is one gradient and one transverse
  field, and the charges sum to `0`.
-/

open Matrix Module

namespace Artform.Stages

variable (a b : ℕ)

/-- The corners of the window: the points `(i, j)` with `i ≤ a` and `j ≤ b`. -/
abbrev WindowCorner := Fin (a + 1) × Fin (b + 1)

/-- The lines of the window: `inl (i, j)` across, from `(i, j)` to `(i + 1, j)`, and `inr (i, j)`
up, from `(i, j)` to `(i, j + 1)`. -/
abbrev WindowLine := (Fin a × Fin (b + 1)) ⊕ (Fin (a + 1) × Fin b)

/-- The squares of the window. -/
abbrev WindowSquare := Fin a × Fin b

/-- **WN1.** The window of `a` by `b` squares with open edges, as a complex of squares: the square
`(i, j)` has the corners `(i, j)`, `(i + 1, j)`, `(i + 1, j + 1)`, `(i, j + 1)` in its turn. -/
def windowComplex : SquareComplex (WindowSquare a b) (WindowLine a b) (WindowCorner a b) where
  corner σ := ![(σ.1.castSucc, σ.2.castSucc), (σ.1.succ, σ.2.castSucc), (σ.1.succ, σ.2.succ),
    (σ.1.castSucc, σ.2.succ)]
  tail := Sum.elim (fun x => (x.1.castSucc, x.2)) (fun x => (x.1, x.2.castSucc))
  head := Sum.elim (fun x => (x.1.succ, x.2)) (fun x => (x.1, x.2.succ))
  side σ := ![.inl (σ.1, σ.2.castSucc), .inr (σ.1.succ, σ.2), .inl (σ.1, σ.2.succ),
    .inr (σ.1.castSucc, σ.2)]
  along _ := ![true, true, false, false]
  corner_injective σ := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [Prod.ext_iff, Fin.ext_iff] at h ⊢
  tail_side σ i := by fin_cases i <;> simp
  head_side σ i := by fin_cases i <;> simp

/-- **WN1.** The maps of the window close up: `C G = 0`. -/
theorem window_incidence_mul_gauge :
    (windowComplex a b).incidence * (windowComplex a b).gauge = 0 :=
  (windowComplex a b).incidence_mul_gauge

/-- **WN2.** The window is wide. -/
theorem window_wide : (windowComplex a b).Wide := by
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ i j h hne p q hc
  fin_cases i <;> fin_cases j <;>
    simp only [windowComplex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc,
      Fin.val_succ] at h <;>
    fin_cases p <;> fin_cases q <;>
    simp only [windowComplex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hc <;>
    first
    | decide
    | (exfalso; omega)
    | (exfalso; apply hne; simp only [Prod.mk.injEq, Fin.ext_iff, and_true]; omega)

/-- **WN2.** So on the window a kick of reach 1 that meets A10 and A11 is `Cᵀ diag K C`. -/
theorem window_kick_forced (M : Matrix (WindowLine a b) (WindowLine a b) ℝ)
    (hR : (windowComplex a b).ReachOne M) (h10 : M * (windowComplex a b).gauge = 0)
    (h11 : (windowComplex a b).gaugeᵀ * M = 0) :
    ∃ K : WindowSquare a b → ℝ,
      M = (windowComplex a b).incidenceᵀ * diagonal K * (windowComplex a b).incidence :=
  (windowComplex a b).kick_forced (window_wide a b) M hR h10 h11

/-- `G φ` at a line of the window is `φ` at its head less `φ` at its tail. -/
theorem window_gauge_mulVec (φ : WindowCorner a b → ℝ) (ℓ : WindowLine a b) :
    ((windowComplex a b).gauge *ᵥ φ) ℓ =
      φ ((windowComplex a b).head ℓ) - φ ((windowComplex a b).tail ℓ) := by
  simp [mulVec, dotProduct, SquareComplex.gauge, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- **WN3.** On the window `G φ = 0` exactly when `φ` is the same at every corner. -/
theorem window_gauge_ker (φ : WindowCorner a b → ℝ) :
    (windowComplex a b).gauge *ᵥ φ = 0 ↔ ∀ w, φ w = φ 0 := by
  constructor
  · intro h
    have hx : ∀ (i : Fin a) (j : Fin (b + 1)), φ (i.succ, j) = φ (i.castSucc, j) := fun i j => by
      have := congrFun h (.inl (i, j))
      rw [window_gauge_mulVec, Pi.zero_apply, sub_eq_zero] at this
      exact this
    have hy : ∀ (i : Fin (a + 1)) (j : Fin b), φ (i, j.succ) = φ (i, j.castSucc) := fun i j => by
      have := congrFun h (.inr (i, j))
      rw [window_gauge_mulVec, Pi.zero_apply, sub_eq_zero] at this
      exact this
    have col : ∀ j : Fin (b + 1), φ (0, j) = φ 0 := by
      intro j
      induction j using Fin.induction with
      | zero => rfl
      | succ j ih => rw [hy 0 j, ih]
    intro w
    obtain ⟨i, j⟩ := w
    induction i using Fin.induction with
    | zero => exact col j
    | succ i ih => rw [hx i j, ih]
  · intro h
    funext ℓ
    rw [window_gauge_mulVec, h, h ((windowComplex a b).tail ℓ), sub_self, Pi.zero_apply]

/-- **WN3.** On the window `Cᵀ ψ = 0` only for `ψ = 0`: an open edge leaves no square free. -/
theorem window_transpose_ker (ψ : WindowSquare a b → ℝ) :
    (windowComplex a b).incidenceᵀ *ᵥ ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    have key : ∀ k : ℕ, ∀ σ : WindowSquare a b, (σ.1 : ℕ) = k → ψ σ = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro σ hσ
        have hz := congrFun h (.inr (σ.1.castSucc, σ.2))
        have hsum : ((windowComplex a b).incidenceᵀ *ᵥ ψ) (.inr (σ.1.castSucc, σ.2)) =
            (windowComplex a b).incidence σ (.inr (σ.1.castSucc, σ.2)) * ψ σ := by
          simp only [mulVec, dotProduct, transpose_apply]
          refine Fintype.sum_eq_single σ fun τ hτ => ?_
          by_cases hk : ∃ c, (windowComplex a b).side τ c = .inr (σ.1.castSucc, σ.2)
          · obtain ⟨c, hc⟩ := hk
            fin_cases c <;>
              simp only [windowComplex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
                Matrix.cons_val, reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq] at hc
            · have hv := congrArg Fin.val hc.1
              simp only [Fin.val_succ, Fin.val_castSucc] at hv
              rw [ih (τ.1 : ℕ) (by omega) τ rfl, mul_zero]
            · exact absurd (Prod.ext (Fin.castSucc_injective _ hc.1) hc.2) hτ
          · rw [(windowComplex a b).incidence_of_not (fun c hc => hk ⟨c, hc⟩), zero_mul]
        have hC : (windowComplex a b).incidence σ (.inr (σ.1.castSucc, σ.2)) = -1 := by
          have h3 := (windowComplex a b).incidence_of_side (σ := σ) (i := 3)
            (ℓ := .inr (σ.1.castSucc, σ.2)) rfl
          rw [h3]
          rfl
        rw [hsum, hC, Pi.zero_apply] at hz
        linarith
    funext σ
    exact key _ σ rfl
  · rintro rfl
    exact mulVec_zero _

/-- **WN4.** The window has no harmonic field: their space has the dimension `0`. -/
theorem window_harmonic_finrank :
    finrank ℝ ↥(LinearMap.ker (windowComplex a b).gaugeᵀ.mulVecLin ⊓
      LinearMap.ker (windowComplex a b).incidence.mulVecLin) = 0 := by
  have h := harmonic_count (windowComplex a b).incidence (windowComplex a b).gauge
    (window_incidence_mul_gauge a b)
  have hG : (windowComplex a b).gauge.rank + 1 = (a + 1) * (b + 1) := by
    have hker : LinearMap.ker (windowComplex a b).gauge.mulVecLin =
        Submodule.span ℝ {fun _ => (1 : ℝ)} := by
      ext φ
      rw [LinearMap.mem_ker, Submodule.mem_span_singleton, Matrix.mulVecLin_apply,
        window_gauge_ker]
      constructor
      · intro hφ
        exact ⟨φ 0, funext fun w => by simp [hφ w]⟩
      · rintro ⟨c, rfl⟩ w
        rfl
    have h1 : finrank ℝ (LinearMap.ker (windowComplex a b).gauge.mulVecLin) = 1 := by
      rw [hker]
      refine finrank_span_singleton fun h0 => ?_
      have := congrFun h0 0
      simp at this
    have hT := LinearMap.finrank_range_add_finrank_ker (windowComplex a b).gauge.mulVecLin
    rw [h1, Module.finrank_fintype_fun_eq_card] at hT
    simp only [Fintype.card_prod, Fintype.card_fin] at hT
    exact hT
  have hC : (windowComplex a b).incidence.rank = a * b := by
    have hker : LinearMap.ker (windowComplex a b).incidenceᵀ.mulVecLin = ⊥ := by
      refine LinearMap.ker_eq_bot'.mpr fun ψ hψ => ?_
      rw [Matrix.mulVecLin_apply] at hψ
      exact (window_transpose_ker a b ψ).mp hψ
    have hT := LinearMap.finrank_range_add_finrank_ker (windowComplex a b).incidenceᵀ.mulVecLin
    rw [hker, finrank_bot, Module.finrank_fintype_fun_eq_card, add_zero] at hT
    simp only [Fintype.card_prod, Fintype.card_fin] at hT
    rw [← rank_transpose]
    exact hT
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  have e : a * (b + 1) + (a + 1) * b + 1 = (a + 1) * (b + 1) + a * b := by ring
  omega

/-- **WN4.** On the window a field with no charge and no curl is `0`. -/
theorem window_no_harmonic (h : WindowLine a b → ℝ) (h1 : (windowComplex a b).gaugeᵀ *ᵥ h = 0)
    (h2 : (windowComplex a b).incidence *ᵥ h = 0) : h = 0 := by
  have hbot := Submodule.finrank_eq_zero.mp (window_harmonic_finrank a b)
  have hmem : h ∈ LinearMap.ker (windowComplex a b).gaugeᵀ.mulVecLin ⊓
      LinearMap.ker (windowComplex a b).incidence.mulVecLin :=
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr h1, LinearMap.mem_ker.mpr h2⟩
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℝ).mp hmem

/-- **WN5.** Every field on the window is one gradient and one transverse field, each unique. -/
theorem window_hodge (E : WindowLine a b → ℝ) :
    (∃ φ ψ, E = (windowComplex a b).gauge *ᵥ φ + (windowComplex a b).incidenceᵀ *ᵥ ψ) ∧
      ∀ φ ψ φ' ψ', (windowComplex a b).gauge *ᵥ φ + (windowComplex a b).incidenceᵀ *ᵥ ψ =
          (windowComplex a b).gauge *ᵥ φ' + (windowComplex a b).incidenceᵀ *ᵥ ψ' →
        (windowComplex a b).gauge *ᵥ φ = (windowComplex a b).gauge *ᵥ φ' ∧
          (windowComplex a b).incidenceᵀ *ᵥ ψ = (windowComplex a b).incidenceᵀ *ᵥ ψ' := by
  refine ⟨?_, fun φ ψ φ' ψ' heq => ?_⟩
  · obtain ⟨φ, ψ, h, hE, h1, h2⟩ := hodge_exists (windowComplex a b).incidence
      (windowComplex a b).gauge (window_incidence_mul_gauge a b) E
    refine ⟨φ, ψ, ?_⟩
    rw [hE, window_no_harmonic a b h h1 h2, add_zero]
  · have := hodge_unique (windowComplex a b).incidence (windowComplex a b).gauge
      (window_incidence_mul_gauge a b) φ φ' ψ ψ' 0 0 ⟨mulVec_zero _, mulVec_zero _⟩
      ⟨mulVec_zero _, mulVec_zero _⟩ (by rw [add_zero, add_zero]; exact heq)
    exact ⟨this.1, this.2.1⟩

/-- **WN5.** On the window the charges of every field sum to `0` over the corners. -/
theorem window_divergence_sum (E : WindowLine a b → ℝ) :
    ∑ w, divergence (windowComplex a b).gauge E w = 0 := by
  simp only [divergence, Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero, mulVec, dotProduct,
    transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [← Finset.sum_mul]
  simp [SquareComplex.gauge, Finset.sum_sub_distrib]

end Artform.Stages
