import ArtformStages.ForcedComplex

/-!
# One rule in a solid

Finding 452 of the research ledger on a layered universe proved that on every wide complex of
squares, and in the cubic torus of side at least 3, the askings leave the kick `Cᵀ diag K C`. Here
one rule, read on paints, leaves one number there (finding 464 of the ledger):

* `SquareComplex.farWeightRead_kick`, `SquareComplex.kick_unique` (OS1): on a wide complex the far
  weight of `Cᵀ diag K C` at a flag of `σ` is `K σ`, so `K` is unique;
* `SquareComplex.one_rule_one_number`, `SquareComplex.drift_one_number` (OS2): where every corner
  has one paint, one rule read on paints leaves one `κ`, and a drift that is one rule one `λ`;
* `cube_paint_const` (OS3): every corner of the cubic torus has one paint;
* `cube_kick_one_number`, `cube_drift_one_number` (OS4): so in the cubic torus of side at least 3
  the law of light is forced up to one `κ`, unique, and one `λ`.
-/

open Matrix

namespace Artform.Stages

namespace SquareComplex

variable {f e v : Type*} (X : SquareComplex f e v)

/-- The paint of a corner of a complex: the number of faces that have it as a corner. -/
def paint [Fintype f] [DecidableEq v] (w : v) : ℕ :=
  (Finset.univ.filter fun σ => ∃ a, X.corner σ a = w).card

/-- The far weight of a kick at the flag `(σ, i)`: from the side `i` of `σ` to the side `i + 2`,
both read along the turn of `σ`. -/
def farWeightRead (M : Matrix e e ℝ) (σ : f) (i : Fin 4) : ℝ :=
  M (X.side σ i) (X.side σ (i + 2)) * Board.turnSign (X.along σ i) *
    Board.turnSign (X.along σ (i + 2))

/-- One rule read on paints: for some list of corners at each flag, the far weight at every flag is
one function of the paints of the corners on its list. -/
def OneRulePaints [Fintype f] [DecidableEq v] (M : Matrix e e ℝ) : Prop :=
  ∃ (r : ℕ) (pos : f → Fin 4 → Fin r → v) (F : (Fin r → ℕ) → ℝ),
    ∀ σ i, X.farWeightRead M σ i = F (fun k => X.paint (pos σ i k))

variable {X}

/-- **OS1.** On a wide complex the far weight of `Cᵀ diag K C` at a flag of `σ` is `K σ`. -/
theorem farWeightRead_kick [Fintype f] [DecidableEq f] [DecidableEq e] (hW : X.Wide) (K : f → ℝ)
    (σ : f) (i : Fin 4) :
    X.farWeightRead (X.incidenceᵀ * diagonal K * X.incidence) σ i = K σ := by
  have k2 : ∀ x : Fin 4, x + 2 ≠ x := by decide
  have e1 : X.incidence σ (X.side σ i) = Board.turnSign (X.along σ i) := X.incidence_of_side rfl
  have e2 : X.incidence σ (X.side σ (i + 2)) = Board.turnSign (X.along σ (i + 2)) :=
    X.incidence_of_side rfl
  have hM : (X.incidenceᵀ * diagonal K * X.incidence) (X.side σ i) (X.side σ (i + 2)) =
      Board.turnSign (X.along σ i) * K σ * Board.turnSign (X.along σ (i + 2)) := by
    rw [Matrix.mul_apply, Fintype.sum_eq_single σ]
    · simp only [mul_diagonal, transpose_apply, e1, e2]
    · intro ρ hρ
      by_cases hC : X.incidence ρ (X.side σ i) = 0
      · simp [mul_diagonal, transpose_apply, hC]
      · obtain ⟨a, haρ⟩ : ∃ a, X.side ρ a = X.side σ i := by
          by_contra hn
          push Not at hn
          exact hC (X.incidence_of_not hn)
        have hne : (σ, i) ≠ (ρ, a) := fun h => hρ (Prod.mk.inj h).1.symm
        have h0 : X.incidence ρ (X.side σ (i + 2)) = 0 :=
          X.incidence_of_not fun k => hW.side_ne haρ.symm hne (k2 i) k
        rw [h0, mul_zero]
  rw [farWeightRead, hM]
  linear_combination
    (K σ * Board.turnSign (X.along σ (i + 2)) * Board.turnSign (X.along σ (i + 2))) *
      Board.turnSign_mul_self (X.along σ i) + K σ * Board.turnSign_mul_self (X.along σ (i + 2))

/-- **OS1.** So on a wide complex two weights that give one kick are equal. -/
theorem kick_unique [Fintype f] [DecidableEq f] [DecidableEq e] (hW : X.Wide) (K K' : f → ℝ)
    (h : X.incidenceᵀ * diagonal K * X.incidence = X.incidenceᵀ * diagonal K' * X.incidence) :
    K = K' := by
  funext σ
  rw [← farWeightRead_kick hW K σ 0, ← farWeightRead_kick hW K' σ 0, h]

/-- **OS2.** On a wide complex whose corners all have one paint, a kick of reach 1 that meets A10,
A11 and one rule read on paints is `Cᵀ diag κ C` for one number `κ`. -/
theorem one_rule_one_number [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e]
    [DecidableEq v] [Nonempty f] (hW : X.Wide) (hpaint : ∀ w w' : v, X.paint w = X.paint w')
    (M : Matrix e e ℝ) (hR : X.ReachOne M) (h10 : M * X.gauge = 0) (h11 : X.gaugeᵀ * M = 0)
    (h1 : X.OneRulePaints M) :
    ∃ κ : ℝ, M = X.incidenceᵀ * diagonal (fun _ : f => κ) * X.incidence := by
  obtain ⟨K, hK⟩ := X.kick_forced hW M hR h10 h11
  obtain ⟨r, pos, F, hF⟩ := h1
  obtain ⟨σ₀⟩ := ‹Nonempty f›
  refine ⟨K σ₀, ?_⟩
  have hK' : K = fun _ => K σ₀ := by
    funext σ
    have h1 := hF σ 0
    have h2 := hF σ₀ 0
    rw [hK, farWeightRead_kick hW] at h1 h2
    rw [h1, h2]
    congr 1
    funext k
    exact hpaint _ _
  rw [hK, hK']

/-- **OS2.** A drift whose `λ` at a line is one function of the paints at its two ends is one
number where every corner has one paint. -/
theorem drift_one_number [Fintype f] [DecidableEq v] [Nonempty e]
    (hpaint : ∀ w w' : v, X.paint w = X.paint w') (l : e → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ ℓ, l ℓ = G (X.paint (X.tail ℓ)) (X.paint (X.head ℓ))) : ∃ c : ℝ, l = fun _ => c := by
  obtain ⟨ℓ₀⟩ := ‹Nonempty e›
  refine ⟨l ℓ₀, funext fun ℓ => ?_⟩
  rw [hG ℓ, hG ℓ₀, hpaint (X.tail ℓ) (X.tail ℓ₀), hpaint (X.head ℓ) (X.head ℓ₀)]

end SquareComplex

section Cube

variable (n : ℕ) [Fact (1 < n)]

/-- A shift of the cubic torus moves the corners of a face by the shift. -/
theorem cube_corner_shift (u t : CubePoint n) (k : Fin 3) (a : Fin 4) :
    (cubeComplex n).corner (u + t, k) a = (cubeComplex n).corner (u, k) a + t := by
  fin_cases a <;>
    simp only [cubeComplex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;> abel

/-- A shift of the cubic torus keeps the paint. -/
theorem cube_paint_shift [NeZero n] (w t : CubePoint n) :
    (cubeComplex n).paint (w + t) = (cubeComplex n).paint w := by
  unfold SquareComplex.paint
  refine Finset.card_bij (fun σ _ => (σ.1 - t, σ.2)) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨a, ha⟩ := hσ
    refine ⟨a, ?_⟩
    have hs := cube_corner_shift n (σ.1 - t) t σ.2 a
    rw [sub_add_cancel, Prod.mk.eta, ha] at hs
    exact (add_right_cancel hs).symm
  · intro σ _ τ _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [sub_left_inj] at h1
    exact Prod.ext h1 h2
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨a, ha⟩ := hτ
    refine ⟨(τ.1 + t, τ.2), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, by rw [cube_corner_shift, Prod.mk.eta, ha]⟩

/-- **OS3.** Every corner of the cubic torus has one paint. -/
theorem cube_paint_const [NeZero n] (w w' : CubePoint n) :
    (cubeComplex n).paint w = (cubeComplex n).paint w' := by
  have h : ∀ x : CubePoint n, (cubeComplex n).paint x = (cubeComplex n).paint 0 := fun x => by
    simpa using cube_paint_shift n 0 x
  rw [h w, h w']

/-- **OS4.** On the cubic torus of side `n ≥ 3` a kick of reach 1 that meets A10, A11 and one rule
read on paints is `Cᵀ diag κ C` for exactly one number `κ`. -/
theorem cube_kick_one_number [NeZero n] (hn : 2 < n)
    (M : Matrix (CubePoint n × Fin 3) (CubePoint n × Fin 3) ℝ)
    (hR : (cubeComplex n).ReachOne M) (h10 : M * cubeGauge n = 0)
    (h11 : (cubeGauge n)ᵀ * M = 0) (h1 : (cubeComplex n).OneRulePaints M) :
    ∃! κ : ℝ, M = (cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) *
      cubeIncidence n := by
  have hW := cubeComplex_wide n hn
  obtain ⟨κ, hκ⟩ := (cubeComplex n).one_rule_one_number hW (cube_paint_const n) M hR
    (by rw [cubeComplex_gauge]; exact h10) (by rw [cubeComplex_gauge]; exact h11) h1
  refine ⟨κ, by rw [hκ, cubeComplex_incidence], fun κ' hκ' => ?_⟩
  have h := SquareComplex.kick_unique hW (fun _ => κ') (fun _ => κ)
    (by rw [cubeComplex_incidence, ← hκ', hκ, cubeComplex_incidence])
  exact congrFun h (0, 0)

/-- **OS4.** On the cubic torus a drift that is one rule, `λ` at a line one function of the paints
at its two ends, is one number. -/
theorem cube_drift_one_number [NeZero n] (l : CubePoint n × Fin 3 → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ ℓ, l ℓ = G ((cubeComplex n).paint ((cubeComplex n).tail ℓ))
      ((cubeComplex n).paint ((cubeComplex n).head ℓ))) :
    ∃ c : ℝ, l = fun _ => c :=
  (cubeComplex n).drift_one_number (cube_paint_const n) l G hG

end Cube

end Artform.Stages
