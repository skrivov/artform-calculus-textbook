import ArtformStages.Forced

/-!
# One rule

Finding 421 of the research ledger on a layered universe proved on paper (its T331(b)) that the
charter's one rule, with A10 and A11, leaves the kick one number on each class of squares. Here it
is proved in Lean, with one rule read on the far weights (finding 449 of the ledger):

* `Board.farWeightRead_kick` (OR1): on a wide board the far weight of `Cᵀ diag K C` at a flag of
  `σ`, read along the turn of `σ`, is `K σ`;
* `Board.one_rule_flags` (OR2): so a kick of reach 1 that meets A10, A11 and one rule for the far
  weights is `Cᵀ diag K C` with `K σ = K τ` whenever a flag of `σ` and a flag of `τ` have the same
  six paints, read the same way or one of them turned over;
* `Board.one_rule_classes` (OR3): `K` is the same on each class of squares;
* `Board.one_rule_one_number`, `Board.drift_one_number` (OR4, OR5): where every corner has one
  paint, the kick is one number times `Cᵀ C` and a drift that is one rule is one number.
-/

open Matrix

namespace Artform.Stages

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- The paint of a corner: the number of squares that have it as a corner. -/
def paint [Fintype f] [DecidableEq v] (w : v) : ℕ :=
  (Finset.univ.filter fun σ => ∃ a, B.corner σ a = w).card

/-- The other flag of the line at the side `i` of `σ`: the one that runs the other way. -/
noncomputable def otherFlag (σ : f) (i : Fin 4) : f × Fin 4 :=
  Classical.choose (B.once_each_way (B.side σ i) (!B.along σ i)).exists

theorem otherFlag_side (σ : f) (i : Fin 4) :
    B.side (B.otherFlag σ i).1 (B.otherFlag σ i).2 = B.side σ i :=
  (Classical.choose_spec (B.once_each_way (B.side σ i) (!B.along σ i)).exists).1

theorem otherFlag_along (σ : f) (i : Fin 4) :
    B.along (B.otherFlag σ i).1 (B.otherFlag σ i).2 = !B.along σ i :=
  (Classical.choose_spec (B.once_each_way (B.side σ i) (!B.along σ i)).exists).2

/-- The six paints of the flag `(σ, i)`, read along the turn of `σ` from its corner `i`: the
paints of its four corners, then those of the two far corners of the other square at the line. -/
noncomputable def flagPaints [Fintype f] [DecidableEq v] (σ : f) (i : Fin 4) : Fin 6 → ℕ :=
  ![B.paint (B.corner σ i), B.paint (B.corner σ (i + 1)), B.paint (B.corner σ (i + 2)),
    B.paint (B.corner σ (i + 3)), B.paint (B.corner (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 2)),
    B.paint (B.corner (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 3))]

/-- Turning a flag over: its six paints read from the other end of the line. -/
def turnOver (p : Fin 6 → ℕ) : Fin 6 → ℕ := ![p 1, p 0, p 3, p 2, p 5, p 4]

/-- The far weight of a kick at the flag `(σ, i)`: from the line to the far side of `σ`, both
read along the turn of `σ`. -/
def farWeightRead (M : Matrix e e ℝ) (σ : f) (i : Fin 4) : ℝ :=
  M (B.side σ i) (B.side σ (i + 2)) * turnSign (B.along σ i) * turnSign (B.along σ (i + 2))

/-- One rule for the far weights: one function of six paints gives the far weight at every flag,
from its six paints read either way. -/
def OneRuleFar [Fintype f] [DecidableEq v] (M : Matrix e e ℝ) : Prop :=
  ∃ F : (Fin 6 → ℕ) → ℝ, ∀ σ i, B.farWeightRead M σ i = F (B.flagPaints σ i) ∧
    B.farWeightRead M σ i = F (turnOver (B.flagPaints σ i))

variable {B}

/-- **OR1.** On a wide board the far weight of `Cᵀ diag K C` at a flag of `σ` is `K σ`. -/
theorem farWeightRead_kick [Fintype f] [DecidableEq f] [DecidableEq e] (hW : B.Wide) (K : f → ℝ)
    (σ : f) (i : Fin 4) : B.farWeightRead (B.incidenceᵀ * diagonal K * B.incidence) σ i = K σ := by
  have k2 : ∀ x : Fin 4, x + 2 ≠ x := by decide
  have hs : B.side (B.otherFlag σ i).1 (B.otherFlag σ i).2 = B.side σ i := B.otherFlag_side σ i
  have hne : B.along σ i ≠ B.along (B.otherFlag σ i).1 (B.otherFlag σ i).2 := by
    rw [B.otherFlag_along]
    cases B.along σ i <;> decide
  have e1 : B.incidence σ (B.side σ i) = turnSign (B.along σ i) := B.incidence_of_side rfl
  have e2 : B.incidence σ (B.side σ (i + 2)) = turnSign (B.along σ (i + 2)) :=
    B.incidence_of_side rfl
  have hM : (B.incidenceᵀ * diagonal K * B.incidence) (B.side σ i) (B.side σ (i + 2)) =
      turnSign (B.along σ i) * K σ * turnSign (B.along σ (i + 2)) := by
    rw [Matrix.mul_apply, Fintype.sum_eq_single σ]
    · simp only [mul_diagonal, transpose_apply, e1, e2]
    · intro ρ hρ
      by_cases hC : B.incidence ρ (B.side σ i) = 0
      · simp [mul_diagonal, transpose_apply, hC]
      · obtain ⟨a, haρ⟩ : ∃ a, B.side ρ a = B.side σ i := by
          by_contra hn
          push Not at hn
          exact hC (B.incidence_of_not hn)
        rcases B.flag_cover hs.symm hne haρ with ⟨h', -⟩ | ⟨h', -⟩
        · exact absurd h' hρ
        · have h0 : B.incidence ρ (B.side σ (i + 2)) = 0 :=
            B.incidence_of_not (h' ▸ hW.side_ne hs.symm hne (k2 i))
          rw [h0, mul_zero]
  rw [farWeightRead, hM]
  linear_combination
    (K σ * turnSign (B.along σ (i + 2)) * turnSign (B.along σ (i + 2))) *
      turnSign_mul_self (B.along σ i) + K σ * turnSign_mul_self (B.along σ (i + 2))

/-- **OR2.** On a wide board, a kick of reach 1 that meets A10, A11 and one rule for the far weights
is `Cᵀ diag K C` with `K σ = K τ` whenever a flag of `σ` and a flag of `τ` have the same six paints,
read the same way or one of them turned over. -/
theorem one_rule_flags [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (hW : B.Wide) (M : Matrix e e ℝ) (hR : B.ReachOne M) (h10 : M * B.gauge = 0)
    (h11 : B.gaugeᵀ * M = 0) (h1 : B.OneRuleFar M) :
    ∃ K : f → ℝ, M = B.incidenceᵀ * diagonal K * B.incidence ∧
      ∀ σ τ i j, (B.flagPaints σ i = B.flagPaints τ j ∨
        B.flagPaints σ i = turnOver (B.flagPaints τ j)) → K σ = K τ := by
  obtain ⟨K, hK⟩ := B.kick_forced hW M hR h10 h11
  obtain ⟨F, hF⟩ := h1
  have hread : ∀ ρ a, K ρ = B.farWeightRead M ρ a := fun ρ a => by
    rw [hK, farWeightRead_kick hW K ρ a]
  refine ⟨K, hK, fun σ τ i j h => ?_⟩
  rcases h with h | h
  · rw [hread σ i, (hF σ i).1, h, ← (hF τ j).1, ← hread τ j]
  · rw [hread σ i, (hF σ i).1, h, ← (hF τ j).2, ← hread τ j]

/-- **OR3.** So `K` is the same on each class of squares, the classes that such pairs of flags
generate. -/
theorem one_rule_classes [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (hW : B.Wide) (M : Matrix e e ℝ) (hR : B.ReachOne M) (h10 : M * B.gauge = 0)
    (h11 : B.gaugeᵀ * M = 0) (h1 : B.OneRuleFar M) :
    ∃ K : f → ℝ, M = B.incidenceᵀ * diagonal K * B.incidence ∧
      ∀ σ τ, Relation.EqvGen (fun ρ ρ' => ∃ i j, B.flagPaints ρ i = B.flagPaints ρ' j ∨
        B.flagPaints ρ i = turnOver (B.flagPaints ρ' j)) σ τ → K σ = K τ := by
  obtain ⟨K, hK, hflags⟩ := one_rule_flags hW M hR h10 h11 h1
  refine ⟨K, hK, fun σ τ h => ?_⟩
  induction h with
  | rel x y hxy =>
    obtain ⟨i, j, hij⟩ := hxy
    exact hflags x y i j hij
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- **OR4.** On a wide board whose corners all have one paint, such a kick is `Cᵀ diag κ C` with
one number `κ` on every square. -/
theorem one_rule_one_number [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e]
    [DecidableEq v] [Nonempty f] (hW : B.Wide) (hpaint : ∀ w w' : v, B.paint w = B.paint w')
    (M : Matrix e e ℝ) (hR : B.ReachOne M) (h10 : M * B.gauge = 0) (h11 : B.gaugeᵀ * M = 0)
    (h1 : B.OneRuleFar M) :
    ∃ κ : ℝ, M = B.incidenceᵀ * diagonal (fun _ : f => κ) * B.incidence := by
  obtain ⟨K, hK, hflags⟩ := one_rule_flags hW M hR h10 h11 h1
  obtain ⟨σ₀⟩ := ‹Nonempty f›
  refine ⟨K σ₀, ?_⟩
  have hK' : K = fun _ => K σ₀ := by
    funext σ
    refine hflags σ σ₀ 0 0 (Or.inl ?_)
    funext k
    fin_cases k <;> exact hpaint _ _
  rw [hK, hK']

/-- **OR5.** A drift that is one rule, `λ` at a line one function of the paints at its two ends, is
one number where every corner has one paint. -/
theorem drift_one_number [Fintype f] [DecidableEq v] [Nonempty e]
    (hpaint : ∀ w w' : v, B.paint w = B.paint w') (l : e → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ ℓ, l ℓ = G (B.paint (B.tail ℓ)) (B.paint (B.head ℓ))) : ∃ c : ℝ, l = fun _ => c := by
  obtain ⟨ℓ₀⟩ := ‹Nonempty e›
  refine ⟨l ℓ₀, funext fun ℓ => ?_⟩
  rw [hG ℓ, hG ℓ₀, hpaint (B.tail ℓ) (B.tail ℓ₀), hpaint (B.head ℓ) (B.head ℓ₀)]

end Board

end Artform.Stages
