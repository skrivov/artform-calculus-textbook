import ArtformStages.Solid
import ArtformStages.Forced

/-!
# The law of light forced in a solid

Finding 440 proved on every wide board that the kicks of reach 1 that are blind to a change at a
corner and keep Gauss's law are `Cᵀ diag K C`. A board has two squares at each line. Here the
proof is carried to a complex of squares in which a line may be a side of any number of squares,
such as the faces of a solid of cubes (finding 452 of the research ledger on a layered universe):

* `SquareComplex.kick_forced` (FC1), `SquareComplex.kick_meets` (FC2);
* `Board.toSquareComplex` and its incidence, gauge and wideness (FC3);
* `cubeComplex`, `cubeComplex_incidence`, `cubeComplex_gauge` (FC4): the cubic torus of finding
  442 as a complex of squares;
* `cubeComplex_wide`, `cube_kick_forced` (FC5, FC6): for side `n ≥ 3` it is wide, so the law of
  light is forced on it.
-/

open Matrix

namespace Artform.Stages

/-- A complex of squares: faces with four corners each, all different, whose side `i` is a line
that joins the corners `i` and `i + 1`; a line may be a side of any number of faces. -/
structure SquareComplex (f e v : Type*) where
  /-- The four corners of a face, in its turn. -/
  corner : f → Fin 4 → v
  /-- The corner where a line starts. -/
  tail : e → v
  /-- The corner where a line ends. -/
  head : e → v
  /-- The side `i` of a face. -/
  side : f → Fin 4 → e
  /-- Whether the side `i` of a face runs from its corner `i` to its corner `i + 1`. -/
  along : f → Fin 4 → Bool
  corner_injective : ∀ σ, Function.Injective (corner σ)
  tail_side : ∀ σ i, tail (side σ i) = bif along σ i then corner σ i else corner σ (i + 1)
  head_side : ∀ σ i, head (side σ i) = bif along σ i then corner σ (i + 1) else corner σ i

namespace SquareComplex

variable {f e v : Type*} (X : SquareComplex f e v)

/-- The incidence of a complex, faces by lines. -/
def incidence [DecidableEq e] : Matrix f e ℝ :=
  Matrix.of fun σ ℓ => ∑ i, if X.side σ i = ℓ then Board.turnSign (X.along σ i) else 0

/-- The gauge of a complex, lines by corners. -/
def gauge [DecidableEq v] : Matrix e v ℝ :=
  Matrix.of fun ℓ w => (if X.head ℓ = w then 1 else 0) - (if X.tail ℓ = w then 1 else 0)

/-- A complex is *wide* when two different flags of a line share no corner but the line's ends. -/
def Wide : Prop :=
  ∀ (σ τ : f) (i j : Fin 4), X.side σ i = X.side τ j → (σ, i) ≠ (τ, j) →
    ∀ a b : Fin 4, X.corner σ a = X.corner τ b → a = i ∨ a = i + 1

/-- A kick has *reach 1* when at each line it reads only the sides of the faces at that line. -/
def ReachOne (M : Matrix e e ℝ) : Prop :=
  ∀ ℓ ℓ', M ℓ ℓ' ≠ 0 → ∃ σ i j, X.side σ i = ℓ ∧ X.side σ j = ℓ'

/-- The weight that a kick gives the far side of a face at its side `i`, with that side's sign. -/
def farWeight (M : Matrix e e ℝ) (σ : f) (i : Fin 4) : ℝ :=
  M (X.side σ i) (X.side σ (i + 2)) * Board.turnSign (X.along σ (i + 2))

theorem side_injective (σ : f) : Function.Injective (X.side σ) := by
  intro i j h
  have inj := X.corner_injective σ
  have ht := (X.tail_side σ i).symm.trans ((congrArg X.tail h).trans (X.tail_side σ j))
  have hh := (X.head_side σ i).symm.trans ((congrArg X.head h).trans (X.head_side σ j))
  have key : ∀ k : Fin 4, k + 1 + 1 ≠ k := by decide
  cases hi : X.along σ i <;> cases hj : X.along σ j <;>
    simp only [hi, hj, Bool.cond_true, Bool.cond_false] at ht hh
  · exact inj hh
  · obtain rfl := inj ht
    exact absurd (inj hh).symm (key i)
  · obtain rfl := inj hh
    exact absurd (inj ht).symm (key i)
  · exact inj ht

theorem incidence_apply [DecidableEq e] (σ : f) (ℓ : e) :
    X.incidence σ ℓ = ∑ i, if X.side σ i = ℓ then Board.turnSign (X.along σ i) else 0 := rfl

theorem incidence_of_side [DecidableEq e] {σ : f} {i : Fin 4} {ℓ : e} (h : X.side σ i = ℓ) :
    X.incidence σ ℓ = Board.turnSign (X.along σ i) := by
  rw [incidence_apply, Fintype.sum_eq_single i fun j hj =>
    ite_eq_right fun hj' => hj (X.side_injective σ (hj'.trans h.symm)), ite_eq_left h]

theorem incidence_of_not [DecidableEq e] {σ : f} {ℓ : e} (h : ∀ i, X.side σ i ≠ ℓ) :
    X.incidence σ ℓ = 0 := by
  rw [incidence_apply]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (h i)

theorem ends_side (σ : f) (i : Fin 4) (w : v) :
    (X.tail (X.side σ i) = w ∨ X.head (X.side σ i) = w) ↔
      (X.corner σ i = w ∨ X.corner σ (i + 1) = w) := by
  rw [X.tail_side, X.head_side]
  cases X.along σ i <;> simp only [Bool.cond_true, Bool.cond_false]
  tauto

section Gauge

variable [DecidableEq v]

theorem gauge_side (σ : f) (i : Fin 4) (w : v) :
    X.gauge (X.side σ i) w = Board.turnSign (X.along σ i) *
      ((if X.corner σ (i + 1) = w then 1 else 0) - (if X.corner σ i = w then 1 else 0)) := by
  simp only [gauge, Matrix.of_apply, X.tail_side, X.head_side]
  cases X.along σ i <;> simp [Board.turnSign]

theorem gauge_side_eq_zero {σ : f} {i : Fin 4} {w : v} (h1 : X.corner σ i ≠ w)
    (h2 : X.corner σ (i + 1) ≠ w) : X.gauge (X.side σ i) w = 0 := by
  simp [X.gauge_side, h1, h2]

theorem gauge_side_succ_ne_zero (σ : f) (i : Fin 4) :
    X.gauge (X.side σ i) (X.corner σ (i + 1)) ≠ 0 := by
  have k : ∀ x : Fin 4, x ≠ x + 1 := by decide
  have hne : X.corner σ i ≠ X.corner σ (i + 1) := (X.corner_injective σ).ne (k i)
  simp [X.gauge_side, hne, Board.turnSign_ne_zero]

theorem gauge_side_self_ne_zero (σ : f) (i : Fin 4) :
    X.gauge (X.side σ i) (X.corner σ i) ≠ 0 := by
  have k : ∀ x : Fin 4, x + 1 ≠ x := by decide
  have hne : X.corner σ (i + 1) ≠ X.corner σ i := (X.corner_injective σ).ne (k i)
  simp [X.gauge_side, hne, Board.turnSign_ne_zero]

theorem incidence_mul_gauge [DecidableEq e] [Fintype e] : X.incidence * X.gauge = 0 := by
  ext σ w
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [incidence_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h2 : ∀ i, Board.turnSign (X.along σ i) * X.gauge (X.side σ i) w =
      (if X.corner σ (i + 1) = w then 1 else 0) - (if X.corner σ i = w then 1 else 0) := by
    intro i
    rw [X.gauge_side, ← mul_assoc, Board.turnSign_mul_self, one_mul]
  simp only [h2, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

end Gauge

variable {X}

theorem Wide.corner_ne (hW : X.Wide) {σ τ : f} {i j : Fin 4} (h : X.side σ i = X.side τ j)
    (hne : (σ, i) ≠ (τ, j)) {a : Fin 4} (ha : a ≠ i ∧ a ≠ i + 1) (b : Fin 4) :
    X.corner σ a ≠ X.corner τ b := fun hc => (hW σ τ i j h hne a b hc).elim ha.1 ha.2

theorem Wide.side_ne (hW : X.Wide) {σ τ : f} {i j : Fin 4} (h : X.side σ i = X.side τ j)
    (hne : (σ, i) ≠ (τ, j)) {c : Fin 4} (hc : c ≠ i) (k : Fin 4) : X.side τ k ≠ X.side σ c := by
  intro hk
  have key : ∀ x y : Fin 4, y ≠ x → ∃ a : Fin 4, (a ≠ x ∧ a ≠ x + 1) ∧ (a = y ∨ a = y + 1) := by
    decide
  obtain ⟨a, ha, hac⟩ := key i c hc
  have hw : X.corner σ c = X.corner σ a ∨ X.corner σ (c + 1) = X.corner σ a := by
    rcases hac with hac | hac
    · exact Or.inl (by rw [hac])
    · exact Or.inr (by rw [hac])
  have hend := (X.ends_side σ c _).mpr hw
  rw [← hk] at hend
  rcases (X.ends_side τ k _).mp hend with h1 | h1
  · exact hW.corner_ne h hne ha k h1.symm
  · exact hW.corner_ne h hne ha (k + 1) h1.symm

variable (X)

private theorem leaf [Fintype e] [DecidableEq v] (R : e → ℝ) (w : v) (a : e)
    (hcyc : ∑ x, R x * X.gauge x w = 0) (ha : X.gauge a w ≠ 0)
    (hothers : ∀ x, x ≠ a → R x = 0 ∨ X.gauge x w = 0) : R a = 0 := by
  rw [Fintype.sum_eq_single a fun x hx => by rcases hothers x hx with h | h <;> simp [h]] at hcyc
  exact (mul_eq_zero.mp hcyc).resolve_right ha

/-- A closed sum of lines on the faces at the side `i` of `σ`, which is `0` on the far side of `σ`,
is `0` on the two sides of `σ` that meet the line. -/
private theorem near_zero [Fintype e] [DecidableEq v] (hW : X.Wide) {σ : f} {i : Fin 4}
    (R : e → ℝ)
    (hsupp : ∀ x, (∀ p : f × Fin 4, X.side p.1 p.2 = X.side σ i → ∀ k, X.side p.1 k ≠ x) →
      R x = 0)
    (hcyc : ∀ w, ∑ x, R x * X.gauge x w = 0) (hfar : R (X.side σ (i + 2)) = 0) :
    R (X.side σ (i + 1)) = 0 ∧ R (X.side σ (i + 3)) = 0 := by
  have inj := X.corner_injective σ
  have four : ∀ x k : Fin 4, k = x ∨ k = x + 1 ∨ k = x + 2 ∨ k = x + 3 := by decide
  have n02 : ∀ x : Fin 4, x ≠ x + 2 := by decide
  have n12 : ∀ x : Fin 4, x + 1 ≠ x + 2 := by decide
  have n32 : ∀ x : Fin 4, x + 3 ≠ x + 2 := by decide
  have n42 : ∀ x : Fin 4, x + 3 + 1 ≠ x + 2 := by decide
  have n03 : ∀ x : Fin 4, x ≠ x + 3 := by decide
  have n13 : ∀ x : Fin 4, x + 1 ≠ x + 3 := by decide
  have n23 : ∀ x : Fin 4, x + 1 + 1 ≠ x + 3 := by decide
  have s2 : ∀ x : Fin 4, x + 1 + 1 = x + 2 := by decide
  -- a corner of `σ` away from the line is no corner of another face at the line
  have away : ∀ a : Fin 4, a ≠ i → a ≠ i + 1 → ∀ p : f × Fin 4, X.side p.1 p.2 = X.side σ i →
      p ≠ (σ, i) → ∀ k, X.gauge (X.side p.1 k) (X.corner σ a) = 0 := by
    intro a ha ha' p hp hpne k
    have hne : ((σ, i) : f × Fin 4) ≠ (p.1, p.2) := fun h => hpne (h.symm)
    exact X.gauge_side_eq_zero (fun hc => hW.corner_ne hp.symm hne ⟨ha, ha'⟩ k hc.symm)
      (fun hc => hW.corner_ne hp.symm hne ⟨ha, ha'⟩ (k + 1) hc.symm)
  have others : ∀ (w : v) (a : e),
      (∀ k, X.side σ k ≠ a → X.side σ k ≠ X.side σ (i + 2) → X.gauge (X.side σ k) w = 0) →
        (∀ p : f × Fin 4, X.side p.1 p.2 = X.side σ i → p ≠ (σ, i) →
          ∀ k, X.gauge (X.side p.1 k) w = 0) →
          ∀ x, x ≠ a → R x = 0 ∨ X.gauge x w = 0 := by
    intro w a hσ hτ x hx
    by_cases h1 : ∃ k, X.side σ k = x
    · obtain ⟨k, rfl⟩ := h1
      by_cases hk2 : X.side σ k = X.side σ (i + 2)
      · exact Or.inl (by rw [hk2]; exact hfar)
      · exact Or.inr (hσ k hx hk2)
    · by_cases h2 : ∃ p : f × Fin 4, X.side p.1 p.2 = X.side σ i ∧ p ≠ (σ, i) ∧
          ∃ k, X.side p.1 k = x
      · obtain ⟨p, hp, hpne, k, rfl⟩ := h2
        exact Or.inr (hτ p hp hpne k)
      · refine Or.inl (hsupp x fun p hp k hk => ?_)
        by_cases hpe : p = (σ, i)
        · subst hpe
          exact h1 ⟨k, hk⟩
        · exact h2 ⟨p, hp, hpe, k, hk⟩
  constructor
  · refine X.leaf R (X.corner σ (i + 2)) (X.side σ (i + 1)) (hcyc _) ?_ ?_
    · rw [← s2]
      exact X.gauge_side_succ_ne_zero σ (i + 1)
    · refine others _ _ (fun k hk hk2 => ?_) (away _ (n02 i).symm (n12 i).symm)
      rcases four i k with hk' | hk' | hk' | hk' <;> rw [hk'] at hk hk2 ⊢
      · exact X.gauge_side_eq_zero (inj.ne (n02 i)) (inj.ne (n12 i))
      · exact absurd rfl hk
      · exact absurd rfl hk2
      · exact X.gauge_side_eq_zero (inj.ne (n32 i)) (inj.ne (n42 i))
  · refine X.leaf R (X.corner σ (i + 3)) (X.side σ (i + 3)) (hcyc _) ?_ ?_
    · exact X.gauge_side_self_ne_zero σ (i + 3)
    · refine others _ _ (fun k hk hk2 => ?_) (away _ (n03 i).symm (n13 i).symm)
      rcases four i k with hk' | hk' | hk' | hk' <;> rw [hk'] at hk hk2 ⊢
      · exact X.gauge_side_eq_zero (inj.ne (n03 i)) (inj.ne (n13 i))
      · exact X.gauge_side_eq_zero (inj.ne (n13 i)) (inj.ne (n23 i))
      · exact absurd rfl hk2
      · exact absurd rfl hk

/-- On a wide complex, A10 makes the row of a kick of reach 1 at a line the sum, over the flags of
the line, of a number times the edge of the flag's face, the numbers read on the far sides. -/
theorem row_form [Fintype f] [Fintype e] [DecidableEq e] [DecidableEq v] (hW : X.Wide)
    (M : Matrix e e ℝ) (hR : X.ReachOne M) (h10 : M * X.gauge = 0) (ℓ ℓ' : e) :
    M ℓ ℓ' = ∑ p : f × Fin 4,
      (if X.side p.1 p.2 = ℓ then X.farWeight M p.1 p.2 else 0) * X.incidence p.1 ℓ' := by
  set R : e → ℝ := fun x => M ℓ x - ∑ p : f × Fin 4,
    (if X.side p.1 p.2 = ℓ then X.farWeight M p.1 p.2 else 0) * X.incidence p.1 x with hRdef
  suffices hR0 : ∀ x, R x = 0 by
    have := hR0 ℓ'
    simp only [hRdef] at this
    linarith
  have k2 : ∀ x : Fin 4, x + 2 ≠ x := by decide
  have four : ∀ x k : Fin 4, k = x ∨ k = x + 1 ∨ k = x + 2 ∨ k = x + 3 := by decide
  -- `R` lives on the faces at the line
  have hsupp : ∀ x, (∀ p : f × Fin 4, X.side p.1 p.2 = ℓ → ∀ k, X.side p.1 k ≠ x) → R x = 0 := by
    intro x hx
    have hM : M ℓ x = 0 := by
      by_contra hM
      obtain ⟨ρ, a, b, ha, hb⟩ := hR _ _ hM
      exact hx (ρ, a) ha b hb
    have hsum : ∑ p : f × Fin 4,
        (if X.side p.1 p.2 = ℓ then X.farWeight M p.1 p.2 else 0) * X.incidence p.1 x = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : X.side p.1 p.2 = ℓ
      · rw [X.incidence_of_not (hx p hp), mul_zero]
      · rw [ite_eq_right hp, zero_mul]
    simp only [hRdef, hM, hsum, sub_zero]
  -- `R` is closed
  have hcyc : ∀ w, ∑ x, R x * X.gauge x w = 0 := by
    intro w
    have h0 := congrFun (congrFun h10 ℓ) w
    simp only [Matrix.mul_apply, Matrix.zero_apply] at h0
    have hCG : ∀ ρ, ∑ x, X.incidence ρ x * X.gauge x w = 0 := fun ρ => by
      have := congrFun (congrFun X.incidence_mul_gauge ρ) w
      simpa [Matrix.mul_apply] using this
    simp only [hRdef, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, h0, zero_sub, neg_eq_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hCG, mul_zero]
  by_cases hflag : ∃ q : f × Fin 4, X.side q.1 q.2 = ℓ
  · obtain ⟨⟨σ₀, i₀⟩, h₀⟩ := hflag
    dsimp only at h₀
    -- `R` is `0` on the far side of each flag
    have hfar : ∀ (σ : f) (i : Fin 4), X.side σ i = ℓ → R (X.side σ (i + 2)) = 0 := by
      intro σ i hσ
      have e1 : X.incidence σ (X.side σ (i + 2)) = Board.turnSign (X.along σ (i + 2)) :=
        X.incidence_of_side rfl
      have hsum : ∑ p : f × Fin 4, (if X.side p.1 p.2 = ℓ then X.farWeight M p.1 p.2 else 0) *
          X.incidence p.1 (X.side σ (i + 2)) =
            X.farWeight M σ i * Board.turnSign (X.along σ (i + 2)) := by
        rw [Fintype.sum_eq_single (σ, i)]
        · simp only [hσ, ↓reduceIte, e1]
        · intro p hp
          by_cases hpl : X.side p.1 p.2 = ℓ
          · have hne : ((σ, i) : f × Fin 4) ≠ (p.1, p.2) := fun h => hp h.symm
            rw [X.incidence_of_not (hW.side_ne (hσ.trans hpl.symm) hne (k2 i)), mul_zero]
          · rw [ite_eq_right hpl, zero_mul]
      have hRx : R (X.side σ (i + 2)) = M ℓ (X.side σ (i + 2)) - ∑ p : f × Fin 4,
          (if X.side p.1 p.2 = ℓ then X.farWeight M p.1 p.2 else 0) *
            X.incidence p.1 (X.side σ (i + 2)) := rfl
      rw [hRx, hsum, farWeight, hσ, mul_assoc, Board.turnSign_mul_self, mul_one, sub_self]
    -- and on the near sides of each flag
    have hnear : ∀ (σ : f) (i : Fin 4), X.side σ i = ℓ →
        R (X.side σ (i + 1)) = 0 ∧ R (X.side σ (i + 3)) = 0 := by
      intro σ i hσ
      refine X.near_zero hW R (fun x hx => hsupp x fun p hp => hx p (hp.trans hσ.symm)) hcyc ?_
      exact hfar σ i hσ
    -- so on every line but the line itself
    have hrest : ∀ x, x ≠ ℓ → R x = 0 := by
      intro x hx
      by_cases h1 : ∃ p : f × Fin 4, X.side p.1 p.2 = ℓ ∧ ∃ k, X.side p.1 k = x
      · obtain ⟨⟨σ, i⟩, hσ, k, rfl⟩ := h1
        dsimp only at hσ ⊢
        rcases four i k with hk | hk | hk | hk <;> rw [hk] at hx ⊢
        · exact absurd hσ hx
        · exact (hnear σ i hσ).1
        · exact hfar σ i hσ
        · exact (hnear σ i hσ).2
      · push Not at h1
        exact hsupp x fun p hp k hk => h1 p hp k hk
    have hline : R ℓ = 0 := by
      rw [← h₀]
      refine X.leaf R (X.corner σ₀ (i₀ + 1)) (X.side σ₀ i₀) (hcyc _)
        (X.gauge_side_succ_ne_zero σ₀ i₀) fun x hx => Or.inl (hrest x (h₀ ▸ hx))
    intro x
    by_cases hx : x = ℓ
    · rw [hx]
      exact hline
    · exact hrest x hx
  · push Not at hflag
    exact fun x => hsupp x fun p hp => absurd hp (hflag p)

/-- **FC1.** On a wide complex of squares, a kick of reach 1 that is blind to a change at a corner
(A10) and keeps Gauss's law (A11) is `Cᵀ diag K C` for a number `K` on each face. -/
theorem kick_forced [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (hW : X.Wide) (M : Matrix e e ℝ) (hR : X.ReachOne M) (h10 : M * X.gauge = 0)
    (h11 : X.gaugeᵀ * M = 0) : ∃ K : f → ℝ, M = X.incidenceᵀ * diagonal K * X.incidence := by
  have m12 : ∀ x : Fin 4, x + 1 ≠ x + 2 := by decide
  have m13 : ∀ x : Fin 4, x + 1 ≠ x + 2 + 1 := by decide
  have hrow := X.row_form hW M hR h10
  -- the kick read at a corner, summed over the flags
  have hflag : ∀ w ℓ', (X.gaugeᵀ * M) w ℓ' = ∑ p : f × Fin 4,
      X.gauge (X.side p.1 p.2) w * (X.farWeight M p.1 p.2 * X.incidence p.1 ℓ') := by
    intro w ℓ'
    rw [Matrix.mul_apply]
    simp only [transpose_apply, hrow _ ℓ', Finset.mul_sum, ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hstep : ∀ σ j, X.farWeight M σ j * Board.turnSign (X.along σ j) =
      X.farWeight M σ (j + 1) * Board.turnSign (X.along σ (j + 1)) := by
    intro σ j
    have h0 := congrFun (congrFun h11 (X.corner σ (j + 1))) (X.side σ (j + 2))
    rw [hflag, Matrix.zero_apply, Fintype.sum_prod_type, Fintype.sum_eq_single σ] at h0
    · have hs : X.incidence σ (X.side σ (j + 2)) = Board.turnSign (X.along σ (j + 2)) :=
        X.incidence_of_side rfl
      simp only [X.gauge_side, (X.corner_injective σ).eq_iff, add_left_inj, hs] at h0
      simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
      have key : Board.turnSign (X.along σ (j + 2)) * (X.farWeight M σ j *
          Board.turnSign (X.along σ j) - X.farWeight M σ (j + 1) *
            Board.turnSign (X.along σ (j + 1))) = 0 := by
        linear_combination h0
      have := (mul_eq_zero.mp key).resolve_left (Board.turnSign_ne_zero _)
      linarith
    · intro ρ hρ
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hC : X.incidence ρ (X.side σ (j + 2)) = 0
      · rw [hC, mul_zero, mul_zero]
      · obtain ⟨b, hb⟩ : ∃ b, X.side ρ b = X.side σ (j + 2) := by
          by_contra hn
          push Not at hn
          exact hC (X.incidence_of_not hn)
        have hne : ((σ, j + 2) : f × Fin 4) ≠ (ρ, b) := fun hp => hρ (Prod.mk.inj hp).1.symm
        rw [X.gauge_side_eq_zero
          (fun hc => hW.corner_ne hb.symm hne ⟨m12 j, m13 j⟩ i hc.symm)
          (fun hc => hW.corner_ne hb.symm hne ⟨m12 j, m13 j⟩ (i + 1) hc.symm), zero_mul]
  have hconst : ∀ σ i, X.farWeight M σ i * Board.turnSign (X.along σ i) =
      X.farWeight M σ 0 * Board.turnSign (X.along σ 0) := by
    intro σ i
    have h1 := hstep σ 0
    have h2 := hstep σ 1
    have h3 := hstep σ 2
    fin_cases i
    · rfl
    · exact h1.symm
    · exact h2.symm.trans h1.symm
    · exact h3.symm.trans (h2.symm.trans h1.symm)
  have hw : ∀ ρ a, X.farWeight M ρ a =
      X.farWeight M ρ 0 * Board.turnSign (X.along ρ 0) * Board.turnSign (X.along ρ a) := by
    intro ρ a
    rw [← hconst ρ a, mul_assoc, Board.turnSign_mul_self, mul_one]
  have hRHS : ∀ (K : f → ℝ) (ℓ ℓ' : e), (X.incidenceᵀ * diagonal K * X.incidence) ℓ ℓ' =
      ∑ p : f × Fin 4, (if X.side p.1 p.2 = ℓ then K p.1 * Board.turnSign (X.along p.1 p.2)
        else 0) * X.incidence p.1 ℓ' := by
    intro K ℓ ℓ'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_diagonal, transpose_apply, X.incidence_apply ρ ℓ, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  refine ⟨fun σ => X.farWeight M σ 0 * Board.turnSign (X.along σ 0), ?_⟩
  ext ℓ ℓ'
  rw [hrow ℓ ℓ', hRHS]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rw [hw p.1 p.2]
  · rfl

/-- **FC2.** On every complex of squares, every `Cᵀ diag K C` has reach 1 and meets A10 and A11. -/
theorem kick_meets [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (K : f → ℝ) :
    X.ReachOne (X.incidenceᵀ * diagonal K * X.incidence) ∧
      X.incidenceᵀ * diagonal K * X.incidence * X.gauge = 0 ∧
      X.gaugeᵀ * (X.incidenceᵀ * diagonal K * X.incidence) = 0 := by
  refine ⟨fun ℓ ℓ' h => ?_, ?_, ?_⟩
  · rw [Matrix.mul_apply] at h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    simp only [mul_diagonal, transpose_apply] at hσ
    have h1 : X.incidence σ ℓ ≠ 0 := fun h0 => hσ (by rw [h0, zero_mul, zero_mul])
    have h2 : X.incidence σ ℓ' ≠ 0 := fun h0 => hσ (by rw [h0, mul_zero])
    obtain ⟨i, hi⟩ : ∃ i, X.side σ i = ℓ := by
      by_contra hn
      push Not at hn
      exact h1 (X.incidence_of_not hn)
    obtain ⟨j, hj⟩ : ∃ j, X.side σ j = ℓ' := by
      by_contra hn
      push Not at hn
      exact h2 (X.incidence_of_not hn)
    exact ⟨σ, i, j, hi, hj⟩
  · rw [Matrix.mul_assoc, X.incidence_mul_gauge, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, X.incidence_mul_gauge,
      transpose_zero, Matrix.zero_mul, Matrix.zero_mul]

end SquareComplex

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- **FC3.** A board as a complex of squares. -/
def toSquareComplex : SquareComplex f e v where
  corner := B.corner
  tail := B.tail
  head := B.head
  side := B.side
  along := B.along
  corner_injective := B.corner_injective
  tail_side := B.tail_side
  head_side := B.head_side

theorem toSquareComplex_incidence [DecidableEq e] : B.toSquareComplex.incidence = B.incidence :=
  rfl

theorem toSquareComplex_gauge [DecidableEq v] : B.toSquareComplex.gauge = B.gauge := rfl

/-- **FC3.** A wide board is a wide complex of squares. -/
theorem toSquareComplex_wide (hW : B.Wide) : B.toSquareComplex.Wide := by
  intro σ τ i j h hne a b hc
  exact hW σ τ i j h (B.along_ne h hne) a b hc

end Board

section Cube

variable (n : ℕ) [Fact (1 < n)]

/-- **FC4.** The cubic torus of side `n` as a complex of squares: the face `(u, k)` has the
corners `u`, `u + e (k + 1)`, `u + e (k + 1) + e (k + 2)`, `u + e (k + 2)`, and the sides of
finding 442. -/
def cubeComplex : SquareComplex (CubePoint n × Fin 3) (CubePoint n × Fin 3) (CubePoint n) where
  corner σ := ![σ.1, σ.1 + cubeStep n (σ.2 + 1),
    σ.1 + cubeStep n (σ.2 + 1) + cubeStep n (σ.2 + 2), σ.1 + cubeStep n (σ.2 + 2)]
  tail ℓ := ℓ.1
  head ℓ := ℓ.1 + cubeStep n ℓ.2
  side σ := ![(σ.1, σ.2 + 1), (σ.1 + cubeStep n (σ.2 + 1), σ.2 + 2),
    (σ.1 + cubeStep n (σ.2 + 2), σ.2 + 1), (σ.1, σ.2 + 2)]
  along _ := ![true, true, false, false]
  corner_injective σ := by
    have hk : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
    intro a b hab
    have e1 := congrFun hab (σ.2 + 1)
    have e2 := congrFun hab (σ.2 + 2)
    fin_cases a <;> fin_cases b <;>
      simp [cubeStep, hk σ.2, (hk σ.2).symm] at e1 e2 ⊢
  tail_side σ i := by fin_cases i <;> simp
  head_side σ i := by fin_cases i <;> simp [add_right_comm]

/-- **FC4.** Its gauge is finding 442's. -/
theorem cubeComplex_gauge : (cubeComplex n).gauge = cubeGauge n := rfl

/-- **FC4.** Its incidence is finding 442's. -/
theorem cubeComplex_incidence : (cubeComplex n).incidence = cubeIncidence n := by
  ext σ ℓ
  simp only [SquareComplex.incidence, cubeIncidence, Matrix.of_apply, Fin.sum_univ_four]
  simp only [cubeComplex, @eq_comm _ ℓ]
  simp [Board.turnSign]
  split_ifs <;> norm_num

/-- The four flags of the line `(x, d)` of the cubic torus. -/
theorem cube_flag {σ : CubePoint n × Fin 3} {i : Fin 4} {x : CubePoint n} {d : Fin 3}
    (h : (cubeComplex n).side σ i = (x, d)) :
    (σ, i) = ((x, d + 2), 0) ∨ (σ, i) = ((x - cubeStep n (d + 2), d + 1), 1) ∨
      (σ, i) = ((x - cubeStep n (d + 1), d + 2), 2) ∨ (σ, i) = ((x, d + 1), 3) := by
  have n1 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
  have n2 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have n3 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
  have n4 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  obtain ⟨u, k⟩ := σ
  fin_cases i <;> simp only [cubeComplex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h <;> subst h1 h2
  · left
    simp [n1]
  · right; left
    simp [n2, n3]
  · right; right; left
    simp [n1, n4]
  · right; right; right
    simp [n2]

set_option maxHeartbeats 4000000 in
-- The case analysis below compares 192 pairs of corners, each by its three coordinates.
/-- **FC5.** For `n ≥ 3` the cubic torus is wide. -/
theorem cubeComplex_wide (hn : 2 < n) : (cubeComplex n).Wide := by
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h11 : (1 : ZMod n) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2
  have h1n : (1 : ZMod n) ≠ -1 := by
    intro h
    apply h11
    nth_rewrite 2 [h]
    exact add_neg_cancel 1
  have hn1 : (-1 : ZMod n) ≠ 1 := fun h => h1n h.symm
  have f01 : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have f02 : ∀ k : Fin 3, k ≠ k + 2 := by decide
  have f12 : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  have n1 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
  have n2 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have n3 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
  have n4 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  intro σ τ i j h hne a b hc
  rcases hl : (cubeComplex n).side τ j with ⟨x, d⟩
  have hσl := h.trans hl
  rcases cube_flag n hσl with h1 | h1 | h1 | h1 <;>
    rcases cube_flag n hl with h3 | h3 | h3 | h3 <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1 <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3 <;>
    first
    | exact absurd rfl hne
    | (have e0 := congrFun hc d
       have e1 := congrFun hc (d + 1)
       have e2 := congrFun hc (d + 2)
       fin_cases a <;> fin_cases b <;>
         simp [cubeComplex, cubeStep, n1, n2, n3, n4, f01 d, f02 d, f12 d, (f01 d).symm,
           (f02 d).symm, (f12 d).symm, sub_eq_add_neg, add_assoc, h1n, hn1] at e0 e1 e2 ⊢)

/-- **FC6.** On the cubic torus of side `n ≥ 3`, a kick of reach 1 that is blind to a change at a
corner and keeps Gauss's law is `Cᵀ diag K C`, with `C` finding 442's incidence. -/
theorem cube_kick_forced [NeZero n] (hn : 2 < n)
    (M : Matrix (CubePoint n × Fin 3) (CubePoint n × Fin 3) ℝ)
    (hR : (cubeComplex n).ReachOne M) (h10 : M * cubeGauge n = 0)
    (h11 : (cubeGauge n)ᵀ * M = 0) :
    ∃ K : CubePoint n × Fin 3 → ℝ, M = (cubeIncidence n)ᵀ * diagonal K * cubeIncidence n := by
  have h := (cubeComplex n).kick_forced (cubeComplex_wide n hn) M hR
    (by rw [cubeComplex_gauge]; exact h10) (by rw [cubeComplex_gauge]; exact h11)
  rw [cubeComplex_incidence] at h
  exact h

end Cube

end Artform.Stages
