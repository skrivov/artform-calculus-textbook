import ArtformStages.Classes

/-!
# The law of light is forced

Finding 421 of the research ledger on a layered universe proved on paper (its T331(a) and (c))
that on a wide board the kicks of light that the askings leave are the kicks `Cᵀ diag K C`.
Here it is proved for every board (finding 440 of the ledger), with `C` the incidence of finding
434's `Board` and `G` its gauge:

* `Board.kick_forced` (FL1): on a wide board, a kick `M` of reach 1 that is blind to a change at
  a corner (`M G = 0`, the asking A10) and keeps Gauss's law (`Gᵀ M = 0`, A11) is `Cᵀ diag K C`;
* `Board.kick_meets` (FL2): on every board every `Cᵀ diag K C` is such a kick;
* `Board.reach_zero` (FL3): a kick of reach 0 that is blind to a change at a corner is `0`;
* `Board.joined_image`, `Board.kick_forced_unique` (FL4): on a joined board the image of `C`
  holds `e σ - e τ` for every two squares, so on a wide joined board of at least three squares
  each such kick has exactly one `K` (with finding 439's `kick_injective`).

The proof of FL1 reads a row of the kick as a closed sum of lines (A10) on the two squares at its
line; on a wide board those squares meet in the line alone, so the row is a number times the edge
of each square (`Board.row_form`); A11 then makes the number the same round each square.
-/

open Matrix

namespace Artform.Stages

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- A board is *wide* when the two squares at a line share no corner but the line's two ends.
The two flags of a line are the one along its square's turn and the one against it. -/
def Wide : Prop :=
  ∀ (σ τ : f) (i j : Fin 4), B.side σ i = B.side τ j → B.along σ i ≠ B.along τ j →
    ∀ a b : Fin 4, B.corner σ a = B.corner τ b → a = i ∨ a = i + 1

/-- A kick has *reach 1* when at each line it reads only the sides of the squares at that
line. -/
def ReachOne (M : Matrix e e ℝ) : Prop :=
  ∀ ℓ ℓ', M ℓ ℓ' ≠ 0 → ∃ σ i j, B.side σ i = ℓ ∧ B.side σ j = ℓ'

/-- The squares of a board are *joined* when any two are linked by a chain of squares, each
sharing a side with the next. -/
def Joined : Prop :=
  ∀ σ τ : f, Relation.ReflTransGen (fun ρ ρ' => ∃ i j, B.side ρ i = B.side ρ' j) σ τ

/-- The weight that a kick `M` gives the far side of the square `σ` at its side `i`, with the
far side's sign. -/
def farWeight (M : Matrix e e ℝ) (σ : f) (i : Fin 4) : ℝ :=
  M (B.side σ i) (B.side σ (i + 2)) * turnSign (B.along σ (i + 2))

theorem turnSign_mul_self (b : Bool) : turnSign b * turnSign b = 1 := by
  cases b <;> norm_num [turnSign]

theorem turnSign_ne_zero (b : Bool) : turnSign b ≠ 0 := by
  cases b <;> norm_num [turnSign]

theorem turnSign_mul_of_ne {b b' : Bool} (h : b ≠ b') : turnSign b * turnSign b' = -1 := by
  revert h
  cases b <;> cases b' <;> norm_num [turnSign]

/-- The ends of the side `i` of a square are its corners `i` and `i + 1`. -/
theorem ends_side (σ : f) (i : Fin 4) (w : v) :
    (B.tail (B.side σ i) = w ∨ B.head (B.side σ i) = w) ↔
      (B.corner σ i = w ∨ B.corner σ (i + 1) = w) := by
  rw [B.tail_side, B.head_side]
  cases B.along σ i <;> simp only [Bool.cond_true, Bool.cond_false]
  tauto

/-- A line has two different ends. -/
theorem tail_ne_head (ℓ : e) : B.tail ℓ ≠ B.head ℓ := by
  obtain ⟨⟨σ, i⟩, ⟨hs, -⟩, -⟩ := B.once_each_way ℓ true
  dsimp only at hs
  subst hs
  have k : ∀ x : Fin 4, x ≠ x + 1 := by decide
  have h := B.corner_injective σ
  rw [B.tail_side, B.head_side]
  cases B.along σ i <;> simp only [Bool.cond_true, Bool.cond_false] <;> intro hc
  · exact k i (h hc).symm
  · exact k i (h hc)

/-- Any flag of the line of `(σ, i)` that runs the same way as `(σ, i)` is `(σ, i)`. -/
theorem flag_eq {σ ρ : f} {i a : Fin 4} (h : B.side ρ a = B.side σ i)
    (ha : B.along ρ a = B.along σ i) : ρ = σ ∧ a = i :=
  Prod.mk.inj ((B.once_each_way (B.side σ i) (B.along σ i)).unique (y₁ := (ρ, a)) (y₂ := (σ, i))
    ⟨h, ha⟩ ⟨rfl, rfl⟩)

/-- Two flags of one line that run opposite ways are all its flags. -/
theorem flag_cover {σ τ ρ : f} {i j a : Fin 4} (h : B.side σ i = B.side τ j)
    (hne : B.along σ i ≠ B.along τ j) (hρ : B.side ρ a = B.side σ i) :
    (ρ = σ ∧ a = i) ∨ (ρ = τ ∧ a = j) := by
  by_cases hb : B.along ρ a = B.along σ i
  · exact Or.inl (B.flag_eq hρ hb)
  · have key : ∀ x y z : Bool, x ≠ y → y ≠ z → x = z := by decide
    exact Or.inr (B.flag_eq (hρ.trans h) (key _ _ _ hb hne))

/-- Two different flags of one line run opposite ways. -/
theorem along_ne {σ τ : f} {i j : Fin 4} (h : B.side σ i = B.side τ j) (hne : (σ, i) ≠ (τ, j)) :
    B.along σ i ≠ B.along τ j := by
  intro ha
  obtain ⟨h1, h2⟩ := B.flag_eq h.symm ha.symm
  exact hne (by rw [h1, h2])

section Gauge

variable [DecidableEq v]

/-- `G` at the side `i` of a square and a corner `w`. -/
theorem gauge_side (σ : f) (i : Fin 4) (w : v) :
    B.gauge (B.side σ i) w = turnSign (B.along σ i) *
      ((if B.corner σ (i + 1) = w then 1 else 0) - (if B.corner σ i = w then 1 else 0)) := by
  simp only [gauge, Matrix.of_apply, B.tail_side, B.head_side]
  cases B.along σ i <;> simp [turnSign]

/-- `G` is `0` at a side of a square and a corner that is not one of the side's ends. -/
theorem gauge_side_eq_zero {σ : f} {i : Fin 4} {w : v} (h1 : B.corner σ i ≠ w)
    (h2 : B.corner σ (i + 1) ≠ w) : B.gauge (B.side σ i) w = 0 := by
  simp [B.gauge_side, h1, h2]

theorem gauge_side_succ_ne_zero (σ : f) (i : Fin 4) :
    B.gauge (B.side σ i) (B.corner σ (i + 1)) ≠ 0 := by
  have k : ∀ x : Fin 4, x ≠ x + 1 := by decide
  have hne : B.corner σ i ≠ B.corner σ (i + 1) := (B.corner_injective σ).ne (k i)
  simp [B.gauge_side, hne, turnSign_ne_zero]

theorem gauge_side_self_ne_zero (σ : f) (i : Fin 4) :
    B.gauge (B.side σ i) (B.corner σ i) ≠ 0 := by
  have k : ∀ x : Fin 4, x + 1 ≠ x := by decide
  have hne : B.corner σ (i + 1) ≠ B.corner σ i := (B.corner_injective σ).ne (k i)
  simp [B.gauge_side, hne, turnSign_ne_zero]

end Gauge

variable {B}

/-- On a wide board, a corner of `σ` that is not an end of the line it shares with `τ` is no
corner of `τ`. -/
theorem Wide.corner_ne (hW : B.Wide) {σ τ : f} {i j : Fin 4} (h : B.side σ i = B.side τ j)
    (hne : B.along σ i ≠ B.along τ j) {a : Fin 4} (ha : a ≠ i ∧ a ≠ i + 1) (b : Fin 4) :
    B.corner σ a ≠ B.corner τ b := fun hc => (hW σ τ i j h hne a b hc).elim ha.1 ha.2

/-- On a wide board, a side of `σ` other than the line it shares with `τ` is no side of `τ`. -/
theorem Wide.side_ne (hW : B.Wide) {σ τ : f} {i j : Fin 4} (h : B.side σ i = B.side τ j)
    (hne : B.along σ i ≠ B.along τ j) {c : Fin 4} (hc : c ≠ i) (k : Fin 4) :
    B.side τ k ≠ B.side σ c := by
  intro hk
  have key : ∀ x y : Fin 4, y ≠ x → ∃ a : Fin 4, (a ≠ x ∧ a ≠ x + 1) ∧ (a = y ∨ a = y + 1) := by
    decide
  obtain ⟨a, ha, hac⟩ := key i c hc
  have hw : B.corner σ c = B.corner σ a ∨ B.corner σ (c + 1) = B.corner σ a := by
    rcases hac with hac | hac
    · exact Or.inl (by rw [hac])
    · exact Or.inr (by rw [hac])
  have hend := (B.ends_side σ c _).mpr hw
  rw [← hk] at hend
  rcases (B.ends_side τ k _).mp hend with h1 | h1
  · exact hW.corner_ne h hne ha k h1.symm
  · exact hW.corner_ne h hne ha (k + 1) h1.symm

variable (B)

/-- A closed sum of lines whose only line at the corner `w` with a value is `a` is `0` at `a`. -/
private theorem leaf [Fintype e] [DecidableEq v] (R : e → ℝ) (w : v) (a : e)
    (hcyc : ∑ x, R x * B.gauge x w = 0) (ha : B.gauge a w ≠ 0)
    (hothers : ∀ x, x ≠ a → R x = 0 ∨ B.gauge x w = 0) : R a = 0 := by
  rw [Fintype.sum_eq_single a fun x hx => by rcases hothers x hx with h | h <;> simp [h]] at hcyc
  exact (mul_eq_zero.mp hcyc).resolve_right ha

/-- A closed sum of lines on the two squares at a line of a wide board, which is `0` on the far
side of `σ`, is `0` on the two sides of `σ` that meet the line. -/
private theorem near_zero [Fintype e] [DecidableEq v] (hW : B.Wide) {σ τ : f} {i j : Fin 4}
    (h : B.side σ i = B.side τ j) (hne : B.along σ i ≠ B.along τ j) (R : e → ℝ)
    (hsupp : ∀ x, (∀ k, B.side σ k ≠ x) → (∀ k, B.side τ k ≠ x) → R x = 0)
    (hcyc : ∀ w, ∑ x, R x * B.gauge x w = 0) (hfar : R (B.side σ (i + 2)) = 0) :
    R (B.side σ (i + 1)) = 0 ∧ R (B.side σ (i + 3)) = 0 := by
  have inj := B.corner_injective σ
  have four : ∀ x k : Fin 4, k = x ∨ k = x + 1 ∨ k = x + 2 ∨ k = x + 3 := by decide
  have n02 : ∀ x : Fin 4, x ≠ x + 2 := by decide
  have n12 : ∀ x : Fin 4, x + 1 ≠ x + 2 := by decide
  have n32 : ∀ x : Fin 4, x + 3 ≠ x + 2 := by decide
  have n42 : ∀ x : Fin 4, x + 3 + 1 ≠ x + 2 := by decide
  have n03 : ∀ x : Fin 4, x ≠ x + 3 := by decide
  have n13 : ∀ x : Fin 4, x + 1 ≠ x + 3 := by decide
  have n23 : ∀ x : Fin 4, x + 1 + 1 ≠ x + 3 := by decide
  have s2 : ∀ x : Fin 4, x + 1 + 1 = x + 2 := by decide
  -- a corner of `σ` away from the line is no corner of `τ`, so no side of `τ` reaches it
  have away : ∀ a : Fin 4, a ≠ i → a ≠ i + 1 → ∀ k, B.gauge (B.side τ k) (B.corner σ a) = 0 :=
    fun a ha ha' k => B.gauge_side_eq_zero (fun hc => hW.corner_ne h hne ⟨ha, ha'⟩ k hc.symm)
      (fun hc => hW.corner_ne h hne ⟨ha, ha'⟩ (k + 1) hc.symm)
  have others : ∀ (w : v) (a : e),
      (∀ k, B.side σ k ≠ a → B.side σ k ≠ B.side σ (i + 2) → B.gauge (B.side σ k) w = 0) →
        (∀ k, B.gauge (B.side τ k) w = 0) → ∀ x, x ≠ a → R x = 0 ∨ B.gauge x w = 0 := by
    intro w a hσ hτ x hx
    by_cases h1 : ∃ k, B.side σ k = x
    · obtain ⟨k, rfl⟩ := h1
      by_cases hk2 : B.side σ k = B.side σ (i + 2)
      · exact Or.inl (by rw [hk2]; exact hfar)
      · exact Or.inr (hσ k hx hk2)
    · by_cases h2 : ∃ k, B.side τ k = x
      · obtain ⟨k, rfl⟩ := h2
        exact Or.inr (hτ k)
      · push Not at h1 h2
        exact Or.inl (hsupp x h1 h2)
  constructor
  · refine B.leaf R (B.corner σ (i + 2)) (B.side σ (i + 1)) (hcyc _) ?_ ?_
    · rw [← s2]
      exact B.gauge_side_succ_ne_zero σ (i + 1)
    · refine others _ _ (fun k hk hk2 => ?_) (away _ (n02 i).symm (n12 i).symm)
      rcases four i k with hk' | hk' | hk' | hk' <;> rw [hk'] at hk hk2 ⊢
      · exact B.gauge_side_eq_zero (inj.ne (n02 i)) (inj.ne (n12 i))
      · exact absurd rfl hk
      · exact absurd rfl hk2
      · exact B.gauge_side_eq_zero (inj.ne (n32 i)) (inj.ne (n42 i))
  · refine B.leaf R (B.corner σ (i + 3)) (B.side σ (i + 3)) (hcyc _) ?_ ?_
    · exact B.gauge_side_self_ne_zero σ (i + 3)
    · refine others _ _ (fun k hk hk2 => ?_) (away _ (n03 i).symm (n13 i).symm)
      rcases four i k with hk' | hk' | hk' | hk' <;> rw [hk'] at hk hk2 ⊢
      · exact B.gauge_side_eq_zero (inj.ne (n03 i)) (inj.ne (n13 i))
      · exact B.gauge_side_eq_zero (inj.ne (n13 i)) (inj.ne (n23 i))
      · exact absurd rfl hk2
      · exact absurd rfl hk

/-- On a wide board, A10 makes the row of a kick of reach 1 at a line a number times the edge of
each of the line's two squares, the numbers read on their far sides. -/
theorem row_form [Fintype e] [DecidableEq e] [DecidableEq v] (hW : B.Wide) (M : Matrix e e ℝ)
    (hR : B.ReachOne M) (h10 : M * B.gauge = 0) {σ τ : f} {i j : Fin 4}
    (h : B.side σ i = B.side τ j) (hne : B.along σ i ≠ B.along τ j) (ℓ' : e) :
    M (B.side σ i) ℓ' =
      B.farWeight M σ i * B.incidence σ ℓ' + B.farWeight M τ j * B.incidence τ ℓ' := by
  set R : e → ℝ := fun x => M (B.side σ i) x - B.farWeight M σ i * B.incidence σ x -
    B.farWeight M τ j * B.incidence τ x with hRdef
  suffices hR0 : ∀ x, R x = 0 by
    have := hR0 ℓ'
    simp only [hRdef] at this
    linarith
  have k2 : ∀ x : Fin 4, x + 2 ≠ x := by decide
  have four : ∀ x k : Fin 4, k = x ∨ k = x + 1 ∨ k = x + 2 ∨ k = x + 3 := by decide
  -- `R` lives on the two squares at the line
  have hsupp : ∀ x, (∀ k, B.side σ k ≠ x) → (∀ k, B.side τ k ≠ x) → R x = 0 := by
    intro x h1 h2
    have hM : M (B.side σ i) x = 0 := by
      by_contra hM
      obtain ⟨ρ, a, b, ha, hb⟩ := hR _ _ hM
      rcases B.flag_cover h hne ha with hρ | hρ
      · exact h1 b (hρ.1 ▸ hb)
      · exact h2 b (hρ.1 ▸ hb)
    simp only [hRdef, hM, B.incidence_of_not h1, B.incidence_of_not h2]
    ring
  -- `R` is closed: A10, and the edge of a square closes up
  have hcyc : ∀ w, ∑ x, R x * B.gauge x w = 0 := by
    intro w
    have h0 := congrFun (congrFun h10 (B.side σ i)) w
    have hσ := congrFun (congrFun B.incidence_mul_gauge σ) w
    have hτ := congrFun (congrFun B.incidence_mul_gauge τ) w
    simp only [Matrix.mul_apply, Matrix.zero_apply] at h0 hσ hτ
    simp only [hRdef, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, h0, hσ, hτ]
    ring
  -- `R` is `0` on the two far sides
  have hfarσ : R (B.side σ (i + 2)) = 0 := by
    have e1 : B.incidence σ (B.side σ (i + 2)) = turnSign (B.along σ (i + 2)) :=
      B.incidence_of_side rfl
    have e2 : B.incidence τ (B.side σ (i + 2)) = 0 :=
      B.incidence_of_not (hW.side_ne h hne (k2 i))
    simp only [hRdef, farWeight, e1, e2, mul_zero, mul_assoc, turnSign_mul_self, mul_one,
      sub_self]
  have hfarτ : R (B.side τ (j + 2)) = 0 := by
    have e1 : B.incidence τ (B.side τ (j + 2)) = turnSign (B.along τ (j + 2)) :=
      B.incidence_of_side rfl
    have e2 : B.incidence σ (B.side τ (j + 2)) = 0 :=
      B.incidence_of_not (hW.side_ne h.symm hne.symm (k2 j))
    simp only [hRdef, farWeight, e1, e2, h, mul_zero, sub_zero, mul_assoc, turnSign_mul_self,
      mul_one, sub_self]
  -- and on the four near sides
  obtain ⟨hσ1, hσ3⟩ := B.near_zero hW h hne R hsupp hcyc hfarσ
  obtain ⟨hτ1, hτ3⟩ :=
    B.near_zero hW h.symm hne.symm R (fun x h1 h2 => hsupp x h2 h1) hcyc hfarτ
  -- so on every line but the line itself
  have hrest : ∀ x, x ≠ B.side σ i → R x = 0 := by
    intro x hx
    by_cases h1 : ∃ k, B.side σ k = x
    · obtain ⟨k, rfl⟩ := h1
      rcases four i k with hk | hk | hk | hk <;> rw [hk] at hx ⊢
      · exact absurd rfl hx
      · exact hσ1
      · exact hfarσ
      · exact hσ3
    · by_cases h2 : ∃ k, B.side τ k = x
      · obtain ⟨k, rfl⟩ := h2
        rcases four j k with hk | hk | hk | hk <;> rw [hk] at hx ⊢
        · exact absurd h.symm hx
        · exact hτ1
        · exact hfarτ
        · exact hτ3
      · push Not at h1 h2
        exact hsupp x h1 h2
  -- and on the line itself, read at its corner `i + 1`
  have hline : R (B.side σ i) = 0 :=
    B.leaf R (B.corner σ (i + 1)) (B.side σ i) (hcyc _) (B.gauge_side_succ_ne_zero σ i)
      fun x hx => Or.inl (hrest x hx)
  intro x
  by_cases hx : x = B.side σ i
  · rw [hx]
    exact hline
  · exact hrest x hx

/-- **FL1.** On a wide board, a kick of reach 1 that is blind to a change at a corner (A10) and
keeps Gauss's law (A11) is `Cᵀ diag K C` for a number `K` on each square. -/
theorem kick_forced [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (hW : B.Wide) (M : Matrix e e ℝ) (hR : B.ReachOne M) (h10 : M * B.gauge = 0)
    (h11 : B.gaugeᵀ * M = 0) : ∃ K : f → ℝ, M = B.incidenceᵀ * diagonal K * B.incidence := by
  have n02 : ∀ x : Fin 4, x + 2 ≠ x := by decide
  have n12 : ∀ x : Fin 4, x + 2 ≠ x + 1 := by decide
  have m12 : ∀ x : Fin 4, x + 1 ≠ x + 2 := by decide
  have m13 : ∀ x : Fin 4, x + 1 ≠ x + 2 + 1 := by decide
  -- each row is a sum over the flags of its line
  have hrow : ∀ ℓ ℓ', M ℓ ℓ' = ∑ p : f × Fin 4,
      if B.side p.1 p.2 = ℓ then B.farWeight M p.1 p.2 * B.incidence p.1 ℓ' else 0 := by
    intro ℓ ℓ'
    obtain ⟨⟨σ, i⟩, ⟨hσ, hσa⟩, -⟩ := B.once_each_way ℓ true
    obtain ⟨⟨τ, j⟩, ⟨hτ, hτa⟩, -⟩ := B.once_each_way ℓ false
    dsimp only at hσ hσa hτ hτa
    subst hσ
    have hne : B.along σ i ≠ B.along τ j := by
      rw [hσa, hτa]
      decide
    have hpq : ((σ, i) : f × Fin 4) ≠ (τ, j) := by
      intro hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact hne rfl
    rw [Fintype.sum_eq_add (σ, i) (τ, j) hpq, ite_eq_left rfl, ite_eq_left hτ]
    · exact B.row_form hW M hR h10 hτ.symm hne ℓ'
    · rintro ⟨ρ, a⟩ ⟨h1, h2⟩
      refine ite_eq_right fun hρ => ?_
      dsimp only at hρ
      rcases B.flag_cover hτ.symm hne hρ with ⟨h', h''⟩ | ⟨h', h''⟩
      · exact h1 (by rw [h', h''])
      · exact h2 (by rw [h', h''])
  -- the kick read at a corner, summed over the flags
  have hflag : ∀ w ℓ', (B.gaugeᵀ * M) w ℓ' = ∑ p : f × Fin 4,
      B.gauge (B.side p.1 p.2) w * (B.farWeight M p.1 p.2 * B.incidence p.1 ℓ') := by
    intro w ℓ'
    rw [Matrix.mul_apply]
    simp only [transpose_apply, hrow _ ℓ', Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- A11 makes the weight of each side of a square, with its sign, one number round it
  have hstep : ∀ σ j, B.farWeight M σ j * turnSign (B.along σ j) =
      B.farWeight M σ (j + 1) * turnSign (B.along σ (j + 1)) := by
    intro σ j
    have h0 := congrFun (congrFun h11 (B.corner σ (j + 1))) (B.side σ (j + 2))
    rw [hflag, Matrix.zero_apply, Fintype.sum_prod_type, Fintype.sum_eq_single σ] at h0
    · have hs : B.incidence σ (B.side σ (j + 2)) = turnSign (B.along σ (j + 2)) :=
        B.incidence_of_side rfl
      simp only [B.gauge_side, (B.corner_injective σ).eq_iff, add_left_inj, hs] at h0
      simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
      have key : turnSign (B.along σ (j + 2)) * (B.farWeight M σ j * turnSign (B.along σ j) -
          B.farWeight M σ (j + 1) * turnSign (B.along σ (j + 1))) = 0 := by
        linear_combination h0
      have := (mul_eq_zero.mp key).resolve_left (turnSign_ne_zero _)
      linarith
    · intro ρ hρ
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hC : B.incidence ρ (B.side σ (j + 2)) = 0
      · rw [hC, mul_zero, mul_zero]
      · obtain ⟨b, hb⟩ : ∃ b, B.side ρ b = B.side σ (j + 2) := by
          by_contra hn
          push Not at hn
          exact hC (B.incidence_of_not hn)
        have hne : B.along σ (j + 2) ≠ B.along ρ b :=
          B.along_ne hb.symm fun hp => hρ (Prod.mk.inj hp).1.symm
        rw [B.gauge_side_eq_zero
          (fun hc => hW.corner_ne hb.symm hne ⟨m12 j, m13 j⟩ i hc.symm)
          (fun hc => hW.corner_ne hb.symm hne ⟨m12 j, m13 j⟩ (i + 1) hc.symm), zero_mul]
  have hconst : ∀ σ i, B.farWeight M σ i * turnSign (B.along σ i) =
      B.farWeight M σ 0 * turnSign (B.along σ 0) := by
    intro σ i
    have h1 := hstep σ 0
    have h2 := hstep σ 1
    have h3 := hstep σ 2
    fin_cases i
    · rfl
    · exact h1.symm
    · exact h2.symm.trans h1.symm
    · exact h3.symm.trans (h2.symm.trans h1.symm)
  have hw : ∀ ρ a, B.farWeight M ρ a =
      B.farWeight M ρ 0 * turnSign (B.along ρ 0) * turnSign (B.along ρ a) := by
    intro ρ a
    rw [← hconst ρ a, mul_assoc, turnSign_mul_self, mul_one]
  -- the kick is `Cᵀ diag K C`
  refine ⟨fun σ => B.farWeight M σ 0 * turnSign (B.along σ 0), ?_⟩
  ext ℓ ℓ'
  obtain ⟨⟨σ, i⟩, ⟨hσ, hσa⟩, -⟩ := B.once_each_way ℓ true
  obtain ⟨⟨τ, j⟩, ⟨hτ, hτa⟩, -⟩ := B.once_each_way ℓ false
  dsimp only at hσ hσa hτ hτa
  subst hσ
  have hne : B.along σ i ≠ B.along τ j := by
    rw [hσa, hτa]
    decide
  have hστ : σ ≠ τ := by
    intro hst
    subst hst
    exact hW.corner_ne hτ.symm hne ⟨n02 i, n12 i⟩ (i + 2) rfl
  have e1 : B.incidence σ (B.side σ i) = turnSign (B.along σ i) := B.incidence_of_side rfl
  have e2 : B.incidence τ (B.side σ i) = turnSign (B.along τ j) := B.incidence_of_side hτ
  rw [B.row_form hW M hR h10 hτ.symm hne ℓ', hw σ i, hw τ j, Matrix.mul_apply,
    Fintype.sum_eq_add σ τ hστ]
  · simp only [mul_diagonal, transpose_apply, e1, e2]
    ring
  · rintro ρ ⟨h1, h2⟩
    have h0 : B.incidence ρ (B.side σ i) = 0 := B.incidence_of_not fun a ha => by
      rcases B.flag_cover hτ.symm hne ha with ⟨h', -⟩ | ⟨h', -⟩
      · exact h1 h'
      · exact h2 h'
    simp only [mul_diagonal, transpose_apply, h0, zero_mul]

/-- **FL2.** On every board, every `Cᵀ diag K C` has reach 1 and meets A10 and A11. -/
theorem kick_meets [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (K : f → ℝ) :
    B.ReachOne (B.incidenceᵀ * diagonal K * B.incidence) ∧
      B.incidenceᵀ * diagonal K * B.incidence * B.gauge = 0 ∧
      B.gaugeᵀ * (B.incidenceᵀ * diagonal K * B.incidence) = 0 := by
  refine ⟨fun ℓ ℓ' h => ?_, ?_, ?_⟩
  · rw [Matrix.mul_apply] at h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    simp only [mul_diagonal, transpose_apply] at hσ
    have h1 : B.incidence σ ℓ ≠ 0 := fun h0 => hσ (by rw [h0, zero_mul, zero_mul])
    have h2 : B.incidence σ ℓ' ≠ 0 := fun h0 => hσ (by rw [h0, mul_zero])
    obtain ⟨i, hi⟩ : ∃ i, B.side σ i = ℓ := by
      by_contra hn
      push Not at hn
      exact h1 (B.incidence_of_not hn)
    obtain ⟨j, hj⟩ : ∃ j, B.side σ j = ℓ' := by
      by_contra hn
      push Not at hn
      exact h2 (B.incidence_of_not hn)
    exact ⟨σ, i, j, hi, hj⟩
  · rw [Matrix.mul_assoc, B.incidence_mul_gauge, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, B.incidence_mul_gauge,
      transpose_zero, Matrix.zero_mul, Matrix.zero_mul]

/-- **FL3.** On every board, a kick of reach 0 that is blind to a change at a corner is `0`. -/
theorem reach_zero [Fintype e] [DecidableEq v] (M : Matrix e e ℝ)
    (hR : ∀ ℓ ℓ', M ℓ ℓ' ≠ 0 → ℓ = ℓ') (h10 : M * B.gauge = 0) : M = 0 := by
  ext ℓ ℓ'
  rw [Matrix.zero_apply]
  by_cases h : ℓ = ℓ'
  · subst h
    have h0 := congrFun (congrFun h10 ℓ) (B.head ℓ)
    have hg : B.gauge ℓ (B.head ℓ) = 1 := by simp [gauge, B.tail_ne_head ℓ]
    rw [Matrix.mul_apply, Matrix.zero_apply, Fintype.sum_eq_single ℓ, hg, mul_one] at h0
    · exact h0
    · intro x hx
      have : M ℓ x = 0 := by
        by_contra hn
        exact hx (hR _ _ hn).symm
      rw [this, zero_mul]
  · by_contra hn
    exact h (hR _ _ hn)

/-- **FL4.** On a joined board, the image of `C` holds `e σ - e τ` for every two squares. -/
theorem joined_image [DecidableEq f] [Fintype e] [DecidableEq e] (hJ : B.Joined) (σ τ : f) :
    ∃ A : e → ℝ, B.incidence *ᵥ A = Pi.single σ 1 - Pi.single τ 1 := by
  obtain hst := hJ σ τ
  induction hst with
  | refl => exact ⟨0, by rw [mulVec_zero, sub_self]⟩
  | @tail ρ τ' _ hr ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨i, j, hij⟩ := hr
    by_cases hρτ : ρ = τ'
    · subst hρτ
      exact ⟨A, hA⟩
    · have hne : B.along ρ i ≠ B.along τ' j :=
        B.along_ne hij fun hp => hρτ (Prod.mk.inj hp).1
      refine ⟨A + turnSign (B.along ρ i) • Pi.single (B.side ρ i) 1, ?_⟩
      have hcol : ∀ ρ', (B.incidence *ᵥ Pi.single (B.side ρ i) 1) ρ' =
          B.incidence ρ' (B.side ρ i) := by
        intro ρ'
        simp [mulVec, dotProduct, Pi.single_apply]
      rw [mulVec_add, mulVec_smul, hA]
      funext ρ'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcol]
      by_cases h1 : ρ' = ρ
      · subst h1
        rw [B.incidence_of_side rfl, turnSign_mul_self, Pi.single_eq_same,
          Pi.single_eq_of_ne hρτ]
        ring
      · by_cases h2 : ρ' = τ'
        · subst h2
          rw [B.incidence_of_side hij.symm, turnSign_mul_of_ne hne, Pi.single_eq_same,
            Pi.single_eq_of_ne (Ne.symm hρτ)]
          ring
        · have h0 : B.incidence ρ' (B.side ρ i) = 0 := B.incidence_of_not fun a ha => by
            rcases B.flag_cover hij hne ha with ⟨h', -⟩ | ⟨h', -⟩
            · exact h1 h'
            · exact h2 h'
          rw [h0, mul_zero, add_zero, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

/-- **FL4.** On a wide board whose squares are joined and number at least three, every kick of
reach 1 that meets A10 and A11 is `Cᵀ diag K C` for exactly one `K`. -/
theorem kick_forced_unique [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e]
    [DecidableEq v] (hW : B.Wide) (hJ : B.Joined) (h3 : 2 < Fintype.card f) (M : Matrix e e ℝ)
    (hR : B.ReachOne M) (h10 : M * B.gauge = 0) (h11 : B.gaugeᵀ * M = 0) :
    ∃! K : f → ℝ, M = B.incidenceᵀ * diagonal K * B.incidence := by
  obtain ⟨K, hK⟩ := B.kick_forced hW M hR h10 h11
  exact ⟨K, hK, fun K' hK' => kick_injective _ (B.joined_image hJ) h3 (hK'.symm.trans hK)⟩

end Board

end Artform.Stages
