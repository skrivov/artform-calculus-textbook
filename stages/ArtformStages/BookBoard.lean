import ArtformStages.OneRule

/-!
# The book's board

Finding 434 of the research ledger on a layered universe built the torus of `n` by `m` squares
as a `Board`, and findings 440 and 449 proved that on a wide board whose corners all have one
paint the askings leave one kick, `κ Cᵀ C`, and one drift, `λ`. Here the torus is shown to be such
a board (finding 453 of the ledger):

* `torus_flag_zero`, `torus_flag_one` (BB1): the two flags of each line of the torus;
* `torus_wide` (BB2): for `n, m ≥ 3` the torus is wide;
* `torus_paint` (BB3): every corner of the torus has the paint 4;
* `torus_kick_forced`, `torus_drift_forced` (BB4): so on the torus a kick of reach 1 that meets
  A10, A11 and one rule for the far weights is `Cᵀ diag κ C` with one `κ`, and a drift that is one
  rule is one number.
-/

open Matrix

namespace Artform.Stages

variable (n m : ℕ) [Fact (1 < n)] [Fact (1 < m)]

/-- **BB1.** The line `(w, 0)` has the two flags `(w, 0)`, along its square's turn, and
`(w - (0, 1), 2)`, against it. -/
theorem torus_flag_zero (σ w : ZMod n × ZMod m) (i : Fin 4) :
    (torus n m).side σ i = (w, 0) ↔
      ((σ, i) = (w, 0) ∧ (torus n m).along σ i = true) ∨
        ((σ, i) = (w - (0, 1), 2) ∧ (torus n m).along σ i = false) := by
  constructor
  · intro h
    fin_cases i <;> simp_all [torus, Prod.ext_iff, eq_sub_iff_add_eq]
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [torus]

/-- **BB1.** The line `(w, 1)` has the two flags `(w - (1, 0), 1)`, along its square's turn, and
`(w, 3)`, against it. -/
theorem torus_flag_one (σ w : ZMod n × ZMod m) (i : Fin 4) :
    (torus n m).side σ i = (w, 1) ↔
      ((σ, i) = (w - (1, 0), 1) ∧ (torus n m).along σ i = true) ∨
        ((σ, i) = (w, 3) ∧ (torus n m).along σ i = false) := by
  constructor
  · intro h
    fin_cases i <;> simp_all [torus, Prod.ext_iff, eq_sub_iff_add_eq]
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [torus]

/-- In `ZMod k` with `k ≥ 3`, `1 ≠ -1`. -/
theorem zmod_one_ne_neg_one {k : ℕ} (hk : 2 < k) : (1 : ZMod k) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod k) = 0 := by
    have : (1 : ZMod k) + 1 = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel 1
    rw [← one_add_one_eq_two] at *
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- **BB2.** For `n, m ≥ 3` the torus is wide: the two squares at a line share no corner but the
line's two ends. -/
theorem torus_wide (hn : 2 < n) (hm : 2 < m) : (torus n m).Wide := by
  have h1n : (1 : ZMod n) ≠ -1 := zmod_one_ne_neg_one hn
  have h1m : (1 : ZMod m) ≠ -1 := zmod_one_ne_neg_one hm
  have hn1 : (-1 : ZMod n) ≠ 1 := fun h => h1n h.symm
  have hm1 : (-1 : ZMod m) ≠ 1 := fun h => h1m h.symm
  intro σ τ i j h hne a b hc
  rcases hl : (torus n m).side τ j with ⟨w, d⟩
  have hσl := h.trans hl
  fin_cases d
  · rcases (torus_flag_zero n m σ w i).mp hσl with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases (torus_flag_zero n m τ w j).mp hl with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1 <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3 <;>
      first
      | exact absurd rfl hne
      | (fin_cases a <;> fin_cases b <;>
          simp [torus, Prod.ext_iff, sub_eq_add_neg, add_assoc, h1m, hm1] at hc ⊢)
  · rcases (torus_flag_one n m σ w i).mp hσl with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases (torus_flag_one n m τ w j).mp hl with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1 <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3 <;>
      first
      | exact absurd rfl hne
      | (fin_cases a <;> fin_cases b <;>
          simp [torus, Prod.ext_iff, sub_eq_add_neg, add_assoc, h1n, hn1] at hc ⊢)

variable [NeZero n] [NeZero m]

/-- **BB3.** Every corner of the torus has the paint 4: it is a corner of the four squares
`w`, `w - (1, 0)`, `w - (1, 1)` and `w - (0, 1)`. -/
theorem torus_paint (w : ZMod n × ZMod m) : (torus n m).paint w = 4 := by
  have hset : (Finset.univ.filter fun σ => ∃ a, (torus n m).corner σ a = w) =
      {w, w - (1, 0), w - (1, 1), w - (0, 1)} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp [torus, eq_sub_iff_add_eq]
  rw [Board.paint, hset]
  simp [Prod.ext_iff, sub_eq_add_neg]

/-- **BB4.** For `n, m ≥ 3`, on the torus a kick of reach 1 that is blind to a change at a corner
(A10), keeps Gauss's law (A11) and is one rule for the far weights is `Cᵀ diag κ C` with one number
`κ` on every square. -/
theorem torus_kick_forced (hn : 2 < n) (hm : 2 < m)
    (M : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (hR : (torus n m).ReachOne M) (h10 : M * (torus n m).gauge = 0)
    (h11 : (torus n m).gaugeᵀ * M = 0) (h1 : (torus n m).OneRuleFar M) :
    ∃ κ : ℝ, M = (torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
      (torus n m).incidence :=
  (torus n m).one_rule_one_number (torus_wide n m hn hm)
    (fun w w' => by rw [torus_paint, torus_paint]) M hR h10 h11 h1

/-- **BB4.** On the torus a drift that is one rule, `λ` at a line one function of the paints at its
two ends, is one number. -/
theorem torus_drift_forced (l : (ZMod n × ZMod m) × Fin 2 → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ ℓ, l ℓ = G ((torus n m).paint ((torus n m).tail ℓ))
      ((torus n m).paint ((torus n m).head ℓ))) :
    ∃ c : ℝ, l = fun _ => c :=
  (torus n m).drift_one_number (fun w w' => by rw [torus_paint, torus_paint]) l G hG

end Artform.Stages
