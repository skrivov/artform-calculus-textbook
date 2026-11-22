import ArtformStages.Coulomb
import ArtformStages.Waves

/-!
# A flat field that no gauge removes

On the torus, the circulation of `A` round a row of lines is a gauge invariant. The row field, `a`
on every line of one direction, is flat, `C A = 0`, yet its circulation is `n a`, so no gauge change
removes it; as an electric field it has no charge, and Pair keeps it while it winds the
circulation without end (finding 446 of the research ledger on a layered universe):

* `row_circulation_gauge` (HO1): the circulation round a row passes every gauge change;
* `row_field_curl`, `row_field_circulation` (HO2, HO3): the row field is flat, with circulation
  `n a`;
* `row_field_not_gauge` (HO4): for `a ≠ 0`, `rowField a + G g ≠ 0` for every `g`;
* `row_field_divergence` (HO5): the row field has no divergence;
* `row_field_pair`, `row_field_pair_iterate` (HO6): Pair sends `(rowField a, rowField ε)` after `k`
  steps to `(rowField (a - k λ ε), rowField ε)`.
-/

open Matrix

namespace Artform.Stages

/-- The circulation of `A` round the row `y` of the torus: the sum of `A` over the lines
`((k, y), 0)`, each from `(k, y)` to `(k + 1, y)`. -/
def rowCirculation {n m : ℕ} [NeZero n] (A : (ZMod n × ZMod m) × Fin 2 → ℝ) (y : ZMod m) : ℝ :=
  ∑ k : ZMod n, A ((k, y), 0)

/-- The row field of `a`: `a` on every line of the direction `0`, and `0` on the others. -/
def rowField (n m : ℕ) (a : ℝ) : (ZMod n × ZMod m) × Fin 2 → ℝ :=
  fun ℓ => if ℓ.2 = 0 then a else 0

variable (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]

/-- HO1. The circulation round every row passes every gauge change. -/
theorem row_circulation_gauge (A : (ZMod n × ZMod m) × Fin 2 → ℝ) (g : ZMod n × ZMod m → ℝ)
    (y : ZMod m) : rowCirculation (A + (torus n m).gauge *ᵥ g) y = rowCirculation A y := by
  simp only [rowCirculation, Pi.add_apply, Finset.sum_add_distrib, Board.gauge_mulVec]
  have hs := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun k => g (k, y))
  simp only [Equiv.coe_addRight] at hs
  have h : ∑ k : ZMod n, (g ((torus n m).head ((k, y), 0)) - g ((torus n m).tail ((k, y), 0))) =
      0 := by
    simp only [torus, Matrix.cons_val_zero, Prod.mk_add_mk, add_zero]
    rw [Finset.sum_sub_distrib, hs, sub_self]
  rw [h, add_zero]

/-- HO2. The row field is flat: `C (rowField a) = 0`. -/
theorem row_field_curl (a : ℝ) : (torus n m).incidence *ᵥ rowField n m a = 0 := by
  funext σ
  rw [Board.incidence_mulVec, Fin.sum_univ_four]
  simp [torus, rowField, Board.turnSign]

omit [NeZero m] [Fact (1 < n)] [Fact (1 < m)] in
/-- HO3. The circulation of the row field round every row is `n a`. -/
theorem row_field_circulation (a : ℝ) (y : ZMod m) :
    rowCirculation (rowField n m a) y = n * a := by
  simp [rowCirculation, rowField, Finset.sum_const, Finset.card_univ, ZMod.card]

/-- HO4. For `a ≠ 0` no gauge change removes the row field. -/
theorem row_field_not_gauge (a : ℝ) (ha : a ≠ 0) (g : ZMod n × ZMod m → ℝ) :
    rowField n m a + (torus n m).gauge *ᵥ g ≠ 0 := by
  intro h
  have h1 : rowCirculation (rowField n m a + (torus n m).gauge *ᵥ g) 0 =
      rowCirculation (0 : (ZMod n × ZMod m) × Fin 2 → ℝ) 0 := by rw [h]
  rw [row_circulation_gauge, row_field_circulation] at h1
  have h0 : rowCirculation (0 : (ZMod n × ZMod m) × Fin 2 → ℝ) 0 = 0 := by simp [rowCirculation]
  rw [h0] at h1
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact ha ((mul_eq_zero.mp h1).resolve_left hn)

/-- HO5. The row field has no divergence: as an electric field it carries no charge. -/
theorem row_field_divergence (ε : ℝ) : divergence (torus n m).gauge (rowField n m ε) = 0 := by
  funext w
  have hline : ∀ x : ZMod n × ZMod m,
      (torus n m).gauge (x, 0) w * rowField n m ε (x, 0) +
          (torus n m).gauge (x, 1) w * rowField n m ε (x, 1) = (torus n m).gauge (x, 0) w * ε := by
    intro x
    simp [rowField]
  have hsum : ∑ x : ZMod n × ZMod m, (torus n m).gauge (x, 0) w = 0 := by
    have h1 : ∀ x : ZMod n × ZMod m, (x + (1, 0) = w) ↔ (x = w - (1, 0)) :=
      fun x => eq_sub_iff_add_eq.symm
    have h2 : ∑ x : ZMod n × ZMod m, (torus n m).gauge (x, 0) w =
        ∑ x : ZMod n × ZMod m,
          ((if x = w - (1, 0) then (1 : ℝ) else 0) - (if x = w then 1 else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases ha : x = w - (1, 0) <;> by_cases hb : x = w <;> simp [Board.gauge, torus, h1, ha, hb]
    rw [h2]
    simp [Finset.sum_sub_distrib]
  have key : ((torus n m).gaugeᵀ *ᵥ rowField n m ε) w = 0 := by
    simp only [mulVec, dotProduct, transpose_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, hline]
    rw [← Finset.sum_mul, hsum, zero_mul]
  simp [divergence, key]

/-- HO6. With a kick `Cᵀ diag κ C` and one drift `λ`, Pair keeps the electric row field and moves
the potential's row field by `- λ ε`. -/
theorem row_field_pair (κ : ZMod n × ZMod m → ℝ) (l a ε : ℝ) :
    pair ((torus n m).incidenceᵀ * diagonal κ * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) (rowField n m a, rowField n m ε) =
      (rowField n m (a - l * ε), rowField n m ε) := by
  have h0 :
      ((torus n m).incidenceᵀ * diagonal κ * (torus n m).incidence) *ᵥ rowField n m a = 0 := by
    rw [← mulVec_mulVec, row_field_curl, mulVec_zero]
  simp only [pair, h0, add_zero, Prod.mk.injEq, and_true]
  funext ℓ
  simp only [rowField, Pi.sub_apply, mulVec_diagonal]
  split_ifs <;> ring

/-- HO6. After `k` steps, `(rowField a, rowField ε)` is `(rowField (a - k λ ε), rowField ε)`: the
circulation falls by `n λ ε` at each step, without end. -/
theorem row_field_pair_iterate (κ : ZMod n × ZMod m → ℝ) (l a ε : ℝ) (k : ℕ) :
    (pair ((torus n m).incidenceᵀ * diagonal κ * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l))^[k] (rowField n m a, rowField n m ε) =
      (rowField n m (a - k * l * ε), rowField n m ε) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, row_field_pair]
    congr 2
    push_cast
    ring

end Artform.Stages
