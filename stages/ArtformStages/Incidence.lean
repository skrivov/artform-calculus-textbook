import ArtformStages.Board
import ArtformStages.Pair

/-!
# A board and its incidence

A closed board turned one way (`Board`) is given as the boards of the research ledger on a layered
universe are given: each square has four corners in its turn, all different; its side `i` is a line
that joins its corners `i` and `i + 1`, running from `i` to `i + 1` (along) or back (against); and
each line is a side exactly once along and exactly once against. From these, with `C` the incidence
and `D` the gauge (findings 432 and 434 of the ledger):

* `Board.incidence_sq`, `Board.incidence_col`, `Board.incidence_col_sum` (BI1): `C² = |C|`, two
  squares at each line, and every column of `C` sums to `0`;
* `Board.incidence_mul_gauge`, `Board.pair_gauge` (BI2): `C D = 0`, so Pair passes the gauge;
* `Board.roundDrift_incidence`, `Board.certificate`, `Board.asked` (BI3): the local tests of the
  window, with the drift round a square the sum of `λ` over its four sides;
* `Board.window` (BI4): the certificate for the table on the lines, `4 / λ - Cᵀ κ C`;
* `torus`, `torus_certificate` (BI5): the torus is a board, and `κ λ < 1 / 2` certifies it.
-/

open Matrix

namespace Artform.Stages

/-- A closed board turned one way, with squares `f`, lines `e` and corners `v`. -/
structure Board (f e v : Type*) where
  /-- The four corners of a square, in its turn. -/
  corner : f → Fin 4 → v
  /-- The corner where a line starts. -/
  tail : e → v
  /-- The corner where a line ends. -/
  head : e → v
  /-- The side `i` of a square: the line that joins its corners `i` and `i + 1`. -/
  side : f → Fin 4 → e
  /-- Whether the side `i` of a square runs from its corner `i` to its corner `i + 1`. -/
  along : f → Fin 4 → Bool
  corner_injective : ∀ σ, Function.Injective (corner σ)
  tail_side : ∀ σ i, tail (side σ i) = bif along σ i then corner σ i else corner σ (i + 1)
  head_side : ∀ σ i, head (side σ i) = bif along σ i then corner σ (i + 1) else corner σ i
  once_each_way : ∀ ℓ b, ∃! p : f × Fin 4, side p.1 p.2 = ℓ ∧ along p.1 p.2 = b

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- The sign of a side: `1` along the turn of its square, `-1` against it. -/
def turnSign (b : Bool) : ℝ := if b then 1 else -1

/-- The four sides of a square are four different lines. -/
theorem side_injective (σ : f) : Function.Injective (B.side σ) := by
  intro i j h
  have inj := B.corner_injective σ
  have ht := (B.tail_side σ i).symm.trans ((congrArg B.tail h).trans (B.tail_side σ j))
  have hh := (B.head_side σ i).symm.trans ((congrArg B.head h).trans (B.head_side σ j))
  have key : ∀ k : Fin 4, k + 1 + 1 ≠ k := by decide
  cases hi : B.along σ i <;> cases hj : B.along σ j <;>
    simp only [hi, hj, Bool.cond_true, Bool.cond_false] at ht hh
  · exact inj hh
  · obtain rfl := inj ht
    exact absurd (inj hh).symm (key i)
  · obtain rfl := inj hh
    exact absurd (inj ht).symm (key i)
  · exact inj ht

private theorem sum_unique {α : Type*} [Fintype α] {P : α → Prop} [DecidablePred P]
    (h : ∃! a, P a) (c : ℝ) : ∑ a, (if P a then c else 0) = c := by
  obtain ⟨a, ha, hu⟩ := h
  rw [Fintype.sum_eq_single a fun b hb => ite_eq_right fun hb' => hb (hu b hb'), ite_eq_left ha]

section Incidence

variable [DecidableEq e]

/-- The incidence of a board, squares by lines: `1` where a side of the square runs along its turn,
`-1` where it runs against it. -/
def incidence : Matrix f e ℝ :=
  Matrix.of fun σ ℓ => ∑ i, if B.side σ i = ℓ then turnSign (B.along σ i) else 0

theorem incidence_apply (σ : f) (ℓ : e) :
    B.incidence σ ℓ = ∑ i, if B.side σ i = ℓ then turnSign (B.along σ i) else 0 := rfl

theorem incidence_of_side {σ : f} {i : Fin 4} {ℓ : e} (h : B.side σ i = ℓ) :
    B.incidence σ ℓ = turnSign (B.along σ i) := by
  rw [incidence_apply, Fintype.sum_eq_single i fun j hj =>
    ite_eq_right fun hj' => hj (B.side_injective σ (hj'.trans h.symm)), ite_eq_left h]

theorem incidence_of_not {σ : f} {ℓ : e} (h : ∀ i, B.side σ i ≠ ℓ) : B.incidence σ ℓ = 0 := by
  rw [incidence_apply]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (h i)

/-- BI1. The entries of the incidence are `-1`, `0` and `1`. -/
theorem incidence_sq (σ : f) (ℓ : e) : B.incidence σ ℓ ^ 2 = |B.incidence σ ℓ| := by
  by_cases h : ∃ i, B.side σ i = ℓ
  · obtain ⟨i, hi⟩ := h
    rw [B.incidence_of_side hi]
    cases B.along σ i <;> norm_num [turnSign]
  · push Not at h
    simp [B.incidence_of_not h]

theorem abs_incidence (σ : f) (ℓ : e) :
    |B.incidence σ ℓ| = ∑ i, if B.side σ i = ℓ then (1 : ℝ) else 0 := by
  by_cases h : ∃ i, B.side σ i = ℓ
  · obtain ⟨i, hi⟩ := h
    rw [B.incidence_of_side hi, Fintype.sum_eq_single i fun j hj =>
      ite_eq_right fun hj' => hj (B.side_injective σ (hj'.trans hi.symm)), ite_eq_left hi]
    cases B.along σ i <;> norm_num [turnSign]
  · push Not at h
    rw [B.incidence_of_not h, abs_zero]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right (h i)).symm

/-- BI1. Each line is a side of two squares: every column's sizes sum to `2`. -/
theorem incidence_col [Fintype f] (ℓ : e) : ∑ σ, |B.incidence σ ℓ| = 2 := by
  simp_rw [B.abs_incidence]
  rw [← Fintype.sum_prod_type']
  have split : ∀ p : f × Fin 4, (if B.side p.1 p.2 = ℓ then (1 : ℝ) else 0) =
      (if B.side p.1 p.2 = ℓ ∧ B.along p.1 p.2 = true then 1 else 0) +
        (if B.side p.1 p.2 = ℓ ∧ B.along p.1 p.2 = false then 1 else 0) := by
    intro p
    by_cases hs : B.side p.1 p.2 = ℓ <;> cases B.along p.1 p.2 <;> simp [hs]
  rw [Finset.sum_congr rfl fun p _ => split p, Finset.sum_add_distrib,
    sum_unique (B.once_each_way ℓ true), sum_unique (B.once_each_way ℓ false)]
  norm_num

/-- BI1. The board is turned one way: every column of the incidence sums to `0`. -/
theorem incidence_col_sum [Fintype f] (ℓ : e) : ∑ σ, B.incidence σ ℓ = 0 := by
  simp_rw [B.incidence_apply]
  rw [← Fintype.sum_prod_type']
  have split : ∀ p : f × Fin 4,
      (if B.side p.1 p.2 = ℓ then turnSign (B.along p.1 p.2) else 0) =
        (if B.side p.1 p.2 = ℓ ∧ B.along p.1 p.2 = true then 1 else 0) +
          (if B.side p.1 p.2 = ℓ ∧ B.along p.1 p.2 = false then -1 else 0) := by
    intro p
    by_cases hs : B.side p.1 p.2 = ℓ <;> cases B.along p.1 p.2 <;> simp [hs, turnSign]
  rw [Finset.sum_congr rfl fun p _ => split p, Finset.sum_add_distrib,
    sum_unique (B.once_each_way ℓ true), sum_unique (B.once_each_way ℓ false)]
  norm_num

/-- BI3. The drift round a square is the sum of `λ` over its four sides. -/
theorem roundDrift_incidence [Fintype e] (l : e → ℝ) (σ : f) :
    roundDrift B.incidence l σ = ∑ i, l (B.side σ i) := by
  simp only [roundDrift, B.abs_incidence, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- BI3. On every board, `κ σ` times the sum of `λ` over the four sides of `σ` below `2` at every
square makes the table on the squares positive definite. -/
theorem certificate [Finite f] [Fintype e] [DecidableEq f] (κ : f → ℝ) (l : e → ℝ)
    (hκ : ∀ σ, 0 < κ σ) (hl : ∀ ℓ, 0 ≤ l ℓ) (h : ∀ σ, κ σ * ∑ i, l (B.side σ i) < 2) :
    (squareTable B.incidence κ l).PosDef := by
  have := Fintype.ofFinite f
  refine board_local_sufficient _ κ l B.incidence_sq B.incidence_col hκ hl fun σ => ?_
  rw [B.roundDrift_incidence]
  exact h σ

/-- BI3. A positive definite table on the squares has `κ σ` times the sum of `λ` over the four
sides of `σ` below `4` at every square. -/
theorem asked [Fintype e] [DecidableEq f] (κ : f → ℝ) (l : e → ℝ) (hκ : ∀ σ, 0 < κ σ)
    (hP : (squareTable B.incidence κ l).PosDef) (σ : f) : κ σ * ∑ i, l (B.side σ i) < 4 := by
  rw [← B.roundDrift_incidence]
  exact board_local_necessary _ κ l B.incidence_sq hκ hP σ

/-- BI4. With every `λ` positive, the same test makes the table on the lines, the diagonal of
`4 / λ` less `Cᵀ diag(κ) C`, positive definite. -/
theorem window [Fintype f] [Finite e] [DecidableEq f] (κ : f → ℝ) (l : e → ℝ)
    (hκ : ∀ σ, 0 < κ σ) (hl : ∀ ℓ, 0 < l ℓ) (h : ∀ σ, κ σ * ∑ i, l (B.side σ i) < 2) :
    (diagonal (fun ℓ => 4 / l ℓ) - B.incidenceᵀ * diagonal κ * B.incidence).PosDef := by
  have := Fintype.ofFinite e
  have hS := B.certificate κ l hκ (fun ℓ => (hl ℓ).le) h
  set C := B.incidence
  have hA : (diagonal fun σ => 4 / κ σ).PosDef := PosDef.diagonal fun σ => div_pos four_pos (hκ σ)
  have hD : (diagonal fun ℓ => 1 / l ℓ).PosDef := PosDef.diagonal fun ℓ => one_div_pos.mpr (hl ℓ)
  have hAi : (diagonal fun σ => κ σ / 4) * diagonal (fun σ => 4 / κ σ) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext σ
    field_simp [(hκ σ).ne']
  have hDi : diagonal l * diagonal (fun ℓ => 1 / l ℓ) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext ℓ
    field_simp [(hl ℓ).ne']
  let iA : Invertible (diagonal fun σ => 4 / κ σ) := invertibleOfLeftInverse _ _ hAi
  let iD : Invertible (diagonal fun ℓ => 1 / l ℓ) := invertibleOfLeftInverse _ _ hDi
  have hL := (window_dual_strict C hA hD).mpr (by
    rw [inv_eq_left_inv hDi, conjTranspose_eq_transpose_of_trivial]
    exact hS)
  rw [inv_eq_left_inv hAi, conjTranspose_eq_transpose_of_trivial] at hL
  have h4 := hL.smul (show (0 : ℝ) < 4 by norm_num)
  convert h4 using 1
  ext ℓ ℓ'
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply, diagonal_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · split_ifs <;> ring
  · exact Finset.sum_congr rfl fun σ _ => by ring

end Incidence

section Gauge

variable [DecidableEq v]

/-- The gauge of a board, lines by corners: it takes `g` to `g (head) - g (tail)`. -/
def gauge : Matrix e v ℝ :=
  Matrix.of fun ℓ w => (if B.head ℓ = w then 1 else 0) - (if B.tail ℓ = w then 1 else 0)

/-- BI2. `C D = 0`: the sides of each square close up round it. -/
theorem incidence_mul_gauge [DecidableEq e] [Fintype e] : B.incidence * B.gauge = 0 := by
  ext σ w
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [incidence_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h2 : ∀ i, turnSign (B.along σ i) * B.gauge (B.side σ i) w =
      (if B.corner σ (i + 1) = w then 1 else 0) - (if B.corner σ i = w then 1 else 0) := by
    intro i
    simp only [gauge, Matrix.of_apply, B.tail_side, B.head_side]
    cases B.along σ i <;> simp [turnSign]
  simp only [h2, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

/-- BI2. On every board, Pair with the kick `Cᵀ K C` passes the gauge (finding 422's PA4). -/
theorem pair_gauge [DecidableEq e] [Fintype f] [Fintype e] [Fintype v] (K : Matrix f f ℝ)
    (L : Matrix e e ℝ) (A E : e → ℝ) (g : v → ℝ) :
    pair (B.incidenceᵀ * K * B.incidence) L (A + B.gauge *ᵥ g, E) =
      ((pair (B.incidenceᵀ * K * B.incidence) L (A, E)).1 + B.gauge *ᵥ g,
        (pair (B.incidenceᵀ * K * B.incidence) L (A, E)).2) :=
  _root_.Artform.Stages.pair_gauge _ _ K L B.incidence_mul_gauge A E g

end Gauge

end Board

/-- The torus of `n` by `m` squares. Its corners and its squares are the pairs of
`ZMod n × ZMod m`; the line `(w, 0)` runs from `w` to `w + (1, 0)` and the line `(w, 1)` from `w`
to `w + (0, 1)`; the square `σ` has the corners `σ`, `σ + (1, 0)`, `σ + (1, 1)`, `σ + (0, 1)` in
its turn. -/
def torus (n m : ℕ) [Fact (1 < n)] [Fact (1 < m)] :
    Board (ZMod n × ZMod m) ((ZMod n × ZMod m) × Fin 2) (ZMod n × ZMod m) where
  corner σ := ![σ, σ + (1, 0), σ + (1, 1), σ + (0, 1)]
  tail ℓ := ℓ.1
  head ℓ := ℓ.1 + ![((1 : ZMod n), (0 : ZMod m)), (0, 1)] ℓ.2
  side σ := ![(σ, 0), (σ + (1, 0), 1), (σ + (0, 1), 0), (σ, 1)]
  along _ := ![true, true, false, false]
  corner_injective σ := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [Prod.ext_iff] at h ⊢
  tail_side σ i := by fin_cases i <;> simp
  head_side σ i := by fin_cases i <;> simp [add_assoc]
  once_each_way := by
    rintro ⟨w, d⟩ b
    fin_cases d <;> cases b
    · exact ⟨(w - (0, 1), 2), by simp, fun ⟨σ, i⟩ h => by
        fin_cases i <;> simp_all [eq_sub_iff_add_eq]⟩
    · exact ⟨(w, 0), by simp, fun ⟨σ, i⟩ h => by fin_cases i <;> simp_all⟩
    · exact ⟨(w, 3), by simp, fun ⟨σ, i⟩ h => by fin_cases i <;> simp_all⟩
    · exact ⟨(w - (1, 0), 1), by simp, fun ⟨σ, i⟩ h => by
        fin_cases i <;> simp_all [eq_sub_iff_add_eq]⟩

/-- BI5. On every torus with one `κ > 0` and one `λ ≥ 0`, `κ λ < 1 / 2` makes the table on the
squares positive definite. -/
theorem torus_certificate (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)] {κ l : ℝ}
    (hκ : 0 < κ) (hl : 0 ≤ l) (h : κ * l < 1 / 2) :
    (squareTable (torus n m).incidence (fun _ => κ) (fun _ => l)).PosDef :=
  (torus n m).certificate _ _ (fun _ => hκ) (fun _ => hl) fun σ => by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    nlinarith

end Artform.Stages
