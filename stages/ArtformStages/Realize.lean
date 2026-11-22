import ArtformStages.Pair

/-!
# The reading of a table on a finite space

On a finite space `H` of laws (a finite group whose laws pass), a filling of `R[H]` is a vector
of numbers, one at each law, and a stencil is a table of numbers: its *regular reading*. Read so,
a table of stencils over `R[H]` with rows `m` and columns `n` is a table over `R` with rows
`m × H` and columns `n × H`, and Pair passes to the reading. This is the realization square
`ρ (T_quotient y) = T_W39 (ρ y)` of astra's wave 39 in the research ledger on a layered
universe, proved for every table of stencils:

* `realize`, `realizeVec`, `realizeState` (RZ1): the reading of a table, of a filling and of a
  state.
* `coeff_mul_fintype`, `realize_mulVec`, `realize_mul`, `realize_turned`,
  `realizeVec_injective` (RZ2): the reading turns products of stencils into products of
  tables, and turning over into the transpose; it loses nothing.
* `realize_pair`, `realize_periodize_pair` (RZ3): the realization square, and astra's two
  squares in one, with `periodize_pair` of `Pair.lean`.

None of this is new: it is the regular representation of a finite group, read on matrices.
-/

open Matrix MonoidAlgebra

namespace Artform.Stages

section Reading

variable {R : Type*} [CommRing R] {H : Type*}

/-- RZ1. The reading of a table of stencils: at `(i, h), (j, h')`, the number of `C i j` at
`h h'⁻¹`. -/
def realize [CommGroup H] {m n : Type*} (C : Matrix m n R[H]) : Matrix (m × H) (n × H) R :=
  Matrix.of fun a b => (C a.1 b.1).coeff (a.2 * b.2⁻¹)

/-- RZ1. The reading of a filling: its numbers, one at each cell and law. -/
def realizeVec {n : Type*} (x : n → R[H]) : n × H → R := fun a => (x a.1).coeff a.2

/-- RZ1. The reading of a state. -/
def realizeState {n : Type*} (x : LightState R[H] n) : LightState R (n × H) :=
  (realizeVec x.1, realizeVec x.2)

/-- RZ2. On a finite group, the number of a product at `g` is a finite sum. -/
theorem coeff_mul_fintype [CommGroup H] [Fintype H] (a b : R[H]) (g : H) :
    (a * b).coeff g = ∑ h : H, a.coeff (g * h⁻¹) * b.coeff h := by
  rw [coeff_mul_apply_right, Finsupp.sum_fintype]
  intro h
  exact mul_zero _

theorem realizeVec_add {n : Type*} (x y : n → R[H]) :
    realizeVec (x + y) = realizeVec x + realizeVec y := by
  funext a
  simp [realizeVec, coeff_add]

theorem realizeVec_sub {n : Type*} (x y : n → R[H]) :
    realizeVec (x - y) = realizeVec x - realizeVec y := by
  funext a
  simp [realizeVec, coeff_sub]

/-- RZ2. The reading of a table times a filling. -/
theorem realize_mulVec [CommGroup H] [Fintype H] {m n : Type*}
    [Fintype n] (M : Matrix m n R[H]) (x : n → R[H]) :
    realizeVec (M *ᵥ x) = realize M *ᵥ realizeVec x := by
  funext ⟨i, h⟩
  simp only [realizeVec, realize, mulVec, dotProduct, Matrix.of_apply, coeff_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, coeff_mul_fintype, Fintype.sum_prod_type]

/-- RZ2. The reading of a product of tables. -/
theorem realize_mul [CommGroup H] [Fintype H] {m n p : Type*} [Fintype n] (X : Matrix m n R[H])
    (Y : Matrix n p R[H]) :
    realize (X * Y) = realize X * realize Y := by
  ext ⟨i, h⟩ ⟨k, h''⟩
  simp only [realize, Matrix.of_apply, Matrix.mul_apply, coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, coeff_mul_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight h'') _ _ fun u => ?_
  simp only [Equiv.coe_mulRight, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel, mul_one]

/-- Turning over, read at a law: the number at its inverse. -/
theorem coeff_turnOver [CommGroup H] (a : R[H]) (g : H) :
    (turnOver R H a).coeff g = a.coeff g⁻¹ := by
  have key := Finsupp.mapDomain_apply_of_injective
    (inv_injective : Function.Injective fun x : H => x⁻¹) a.coeff g⁻¹
  rw [inv_inv] at key
  exact key

/-- RZ2. The reading of a table turned over is the transpose of its reading. -/
theorem realize_turned [CommGroup H] {m n : Type*} (C : Matrix m n R[H]) :
    realize (turned C) = (realize C)ᵀ := by
  ext ⟨j, h⟩ ⟨i, h'⟩
  simp only [realize, turned, Matrix.of_apply, transpose_apply, Matrix.map_apply, coeff_turnOver,
    _root_.mul_inv_rev, inv_inv]

/-- RZ2. The reading of fillings loses nothing. -/
theorem realizeVec_injective {n : Type*} :
    Function.Injective (realizeVec (R := R) (H := H) (n := n)) := by
  intro x y hxy
  funext j
  ext h
  exact congrFun hxy (j, h)

/-- RZ3. The realization square: the reading of the Pair built from `S` and `L` over `R[H]` is
the Pair built from their readings. -/
theorem realize_pair [CommGroup H] [Fintype H] {n : Type*} [Fintype n] (S L : Matrix n n R[H])
    (x : LightState R[H] n) :
    realizeState (pair S L x) = pair (realize S) (realize L) (realizeState x) := by
  obtain ⟨A, E⟩ := x
  simp only [realizeState, pair, realizeVec_add, realizeVec_sub, realize_mulVec]

/-- RZ3. Astra's two squares in one: the reading of the periodized Pair of the plane is the
Pair on the finite board whose kick is `Cᵀ K C`, with `C` the reading of the periodized edge
and `K` the reading of the periodized weights. -/
theorem realize_periodize_pair [CommGroup H] [Fintype H] {G : Type*} [CommGroup G] {f n : Type*}
    [Fintype f] [Fintype n]
    (p : G →* H) (C : Matrix f n R[G]) (K : Matrix f f R[G]) (L : Matrix n n R[G])
    (x : LightState R[G] n) :
    realizeState (mapState (mapDomainRingHom R p) (pair (turned C * K * C) L x)) =
      pair ((realize (C.map (mapDomainRingHom R p)))ᵀ * realize (K.map (mapDomainRingHom R p)) *
          realize (C.map (mapDomainRingHom R p)))
        (realize (L.map (mapDomainRingHom R p)))
        (realizeState (mapState (mapDomainRingHom R p) x)) := by
  rw [periodize_pair, realize_pair, realize_mul, realize_mul, realize_turned]

end Reading

end Artform.Stages
