import ArtformTextbook.Ch05.Statements

/-!
# Holonomy descent, and pure gauge equals loop-flat

Theorem 5.23 (`thm:holonomy-descent`) and Theorem 5.27 (`thm:pure-gauge`),
with what their proofs use about the paths of a transport skeleton: joining
two paths, reversing a path, and the holonomy of each.

The last section checks both theorems on the book's running example, the
transport skeleton of the two squares with the group `C₃`.
-/

namespace Artform

namespace Skeleton

variable {X : Skeleton}

/-- The target of `ē` is the source of `e`. -/
theorem tgt_rev (e : X.E) : X.tgt (X.rev e) = X.src e := by
  rw [← X.src_rev, X.rev_rev]

namespace Path

/-- The path `γ δ`, which runs along `δ` from `u` to `v` and then along `γ`
from `v` to `w`. It is written right to left, as the book writes paths. -/
def comp {u v : X.V} : {w : X.V} → X.Path v w → X.Path u v → X.Path u w
  | _, .nil _, δ => δ
  | _, .cons e γ, δ => .cons e (comp γ δ)

/-- A path whose ends are renamed along equalities. -/
def cast {u u' v v' : X.V} (hu : u = u') (hv : v = v') (γ : X.Path u v) : X.Path u' v' :=
  hu ▸ hv ▸ γ

/-- The path of one step along `ē`, from the target of `e` to its source. -/
def back (e : X.E) : X.Path (X.tgt e) (X.src e) :=
  (Path.cons (X.rev e) (.nil _)).cast (X.src_rev e) (X.tgt_rev e)

/-- The reversed path, from the end of `γ` to its start: for `γ = e_k ⋯ e₁` it
is `ē₁ ⋯ ē_k`. -/
def reverse {u : X.V} : {v : X.V} → X.Path u v → X.Path v u
  | _, .nil _ => .nil _
  | _, .cons e γ => comp (reverse γ) (back e)

/-- The oriented edges of a path `γ = e_k ⋯ e₁`, in the book's order
`[e_k, …, e₁]`: the edge traversed first comes last. -/
def edges {u : X.V} : {v : X.V} → X.Path u v → List X.E
  | _, .nil _ => []
  | _, .cons e γ => e :: edges γ

end Path

/-- A skeleton is connected as soon as paths run from one vertex `v₀` to every
vertex: a path from `u` to `v` goes back from `u` to `v₀`, then on to `v`. -/
theorem connected_of_base (v₀ : X.V) (h : ∀ v, Nonempty (X.Path v₀ v)) : X.Connected := by
  intro u v
  obtain ⟨p⟩ := h u
  obtain ⟨q⟩ := h v
  exact ⟨q.comp p.reverse⟩

variable {G : Type*} [Group G] (U : X.LinkTable G)

/-- The holonomy of the empty path is `1`. -/
@[simp]
theorem hol_nil (v : X.V) : hol U (.nil v) = 1 := by
  simp [hol]

/-- One more step `e` multiplies the holonomy by `U_e` on the left. -/
@[simp]
theorem hol_cons {u : X.V} (e : X.E) (γ : X.Path u (X.src e)) :
    hol U (.cons e γ) = U e * hol U γ := by
  simp [hol]

/-- Equation `eq:path-holonomy`: `Hol_U(γ) = U_{e_k} ⋯ U_{e₁}` for
`γ = e_k ⋯ e₁`. -/
theorem hol_eq_prod {u v : X.V} (γ : X.Path u v) : hol U γ = (γ.edges.map U).prod := by
  induction γ with
  | nil => simp [Path.edges]
  | cons e γ ih => simp [Path.edges, ih]

/-- The holonomy of `γ δ` is `Hol(γ) Hol(δ)`. -/
@[simp]
theorem hol_comp {u v w : X.V} (γ : X.Path v w) (δ : X.Path u v) :
    hol U (γ.comp δ) = hol U γ * hol U δ := by
  induction γ with
  | nil => simp [Path.comp]
  | cons e γ ih => simp [Path.comp, ih, mul_assoc]

/-- Renaming the ends of a path does not change its holonomy. -/
@[simp]
theorem hol_cast {u u' v v' : X.V} (hu : u = u') (hv : v = v') (γ : X.Path u v) :
    hol U (γ.cast hu hv) = hol U γ := by
  subst hu hv
  rfl

/-- By the reversal law, one step along `ē` carries `U_ē = U_e⁻¹`. -/
@[simp]
theorem hol_back (e : X.E) : hol U (Path.back e) = (U e)⁻¹ := by
  simp [Path.back, U.reversal]

/-- The reversed path has the inverse holonomy. -/
@[simp]
theorem hol_reverse {u v : X.V} (γ : X.Path u v) : hol U γ.reverse = (hol U γ)⁻¹ := by
  induction γ with
  | nil => simp [Path.reverse]
  | cons e γ ih => simp [Path.reverse, ih]

/-- The gauge action on one oriented edge, `U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`. -/
theorem gaugeAct_apply (h : X.V → G) (e : X.E) :
    gaugeAct h U e = h (X.tgt e) * U e * (h (X.src e))⁻¹ :=
  rfl

/-- Equation `eq:holonomy-covariance`: under the gauge action the holonomy of a
path from `u` to `v` becomes `h_v Hol_U(γ) h_u⁻¹`. At every interior vertex the
factor `h⁻¹` of one edge meets the factor `h` of the next, and the two cancel. -/
theorem hol_gaugeAct (h : X.V → G) {u v : X.V} (γ : X.Path u v) :
    hol (gaugeAct h U) γ = h v * hol U γ * (h u)⁻¹ := by
  induction γ with
  | nil => simp
  | cons e γ ih =>
    rw [hol_cons, hol_cons, ih, gaugeAct_apply]
    group

/-- If `U_e = c_{t(e)} c_{s(e)}⁻¹` on every oriented edge, the holonomy of a
path from `u` to `v` telescopes to `c_v c_u⁻¹`. -/
theorem hol_eq_of_pureGauge {c : X.V → G} (hc : ∀ e, U e = c (X.tgt e) * (c (X.src e))⁻¹)
    {u v : X.V} (γ : X.Path u v) : hol U γ = c v * (c u)⁻¹ := by
  induction γ with
  | nil => simp
  | cons e γ ih =>
    rw [hol_cons, ih, hc]
    group

/-- On a loop-flat link table, two paths with the same ends have the same
holonomy: `δ̄ γ` is a loop, and its holonomy is `Hol(δ)⁻¹ Hol(γ) = 1`. -/
theorem hol_eq_of_loopFlat (hU : LoopFlat U) {u v : X.V} (γ δ : X.Path u v) :
    hol U γ = hol U δ := by
  have h := hU u (δ.reverse.comp γ)
  rw [hol_comp, hol_reverse, inv_mul_eq_one] at h
  exact h.symm

end Skeleton

open Skeleton

/-- **Theorem 5.23** (Holonomy descent). Under the substitution
`U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`, the holonomy of a path from `v₀` to `v_k`
becomes `h_{v_k} Hol_U(γ) h_{v₀}⁻¹`; for a loop this is a conjugation, so the
conjugacy class of the holonomy is unchanged. The proof is the book's: the
factors at the interior vertices cancel (`Skeleton.hol_gaugeAct`, by induction
on the path). -/
@[book "thm:holonomy-descent"]
theorem holonomyDescent : Statement.holonomyDescent := by
  intro X G _ U h
  refine ⟨fun u v γ => hol_gaugeAct U h γ, fun v γ => ?_⟩
  rw [hol_gaugeAct, ConjClasses.mk_eq_mk_iff_isConj]
  exact (isConj_iff.mpr ⟨h v, rfl⟩).symm

/-- **Theorem 5.27** (Pure gauge equals loop-flat). On a connected transport
skeleton, a link table is pure gauge if and only if it is loop-flat. The proof
is the book's. If `U_e = c_{t(e)} c_{s(e)}⁻¹`, the holonomy of every path
telescopes to `c_v c_u⁻¹`, which is `1` on a loop. Conversely, choose a base
vertex `v_*` and a path `p_v` from it to every vertex `v`, and put
`c_v = Hol(p_v)`. For an edge `e` from `u` to `v`, the paths `p_v` and `e p_u`
have the same ends, hence the same holonomy, so `c_v = U_e c_u`. A skeleton
with no vertex has no edge, and every table on it is pure gauge. -/
@[book "thm:pure-gauge"]
theorem pureGauge : Statement.pureGauge := by
  intro X G _ U hX
  constructor
  · rintro ⟨c, hc⟩ v γ
    rw [hol_eq_of_pureGauge U hc γ, mul_inv_cancel]
  · intro hU
    rcases isEmpty_or_nonempty X.V with hV | ⟨⟨v₀⟩⟩
    · exact ⟨fun _ => 1, fun e => (hV.false (X.src e)).elim⟩
    · let p : ∀ v, X.Path v₀ v := fun v => (hX v₀ v).some
      refine ⟨fun v => hol U (p v), fun e => ?_⟩
      have h := hol_eq_of_loopFlat U hU (p (X.tgt e)) (.cons e (p (X.src e)))
      rw [hol_cons] at h
      beta_reduce
      rw [h, mul_inv_cancel_right]

/-! ## Non-vacuity

The running example of Part B of Chapter 5 (`sec:transport-skeleton`): the two
squares `K = SquareGrid(2,1)`, with vertices `v₀, …, v₅` and edges
`e₁, …, e₇`. The six outer edges point anticlockwise round the outside, and the
shared edge `e₂` points up; the transport skeleton has both traversals of every
edge. The group is `C₃`, as `Multiplicative (ZMod 3)`: `Multiplicative.ofAdd k`
is the book's `r^k`, which the book writes `k`.

The skeleton is connected, which is the hypothesis of Theorem 5.27. The link
table of `fig:square-gauge` has holonomy `r²` round the left face, so it is not
loop-flat, and by Theorem 5.27 it is not pure gauge. The table that the gauge
change at `v₁` makes of the trivial table is pure gauge, so by Theorem 5.27 it
is loop-flat. -/

namespace Skeleton

/-- The transport skeleton of a graph whose edges are stored with a direction.
Its oriented edges are the steps `(e, true)`, along the stored direction, and
`(e, false)`, against it, as in a boundary walk of a canvas (`stepStart`,
`stepEnd`); the reversal turns one into the other. -/
abbrev ofGraph {V E : Type} (src tgt : E → V) : Skeleton where
  V := V
  E := E × Bool
  src := stepStart src tgt
  tgt := stepEnd src tgt
  rev s := (s.1, !s.2)
  rev_rev := by rintro ⟨e, _ | _⟩ <;> rfl
  src_rev := by rintro ⟨e, _ | _⟩ <;> rfl

/-- A link table on the transport skeleton of a graph, from its values on the
stored directions; the reversal law gives the other traversals. -/
def LinkTable.ofGraph {V E : Type} {src tgt : E → V} {G : Type*} [Group G] (u : E → G) :
    (Skeleton.ofGraph src tgt).LinkTable G where
  val
    | (e, true) => u e
    | (e, false) => (u e)⁻¹
  reversal := by
    rintro ⟨e, _ | _⟩
    · exact (inv_inv (u e)).symm
    · rfl

namespace TwoSquares

/-- The six vertices `v₀, …, v₅` of the two squares: `v₀`, `v₁`, `v₄` along the
bottom from left to right, and `v₃`, `v₂`, `v₅` along the top. -/
inductive Vertex
  | v₀ | v₁ | v₂ | v₃ | v₄ | v₅

/-- The seven edges `e₁, …, e₇` of the two squares. -/
inductive Edge
  | e₁ | e₂ | e₃ | e₄ | e₅ | e₆ | e₇

open Vertex Edge

/-- The source of each edge in its stored direction. The six outer edges point
anticlockwise round the outside, `e₁ e₅ e₆ e₇ e₃ e₄` from `v₀`, and the shared
edge `e₂` points up, from `v₁` to `v₂`. -/
def Edge.src : Edge → Vertex
  | e₁ => v₀ | e₂ => v₁ | e₃ => v₂ | e₄ => v₃ | e₅ => v₁ | e₆ => v₄ | e₇ => v₅

/-- The target of each edge in its stored direction. -/
def Edge.tgt : Edge → Vertex
  | e₁ => v₁ | e₂ => v₂ | e₃ => v₃ | e₄ => v₀ | e₅ => v₄ | e₆ => v₅ | e₇ => v₂

/-- The transport skeleton of the two squares `K = SquareGrid(2,1)`. -/
abbrev skeleton : Skeleton := ofGraph Edge.src Edge.tgt

/-- The oriented edge `e`, along the stored direction of the edge `e`. -/
def along (e : Edge) : skeleton.E := (e, true)

/-- The oriented edge `ē`, against the stored direction of the edge `e`. -/
def against (e : Edge) : skeleton.E := (e, false)

/-- The two squares are connected: from `v₀`, the paths `e₁`, `e₂ e₁`, `ē₄`,
`e₅ e₁` and `e₆ e₅ e₁` reach `v₁`, `v₂`, `v₃`, `v₄` and `v₅`. -/
theorem connected : skeleton.Connected := by
  refine connected_of_base v₀ fun v => ?_
  cases v
  · exact ⟨.nil _⟩
  · exact ⟨.cons (along e₁) (.nil _)⟩
  · exact ⟨.cons (along e₂) (.cons (along e₁) (.nil _))⟩
  · exact ⟨.cons (against e₄) (.nil _)⟩
  · exact ⟨.cons (along e₅) (.cons (along e₁) (.nil _))⟩
  · exact ⟨.cons (along e₆) (.cons (along e₅) (.cons (along e₁) (.nil _)))⟩

/-- A link table over `C₃` from the book's numbers `(U₁, …, U₇)`: the number
`k` on `eᵢ` stands for `r^k`, and the reversal law puts `r^{-k}` on `ēᵢ`. -/
def table (u : Edge → ZMod 3) : skeleton.LinkTable (Multiplicative (ZMod 3)) :=
  LinkTable.ofGraph fun e => Multiplicative.ofAdd (u e)

/-- The link table `(U₁, …, U₇) = (1, 0, 1, 0, 1, 0, 1)` of `fig:square-gauge`.
Both faces have curvature `2`. -/
def curvedTable : skeleton.LinkTable (Multiplicative (ZMod 3)) :=
  table fun | e₁ | e₃ | e₅ | e₇ => 1 | e₂ | e₄ | e₆ => 0

/-- The loop `e₄ e₃ e₂ e₁` round the left face `f_L`, from `v₀`. -/
def loopL : skeleton.Path v₀ v₀ :=
  .cons (along e₄) (.cons (along e₃) (.cons (along e₂) (.cons (along e₁) (.nil _))))

/-- The path `e₁`, from `v₀` to `v₁`. -/
def pathE₁ : skeleton.Path v₀ v₁ :=
  .cons (along e₁) (.nil _)

/-- The gauge change of `fig:square-gauge`: `r` at `v₁`, and `1` at every other
vertex. -/
def gaugeChange : skeleton.V → Multiplicative (ZMod 3)
  | v₁ => Multiplicative.ofAdd 1
  | _ => 1

/-- The link table `(1, 2, 0, 0, 2, 0, 0)`, which `gaugeChange` makes of the
trivial table: `U_e = h_{t(e)} h_{s(e)}⁻¹`, in the book's numbers
`h_{t(e)} − h_{s(e)}`. -/
def gaugedTable : skeleton.LinkTable (Multiplicative (ZMod 3)) :=
  table fun | e₁ => 1 | e₂ | e₅ => 2 | e₃ | e₄ | e₆ | e₇ => 0

/-- `gaugedTable` is pure gauge, with `c = gaugeChange`. -/
theorem gaugedTable_pureGauge : PureGauge gaugedTable :=
  ⟨gaugeChange, by rintro ⟨_ | _ | _ | _ | _ | _ | _, _ | _⟩ <;> decide⟩

/-- The hypothesis of Theorem 5.27 is met: the two squares are connected. -/
example : skeleton.Connected := connected

/-- The holonomy of `curvedTable` round the left face is `r²`, the curvature
`F_L = 2` of the book. -/
example : hol curvedTable loopL = Multiplicative.ofAdd 2 := by
  rw [hol_eq_prod]
  decide

/-- So `curvedTable` is not loop-flat. -/
example : ¬ LoopFlat curvedTable := by
  intro h
  have h₁ := h v₀ loopL
  rw [hol_eq_prod] at h₁
  revert h₁
  decide

/-- By Theorem 5.27 on the connected two squares, `curvedTable` is not pure
gauge. -/
example : ¬ PureGauge curvedTable := by
  intro h
  have h₁ := (pureGauge skeleton _ curvedTable connected).mp h v₀ loopL
  rw [hol_eq_prod] at h₁
  revert h₁
  decide

/-- `gaugedTable` is pure gauge. -/
example : PureGauge gaugedTable := gaugedTable_pureGauge

/-- By Theorem 5.27 on the connected two squares, `gaugedTable` is loop-flat. -/
example : LoopFlat gaugedTable :=
  (pureGauge skeleton _ gaugedTable connected).mp gaugedTable_pureGauge

/-- Theorem 5.23 on the two squares. The holonomy of `e₁` is `r`, and the gauge
change turns it into `h_{v₁} r h_{v₀}⁻¹ = r²`. -/
example : hol (gaugeAct gaugeChange curvedTable) pathE₁ = Multiplicative.ofAdd 2 := by
  rw [(holonomyDescent skeleton _ curvedTable gaugeChange).1, hol_eq_prod]
  decide

/-- Theorem 5.23 on the two squares. Round the loop `f_L` from `v₀`, the vertex
`v₁` is interior, and the holonomy does not change. -/
example : hol (gaugeAct gaugeChange curvedTable) loopL = hol curvedTable loopL := by
  rw [(holonomyDescent skeleton _ curvedTable gaugeChange).1, hol_eq_prod]
  decide

end TwoSquares

end Skeleton

end Artform
