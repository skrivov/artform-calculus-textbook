import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group
import ArtformTextbook.Meta.Book

/-!
# Transport, link tables and holonomy (Sections 5.5 to 5.8)

A statement about transport is a statement about the transport skeleton of a
canvas: the directed graph on its vertices whose edges are both traversals
`e` and `ē` of each underlying edge, with source, target and reversal
(Section 5.5, "The canvas K and its transport skeleton").
-/

namespace Artform

/-- The transport skeleton of a canvas: vertices, oriented edges with a source
and a target, and the reversal `e ↦ ē`, which swaps source and target. -/
structure Skeleton where
  /-- The vertices `C₀(K)`. -/
  V : Type
  /-- The oriented edges `E^or(K)`, both traversals of every edge. -/
  E : Type
  /-- The source `s(e)`. -/
  src : E → V
  /-- The target `t(e)`. -/
  tgt : E → V
  /-- The reversal `e ↦ ē`. -/
  rev : E → E
  rev_rev : ∀ e, rev (rev e) = e
  src_rev : ∀ e, src (rev e) = tgt e

namespace Skeleton

variable (X : Skeleton)

/-- **Definition 5.19** (link table). A table with one group element `U_e` at
every oriented edge, subject to the reversal law `U_ē = U_e⁻¹`. -/
@[book "def:trivialization"]
structure LinkTable (G : Type*) [Group G] where
  /-- The element `U_e` on each oriented edge. -/
  val : X.E → G
  /-- The reversal law `U_ē = U_e⁻¹`. -/
  reversal : ∀ e, val (X.rev e) = (val e)⁻¹

instance (G : Type*) [Group G] : CoeFun (X.LinkTable G) (fun _ => X.E → G) := ⟨LinkTable.val⟩

/-- An oriented path from `u` to `v`: a composable list `γ = e_k ⋯ e₁`, the
edge traversed first on the right. `cons e p` extends the path `p`, which
ends at the source of `e`, by the edge `e`. -/
inductive Path : X.V → X.V → Type
  | nil (v : X.V) : Path v v
  | cons {u : X.V} (e : X.E) (p : Path u (X.src e)) : Path u (X.tgt e)

variable {X} {G : Type*} [Group G]

/-- The holonomy of a path, `Hol_U(γ) = U_{e_k} ⋯ U_{e₁}`
(equation (5.12) of the book, `eq:path-holonomy`). -/
def hol (U : X.LinkTable G) : {u v : X.V} → X.Path u v → G
  | _, _, .nil _ => 1
  | _, _, .cons e p => U e * hol U p

/-- The gauge action on link tables, `U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`
(`eq:gauge-action`). It keeps the reversal law. -/
@[book "def:gauge-group"]
def gaugeAct (h : X.V → G) (U : X.LinkTable G) : X.LinkTable G where
  val e := h (X.tgt e) * U e * (h (X.src e))⁻¹
  reversal e := by
    have ht : X.tgt (X.rev e) = X.src e := by rw [← X.src_rev, X.rev_rev]
    simp only [ht, X.src_rev]
    rw [U.reversal e]
    group

/-- **Definition 5.26** (loop-flat): `Hol_U(γ) = 1` for every based loop `γ`
of the transport skeleton. -/
@[book "def:flatness"]
def LoopFlat (U : X.LinkTable G) : Prop := ∀ v (γ : X.Path v v), hol U γ = 1

/-- **Definition 5.26** (pure gauge): there are elements `c_v` with
`U_e = c_{t(e)} c_{s(e)}⁻¹` for every oriented edge. -/
@[book "def:flatness"]
def PureGauge (U : X.LinkTable G) : Prop :=
  ∃ c : X.V → G, ∀ e, U e = c (X.tgt e) * (c (X.src e))⁻¹

variable (X) in
/-- A transport skeleton is connected when an oriented path joins any vertex
to any other. -/
def Connected : Prop := ∀ u v : X.V, Nonempty (X.Path u v)

end Skeleton

end Artform
