import ArtformTextbook.Ch05.Holonomy

/-!
# Gauge equivalence, the transport skeleton of a canvas, and face curvature
(Sections 5.7, 5.10, 5.12 and 5.13)

Two link tables are gauge equivalent when a gauge transformation carries one to
the other (Definition 5.21, in coordinates). The transport skeleton of a canvas
has as oriented edges both traversals of every stored edge, the steps
`(e, true)` and `(e, false)` of its boundary walks. A face's curvature is the
holonomy of its declared boundary word, read as a loop from one of its corners
(Definition 5.25), and a link table is face-flat when every face has curvature
`1` (Definition 5.26).
-/

namespace Artform

namespace Skeleton

variable {X : Skeleton} {G : Type*} [Group G]

/-- Two link tables with the same element on every oriented edge are equal. -/
@[ext]
theorem LinkTable.ext {U V : X.LinkTable G} (h : ∀ e, U e = V e) : U = V := by
  obtain ⟨u, hu⟩ := U
  obtain ⟨v, hv⟩ := V
  have : u = v := funext h
  subst this
  rfl

/-- Two gauge transformations in succession are their pointwise product. -/
theorem gaugeAct_gaugeAct (h k : X.V → G) (U : X.LinkTable G) :
    gaugeAct h (gaugeAct k U) = gaugeAct (h * k) U := by
  ext e
  simp only [gaugeAct_apply, Pi.mul_apply, mul_inv_rev]
  group

/-- The identity gauge transformation does nothing. -/
theorem gaugeAct_one (U : X.LinkTable G) : gaugeAct (1 : X.V → G) U = U := by
  ext e
  simp [gaugeAct_apply]

/-- **Definition 5.21** (gauge equivalent), in the coordinates of a
trivialization, which identify the gauge group `𝒢_K = Π_v Aut_G(T_v)` with
`Π_v G` acting on link tables by `U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`
(`eq:gauge-action`): two link tables are gauge equivalent when they lie in one
orbit, `U' = U^h` for some `h`. -/
@[book "def:gauge-group"]
def GaugeEquivalent (U U' : X.LinkTable G) : Prop := ∃ h : X.V → G, gaugeAct h U = U'

/-- Gauge equivalence is an equivalence relation: the orbits of a group action
partition the link tables. -/
theorem gaugeEquivalent_equivalence : Equivalence (GaugeEquivalent (X := X) (G := G)) where
  refl U := ⟨1, gaugeAct_one U⟩
  symm := by
    rintro U U' ⟨h, rfl⟩
    refine ⟨h⁻¹, ?_⟩
    rw [gaugeAct_gaugeAct, inv_mul_cancel, gaugeAct_one]
  trans := by
    rintro U U' U'' ⟨h, rfl⟩ ⟨k, rfl⟩
    exact ⟨k * h, (gaugeAct_gaugeAct k h U).symm⟩

end Skeleton

namespace Canvas

variable (K : Canvas)

/-- The transport skeleton of a canvas (Section 5.7, `sec:transport-skeleton`):
the directed graph on its vertices whose oriented edges are both traversals of
every stored edge, `e = (e, true)` along the stored direction and
`ē = (e, false)` against it, with source, target and reversal. Its oriented
edges are exactly the steps of the canvas's boundary walks. -/
abbrev skeleton : Skeleton := Skeleton.ofGraph K.src K.tgt

variable {K} {G : Type*} [Group G]

/-- **Definition 5.25** (face curvature). Read the declared boundary word of the
face `f` as a loop `∂_v f` based at the corner `v` where its `i`-th step starts
(the boundary cycle `K.boundary f`, rotated to start there). The curvature of
`f` at that corner is the holonomy of the loop,
`F^v_U(f) = Hol_U(∂_v f) = U_{e_k} ⋯ U_{e₁}`, the step taken first on the right
(`eq:path-holonomy`). -/
@[book "def:curvature-general"]
def curvature (U : K.skeleton.LinkTable G) (f : K.F) (i : ℕ) : G :=
  (((K.boundary f).rotate i).map fun s => U s).reverse.prod

/-- **Definition 5.25** (flat at a face): the curvature of `f` is the identity.
The book notes that the condition does not depend on the corner chosen; Lean
asks it at every corner. -/
@[book "def:curvature-general"]
def FlatAt (U : K.skeleton.LinkTable G) (f : K.F) : Prop := ∀ i, curvature U f i = 1

/-- **Definition 5.26** (face-flat): `F^{v_f}_U(f) = 1` for every face `f`, with
`v_f` any corner of `f`. The loop-flat and pure-gauge clauses of the definition
are `Skeleton.LoopFlat` and `Skeleton.PureGauge`. -/
@[book "def:flatness"]
def FaceFlat (U : K.skeleton.LinkTable G) : Prop := ∀ f, FlatAt U f

end Canvas

end Artform
