import ArtformTextbook.Ch05.Defs.Torsor
import ArtformTextbook.Ch05.Holonomy

/-!
# Localizations, connections and trivializations (Sections 5.8 and 5.9)

A localization puts one right `G`-torsor at every vertex of the transport
skeleton (Definition 5.17). A connection carries each fibre to the next along
every oriented edge, by an equivariant bijection, with the reversal law
(Definition 5.18). A trivialization chooses an origin in every fibre, and then
the connection has a link table (Definition 5.19), a `Skeleton.LinkTable` of
`Ch05/Defs/Gauge.lean`.

The fibres over `s(ē)` and over `t(e)` are the same torsor, but Lean sees the
equality `s(ē) = t(e)` of vertices only as a proof, so a point of one fibre is
read in the other through `Localization.cast`.
-/

namespace Artform

namespace RightTorsor

variable {G : Type*} [Group G] (T : RightTorsor G)

/-- `x · 1 = x`. -/
theorem act_one (x : T) : T.act x 1 = x := T.isRightTorsor.act_one x

/-- `(x · g) · k = x · (g k)`. -/
theorem act_mul (x : T) (g k : G) : T.act (T.act x g) k = T.act x (g * k) :=
  T.isRightTorsor.act_mul x g k

/-- By freeness, `x · g = x · k` forces `g = k`. -/
theorem act_left_cancel {x : T} {g k : G} (h : T.act x g = T.act x k) : g = k := by
  have h2 : T.act (T.act x g) k⁻¹ = T.act (T.act x k) k⁻¹ := by rw [h]
  rw [T.act_mul, T.act_mul, mul_inv_cancel, T.act_one] at h2
  exact mul_inv_eq_one.mp (T.isRightTorsor.free x _ h2)

/-- The coordinate of `y` from the origin `o`: the element `g` with `o · g = y`,
which transitivity supplies and freeness makes unique. -/
noncomputable def coord (o y : T) : G := Classical.choose (T.isRightTorsor.transitive o y)

/-- `o · coord o y = y`. -/
theorem act_coord (o y : T) : T.act o (T.coord o y) = y :=
  Classical.choose_spec (T.isRightTorsor.transitive o y)

/-- `coord o (o · g) = g`. -/
theorem coord_act (o : T) (g : G) : T.coord o (T.act o g) = g :=
  T.act_left_cancel (T.act_coord o _)

/-- **Definition 5.18** (equivariant map of right `G`-torsors): a bijection
`σ : T → T'` with `σ(x · g) = σ(x) · g`. -/
@[book "def:connection-general"]
structure EquivariantMap (T T' : RightTorsor G) where
  /-- The map `σ`. -/
  toFun : T → T'
  /-- `σ` is a bijection. -/
  bijective : Function.Bijective toFun
  /-- `σ(x · g) = σ(x) · g`. -/
  map_act : ∀ x g, toFun (T.act x g) = T'.act (toFun x) g

instance (T T' : RightTorsor G) : CoeFun (EquivariantMap T T') (fun _ => T → T') :=
  ⟨EquivariantMap.toFun⟩

end RightTorsor

namespace Skeleton

variable (X : Skeleton) (G : Type*) [Group G]

/-- **Definition 5.17** (localization): a choice of one right `G`-torsor `T_v`
at each vertex `v`, `𝒯 = (T_v)_v : Localize(K, G) = Π_{v : C₀(K)} Torsor(G)`.
The torsor `T_v` is the fibre of `𝒯` over `v`. The vertices are those of the
transport skeleton, which are the vertices `C₀(K)` of the canvas. -/
@[book "def:localization"]
abbrev Localization : Type _ := X.V → RightTorsor G

variable {X G}

/-- A point of the fibre over `u`, read in the fibre over `v`, when `u = v`. -/
def Localization.cast (T : X.Localization G) {u v : X.V} (h : u = v) (x : T u) : T v :=
  h ▸ x

/-- **Definition 5.18** (connection). A connection on the localization `𝒯` is a
family `𝒰 = (𝒰_e)_{e ∈ E^or(K)}` of equivariant bijections
`𝒰_e : T_{s(e)} → T_{t(e)}`, one for each oriented edge of the transport
skeleton, subject to the reversal law `𝒰_ē = 𝒰_e⁻¹`. The reversal law is
written pointwise, `𝒰_ē(𝒰_e(x)) = x`, reading the point `𝒰_e(x)` of `T_{t(e)}`
in `T_{s(ē)}` and the point `x` of `T_{s(e)}` in `T_{t(ē)}`; since `𝒰_e` is a
bijection, this says that `𝒰_ē` is its inverse. -/
@[book "def:connection-general"]
structure Connection (T : X.Localization G) where
  /-- The equivariant bijection `𝒰_e : T_{s(e)} → T_{t(e)}` on each oriented
  edge. -/
  map : ∀ e, RightTorsor.EquivariantMap (T (X.src e)) (T (X.tgt e))
  /-- The reversal law `𝒰_ē = 𝒰_e⁻¹`: walking back along `ē` undoes `𝒰_e`. -/
  reversal : ∀ e (x : T (X.src e)),
    map (X.rev e) (T.cast (X.src_rev e).symm (map e x)) = T.cast (X.tgt_rev e).symm x

/-- **Definition 5.19** (trivialization): a choice of origin `t_v ∈ T_v` at
every vertex, a complete assignment `t : Π_{v : C₀(K)} T_v`. -/
@[book "def:trivialization"]
abbrev Trivialization (T : X.Localization G) : Type := ∀ v, T v

/-- Reading a point back in its own fibre changes nothing. -/
@[simp]
theorem Localization.cast_rfl (T : X.Localization G) {u : X.V} (x : T u) : T.cast rfl x = x :=
  rfl

/-- Reading a point in another name of its fibre commutes with the action. -/
theorem Localization.cast_act (T : X.Localization G) {u v : X.V} (h : u = v) (x : T u)
    (g : G) : T.cast h ((T u).act x g) = (T v).act (T.cast h x) g := by
  subst h
  rfl

/-- The origin over `u`, read over `v = u`, is the origin over `v`. -/
theorem Localization.cast_origin (T : X.Localization G) (t : X.Trivialization T) {u v : X.V}
    (h : u = v) : T.cast h (t u) = t v := by
  subst h
  rfl

/-- **Definition 5.19** (link table). Given a trivialization `t`, freeness and
transitivity supply for each oriented edge a unique group element `U_e` with
`𝒰_e(t_{s(e)}) = t_{t(e)} · U_e` (`eq:link-coordinate`). The table
`U = (U_e)_e` is the link table of `𝒰` in that trivialization, and it inhabits
`LinkTable(K, G)`: the reversal law `U_ē = U_e⁻¹` follows from that of `𝒰`. -/
@[book "def:trivialization"]
noncomputable def Connection.linkTable {T : X.Localization G} (𝒰 : X.Connection T)
    (t : X.Trivialization T) : X.LinkTable G where
  val e := (T (X.tgt e)).coord (t (X.tgt e)) (𝒰.map e (t (X.src e)))
  reversal e := by
    set g := (T (X.tgt e)).coord (t (X.tgt e)) (𝒰.map e (t (X.src e)))
    have h1 : (T (X.tgt e)).act (t (X.tgt e)) g = 𝒰.map e (t (X.src e)) :=
      (T (X.tgt e)).act_coord _ _
    have h2 : t (X.tgt e) = 𝒰.map e ((T (X.src e)).act (t (X.src e)) g⁻¹) := by
      rw [(𝒰.map e).map_act, ← h1, RightTorsor.act_mul, mul_inv_cancel, RightTorsor.act_one]
    have h3 : 𝒰.map (X.rev e) (t (X.src (X.rev e))) =
        (T (X.tgt (X.rev e))).act (t (X.tgt (X.rev e))) g⁻¹ := by
      rw [← T.cast_origin t (X.src_rev e).symm, h2, 𝒰.reversal, T.cast_act, T.cast_origin]
    change (T (X.tgt (X.rev e))).coord _ (𝒰.map (X.rev e) (t (X.src (X.rev e)))) = g⁻¹
    rw [h3, RightTorsor.coord_act]

end Skeleton

end Artform
