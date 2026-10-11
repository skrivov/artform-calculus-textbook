import ArtformTextbook.Ch05.Statements.Gauge

/-!
# Connection and coordinates (Proposition 5.20)

The book gives the inverse map without a proof: a trivialization `t` rebuilds
the connection from a table by `𝒰_e(t_{s(e)} · g) = t_{t(e)} · U_e g`. Here
both directions are checked. The equation `𝒰_e(t_{s(e)}) = t_{t(e)} · U_e`
determines `U_e` by freeness, so at most one map satisfies it, and the link
table of Definition 5.19 does. That map is injective, because by equivariance
an equivariant map is fixed by its value at one point; and it is surjective,
because the formula above is an equivariant bijection on every edge and obeys
the reversal law when the table does.
-/

namespace Artform

namespace RightTorsor

variable {G : Type*} [Group G] (T : RightTorsor G)

/-- The origin has coordinate `1`. -/
private theorem coord_self (o : T) : T.coord o o = 1 := by
  have h := T.coord_act o 1
  rwa [T.act_one] at h

/-- Acting by `k` adds `k` on the right of the coordinate. -/
private theorem coord_act_act (o x : T) (k : G) : T.coord o (T.act x k) = T.coord o x * k := by
  conv_lhs => rw [← T.act_coord o x, T.act_mul]
  exact T.coord_act o _

/-- Two equivariant maps that agree everywhere are equal. -/
private theorem EquivariantMap.ext' {T T' : RightTorsor G} {σ τ : EquivariantMap T T'}
    (h : ∀ x, σ x = τ x) : σ = τ := by
  obtain ⟨f, hf, hf'⟩ := σ
  obtain ⟨g, hg, hg'⟩ := τ
  have : f = g := funext h
  subst this
  rfl

end RightTorsor

namespace Skeleton

variable {X : Skeleton} {G : Type*} [Group G] {T : X.Localization G}

/-- Two connections with the same maps are equal. -/
private theorem Connection.ext' {𝒰 𝒱 : X.Connection T} (h : ∀ e x, 𝒰.map e x = 𝒱.map e x) :
    𝒰 = 𝒱 := by
  obtain ⟨m, hm⟩ := 𝒰
  obtain ⟨n, hn⟩ := 𝒱
  have : m = n := funext fun e => RightTorsor.EquivariantMap.ext' (h e)
  subst this
  rfl

/-- The link table of Definition 5.19 satisfies `eq:link-coordinate`. -/
private theorem Connection.linkTable_spec (𝒰 : X.Connection T) (t : X.Trivialization T)
    (e : X.E) : 𝒰.map e (t (X.src e)) = (T (X.tgt e)).act (t (X.tgt e)) (𝒰.linkTable t e) :=
  ((T (X.tgt e)).act_coord _ _).symm

/-- The connection that a trivialization rebuilds from a link table:
`𝒰_e(x) = t_{t(e)} · U_e g`, for the point `x = t_{s(e)} · g`. -/
private noncomputable def ofLinkTable (t : X.Trivialization T) (U : X.LinkTable G) :
    X.Connection T where
  map e :=
    { toFun := fun x => (T (X.tgt e)).act (t (X.tgt e)) (U e * (T (X.src e)).coord (t (X.src e)) x)
      bijective := by
        constructor
        · intro x y hxy
          have h := mul_left_cancel ((T (X.tgt e)).act_left_cancel hxy)
          rw [← (T (X.src e)).act_coord (t (X.src e)) x, h, (T (X.src e)).act_coord]
        · intro y
          refine ⟨(T (X.src e)).act (t (X.src e)) ((U e)⁻¹ * (T (X.tgt e)).coord (t (X.tgt e)) y),
            ?_⟩
          simp only
          rw [RightTorsor.coord_act, mul_inv_cancel_left, RightTorsor.act_coord]
      map_act := by
        intro x k
        rw [RightTorsor.coord_act_act, RightTorsor.act_mul, mul_assoc] }
  reversal e x := by
    dsimp only
    rw [Localization.cast_act, Localization.cast_origin, RightTorsor.coord_act,
      U.reversal, inv_mul_cancel_left]
    conv_rhs => rw [← (T (X.src e)).act_coord (t (X.src e)) x]
    rw [Localization.cast_act, Localization.cast_origin]

/-- The rebuilt connection has the table it was built from. -/
private theorem linkTable_ofLinkTable (t : X.Trivialization T) (U : X.LinkTable G) :
    (ofLinkTable t U).linkTable t = U := by
  ext e
  change (T (X.tgt e)).coord (t (X.tgt e))
    ((T (X.tgt e)).act (t (X.tgt e)) (U e * (T (X.src e)).coord (t (X.src e)) (t (X.src e))))
    = U e
  rw [RightTorsor.coord_act, RightTorsor.coord_self, mul_one]

end Skeleton

open Skeleton

/-- **Proposition 5.20** (connection and coordinates). For a localization and a
trivialization, `𝒰_e(t_{s(e)}) = t_{t(e)} · U_e` determines exactly one map
from connections to link tables, the link table of Definition 5.19, and that
map is a bijection. -/
@[book "prop:connection-coordinates"]
theorem connectionCoordinates : Statement.connectionCoordinates := by
  intro X G _ T t
  -- any map satisfying the equation is the link table of Definition 5.19
  have unique : ∀ Φ : X.Connection T → X.LinkTable G,
      (∀ 𝒰 e, 𝒰.map e (t (X.src e)) = (T (X.tgt e)).act (t (X.tgt e)) (Φ 𝒰 e)) →
      Φ = fun 𝒰 => 𝒰.linkTable t := by
    intro Φ hΦ
    funext 𝒰
    ext e
    exact (T (X.tgt e)).act_left_cancel ((hΦ 𝒰 e).symm.trans (𝒰.linkTable_spec t e))
  have bij : Function.Bijective fun 𝒰 : X.Connection T => 𝒰.linkTable t := by
    constructor
    · intro 𝒰 𝒱 h
      refine Connection.ext' fun e x => ?_
      have h0 : 𝒰.map e (t (X.src e)) = 𝒱.map e (t (X.src e)) := by
        rw [𝒰.linkTable_spec t e, 𝒱.linkTable_spec t e]
        exact congrArg (fun U : X.LinkTable G => (T (X.tgt e)).act (t (X.tgt e)) (U e)) h
      rw [← (T (X.src e)).act_coord (t (X.src e)) x, (𝒰.map e).map_act, (𝒱.map e).map_act, h0]
    · intro U
      exact ⟨ofLinkTable t U, linkTable_ofLinkTable t U⟩
  refine ⟨⟨fun 𝒰 => 𝒰.linkTable t, fun 𝒰 e => 𝒰.linkTable_spec t e, fun Φ hΦ => unique Φ hΦ⟩,
    fun Φ hΦ => ?_⟩
  rw [unique Φ hΦ]
  exact bij

/-! ## Non-vacuity

The two squares over `C₃`, localized as in `fig:square-localized`: the fibre
over every vertex is a copy of the three rotations, which `C₃` acts on from the
right without a chosen origin, and the trivialization picks the rotation `1`
in each fibre. By Proposition 5.20 there is a connection whose link table is
the table `(1, 0, 1, 0, 1, 0, 1)` of `fig:square-gauge`. -/

/-- `C₃`, acting on itself from the right, as a right `C₃`-torsor: a fibre of
three poses. -/
private def posesC₃ : RightTorsor (Multiplicative (ZMod 3)) where
  carrier := Multiplicative (ZMod 3)
  act x g := x * g
  isRightTorsor :=
    { act_one := mul_one
      act_mul := mul_assoc
      nonempty := ⟨1⟩
      free := fun _ _ h => mul_eq_left.mp h
      transitive := fun x y => ⟨x⁻¹ * y, mul_inv_cancel_left x y⟩ }

/-- The localization of the two squares with a fibre of three poses at every
vertex. -/
private def localized : Skeleton.TwoSquares.skeleton.Localization (Multiplicative (ZMod 3)) :=
  fun _ => posesC₃

/-- A trivialization of it: the pose `1` in every fibre. -/
private def origins : Skeleton.Trivialization localized := fun _ => (1 : Multiplicative (ZMod 3))

/-- There is a connection with the link table of `fig:square-gauge` in these
origins. -/
example : ∃ 𝒰 : Skeleton.TwoSquares.skeleton.Connection localized,
    ∀ e, 𝒰.map e (origins (Skeleton.TwoSquares.skeleton.src e)) =
      (localized (Skeleton.TwoSquares.skeleton.tgt e)).act
        (origins (Skeleton.TwoSquares.skeleton.tgt e)) (Skeleton.TwoSquares.curvedTable e) := by
  obtain ⟨⟨Φ, hΦ, -⟩, hbij⟩ := connectionCoordinates _ _ localized origins
  obtain ⟨𝒰, h𝒰⟩ := (hbij Φ hΦ).2 Skeleton.TwoSquares.curvedTable
  exact ⟨𝒰, fun e => h𝒰 ▸ hΦ 𝒰 e⟩

end Artform
