import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.TypeTags
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite
import ArtformTextbook.Ch05.Defs.Connection
import ArtformTextbook.Ch05.Defs.Loops
import ArtformTextbook.Ch05.Defs.PoseLaw
import ArtformTextbook.Ch05.Defs.Calculus

/-!
# Statements of Chapter 5: the gauge construction, part B

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.

The book's group is finite throughout Part B; Lean states each statement for
every group.
-/

namespace Artform.Statement

open scoped BigOperators

open Skeleton Skeleton.TwoSquares Skeleton.TwoSquares.Vertex Skeleton.TwoSquares.Edge

/-- **Lemma 5.16** (pose orbit). Let a group `G` act on marked data `m`, and
suppose the mark is rigid, `Stab_G(m) = 1`: no symmetry but the identity leaves
the mark where it was. Then the orbit `PoseOrbit(P, m) = {g · m | g ∈ G}` is a
right `G`-torsor under `(g · m) · k := (gk) · m`: there is a map of the orbit
that satisfies this formula, and with it the orbit is a right `G`-torsor.

For the marked octagon and its rotations, `G = C₈`, `m` is the marked corner,
and the orbit is the eight poses: the rotations `C₈` act on the corners
`ZMod 8` of the octagon by turning them, the marked corner `0` is rigid, and
its orbit has eight elements.

The book's group is `Aut(P)`, the symmetries of a recognition pattern `P`
acting on marked data carried by `P`; Lean states the lemma for any group
acting on any set. -/
@[book "lem:pose-torsor"]
def poseTorsor : Prop :=
  (∀ (G M : Type) [Group G] [MulAction G M] (m : M), MulAction.stabilizer G m = ⊥ →
    ∃ act : MulAction.orbit G m → G → MulAction.orbit G m,
      (∀ g k : G, act ⟨g • m, MulAction.mem_orbit m g⟩ k =
        ⟨(g * k) • m, MulAction.mem_orbit m (g * k)⟩) ∧
      IsRightTorsor G (MulAction.orbit G m) act) ∧
  (MulAction.stabilizer (Multiplicative (ZMod 8)) (0 : ZMod 8) = ⊥ ∧
    Nat.card (MulAction.orbit (Multiplicative (ZMod 8)) (0 : ZMod 8)) = 8)

/-- **Proposition 5.20** (connection and coordinates). Fix a localization `𝒯`
and a trivialization `t = (t_v)_v`. Then `𝒰_e(t_{s(e)}) = t_{t(e)} · U_e`
(`eq:link-coordinate`) defines a bijection
`Φ_t : Connection(K; G) → LinkTable(K, G)`: exactly one map from connections to
link tables satisfies the equation on every oriented edge, and a map that
satisfies it is a bijection. -/
@[book "prop:connection-coordinates"]
def connectionCoordinates : Prop :=
  ∀ (X : Skeleton) (G : Type) [Group G] (T : X.Localization G) (t : X.Trivialization T),
    (∃! Φ : X.Connection T → X.LinkTable G,
      ∀ 𝒰 e, 𝒰.map e (t (X.src e)) = (T (X.tgt e)).act (t (X.tgt e)) (Φ 𝒰 e)) ∧
    ∀ Φ : X.Connection T → X.LinkTable G,
      (∀ 𝒰 e, 𝒰.map e (t (X.src e)) = (T (X.tgt e)).act (t (X.tgt e)) (Φ 𝒰 e)) →
      Function.Bijective Φ

/-- **Theorem 5.28** (spanning-tree gauge fixing). Let the transport skeleton be
finite and connected, and let `τ` be a spanning tree.
1. Every link table is gauge equivalent to one with `U_e = 1` on every edge
   of `τ`.
2. The gauge transformations preserving that normalization are exactly the
   constant ones, `h_v = k`;
3. and they conjugate every remaining label by the same `k`.
4. Writing `E⁺(K)` for one orientation of each underlying edge (`e ∈ E⁺(K)`
   exactly when `ē ∉ E⁺(K)`),
   `LinkTable(K, G)/𝒢_K ≅ G^{|E⁺(K)| − |C₀(K)| + 1}/G`, where the final `G`
   acts by simultaneous conjugation: there is a bijection between the two
   quotient sets.

The gauge group `𝒢_K` acts on link tables in the coordinates of a
trivialization, as `Π_v G` by `eq:gauge-action` (`GaugeEquivalent`). A
connected skeleton is taken to have a vertex, as a tree does; on the empty
skeleton the count would fail. The exponent is computed in `ℕ` as
`|E⁺(K)| + 1 − |C₀(K)|`: the tree's `|C₀(K)| − 1` edges lie among `E⁺(K)`, so
the subtraction does not truncate and the number is the book's. -/
@[book "thm:tree-gauge-fixing"]
def treeGaugeFixing : Prop :=
  ∀ (X : Skeleton) [Finite X.V] [Finite X.E] (G : Type) [Group G] (τ : Set X.E),
    Nonempty X.V → X.Connected → X.IsSpanningTree τ →
    (∀ U : X.LinkTable G, ∃ U' : X.LinkTable G, GaugeEquivalent U U' ∧ ∀ e ∈ τ, U' e = 1) ∧
    (∀ U : X.LinkTable G, (∀ e ∈ τ, U e = 1) → ∀ h : X.V → G,
      ((∀ e ∈ τ, gaugeAct h U e = 1) ↔ ∃ k : G, ∀ v, h v = k)) ∧
    (∀ U : X.LinkTable G, (∀ e ∈ τ, U e = 1) → ∀ (k : G) (e : X.E), e ∉ τ →
      gaugeAct (fun _ => k) U e = k * U e * k⁻¹) ∧
    ∀ Eplus : Set X.E, (∀ e, e ∈ Eplus ↔ X.rev e ∉ Eplus) →
      Nonempty (Quot (GaugeEquivalent (X := X) (G := G)) ≃
        Quot fun a b : Fin (Nat.card Eplus + 1 - Nat.card X.V) → G =>
          ∃ k : G, ∀ i, b i = k * a i * k⁻¹)

/-- **Theorem 5.29** (classification of face-flat connections). Let the
transport skeleton of the canvas `K` be connected, and let `v_*` be a vertex.
Define `π₁(K, v_*)` combinatorially: based edge loops at `v_*`, modulo deletion
of immediate backtracks and insertion or deletion of declared face-boundary
words (`Canvas.EdgeLoopGroup`). Then holonomy induces a bijection
`{face-flat connections}/gauge ≅ Hom(π₁(K, v_*), G)/G`, with `G` acting by
conjugating all values:
1. for every face-flat link table `U`, the holonomy `γ ↦ Hol_U(γ)` of based
   loops is a homomorphism `π₁(K, v_*) → G`;
2. there is a bijection `Φ` that sends the gauge class of each face-flat `U`
   to the class of that homomorphism;
3. the pure-gauge connections correspond to the trivial homomorphism: a
   face-flat `U` is pure gauge exactly when `Φ` sends its class to the class
   of the trivial homomorphism.

Connections are given by their link tables, and gauge acts by
`eq:gauge-action`. -/
@[book "thm:flat-classification"]
def flatClassification : Prop :=
  ∀ (K : Canvas) (G : Type) [Group G] (v : K.V), K.skeleton.Connected →
    (∀ U : K.skeleton.LinkTable G, K.FaceFlat U →
      ∃ φ : K.EdgeLoopGroup v →* G, ∀ γ, φ (Canvas.EdgeLoopGroup.mk γ) = hol U γ) ∧
    ∃ Φ : K.FaceFlatClasses G → K.HomClasses G v,
      (∀ (U : {U : K.skeleton.LinkTable G // K.FaceFlat U}) (φ : K.EdgeLoopGroup v →* G),
        (∀ γ, φ (Canvas.EdgeLoopGroup.mk γ) = hol U.1 γ) → Φ (Quot.mk _ U) = Quot.mk _ φ) ∧
      Function.Bijective Φ ∧
      ∀ U : {U : K.skeleton.LinkTable G // K.FaceFlat U},
        (PureGauge U.1 ↔ Φ (Quot.mk _ U) = Quot.mk _ 1)

/-- **Proposition 5.37** (five ticks read the outside). Under the pose law on
the two squares, five ticks carry the pose at `v₀` once round the outside of
`K`: `g⁽⁵⁾_{v₀} = U_{e₄} U_{e₃} U_{e₇} U_{e₆} U_{e₅} U_{e₁} g_{v₀}`, the
holonomy (`eq:path-holonomy`) of the outside, based at `v₀`, applied to the
pose. Likewise at `v₂`, `v₃`, `v₄` and `v₅`, with the loop based there. The
pose at `v₁` is carried over `e₂` and straight back at every tick, and is
never turned: at every tick the left turn carries it to `v₂` as `U_{e₂} g_{v₁}`,
the right turn carries that back to `v₁` across `ē₂`, and the pose at `v₁`
stays `g_{v₁}`. -/
@[book "prop:five-ticks"]
def fiveTicks : Prop :=
  ∀ (G : Type) [Group G] (U : skeleton.LinkTable G) (g : Vertex → G),
    (poseLaw.run (U, g) 5).2 v₀ =
        U (along e₄) * U (along e₃) * U (along e₇) * U (along e₆) * U (along e₅) *
          U (along e₁) * g v₀ ∧
      (poseLaw.run (U, g) 5).2 v₀ = hol U (outside v₀) * g v₀ ∧
      (∀ v, v ≠ v₁ → (poseLaw.run (U, g) 5).2 v = hol U (outside v) * g v) ∧
      ∀ n : ℕ,
        poseLeft U (poseLaw.run (U, g) n).2 v₂ = U (along e₂) * (poseLaw.run (U, g) n).2 v₁ ∧
        (poseLaw.run (U, g) (n + 1)).2 v₁ =
          U (against e₂) * poseLeft U (poseLaw.run (U, g) n).2 v₂ ∧
        (poseLaw.run (U, g) n).2 v₁ = g v₁

/-- **Theorem 5.40** (closed-window conservation). Let `ρ_t` be a site field
(the charge) and `J_t` a link flux on a canvas, for every time `t`.
1. If the local continuity equation `ρ_{t+1} − ρ_t + div J_t = 0` holds at
   every site of a finite canvas, its total charge `Σ_v ρ_t(v)` is constant in
   time.
2. So is the total charge `Σ_{v ∈ W} ρ_t(v)` of a window `W` of a larger
   canvas, if no edge that leaves the window carries flux: an edge with one
   end in `W` and one outside has `J_t = 0`.

The charges and fluxes take values in a commutative ring; for the window, the
continuity equation is needed only at the sites of the window. -/
@[book "thm:closed-window"]
def closedWindow : Prop :=
  ∀ (K : Canvas) (R : Type) [CommRing R] (ρ : ℕ → K.V → R) (J : ℕ → K.E → R),
    ((∀ t v, ρ (t + 1) v - ρ t v + K.div (J t) v = 0) →
      ∀ t s, ∑ v, ρ t v = ∑ v, ρ s v) ∧
    ∀ W : Finset K.V,
      (∀ t, ∀ v ∈ W, ρ (t + 1) v - ρ t v + K.div (J t) v = 0) →
      (∀ t e, (K.src e ∈ W ∧ K.tgt e ∉ W) ∨ (K.tgt e ∈ W ∧ K.src e ∉ W) → J t e = 0) →
      ∀ t s, ∑ v ∈ W, ρ t v = ∑ v ∈ W, ρ s v

end Artform.Statement
