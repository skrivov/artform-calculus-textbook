import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Basic
import ArtformTextbook.Ch05.Defs.Laws
import ArtformTextbook.Ch05.Defs.Affine
import ArtformTextbook.Ch05.Defs.Gauge
import ArtformTextbook.Ch05.Defs.Calculus

/-!
# The statements of Chapter 5

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open scoped BigOperators

/-- **Theorem 5.4** (what a conserved reading can see). Let the tick `F` of a
deterministic law be a bijection of its finite set of states, so that the
states fall into orbits `{x, F(x), F²(x), …}`.
1. A reading is conserved exactly when it is constant on each orbit.
2. A symmetry `s` carries every orbit onto an orbit. Some conserved reading
   tells `x` from `s(x)`, for some `x`, exactly when `s` carries some orbit
   onto a different orbit. -/
@[book "thm:orbit-criterion"]
def orbitCriterion : Prop :=
  ∀ (S : Type) [Finite S] (L : DetLaw S), Function.Bijective L.tick →
    (∀ (V : Type) (q : S → V), L.Conserved q ↔ ∀ x, ∀ y ∈ L.orbit x, q y = q x) ∧
    (∀ s : S → S, L.IsSymmetry s →
      (∀ x, s '' L.orbit x = L.orbit (s x)) ∧
      ((∃ (V : Type) (q : S → V), L.Conserved q ∧ ∃ x, q x ≠ q (s x)) ↔
        ∃ x, s '' L.orbit x ≠ L.orbit x))

/-- **Theorem 5.6** (Noether's theorem for affine laws). Let an affine law
`F(p) = M(p) + b` keep a pairing `⟨ , ⟩`.
1. For every table `w` with `M(w) = w`, adding `w` to every state is a
   symmetry of the law, and the tally `T_w(p) = ⟨w, p⟩` changes at every tick
   by exactly the source's share: `T_w(F(p)) = T_w(p) + ⟨w, b⟩`. In particular
   `T_w` is conserved when `⟨w, b⟩ = 0`.
2. If the pairing is perfect, every conserved tally is `T_w` for exactly one
   table `w`, and that `w` has `M(w) = w` and `⟨w, b⟩ = 0`. -/
@[book "thm:noether"]
def noether : Prop :=
  ∀ (C : Type) [Fintype C] (n : ℕ) (L : AffineLaw C n) (P : Pairing C n), L.Keeps P →
    (∀ w, L.M w = w →
      L.toDetLaw.IsSymmetry (· + w) ∧
      (∀ p, P w (L.tick p) = P w p + P w L.b) ∧
      (P w L.b = 0 → L.toDetLaw.Conserved (P w))) ∧
    (P.Perfect → ∀ T : Tally C n, L.toDetLaw.Conserved T →
      (∃! w, P w = T) ∧ ∀ w, P w = T → L.M w = w ∧ P w L.b = 0)

/-- **Corollary 5.7** (Noether's theorem on the square). For the law of the
square and the pairing `⟨p, q⟩ = Σᵢ p(vᵢ) q(vᵢ)`, the tables fixed by the tick
are the three constant ones; adding the same number at every corner is a
symmetry; the tally paired with adding `1` at every corner is the total
`T(p) = p(v₀) + p(v₁) + p(v₂) + p(v₃)` modulo `3`, and it is conserved; and
every conserved tally is `0`, `T` or `2T`. -/
@[book "cor:noether-square"]
def noetherSquare : Prop :=
  {w | squareLaw.tick w = w} = Set.range (fun c : ZMod 3 => fun _ : Fin 4 => c) ∧
  (∀ c : ZMod 3, squareLaw.toDetLaw.IsSymmetry (· + fun _ => c)) ∧
  dotPairing (Fin 4) 3 (fun _ => 1) = squareTotal ∧
  squareLaw.toDetLaw.Conserved squareTotal ∧
  ∀ T : Tally (Fin 4) 3, squareLaw.toDetLaw.Conserved T →
    T = 0 ∨ T = squareTotal ∨ T = 2 • squareTotal

/-- **Theorem 5.23** (holonomy descent). Under the substitution
`U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹`, the holonomy of a path from `v₀` to `v_k`
becomes `Hol_{U^h}(γ) = h_{v_k} Hol_U(γ) h_{v₀}⁻¹`. In particular, for a loop
the holonomy changes by conjugation, so its conjugacy class is unchanged: the
class descends to gauge orbits. The book's group is finite; Lean states it for
every group. -/
@[book "thm:holonomy-descent"]
def holonomyDescent : Prop :=
  ∀ (X : Skeleton) (G : Type) [Group G] (U : X.LinkTable G) (h : X.V → G),
    (∀ (u v : X.V) (γ : X.Path u v),
      Skeleton.hol (Skeleton.gaugeAct h U) γ = h v * Skeleton.hol U γ * (h u)⁻¹) ∧
    (∀ (v : X.V) (γ : X.Path v v),
      ConjClasses.mk (Skeleton.hol (Skeleton.gaugeAct h U) γ) = ConjClasses.mk (Skeleton.hol U γ))

/-- **Theorem 5.27** (pure gauge equals loop-flat). On a connected transport
skeleton, a connection is pure gauge if and only if it is loop-flat. The
connection is given by its link table; the book's group is finite, and Lean
states it for every group. -/
@[book "thm:pure-gauge"]
def pureGauge : Prop :=
  ∀ (X : Skeleton) (G : Type) [Group G] (U : X.LinkTable G),
    X.Connected → (Skeleton.PureGauge U ↔ Skeleton.LoopFlat U)

/-- **Proposition 5.38** (discrete Stokes and divergence theorems). Let the
canvas carry its stored orientation, each face read anticlockwise.
1. `curl D = 0` and `div curl* = 0`.
2. Stokes: for a set `S` of faces, `Σ_{f ∈ S} curl A(f)` is the sum of `A`
   round the boundary of `S`: over the edges that lie on exactly one face of
   `S`, each read as that face reads it (for such an edge `e`,
   `Σ_{f ∈ S} inc(e, f)` is how that one face reads it).
3. Divergence: for a set `U` of vertices, `Σ_{v ∈ U} div E(v)` is the sum of
   `E` over the edges with exactly one end in `U`, each read in the direction
   leaving `U`.
4. Summation by parts, over the stored edges:
   `Σ_e Dφ(e) E(e) = −Σ_v φ(v) div E(v)` and
   `Σ_f curl A(f) B(f) = Σ_e A(e) curl* B(e)`.
Only part 2 uses that the faces are read anticlockwise. -/
@[book "prop:discrete-stokes"]
def discreteStokes : Prop :=
  ∀ (K : Canvas) (R : Type) [CommRing R],
    (∀ φ : K.V → R, K.curl (K.diff φ) = 0) ∧
    (∀ B : K.F → R, K.div (K.curlStar B) = 0) ∧
    (K.Anticlockwise → ∀ (S : Finset K.F) (A : K.E → R),
      ∑ f ∈ S, K.curl A f =
        ∑ e ∈ Finset.univ.filter
            (fun e => (S.filter fun f => e ∈ (K.boundary f).map Prod.fst).card = 1),
          (∑ f ∈ S, (K.inc e f : R)) * A e) ∧
    (∀ (U : Finset K.V) (E : K.E → R),
      ∑ v ∈ U, K.div E v =
        ∑ e ∈ Finset.univ.filter (fun e => K.src e ∈ U ∧ K.tgt e ∉ U), E e -
        ∑ e ∈ Finset.univ.filter (fun e => K.tgt e ∈ U ∧ K.src e ∉ U), E e) ∧
    (∀ (φ : K.V → R) (E : K.E → R), ∑ e, K.diff φ e * E e = -∑ v, φ v * K.div E v) ∧
    (∀ (A : K.E → R) (B : K.F → R), ∑ f, K.curl A f * B f = ∑ e, A e * K.curlStar B e)

/-- **Proposition 5.39** (reversing a tick of two steps). Let a tick be
`F = S₁ ∘ S₀`, and let an involution `R` of the states undo each step:
`R ∘ S₀ ∘ R = S₀⁻¹` and `R ∘ S₁ ∘ R = S₁⁻¹`. Then `I₀ = R ∘ S₀` and
`I₁ = S₁ ∘ R` are involutions, and each reverses the tick:
`I₀ ∘ F ∘ I₀ = F⁻¹ = I₁ ∘ F ∘ I₁`. (In `Equiv.Perm`, `f * g` is `f ∘ g`.) -/
@[book "prop:two-step-reversal"]
def twoStepReversal : Prop :=
  ∀ (S : Type) (S₀ S₁ R : Equiv.Perm S),
    R * R = 1 → R * S₀ * R = S₀⁻¹ → R * S₁ * R = S₁⁻¹ →
      (R * S₀) * (R * S₀) = 1 ∧ (S₁ * R) * (S₁ * R) = 1 ∧
      (R * S₀) * (S₁ * S₀) * (R * S₀) = (S₁ * S₀)⁻¹ ∧
      (S₁ * R) * (S₁ * S₀) * (S₁ * R) = (S₁ * S₀)⁻¹

open Classical in
/-- **Theorem 5.44** (Hall; supplies and demands). Let finitely many stores
hold goods `s(u) ≥ 0` and finitely many shops need goods `d(y) ≥ 0`, with equal
totals, and let each store be allowed to supply some of the shops. All the
goods can be sent along allowed pairs, every need met, if and only if every
set `U` of stores holds at most what the shops it may supply need together.
Goods are counted in whole units, as the tokens of a weave are. -/
@[book "thm:hall"]
def hall : Prop :=
  ∀ (Stores Shops : Type) [Fintype Stores] [Fintype Shops]
    (s : Stores → ℕ) (d : Shops → ℕ) (allowed : Stores → Shops → Prop),
    ∑ u, s u = ∑ y, d y →
    ((∃ x : Stores → Shops → ℕ, (∀ u y, x u y ≠ 0 → allowed u y) ∧
        (∀ u, ∑ y, x u y = s u) ∧ (∀ y, ∑ u, x u y = d y)) ↔
      ∀ U : Finset Stores,
        ∑ u ∈ U, s u ≤ ∑ y ∈ Finset.univ.filter (fun y => ∃ u ∈ U, allowed u y), d y)

end Artform.Statement
