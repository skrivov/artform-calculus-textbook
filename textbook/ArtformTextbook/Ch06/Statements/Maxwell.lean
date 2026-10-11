import ArtformTextbook.Ch05.Defs.Laws
import ArtformTextbook.Ch06.Defs.Source
import ArtformTextbook.Ch06.Defs.MaxwellLaw
import ArtformTextbook.Ch06.Defs.Pairing
import ArtformTextbook.Ch06.Defs.Temporal
import ArtformTextbook.Ch06.Defs.Hop
import ArtformTextbook.Ch06.Defs.Window

/-!
# Statements of Chapter 6: the toy electrodynamics

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition. Every statement about the Maxwell law is made on
every canvas, the chapter's window `W = SquareGrid(3, 3)` among them; every
value is a residue modulo eight.
-/

namespace Artform.Statement

/-- **Corollary 6.2** (time reversal of the Maxwell tick). On states
`(A, E, J, ρ)` that carry their source, which the tick `F` carries unchanged,
the map `I(A, E, J, ρ) = (−A − E, E, −J, ρ)` is an involution; it reads each
link and each site alone: what it writes at a link depends only on `A`, `E`
and `J` there, and what it writes at a site only on `ρ` there; and
`I ∘ F ∘ I = F⁻¹`, that is, `I ∘ F ∘ I` undoes `F` on either side. A run read
backwards through `I` is a run: from `I(x_m)`, the run passes through
`I(x_{m−1}), …, I(x_0)`, where `x_0, x_1, …` is the run from `x_0`. -/
@[book "cor:maxwell-reversal"]
def maxwellReversal : Prop :=
  ∀ K : Canvas,
    let F := maxwellSourceTick K
    let I := maxwellTimeReversal K
    I ∘ I = id ∧
    (∀ (s t : MaxwellSourceState K) (e : K.E), s.A e = t.A e → s.E e = t.E e →
      s.J e = t.J e → (I s).A e = (I t).A e ∧ (I s).E e = (I t).E e ∧ (I s).J e = (I t).J e) ∧
    (∀ (s t : MaxwellSourceState K) (v : K.V), s.ρ v = t.ρ v → (I s).ρ v = (I t).ρ v) ∧
    (I ∘ F ∘ I) ∘ F = id ∧ F ∘ (I ∘ F ∘ I) = id ∧
    ∀ (x : MaxwellSourceState K) (m t : ℕ), t ≤ m →
      (maxwellSourceLaw K).run (I ((maxwellSourceLaw K).run x m)) t =
        I ((maxwellSourceLaw K).run x (m - t))

/-- **Theorem 6.3** (gauge covariance of the Maxwell tick). For fixed source
`J`, the Maxwell macro-tick commutes with the gauge action `A ↦ A + Dg`, which
fixes `E` and `ρ`: if `(A, E, ρ)` goes to `(A', E', ρ')`, then
`(A + Dg, E, ρ)` goes to `(A' + Dg, E', ρ')`. The law of Section 6.3, on the
frame that carries `A`, `E`, `J` on the links and `ρ` at the sites, is gauge
covariant in the sense of Definition 5.35 for the gauge action that adds `Dg`
to the potential and fixes `E`, `ρ` and `J`: so are its moves, and its
invariant `div E = ρ`. So is its realizer, which takes every link at every
phase: in each step it selects at `g · x` the same batch as at `x`. -/
@[book "thm:maxwell-covariant"]
def maxwellCovariant : Prop :=
  (∀ (K : Canvas) (J : K.E → ZMod 8) (g : K.V → ZMod 8) (s : MaxwellState K),
      maxwellTick K J (s.gauge g) = (maxwellTick K J s).gauge g) ∧
    (∀ K : Canvas,
      (maxwellGaugeAction K).CovariantLaw (maxwellInvariants K) (maxwellMoves K)) ∧
    ∀ (K : Canvas) (σ : MaxwellStep),
      (maxwellGaugeAction K).SameBatch (maxwellLegal K) (maxwellSelect K σ)

/-- **Theorem 6.4** (Gauss preservation). If the pre-tick state satisfies
Gauss, `div E = ρ`, and the source transition satisfies continuity,
`ρ' − ρ + div J = 0`, then the post-kick state satisfies `div E' = ρ'`, where
`E' = E + curl*(curl A) − J` is what the kick writes. -/
@[book "thm:gauss-preserved"]
def gaussPreserved : Prop :=
  ∀ (K : Canvas) (J : K.E → ZMod 8) (s : MaxwellState K) (ρ' : K.V → ZMod 8),
    K.div s.E = s.ρ → ρ' - s.ρ + K.div J = 0 → K.div (maxwellTick K J s).E = ρ'

/-- **Lemma 6.5** (the Maxwell shears keep the canonical pairing). On states
`(A, E)`, written as tables on two copies of the links, the pairing
`Ω((A, E), (a, e)) = ⟨A, e⟩ − ⟨E, a⟩` (`maxwellOmega`), where `⟨ , ⟩`
multiplies link tables link by link, each link once in its stored
orientation, and adds, is perfect; and the source-free kick
`E ↦ E + curl*(curl A)` and the move `A ↦ A − E` each keep it. -/
@[book "lem:maxwell-pairing"]
def maxwellPairing : Prop :=
  ∀ K : Canvas, (maxwellOmega K).Perfect ∧
    (∀ p q, maxwellOmega K (maxwellKick K p) (maxwellKick K q) = maxwellOmega K p q) ∧
    ∀ p q, maxwellOmega K (maxwellMove K p) (maxwellMove K q) = maxwellOmega K p q

/-- **Corollary 6.6** (Gauss's law from the tally of gauge symmetry). Write the
tick on the tables of `(A, E)` as the affine law `F(p) = M(p) + b`. For every
site function `g`, the source-free tick fixes `w_g = (Dg, 0)`; the tally that
Theorem 5.6 pairs with it, `Ω(w_g, ·)`, is conserved by the source-free law;
and `Ω(w_g, (A, E)) = ⟨Dg, E⟩ = −⟨g, div E⟩`. With no source, `div E` is
therefore kept at every site. With a source `J` the tick is affine with source
`b = (J, −J)`: it is the Maxwell tick on `(A, E)`; the tally changes at every
tick by `Ω(w_g, b)`, which is `⟨g, div J⟩`; and continuity
`ρ' − ρ + div J = 0` turns this into the conservation of `div E − ρ` at every
site. -/
@[book "cor:gauss-noether"]
def gaussNoether : Prop :=
  ∀ (K : Canvas) (g : K.V → ZMod 8),
    let w := gaugeDirection K g
    (maxwellAffine K 0).tick w = w ∧
    (maxwellAffine K 0).toDetLaw.Conserved (maxwellOmega K w) ∧
    (∀ A E : K.E → ZMod 8, maxwellOmega K w (fieldPair A E) = K.linkDot (K.diff g) E ∧
      K.linkDot (K.diff g) E = -K.siteDot g (K.div E)) ∧
    (∀ v : K.V, (maxwellAffine K 0).toDetLaw.Conserved (fun p => K.div (p ∘ Sum.inr) v)) ∧
    ∀ J : K.E → ZMod 8,
      (maxwellAffine K J).b = fieldPair J (-J) ∧
      (∀ s : MaxwellState K, (maxwellAffine K J).tick (fieldPair s.A s.E) =
        fieldPair (maxwellTick K J s).A (maxwellTick K J s).E) ∧
      (∀ p, maxwellOmega K w ((maxwellAffine K J).tick p) =
        maxwellOmega K w p + maxwellOmega K w (maxwellAffine K J).b) ∧
      maxwellOmega K w (maxwellAffine K J).b = K.siteDot g (K.div J) ∧
      ∀ (s : MaxwellState K) (ρ' : K.V → ZMod 8), ρ' - s.ρ + K.div J = 0 →
        K.div (maxwellTick K J s).E - ρ' = K.div s.E - s.ρ

/-- **Proposition 6.7** (a gauge change that varies from tick to tick). Let
`(A_t, E_t, ρ_t)` be a run of the Maxwell tick, and replace each `A_t` by
`A_t + Dχ_t`. The new frame keeps every kick, with its charge update, and
Gauss's law at every tick, and each Faraday move fails by exactly
`D(χ_{t+1} − χ_t)`:
`A_{t+1} + Dχ_{t+1} = (A_t + Dχ_t) − E_{t+1} + D(χ_{t+1} − χ_t)`. -/
@[book "prop:gauge-defect"]
def gaugeDefect : Prop :=
  ∀ (K : Canvas) (J : K.E → ZMod 8) (s : ℕ → MaxwellState K) (χ : ℕ → K.V → ZMod 8),
    IsMaxwellRun K J s → ∀ t : ℕ,
      (maxwellTick K J ((s t).gauge (χ t))).E = ((s (t + 1)).gauge (χ (t + 1))).E ∧
      (maxwellTick K J ((s t).gauge (χ t))).ρ = ((s (t + 1)).gauge (χ (t + 1))).ρ ∧
      (K.div ((s t).gauge (χ t)).E = ((s t).gauge (χ t)).ρ ↔ K.div (s t).E = (s t).ρ) ∧
      (s (t + 1)).A + K.diff (χ (t + 1)) =
        ((s t).A + K.diff (χ t)) - (s (t + 1)).E + K.diff (χ (t + 1) - χ t)

/-- **Theorem 6.9** (temporal links). Let the tick be the extended tick of
Definition 6.8.
1. Every gauge change carries runs of the extended tick to runs.
2. The gauge change with `χ_0 = 0` and `χ_{t+1} = χ_t − a₀(t)` carries every
   run of the extended tick to one whose temporal links are all `0`, that is,
   to a run of the Maxwell tick, with the same electric field, the same
   `curl A` and the same `div E − ρ` at every tick. -/
@[book "thm:temporal-links"]
def temporalLinks : Prop :=
  ∀ (K : Canvas) (J : K.E → ZMod 8),
    (∀ (s : ℕ → MaxwellState K) (a : TemporalLinks K) (χ : ℕ → K.V → ZMod 8),
      IsExtendedRun K J s a → IsExtendedRun K J (gaugeStates χ s) (gaugeLinks χ a)) ∧
    ∀ (s : ℕ → MaxwellState K) (a : TemporalLinks K) (χ : ℕ → K.V → ZMod 8),
      χ 0 = 0 → (∀ t, χ (t + 1) = χ t - a t) → IsExtendedRun K J s a →
        (∀ t, gaugeLinks χ a t = 0) ∧ IsMaxwellRun K J (gaugeStates χ s) ∧
        ∀ t, (gaugeStates χ s t).E = (s t).E ∧
          K.curl (gaugeStates χ s t).A = K.curl (s t).A ∧
          K.div (gaugeStates χ s t).E - (gaugeStates χ s t).ρ = K.div (s t).E - (s t).ρ

/-- **Proposition 6.10** (gauge covariance of a hop). The coupled hop of a
walker of charge `q` along an oriented link `ℓ : u → v` commutes with the
simultaneous gauge action on `A` and `ψ`: hopping in the transformed
potential `A + Dg` from the transformed amplitudes `ζ^{q g(x)} ψ(x)` gives the
gauge transform `ζ^{q g(v)}` of the amplitude transported to the target `v`.
Lean states it on every canvas, the line among them, for amplitudes in any
complex vector space. -/
@[book "prop:hop-covariance"]
def hopCovariance : Prop :=
  ∀ (K : Canvas) (M : Type) [AddCommGroup M] [Module ℂ M] (q : ZMod 8)
    (A : K.E → ZMod 8) (g : K.V → ZMod 8) (ψ : K.V → M) (ℓ : K.E × Bool),
    hop K q (A + K.diff g) (gaugeAmplitude q g ψ) ℓ =
      phase8 (q * g (stepEnd K.src K.tgt ℓ)) • hop K q A ψ ℓ

/-- **Proposition 6.11** (what the two steps force). Let a law on the links
of a square window `SquareGrid(m, n)` carry `A` and `E`, with no current, and
let its score open two steps in turn: a kick that adds to the `E` of every
link a value `φ(A)` computed from `A` on the faces at that link, and a move
that adds to the `A` of every link a value computed from that link's new `E`.
Suppose both additions are additive and the same at every face and every link:
the kick is built face by face by one rule `r` (`faceKick`), and the move adds
`μ(E'(e))` with one rule `μ` (`twoStepTick`). Suppose the kick is blind to
gauge changes, `φ(A + Dg) = φ(A)` for every site function `g`, and keeps
Gauss's law, `div φ(A) = 0` for every `A`. Then for some `κ` and `λ` in
`ℤ/8`, `E' = E + κ curl*(curl A)` and `A' = A − λ E'`. Conversely, every such
pair of steps is reversible and gauge covariant, and it keeps Gauss's law;
Lean states the converse on every canvas. -/
@[book "prop:maxwell-shape"]
def maxwellShape : Prop :=
  (∀ (m n : ℕ) (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8) (μ : ZMod 8 → ZMod 8),
    (∀ A A' : GridEdge m n → ZMod 8, faceKick r (A + A') = faceKick r A + faceKick r A') →
    (∀ x y : ZMod 8, μ (x + y) = μ x + μ y) →
    (∀ (A : GridEdge m n → ZMod 8) (g : GridVertex m n → ZMod 8),
      faceKick r (A + (squareGrid m n).diff g) = faceKick r A) →
    (∀ A : GridEdge m n → ZMod 8, (squareGrid m n).div (faceKick r A) = 0) →
    ∃ κ lam : ZMod 8, ∀ A E : GridEdge m n → ZMod 8,
      twoStepTick r μ (A, E) =
        (fun e => A e - lam * (E e + κ * (squareGrid m n).curlStar ((squareGrid m n).curl A) e),
          fun e => E e + κ * (squareGrid m n).curlStar ((squareGrid m n).curl A) e)) ∧
  ∀ (K : Canvas) (κ lam : ZMod 8),
    let kick : (K.E → ZMod 8) × (K.E → ZMod 8) → (K.E → ZMod 8) × (K.E → ZMod 8) :=
      fun s => (s.1, fun e => s.2 e + κ * K.curlStar (K.curl s.1) e)
    let move : (K.E → ZMod 8) × (K.E → ZMod 8) → (K.E → ZMod 8) × (K.E → ZMod 8) :=
      fun s => (fun e => s.1 e - lam * s.2 e, s.2)
    Function.Bijective kick ∧ Function.Bijective move ∧ Function.Bijective (move ∘ kick) ∧
    (∀ (A E : K.E → ZMod 8) (g : K.V → ZMod 8),
      kick (A + K.diff g, E) = ((kick (A, E)).1 + K.diff g, (kick (A, E)).2)) ∧
    (∀ (A E : K.E → ZMod 8) (g : K.V → ZMod 8),
      move (A + K.diff g, E) = ((move (A, E)).1 + K.diff g, (move (A, E)).2)) ∧
    ∀ (A E : K.E → ZMod 8) (ρ : K.V → ZMod 8), K.div E = ρ → K.div (move (kick (A, E))).2 = ρ

end Artform.Statement
