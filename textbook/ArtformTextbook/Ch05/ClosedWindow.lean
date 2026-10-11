import Mathlib.Data.Fin.VecNotation
import ArtformTextbook.Ch05.Statements.Gauge
import ArtformTextbook.Ch05.Stokes

/-!
# Closed-window conservation (Theorem 5.40)

The proof is the book's. Sum the continuity equation over the sites of the
window: by the divergence part of Proposition 5.38, the divergences add up to
the flux along the edges with exactly one end in the window, each read leaving
it, and the boundary condition makes that flux zero. So the total charge of the
window does not change from one tick to the next. A whole finite canvas is the
window of all its sites, which no edge leaves.
-/

namespace Artform

open scoped BigOperators

/-- **Theorem 5.40** (closed-window conservation). Under the local continuity
equation, the total charge of a finite canvas is constant in time, and so is
the total charge of a window that no edge carrying flux leaves. -/
@[book "thm:closed-window"]
theorem closedWindow : Statement.closedWindow := by
  intro K R _ ρ J
  have window : ∀ W : Finset K.V,
      (∀ t, ∀ v ∈ W, ρ (t + 1) v - ρ t v + K.div (J t) v = 0) →
      (∀ t e, (K.src e ∈ W ∧ K.tgt e ∉ W) ∨ (K.tgt e ∈ W ∧ K.src e ∉ W) → J t e = 0) →
      ∀ t s, ∑ v ∈ W, ρ t v = ∑ v ∈ W, ρ s v := by
    intro W hc hb
    have step : ∀ t, ∑ v ∈ W, ρ (t + 1) v = ∑ v ∈ W, ρ t v := by
      intro t
      -- the divergence theorem, with no flux across the edge of the window
      have hdiv : ∑ v ∈ W, K.div (J t) v = 0 := by
        rw [(discreteStokes K R).2.2.2.1 W (J t),
          Finset.sum_eq_zero fun e he => hb t e (Or.inl (Finset.mem_filter.mp he).2),
          Finset.sum_eq_zero fun e he => hb t e (Or.inr (Finset.mem_filter.mp he).2),
          sub_zero]
      have h := Finset.sum_eq_zero (hc t)
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hdiv, add_zero, sub_eq_zero] at h
      exact h
    have h0 : ∀ t, ∑ v ∈ W, ρ t v = ∑ v ∈ W, ρ 0 v := by
      intro t
      induction t with
      | zero => rfl
      | succ n ih => rw [step, ih]
    intro t s
    rw [h0 t, h0 s]
  refine ⟨fun hc t s => ?_, window⟩
  have h := window Finset.univ (fun t v _ => hc t v) (fun t e he => by simp at he) t s
  simpa using h

/-! ## Non-vacuity

The two squares of Section 5.5 as a canvas (vertices `v₀, …, v₅` as `0, …, 5`,
edges `e₁, …, e₇` as `0, …, 6`, faces `f_L, f_R` as `0, 1`, as in the example of
Proposition 5.38), and the window of the left square, `v₀, …, v₃`. A unit charge
at `v₀` hops along `e₁` to `v₁` at the first tick and then stays: the flux is
`1` on `e₁` at tick `0` and `0` otherwise. The continuity equation holds at
every site, and the two edges that leave the window, `e₅` and `e₇`, carry no
flux. -/

/-- The two squares `K = SquareGrid(2,1)` as a canvas. -/
private abbrev twoSquaresCanvas : Canvas where
  V := Fin 6
  E := Fin 7
  F := Fin 2
  src := ![0, 1, 2, 3, 1, 4, 5]
  tgt := ![1, 2, 3, 0, 4, 5, 2]
  boundary := ![[(0, true), (1, true), (2, true), (3, true)],
    [(4, true), (5, true), (6, true), (1, false)]]
  closed := by unfold IsClosedWalk; decide

/-- The charge: `1` at `v₀` at tick `0`, then `1` at `v₁`. -/
private def hopCharge (t : ℕ) (v : Fin 6) : ℤ :=
  if t = 0 then (if v = 0 then 1 else 0) else (if v = 1 then 1 else 0)

/-- The flux: `1` along `e₁` at tick `0`, and nothing afterwards. -/
private def hopFlux (t : ℕ) (e : Fin 7) : ℤ :=
  if t = 0 ∧ e = 0 then 1 else 0

/-- The hypotheses of the window part of Theorem 5.40 are met, so the charge of
the left square stays `1`. -/
example : ∀ t, ∑ v ∈ ({0, 1, 2, 3} : Finset (Fin 6)), hopCharge t v = 1 := by
  have hc : ∀ t, ∀ v ∈ ({0, 1, 2, 3} : Finset (Fin 6)),
      hopCharge (t + 1) v - hopCharge t v + twoSquaresCanvas.div (hopFlux t) v = 0 := by
    intro t v _
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · revert v
      decide
    · have h2 : t ≠ 0 := by omega
      simp [hopCharge, hopFlux, h2, Canvas.div]
  have hb : ∀ t e, (twoSquaresCanvas.src e ∈ ({0, 1, 2, 3} : Finset (Fin 6)) ∧
      twoSquaresCanvas.tgt e ∉ ({0, 1, 2, 3} : Finset (Fin 6))) ∨
      (twoSquaresCanvas.tgt e ∈ ({0, 1, 2, 3} : Finset (Fin 6)) ∧
        twoSquaresCanvas.src e ∉ ({0, 1, 2, 3} : Finset (Fin 6))) → hopFlux t e = 0 := by
    intro t e he
    have : e ≠ 0 := by
      rintro rfl
      revert he
      decide
    simp [hopFlux, this]
  intro t
  exact ((closedWindow twoSquaresCanvas ℤ hopCharge hopFlux).2 _ hc hb t 0).trans (by decide)

end Artform
