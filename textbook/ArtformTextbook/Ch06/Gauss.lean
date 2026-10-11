import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import ArtformTextbook.Ch05.Noether
import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# Gauss's law rides with the dynamics (Section 6.4)

Theorem 6.4 by the book's calculation: `div curl* = 0` removes the middle
term of `div E' = div E + div curl* B − div J`, and continuity does the rest.
Lemma 6.5: the pairing `Ω` is the multiply-and-add pairing after the turn
`(A, E) ↦ (−E, A)`, so it is perfect, and the two shears keep it because
`curl*` is the transpose of `curl`. Corollary 6.6 applies Theorem 5.6
(`Artform.noether`) to the tick on the tables of `(A, E)`.
-/

namespace Artform

open scoped BigOperators

/-- **Theorem 6.4** (Gauss preservation). If `div E = ρ` before the tick and
`ρ' − ρ + div J = 0`, then `div E' = ρ'` after the kick. -/
@[book "thm:gauss-preserved"]
theorem gaussPreserved : Statement.gaussPreserved := by
  intro K J s ρ' hG hC
  have hρ' : ρ' = s.ρ - K.div J := by
    rw [← sub_eq_zero, ← hC]
    abel
  simp only [maxwellTick, Canvas.div_sub, Canvas.div_add, Canvas.div_curlStar, add_zero, hG,
    hρ']

variable (K : Canvas)

/-- The turn `(A, E) ↦ (−E, A)` of the tables of `(A, E)`. -/
def omegaTurn (p : K.E ⊕ K.E → ZMod 8) : K.E ⊕ K.E → ZMod 8 :=
  fieldPair (-(p ∘ Sum.inr)) (p ∘ Sum.inl)

/-- The turn back, `(A, E) ↦ (E, −A)`. -/
def omegaUnturn (p : K.E ⊕ K.E → ZMod 8) : K.E ⊕ K.E → ZMod 8 :=
  fieldPair (p ∘ Sum.inr) (-(p ∘ Sum.inl))

theorem omegaTurn_unturn (p : K.E ⊕ K.E → ZMod 8) : omegaTurn K (omegaUnturn K p) = p := by
  funext c
  cases c <;> simp [omegaTurn, omegaUnturn, fieldPair]

theorem omegaUnturn_turn (p : K.E ⊕ K.E → ZMod 8) : omegaUnturn K (omegaTurn K p) = p := by
  funext c
  cases c <;> simp [omegaTurn, omegaUnturn, fieldPair]

/-- `Ω(p, q)` is the multiply-and-add pairing of the turned `p` with `q`. -/
theorem maxwellOmega_eq_dot (p q : K.E ⊕ K.E → ZMod 8) :
    maxwellOmega K p q = dotPairing (K.E ⊕ K.E) 8 (omegaTurn K p) q := by
  simp only [maxwellOmega, dotPairing, AddMonoidHom.mk'_apply, Canvas.linkDot,
    Fintype.sum_sum_type, omegaTurn, fieldPair, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

/-- The pairing of `(A, E)` and `(a, e)` is `⟨A, e⟩ − ⟨E, a⟩`. -/
theorem maxwellOmega_fieldPair (A E a e : K.E → ZMod 8) :
    maxwellOmega K (fieldPair A E) (fieldPair a e) = K.linkDot A e - K.linkDot E a := rfl

/-- `Ω` is perfect: a tally is `Ω(w, ·)` for exactly one table `w`. -/
theorem maxwellOmega_perfect : (maxwellOmega K).Perfect := by
  intro T
  obtain ⟨w', hw', huniq⟩ := dotPairing_perfect (K.E ⊕ K.E) 8 T
  have hΩ : ∀ w, maxwellOmega K w = dotPairing (K.E ⊕ K.E) 8 (omegaTurn K w) := fun w =>
    AddMonoidHom.ext fun q => maxwellOmega_eq_dot K w q
  refine ⟨omegaUnturn K w', ?_, fun w hw => ?_⟩
  · change maxwellOmega K (omegaUnturn K w') = T
    rw [hΩ, omegaTurn_unturn, hw']
  · rw [← huniq (omegaTurn K w) ((hΩ w).symm.trans hw), omegaUnturn_turn]

/-- `⟨A, curl*(curl a)⟩ = ⟨curl*(curl A), a⟩`: `curl*` is the transpose of
`curl`. -/
theorem linkDot_curlStar_curl (A a : K.E → ZMod 8) :
    K.linkDot A (K.curlStar (K.curl a)) = K.linkDot (K.curlStar (K.curl A)) a := by
  unfold Canvas.linkDot
  rw [← K.sum_curl_mul A (K.curl a),
    Finset.sum_congr rfl fun e _ => mul_comm (K.curlStar (K.curl A) e) (a e),
    ← K.sum_curl_mul a (K.curl A)]
  exact Finset.sum_congr rfl fun f _ => mul_comm _ _

/-- The source-free kick keeps `Ω`. -/
theorem maxwellKick_keeps (p q : K.E ⊕ K.E → ZMod 8) :
    maxwellOmega K (maxwellKick K p) (maxwellKick K q) = maxwellOmega K p q := by
  have h := linkDot_curlStar_curl K (p ∘ Sum.inl) (q ∘ Sum.inl)
  simp only [maxwellOmega, maxwellKick, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    AddMonoidHom.mk'_apply, fieldPair, Sum.elim_comp_inl, Sum.elim_comp_inr] at h ⊢
  simp only [Canvas.linkDot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib] at h ⊢
  rw [h]
  abel

/-- The move keeps `Ω`. -/
theorem maxwellMove_keeps (p q : K.E ⊕ K.E → ZMod 8) :
    maxwellOmega K (maxwellMove K p) (maxwellMove K q) = maxwellOmega K p q := by
  simp only [maxwellOmega, maxwellMove, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    AddMonoidHom.mk'_apply, fieldPair, Sum.elim_comp_inl, Sum.elim_comp_inr, Canvas.linkDot,
    Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm]
  abel

/-- **Lemma 6.5** (the Maxwell shears keep the canonical pairing). `Ω` is
perfect, and the source-free kick and the move each keep it. -/
@[book "lem:maxwell-pairing"]
theorem maxwellPairing : Statement.maxwellPairing := fun K =>
  ⟨maxwellOmega_perfect K, maxwellKick_keeps K, maxwellMove_keeps K⟩

/-- The tick with any source keeps `Ω`: its additive part is the kick followed
by the move. -/
theorem maxwellAffine_keeps (J : K.E → ZMod 8) : (maxwellAffine K J).Keeps (maxwellOmega K) :=
  fun p q => by
    change maxwellOmega K (maxwellMove K (maxwellKick K p)) (maxwellMove K (maxwellKick K q)) = _
    rw [maxwellMove_keeps, maxwellKick_keeps]

/-- The source-free tick fixes `w_g = (Dg, 0)`. -/
theorem maxwellLinear_gaugeDirection (g : K.V → ZMod 8) :
    maxwellLinear K (gaugeDirection K g) = gaugeDirection K g := by
  funext c
  cases c <;>
    simp [maxwellLinear, maxwellKick, maxwellMove, gaugeDirection, fieldPair,
      Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- `Ω(w_g, (A, E)) = ⟨Dg, E⟩`. -/
theorem maxwellOmega_gaugeDirection (g : K.V → ZMod 8) (A E : K.E → ZMod 8) :
    maxwellOmega K (gaugeDirection K g) (fieldPair A E) = K.linkDot (K.diff g) E := by
  simp [gaugeDirection, maxwellOmega_fieldPair, Canvas.linkDot]

/-- `⟨Dg, E⟩ = −⟨g, div E⟩`, summation by parts. -/
theorem linkDot_diff (g : K.V → ZMod 8) (E : K.E → ZMod 8) :
    K.linkDot (K.diff g) E = -K.siteDot g (K.div E) :=
  K.sum_diff_mul g E

/-- **Corollary 6.6** (Gauss's law from the tally of gauge symmetry). The
source-free tick fixes `w_g = (Dg, 0)`; Theorem 5.6 makes `Ω(w_g, ·)` a
conserved tally, equal to `⟨Dg, E⟩ = −⟨g, div E⟩`; with a source `J` the tick
is affine with source `(J, −J)`, the tally changes by `Ω(w_g, b) = ⟨g, div J⟩`,
and continuity keeps `div E − ρ`. -/
@[book "cor:gauss-noether"]
theorem gaussNoether : Statement.gaussNoether := by
  intro K g
  have hM : (maxwellAffine K 0).M (gaugeDirection K g) = gaugeDirection K g :=
    maxwellLinear_gaugeDirection K g
  have hb0 : (maxwellAffine K 0).b = 0 := by
    funext c
    cases c <;> simp [maxwellAffine, fieldPair]
  have hN0 := (noether (K.E ⊕ K.E) 8 (maxwellAffine K 0) (maxwellOmega K)
    (maxwellAffine_keeps K 0)).1 _ hM
  refine ⟨?_, hN0.2.2 (by rw [hb0, map_zero]), fun A E =>
    ⟨maxwellOmega_gaugeDirection K g A E, linkDot_diff K g E⟩, fun v p => ?_, fun J => ?_⟩
  · rw [AffineLaw.tick, hM, hb0, add_zero]
  · -- the source-free kick adds `curl*(curl A)`, which has no divergence
    change K.div ((maxwellAffine K 0).tick p ∘ Sum.inr) v = K.div (p ∘ Sum.inr) v
    have h : (maxwellAffine K 0).tick p ∘ Sum.inr =
        p ∘ Sum.inr + K.curlStar (K.curl (p ∘ Sum.inl)) := by
      funext e
      simp [AffineLaw.tick, maxwellAffine, maxwellLinear, maxwellKick, maxwellMove, fieldPair]
    rw [h, Canvas.div_add, Canvas.div_curlStar, add_zero]
  · have hNJ := (noether (K.E ⊕ K.E) 8 (maxwellAffine K J) (maxwellOmega K)
      (maxwellAffine_keeps K J)).1 _ hM
    refine ⟨rfl, fun s => ?_, hNJ.2.1, ?_, fun s ρ' hC => ?_⟩
    · funext c
      cases c with
      | inl e =>
        simp only [AffineLaw.tick, maxwellAffine, maxwellLinear, maxwellKick, maxwellMove,
          AddEquiv.trans_apply, AddEquiv.coe_mk, Equiv.coe_fn_mk, fieldPair, Pi.add_apply,
          Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.sub_apply, maxwellTick]
        abel
      | inr e =>
        simp only [AffineLaw.tick, maxwellAffine, maxwellLinear, maxwellKick, maxwellMove,
          AddEquiv.trans_apply, AddEquiv.coe_mk, Equiv.coe_fn_mk, fieldPair, Pi.add_apply,
          Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.neg_apply, Pi.sub_apply,
          maxwellTick]
        abel
    · -- `Ω((Dg, 0), (J, −J)) = −⟨Dg, J⟩ = ⟨g, div J⟩`
      change maxwellOmega K (fieldPair (K.diff g) 0) (fieldPair J (-J)) = _
      rw [maxwellOmega_fieldPair]
      simp only [Canvas.linkDot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, sub_zero]
      rw [K.sum_diff_mul g J, neg_neg]
      rfl
    · have hρ' : ρ' = s.ρ - K.div J := by
        rw [← sub_eq_zero, ← hC]
        abel
      simp only [maxwellTick, Canvas.div_sub, Canvas.div_add, Canvas.div_curlStar, add_zero,
        hρ']
      abel

/-! ## Non-vacuity -/

/-- The hypotheses of Theorem 6.4 met on the face of Figure 6.7: with
`E = (0, 0, 1, 0)`, the charges `0, 0, 1, 7` satisfy Gauss's law, and with no
current, continuity keeps them (the checkpoint after Figure 6.9). -/
example : let s : MaxwellState oneFace := ⟨![1, 2, 0, 3], ![0, 0, 1, 0], ![0, 0, 1, 7]⟩
    oneFace.div s.E = s.ρ ∧ s.ρ - s.ρ + oneFace.div 0 = 0 := by
  intro s
  constructor <;> decide

/-- On the face of Figure 6.7, `Ω` is not the zero pairing: it pairs the
potential `1` on `ℓ₁` with the electric value `1` on `ℓ₁` to `1`. -/
example : maxwellOmega oneFace (fieldPair ![1, 0, 0, 0] 0) (fieldPair 0 ![1, 0, 0, 0]) = 1 := by
  rw [maxwellOmega_fieldPair]
  decide

/-- On the face of Figure 6.7, the source-free tick fixes the gauge direction of
`g = (1, 0, 0, 0)`, which is not `0`. -/
example : (maxwellAffine oneFace 0).tick (gaugeDirection oneFace ![1, 0, 0, 0]) =
      gaugeDirection oneFace ![1, 0, 0, 0] ∧
    gaugeDirection oneFace (![1, 0, 0, 0] : Fin 4 → ZMod 8) ≠ 0 := by
  refine ⟨(gaussNoether oneFace ![1, 0, 0, 0]).1, fun h => ?_⟩
  have h1 := congrFun h (Sum.inl 0)
  revert h1
  decide

end Artform
