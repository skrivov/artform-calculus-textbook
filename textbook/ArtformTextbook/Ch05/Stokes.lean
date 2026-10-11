import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import ArtformTextbook.Ch05.Statements

/-!
# Discrete Stokes and divergence theorems (Proposition 5.38)

The curl of a link field on a face is first written as the signed sum of the
link values round the face's boundary cycle. On a difference `Dφ`, each step
of the cycle contributes `φ(end) − φ(start)`, and round a closed walk these
telescope to zero: `curl D = 0`. Summation by parts exchanges finite sums;
`div curl* = 0` follows from it and `curl D = 0`, tested against the site
field that is `1` at one vertex and `0` elsewhere. The divergence theorem
exchanges the sums and counts each edge at its two ends. Stokes exchanges the
sums and uses that the canvas is anticlockwise: no face reads an edge twice,
and an edge on two faces of `S` is read by them in opposite directions, so its
two terms cancel and only the edges on exactly one face of `S` remain.
-/

namespace Artform

open scoped BigOperators

/-- Along a list `a :: t` followed by `b`, in which `g` of each element is `h`
of the next, the differences `φ (g x) - φ (h x)` add up to
`φ (h b) - φ (h a)`. -/
private theorem sum_map_sub_of_isChain {α γ β : Type*} [AddCommGroup β] {g h : α → γ}
    (φ : γ → β) :
    ∀ (t : List α) (a b : α), List.IsChain (fun x y => g x = h y) (a :: (t ++ [b])) →
      ((a :: t).map fun x => φ (g x) - φ (h x)).sum = φ (h b) - φ (h a)
  | [], a, b, hc => by
    simp only [List.nil_append, List.isChain_cons_cons, List.IsChain.singleton,
      and_true] at hc
    simp [hc]
  | c :: t, a, b, hc => by
    rw [List.cons_append, List.isChain_cons_cons] at hc
    rw [List.map_cons, List.sum_cons, sum_map_sub_of_isChain φ t c b hc.2, hc.1]
    abel

/-- Round a closed walk, the differences `φ(end) − φ(start)` of its steps add
up to zero. -/
private theorem sum_map_sub_eq_zero {V E β : Type*} [AddCommGroup β] {src tgt : E → V}
    {w : List (E × Bool)} (hw : IsClosedWalk src tgt w) (φ : V → β) :
    (w.map fun st => φ (stepEnd src tgt st) - φ (stepStart src tgt st)).sum = 0 := by
  obtain ⟨hne, hc⟩ := hw
  obtain ⟨a, t, rfl⟩ := List.ne_nil_iff_exists_cons.mp hne
  rw [sum_map_sub_of_isChain φ t a a hc, sub_self]

/-- Two different directions read an edge with opposite signs. -/
private theorem sign_add_sign : ∀ b c : Bool, b ≠ c →
    (if b then 1 else -1 : ℤ) + (if c then 1 else -1) = 0 := by
  decide

/-- Three directions of an edge cannot differ pairwise: there are only two. -/
private theorem bool_pigeonhole : ∀ b c d : Bool, b ≠ c → b ≠ d → c ≠ d → False := by
  decide

namespace Canvas

variable (K : Canvas) {R : Type*} [CommRing R]

/-- The curl of `A` on `f` is the sum of `A` round the boundary cycle of `f`,
each step counted `1` along its edge's stored direction and `-1` against it. -/
private theorem curl_eq_sum_boundary (A : K.E → R) (f : K.F) :
    K.curl A f = ((K.boundary f).map fun st => (if st.2 then 1 else -1 : R) * A st.1).sum := by
  unfold Canvas.curl Canvas.inc
  generalize K.boundary f = L
  induction L with
  | nil => simp
  | cons st L ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, add_mul, Finset.sum_add_distrib, ih]
    congr 1
    obtain ⟨e, b⟩ := st
    cases b <;> simp [apply_ite (Int.cast : ℤ → R), ite_mul]

/-- Part 1, first half: a difference has no curl. -/
private theorem curl_diff (φ : K.V → R) : K.curl (K.diff φ) = 0 := by
  funext f
  rw [curl_eq_sum_boundary, Pi.zero_apply, ← sum_map_sub_eq_zero (K.closed f) φ]
  congr 1
  refine List.map_congr_left fun ⟨e, b⟩ _ => ?_
  cases b <;> simp [Canvas.diff, stepEnd, stepStart]

/-- Part 4, second identity: `curl` and `curl*` are adjoint. -/
private theorem sum_curl_mul (A : K.E → R) (B : K.F → R) :
    ∑ f, K.curl A f * B f = ∑ e, A e * K.curlStar B e := by
  simp only [Canvas.curl, Canvas.curlStar, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ring

/-- Part 4, first identity: `D` and `-div` are adjoint. -/
private theorem sum_diff_mul (φ : K.V → R) (E : K.E → R) :
    ∑ e, K.diff φ e * E e = -∑ v, φ v * K.div E v := by
  simp only [Canvas.div, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Canvas.diff]
  ring

/-- Part 1, second half: an adjoint curl has no divergence. Test it against the
site field `δ` that is `1` at `v`: by summation by parts and `curl D = 0`,
`-div (curl* B) v = Σ_e Dδ(e) curl* B(e) = Σ_f curl (Dδ)(f) B(f) = 0`. -/
private theorem div_curlStar (B : K.F → R) : K.div (K.curlStar B) = 0 := by
  funext v
  have h := sum_diff_mul K (fun u => if u = v then (1 : R) else 0) (K.curlStar B)
  rw [← sum_curl_mul, curl_diff] at h
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, ite_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [Pi.zero_apply]
  exact neg_eq_zero.mp h.symm

/-- Part 3, the divergence theorem: an edge with both ends in `U` is counted
`+1` at its source and `-1` at its target, and one with a single end in `U`
once, with the sign of leaving `U`. -/
private theorem sum_div (U : Finset K.V) (E : K.E → R) :
    ∑ v ∈ U, K.div E v =
      ∑ e ∈ Finset.univ.filter (fun e => K.src e ∈ U ∧ K.tgt e ∉ U), E e -
      ∑ e ∈ Finset.univ.filter (fun e => K.tgt e ∈ U ∧ K.src e ∉ U), E e := by
  simp only [Canvas.div]
  rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  by_cases hs : K.src e ∈ U <;> by_cases ht : K.tgt e ∈ U <;> simp [hs, ht]

/-- A boundary cycle that does not cross `e` reads it `0` times. -/
private theorem sum_sign_eq_zero (L : List (K.E × Bool)) (e : K.E)
    (h : e ∉ L.map Prod.fst) :
    (L.map fun st => if st.1 = e then (if st.2 then 1 else -1 : ℤ) else 0).sum = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
  have : st.1 ≠ e := fun h' => h (List.mem_map.mpr ⟨st, hst, h'⟩)
  simp [this]

/-- A boundary cycle that crosses each edge at most once reads an edge it
crosses as `1` if it runs along the edge's stored direction, and as `-1` if it
runs against it. -/
private theorem sum_sign_eq_of_mem : ∀ (L : List (K.E × Bool)) (e : K.E) (b : Bool),
    (L.map Prod.fst).Nodup → (e, b) ∈ L →
    (L.map fun st => if st.1 = e then (if st.2 then 1 else -1 : ℤ) else 0).sum =
      if b then 1 else -1
  | [], _, _, _, h => absurd h List.not_mem_nil
  | st :: L, e, b, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h
      rw [sum_sign_eq_zero K L e hnd.1]
      simp
    · have hne : st.1 ≠ e := by
        rintro rfl
        exact hnd.1 (List.mem_map.mpr ⟨_, h, rfl⟩)
      rw [ite_eq_right hne, zero_add, sum_sign_eq_of_mem L e b hnd.2 h]

/-- On an anticlockwise canvas, the faces of `S` read an edge `e` with total
`0` unless exactly one of them crosses it. If none does, every term is `0`. If
two do, they read `e` in opposite directions, once each. Three cannot, since
two of them would read `e` in the same direction. -/
private theorem sum_inc_eq_zero (hK : K.Anticlockwise) (S : Finset K.F) (e : K.E)
    (he : (S.filter fun f => e ∈ (K.boundary f).map Prod.fst).card ≠ 1) :
    ∑ f ∈ S, K.inc e f = 0 := by
  have hsum : ∑ f ∈ S, K.inc e f =
      ∑ f ∈ S.filter fun f => e ∈ (K.boundary f).map Prod.fst, K.inc e f := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · rfl
    · exact sum_sign_eq_zero K _ e h
  rw [hsum]
  set T := S.filter fun f => e ∈ (K.boundary f).map Prod.fst
  have hdir : ∀ f ∈ T, ∃ b, (e, b) ∈ K.boundary f := by
    intro f hf
    obtain ⟨st, hst, h⟩ := List.mem_map.mp (Finset.mem_filter.mp hf).2
    exact ⟨st.2, h ▸ hst⟩
  match hT : T.card, he with
  | 0, _ => rw [Finset.card_eq_zero.mp hT, Finset.sum_empty]
  | 1, he => exact absurd rfl he
  | 2, _ =>
    obtain ⟨f, g, hfg, hTfg⟩ := Finset.card_eq_two.mp hT
    rw [hTfg] at hdir ⊢
    rw [Finset.sum_pair hfg]
    obtain ⟨b, hfb⟩ := hdir f (Finset.mem_insert_self f {g})
    obtain ⟨c, hgc⟩ := hdir g (Finset.mem_insert_of_mem (Finset.mem_singleton_self g))
    unfold Canvas.inc
    rw [sum_sign_eq_of_mem K _ e b (hK.nodup f) hfb,
      sum_sign_eq_of_mem K _ e c (hK.nodup g) hgc]
    exact sign_add_sign b c (hK.opposite e f g b c hfg hfb hgc)
  | n + 3, _ =>
    obtain ⟨f, hf, g, hg, h, hh, hfg, hfh, hgh⟩ :=
      Finset.two_lt_card.mp (show 2 < T.card by omega)
    obtain ⟨b, hfb⟩ := hdir f hf
    obtain ⟨c, hgc⟩ := hdir g hg
    obtain ⟨d, hhd⟩ := hdir h hh
    exact (bool_pigeonhole b c d (hK.opposite e f g b c hfg hfb hgc)
      (hK.opposite e f h b d hfh hfb hhd) (hK.opposite e g h c d hgh hgc hhd)).elim

/-- Part 2, Stokes: on an anticlockwise canvas, the curls over a set `S` of
faces add up to the sum of `A` over the edges on exactly one face of `S`. -/
private theorem stokes (hK : K.Anticlockwise) (S : Finset K.F) (A : K.E → R) :
    ∑ f ∈ S, K.curl A f =
      ∑ e ∈ Finset.univ.filter
          (fun e => (S.filter fun f => e ∈ (K.boundary f).map Prod.fst).card = 1),
        (∑ f ∈ S, (K.inc e f : R)) * A e := by
  have h1 : ∑ f ∈ S, K.curl A f = ∑ e, (∑ f ∈ S, (K.inc e f : R)) * A e := by
    simp only [Canvas.curl, Finset.sum_mul]
    exact Finset.sum_comm
  rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_).symm
  rw [Finset.mem_filter, not_and] at he
  rw [← Int.cast_sum, sum_inc_eq_zero K hK S e (he (Finset.mem_univ e)), Int.cast_zero,
    zero_mul]

end Canvas

-- ANCHOR: lstokesproof
/-- **Proposition 5.38** (discrete Stokes and divergence theorems). On every
canvas, `curl D = 0` and `div curl* = 0`; on an anticlockwise canvas, the curls
over a set of faces add up to the sum round its boundary (Stokes); the
divergences over a set of vertices add up to the flux out of it; and `D`,
`-div` and `curl`, `curl*` are adjoint pairs (summation by parts). -/
@[book "prop:discrete-stokes"]
theorem discreteStokes : Statement.discreteStokes := fun K _ _ =>
  ⟨K.curl_diff, K.div_curlStar, K.stokes, K.sum_div, K.sum_diff_mul,
    K.sum_curl_mul⟩
-- ANCHOR_END: lstokesproof

/-! ## Non-vacuity -/

-- ANCHOR: ltwosquares
/-- The book's two squares `K = SquareGrid(2,1)` of Section 5.5 are an
anticlockwise canvas, so part 2 applies to them. The vertices `v₀, …, v₅` are
`0, …, 5`, the faces `f_L, f_R` are `0, 1`, and the edges `e₁, …, e₇` are
`0, …, 6`, stored as the book orients them: the six outer edges anticlockwise
round the outside, the shared edge `e₂` from `v₁` up to `v₂`. The boundary of
`f_L` runs along `e₁, e₂, e₃, e₄`; that of `f_R` along `e₅, e₆, e₇` and then
against `e₂`. -/
example : Canvas.Anticlockwise
    { V := Fin 6, E := Fin 7, F := Fin 2
      src := ![0, 1, 2, 3, 1, 4, 5]
      tgt := ![1, 2, 3, 0, 4, 5, 2]
      boundary := ![[(0, true), (1, true), (2, true), (3, true)],
        [(4, true), (5, true), (6, true), (1, false)]]
      closed := by unfold IsClosedWalk; decide } :=
  ⟨by decide, by decide⟩
-- ANCHOR_END: ltwosquares

end Artform
