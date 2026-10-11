import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import ArtformTextbook.Ch05.Statements

/-!
# What a conserved reading can see (Section 5.2)

Theorem 5.4, by the book's proof. The orbit of a state is its forward orbit
`{x, F(x), F²(x), …}`. Only the converse half of the last claim uses that the
tick is a bijection of a finite set: then the run from every state comes back
to it, so `x` and `F(x)` have the same orbit, and the reading that gives each
state its orbit is conserved. That reading stands in for the book's, `1` on
one orbit and `0` elsewhere.
-/

namespace Artform

/-- **Theorem 5.4** (what a conserved reading can see). Let the tick `F` of a
deterministic law be a bijection of its finite set of states, so that the
states fall into orbits `{x, F(x), F²(x), …}`.
1. A reading is conserved exactly when it is constant on each orbit.
2. A symmetry `s` carries every orbit onto an orbit. Some conserved reading
   tells `x` from `s(x)`, for some `x`, exactly when `s` carries some orbit
   onto a different orbit. -/
@[book "thm:orbit-criterion"]
theorem orbitCriterion : Statement.orbitCriterion := by
  intro S _ L hF
  have self_mem : ∀ x, x ∈ L.orbit x := fun x => ⟨0, rfl⟩
  -- (i) `q(F(x)) = q(x)` for every `x` makes `q` constant along `x, F(x), F²(x), …`.
  have conserved_iff : ∀ (V : Type) (q : S → V),
      L.Conserved q ↔ ∀ x, ∀ y ∈ L.orbit x, q y = q x := by
    intro V q
    refine ⟨fun hq x => ?_, fun h x => h x _ ⟨1, rfl⟩⟩
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      change q (L.tick^[n + 1] x) = q x
      rw [Function.iterate_succ_apply', hq]
      exact ih
  -- (ii) From `s(Fᵏ(x)) = Fᵏ(s(x))`, `s` carries the orbit of `x` onto that of `s(x)`.
  have image_orbit : ∀ s, L.IsSymmetry s → ∀ x, s '' L.orbit x = L.orbit (s x) := by
    intro s hs x
    change s '' Set.range (L.run x) = Set.range (L.run (s x))
    rw [← Set.range_comp]
    congr 1
    funext n
    exact ((show Function.Commute L.tick s from hs).iterate_left n x).symm
  have orbit_subset : ∀ x y, y ∈ L.orbit x → L.orbit y ⊆ L.orbit x := by
    rintro x _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨n + m, Function.iterate_add_apply _ _ _ _⟩
  -- The run from `y` meets some state twice, since the states are finite; as the
  -- tick is injective, it comes back to `y`, so `y` lies on the orbit of `F(y)`.
  have periodic : ∀ y, y ∈ L.orbit (L.tick y) := by
    intro y
    have back : ∀ m n, m < n → L.run y m = L.run y n → y ∈ L.orbit (L.tick y) := by
      intro m n hlt h
      have hy : L.tick^[n - m] y = y := by
        apply hF.1.iterate m
        rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
        exact h.symm
      refine ⟨n - m - 1, ?_⟩
      change L.tick^[n - m - 1] (L.tick y) = y
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (Nat.sub_pos_of_lt hlt)]
      exact hy
    obtain ⟨m, n, h, hne⟩ := Function.not_injective_iff.1
      (not_injective_infinite_finite (L.run y))
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    exacts [back m n hlt h, back n m hlt h.symm]
  have orbit_tick : ∀ y, L.orbit (L.tick y) = L.orbit y := fun y =>
    Set.Subset.antisymm (orbit_subset _ _ ⟨1, rfl⟩) (orbit_subset _ _ (periodic y))
  refine ⟨conserved_iff, fun s hs => ⟨image_orbit s hs, ?_, ?_⟩⟩
  · -- If `s` carries the orbit of `x` onto itself, `s(x)` lies on it, and every
    -- conserved reading agrees on `x` and `s(x)` by (i).
    rintro ⟨V, q, hq, x, hx⟩
    refine ⟨x, fun h => hx ((conserved_iff V q).1 hq x (s x) ?_).symm⟩
    exact h ▸ Set.mem_image_of_mem s (self_mem x)
  · -- The orbit itself is a conserved reading, and it tells `x` from `s(x)`.
    rintro ⟨x, hx⟩
    refine ⟨Set S, L.orbit, orbit_tick, x, ?_⟩
    rw [← image_orbit s hs x]
    exact fun h => hx h.symm

/-! ## Non-vacuity

The law of the square of Section 5.1 meets the hypotheses: its tick is a
bijection of the finite set of tables `Fin 4 → ZMod 3`. On it, as in
Figure 5.2(c), adding `1` at every corner is a symmetry, and the total modulo
`3` is a conserved reading that tells `(0, 1, 2, 0)` from `(1, 2, 0, 1)`. -/

/-- The tick of the square is a bijection of the finite set of tables; its
inverse copies the corner ahead. -/
example : Finite (Fin 4 → ZMod 3) ∧ Function.Bijective squareLaw.toDetLaw.tick := by
  refine ⟨inferInstance, ?_⟩
  have h : squareLaw.toDetLaw.tick = squareShift := funext fun p => add_zero (squareShift p)
  rw [h]
  exact squareShift.bijective

/-- Part 2 of Theorem 5.4 on the square: adding `1` at every corner is a
symmetry, the total is conserved and tells `(0, 1, 2, 0)` from its image
`(1, 2, 0, 1)`, so the symmetry carries some orbit onto a different orbit. -/
example : ∃ x, (· + fun _ => (1 : ZMod 3)) '' squareLaw.toDetLaw.orbit x ≠
    squareLaw.toDetLaw.orbit x := by
  have hF : Function.Bijective squareLaw.toDetLaw.tick := by
    have h : squareLaw.toDetLaw.tick = squareShift := funext fun p => add_zero (squareShift p)
    rw [h]
    exact squareShift.bijective
  have hs : squareLaw.toDetLaw.IsSymmetry (· + fun _ => 1) := by
    intro p
    funext i
    simp [squareLaw, AffineLaw.toDetLaw, AffineLaw.tick, squareShift]
  have hT : squareLaw.toDetLaw.Conserved squareTotal := by
    intro p
    change p 3 + 0 + (p 0 + 0) + (p 1 + 0) + (p 2 + 0) = p 0 + p 1 + p 2 + p 3
    ring
  have hx : squareTotal ![0, 1, 2, 0] ≠ squareTotal (![0, 1, 2, 0] + fun _ => 1) := by decide
  exact ((orbitCriterion _ _ hF).2 _ hs).2.1 ⟨ZMod 3, squareTotal, hT, ![0, 1, 2, 0], hx⟩

end Artform
