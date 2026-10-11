import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases
import ArtformTextbook.Ch05.Statements

/-!
# Noether's theorem for affine laws (Section 5.3)

The proofs of Theorem 5.6 and of Corollary 5.7. The corollary applies the
theorem to the law of the square: its tick keeps the multiply-and-add pairing,
that pairing is perfect, and the source is `0`.
-/

namespace Artform

/-- **Theorem 5.6** (Noether's theorem for affine laws). Let an affine law
`F(p) = M(p) + b` keep a pairing `⟨ , ⟩`. For every table `w` with `M(w) = w`,
adding `w` is a symmetry and `T_w(F(p)) = T_w(p) + ⟨w, b⟩`; if the pairing is
perfect, every conserved tally is `T_w` for exactly one `w`, and that `w` has
`M(w) = w` and `⟨w, b⟩ = 0`. -/
@[book "thm:noether"]
theorem noether : Statement.noether := by
  intro C _ n L P hP
  refine ⟨fun w hw => ?_, fun hPerf T hT => ?_⟩
  · -- (i) `⟨w, M(p)⟩ = ⟨M(w), M(p)⟩ = ⟨w, p⟩`.
    have hwM : ∀ p, P w (L.M p) = P w p := fun p => by
      have h := hP w p
      rwa [hw] at h
    have hshare : ∀ p, P w (L.tick p) = P w p + P w L.b := fun p => by
      rw [AffineLaw.tick, map_add, hwM]
    refine ⟨fun x => ?_, hshare, fun hb p => ?_⟩
    · change L.M (x + w) + L.b = L.M x + L.b + w
      rw [map_add, hw, add_right_comm]
    · change P w (L.tick p) = P w p
      rw [hshare, hb, add_zero]
  · -- (ii) `T(b) = T(F(0)) = T(0) = 0`, so `T(M(p)) = T(p)`.
    obtain ⟨w₀, -, huniq⟩ := hPerf T
    have hTb : T L.b = 0 := by
      have h := hT 0
      change T (L.M 0 + L.b) = T 0 at h
      rwa [map_zero L.M, zero_add, map_zero T] at h
    have hTM : ∀ p, T (L.M p) = T p := fun p => by
      have h := hT p
      change T (L.M p + L.b) = T p at h
      rwa [map_add, hTb, add_zero] at h
    refine ⟨hPerf T, fun w hw => ⟨?_, by rw [hw, hTb]⟩⟩
    -- `⟨M(w), M(p)⟩ = ⟨w, p⟩ = T(p) = T(M(p))`, and `M(p)` runs through every
    -- table.
    have hMw : P (L.M w) = T := AddMonoidHom.ext fun q => by
      rw [← L.M.apply_symm_apply q, hP, hw, hTM]
    exact (huniq _ hMw).trans (huniq _ hw).symm

/-- The multiply-and-add pairing on the tables of a finite set of cells is
perfect: a tally `T` is `⟨w, ·⟩` for the one table `w` that holds its values
`w(i) = T(eᵢ)` on the tables `eᵢ` with a single `1`. -/
theorem dotPairing_perfect (C : Type*) [Fintype C] (n : ℕ) : (dotPairing C n).Perfect := by
  classical
  intro T
  have hsingle : ∀ (w : C → ZMod n) (i : C), dotPairing C n w (Pi.single i 1) = w i := by
    intro w i
    simp [dotPairing, Pi.single_apply]
  refine ⟨fun i => T (Pi.single i 1), ?_, fun w hw => funext fun i => ?_⟩
  · refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
    have hx : (Pi.single i x : C → ZMod n) = x • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hx, ZMod.map_smul, ZMod.map_smul, hsingle]
  · rw [← hsingle w i, hw]

/-- The tick of the square copies each corner's value to the next corner, so it
keeps the multiply-and-add pairing. -/
theorem squareLaw_keeps : squareLaw.Keeps (dotPairing (Fin 4) 3) := fun p q =>
  Equiv.sum_comp (Equiv.subRight (1 : Fin 4)) fun i => p i * q i

/-- The tables fixed by the tick of the square are the constant ones. -/
theorem squareLaw_tick_eq_self (w : Fin 4 → ZMod 3) :
    squareLaw.tick w = w ↔ ∃ c, (fun _ => c) = w := by
  constructor
  · intro h
    have h' : ∀ i, w (i - 1) = w i := fun i => by
      simpa [squareLaw, AffineLaw.tick, squareShift] using congrFun h i
    refine ⟨w 0, funext fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h' 1
    · exact (h' 1).trans (h' 2)
    · exact ((h' 1).trans (h' 2)).trans (h' 3)
  · rintro ⟨c, rfl⟩
    ext i
    simp [squareLaw, AffineLaw.tick, squareShift]

/-- **Corollary 5.7** (Noether's theorem on the square). The tables fixed by the
tick are the three constant ones; adding the same number at every corner is a
symmetry; the tally paired with `1` at every corner is the total, and it is
conserved; and every conserved tally is `0`, `T` or `2T`. -/
@[book "cor:noether-square"]
theorem noetherSquare : Statement.noetherSquare := by
  have hN := noether (Fin 4) 3 squareLaw (dotPairing (Fin 4) 3) squareLaw_keeps
  have hconst : ∀ c : ZMod 3, squareLaw.M (fun _ => c) = fun _ => c := fun _ => rfl
  have hone : dotPairing (Fin 4) 3 (fun _ => 1) = squareTotal := AddMonoidHom.ext fun p => by
    simp [dotPairing, squareTotal, Fin.sum_univ_four]
  refine ⟨Set.ext squareLaw_tick_eq_self, fun c => (hN.1 _ (hconst c)).1, hone, ?_, ?_⟩
  · rw [← hone]
    exact (hN.1 _ (hconst 1)).2.2 (map_zero _)
  · intro T hT
    obtain ⟨⟨w, hw, -⟩, h2⟩ := hN.2 (dotPairing_perfect _ _) T hT
    have hMw : squareLaw.tick w = w := by
      rw [AffineLaw.tick, (h2 w hw).1]
      exact add_zero w
    obtain ⟨c, rfl⟩ := (squareLaw_tick_eq_self w).1 hMw
    subst hw
    have hc : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
    rcases hc c with rfl | rfl | rfl
    · exact Or.inl (AddMonoidHom.ext fun p => by simp [dotPairing])
    · exact Or.inr (Or.inl hone)
    · refine Or.inr (Or.inr (AddMonoidHom.ext fun p => ?_))
      simp [dotPairing, squareTotal, Fin.sum_univ_four]

/-! ## Non-vacuity -/

/-- The law of the square keeps the multiply-and-add pairing. -/
example : squareLaw.Keeps (dotPairing (Fin 4) 3) := squareLaw_keeps

/-- The multiply-and-add pairing on the square is perfect. -/
example : (dotPairing (Fin 4) 3).Perfect := dotPairing_perfect (Fin 4) 3

/-- The table `𝟏 = (1, 1, 1, 1)`, which is not `0`, is fixed by `M`. -/
example : squareLaw.M (fun _ => 1) = (fun _ => 1) ∧ (fun _ : Fin 4 => (1 : ZMod 3)) ≠ 0 :=
  ⟨rfl, fun h => absurd (congrFun h 0) (by decide)⟩

end Artform
