import ArtformTextbook.Ch05.Statements.Gauge

/-!
# Five ticks read the outside (Proposition 5.37)

The proof is the book's. One tick, the left turn and then the right, carries
the pose at `v₀` over `e₁` and `e₅` to `v₄`; the next three ticks carry it over
`e₆`, `e₇` and `e₃`, and the fifth over `e₄` home. The pose at `v₁` is carried
to `v₂` as `U_{e₂} g_{v₁}` by the left turn, and back by the right turn as
`U_{e₂}⁻¹ U_{e₂} g_{v₁} = g_{v₁}`.
-/

namespace Artform

namespace Skeleton.TwoSquares

open Vertex Edge

variable {G : Type*} [Group G]

/-- The links stay as they are. -/
private theorem run_fst (U : skeleton.LinkTable G) (g : Vertex → G) :
    ∀ n, (poseLaw.run (U, g) n).1 = U
  | 0 => rfl
  | n + 1 => by
    rw [DetLaw.run, Function.iterate_succ_apply']
    exact run_fst U g n

/-- One tick from the state reached after `n` ticks. -/
private theorem run_succ (U : skeleton.LinkTable G) (g : Vertex → G) (n : ℕ) :
    (poseLaw.run (U, g) (n + 1)).2 =
      poseRight U (poseLeft U (poseLaw.run (U, g) n).2) := by
  rw [DetLaw.run, Function.iterate_succ_apply', ← DetLaw.run]
  change poseRight (poseLaw.run (U, g) n).1 (poseLeft (poseLaw.run (U, g) n).1 _) = _
  rw [run_fst]

end Skeleton.TwoSquares

open Skeleton Skeleton.TwoSquares Skeleton.TwoSquares.Vertex Skeleton.TwoSquares.Edge

/-- **Proposition 5.37** (five ticks read the outside). Under the pose law, five
ticks turn the pose at every corner but `v₁` by the holonomy of the outside,
based at that corner; the pose at `v₁` goes over `e₂` and straight back at
every tick. -/
@[book "prop:five-ticks"]
theorem fiveTicks : Statement.fiveTicks := by
  intro G _ U g
  -- one tick, corner by corner
  have t₀ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₀ = U (along e₄) * (poseLaw.run (U, g) n).2 v₃ :=
    fun n => by rw [run_succ]; rfl
  have t₁ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₁ =
      U (against e₂) * (U (along e₂) * (poseLaw.run (U, g) n).2 v₁) :=
    fun n => by rw [run_succ]; rfl
  have t₂ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₂ = U (along e₇) * (poseLaw.run (U, g) n).2 v₅ :=
    fun n => by rw [run_succ]; rfl
  have t₃ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₃ = U (along e₃) * (poseLaw.run (U, g) n).2 v₂ :=
    fun n => by rw [run_succ]; rfl
  have t₄ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₄ =
      U (along e₅) * (U (along e₁) * (poseLaw.run (U, g) n).2 v₀) :=
    fun n => by rw [run_succ]; rfl
  have t₅ : ∀ n, (poseLaw.run (U, g) (n + 1)).2 v₅ = U (along e₆) * (poseLaw.run (U, g) n).2 v₄ :=
    fun n => by rw [run_succ]; rfl
  have r₀ : ∀ v, (poseLaw.run (U, g) 0).2 v = g v := fun v => rfl
  -- the reversal law on the shared edge
  have hrev : U (against e₂) = (U (along e₂))⁻¹ := U.reversal (along e₂)
  -- the holonomies of the outside, read from each corner
  have o₀ : hol U (outside v₀) = U (along e₄) * (U (along e₃) * (U (along e₇) *
      (U (along e₆) * (U (along e₅) * (U (along e₁) * 1))))) := rfl
  have o₂ : hol U (outside v₂) = U (along e₇) * (U (along e₆) * (U (along e₅) *
      (U (along e₁) * (U (along e₄) * (U (along e₃) * 1))))) := rfl
  have o₃ : hol U (outside v₃) = U (along e₃) * (U (along e₇) * (U (along e₆) *
      (U (along e₅) * (U (along e₁) * (U (along e₄) * 1))))) := rfl
  have o₄ : hol U (outside v₄) = U (along e₅) * (U (along e₁) * (U (along e₄) *
      (U (along e₃) * (U (along e₇) * (U (along e₆) * 1))))) := rfl
  have o₅ : hol U (outside v₅) = U (along e₆) * (U (along e₅) * (U (along e₁) *
      (U (along e₄) * (U (along e₃) * (U (along e₇) * 1))))) := rfl
  have h₀ : (poseLaw.run (U, g) 5).2 v₀ = hol U (outside v₀) * g v₀ := by
    rw [t₀, t₃, t₂, t₅, t₄, r₀, o₀]
    simp only [mul_one, mul_assoc]
  refine ⟨?_, h₀, fun v hv => ?_, fun n => ⟨rfl, ?_, ?_⟩⟩
  · rw [h₀, o₀]
    simp only [mul_one, mul_assoc]
  · cases v with
    | v₀ => exact h₀
    | v₁ => exact absurd rfl hv
    | v₂ =>
      rw [t₂, t₅, t₄, t₀, t₃, r₀, o₂]
      simp only [mul_one, mul_assoc]
    | v₃ =>
      rw [t₃, t₂, t₅, t₄, t₀, r₀, o₃]
      simp only [mul_one, mul_assoc]
    | v₄ =>
      rw [t₄, t₀, t₃, t₂, t₅, r₀, o₄]
      simp only [mul_one, mul_assoc]
    | v₅ =>
      rw [t₅, t₄, t₀, t₃, t₂, r₀, o₅]
      simp only [mul_one, mul_assoc]
  · rw [run_succ]
    rfl
  · induction n with
    | zero => rfl
    | succ n ih => rw [t₁, hrev, inv_mul_cancel_left, ih]

/-! ## Non-vacuity

The run of `fig:pose-run`: the two squares over `C₃`, written as
`Multiplicative (ZMod 3)`, with the links `1, 0, 1, 0, 1, 0, 1` on
`e₁, …, e₇` (`curvedTable`) and every pose `0`. Five ticks turn the pose at
`v₀` by the holonomy round the outside, `F_L + F_R = 2 + 2 = 1`, and leave the
pose at `v₁` where it was. -/

/-- After five ticks the pose at `v₀` is `1`, the holonomy of the outside. -/
example : (poseLaw.run (curvedTable, fun _ => (1 : Multiplicative (ZMod 3))) 5).2 v₀ =
    Multiplicative.ofAdd 1 := by
  rw [(fiveTicks _ curvedTable _).2.1, hol_eq_prod]
  decide

/-- The pose at `v₁` is never turned. -/
example (n : ℕ) :
    (poseLaw.run (curvedTable, fun _ => (1 : Multiplicative (ZMod 3))) n).2 v₁ = 1 :=
  ((fiveTicks _ curvedTable _).2.2.2 n).2.2

end Artform
