import ArtformScores.Caller

/-!
# Callers' rules, one cue and the duet

The ledger's T14 (finding 080, Theorems S8.5 and S8.6) and T16 (the book's `06-controller`).
- **The rule decides the cancellation.** The share of the patterns that a rule sends to `xy` is its
  weight in the mean tick.
- **One cue.** A placed kick is a stencil exactly when its set of cells is invariant.
- **The duet.** Two choices agree every time, and vary, only through a cause they share.
-/

namespace Artform.Scores

/-! ## T14: the caller's rules and the shared cue; T16: the duet -/

section Rules

theorem shares : share turnOn11 = 1 / 4 ∧ share turnOnA = 1 / 2 ∧ share turnOnNe = 1 / 2 := by
  have h1 : (Finset.univ.filter fun p => turnOn11 p = true).card = 1 := by decide
  have h2 : (Finset.univ.filter fun p => turnOnA p = true).card = 2 := by decide
  have h3 : (Finset.univ.filter fun p => turnOnNe p = true).card = 2 := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp only [share, h1, h2, h3] <;> norm_num

end Rules

section Cue

variable {Λ R : Type*} [AddCommGroup Λ] [CommRing R]

open scoped Classical in
/-- A mask commutes with a shift exactly when the set is invariant. -/
theorem mask_comm_iff [Nontrivial R] (X : Set Λ) (w : Λ) :
    (∀ u : Λ → R, shiftField w (maskField X u) = maskField X (shiftField w u)) ↔
      ∀ z, z + w ∈ X ↔ z ∈ X := by
  constructor
  · intro h z
    have hz := congrFun (h fun _ => 1) z
    simp only [shiftField, maskField] at hz
    by_cases h1 : z + w ∈ X <;> by_cases h2 : z ∈ X <;> simp [h1, h2] at hz ⊢
  · intro h u
    ext z
    simp only [shiftField, maskField, h z]

/-- A mask commutes with all the shifts exactly when the set is empty or everything. -/
theorem mask_comm_all_iff [Nontrivial R] (X : Set Λ) :
    (∀ (w : Λ) (u : Λ → R), shiftField w (maskField X u) = maskField X (shiftField w u)) ↔
      X = ∅ ∨ X = Set.univ := by
  constructor
  · intro h
    by_cases hX : X = ∅
    · exact Or.inl hX
    · right
      obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hX
      ext z
      simp only [Set.mem_univ, iff_true]
      have := (mask_comm_iff (R := R) X (z - z₀)).mp (h _) z₀
      rw [show z₀ + (z - z₀) = z by abel] at this
      exact this.mpr hz₀
  · rintro (rfl | rfl) w u
    · ext z
      simp [shiftField, maskField]
    · ext z
      simp [shiftField, maskField]

end Cue

section Duet

/-- One cue read by both dancers: they never disagree, and both orbit on one pattern of four. -/
theorem one_cue : (Finset.univ.filter fun p : Bool × Bool => turnOn11 p ≠ turnOn11 p).card = 0 ∧
    (Finset.univ.filter fun p : Bool × Bool => turnOn11 p = true ∧ turnOn11 p = true).card = 1 := by
  decide

/-- Two coins: the dancers disagree on `6` of the `16` patterns (`3/8`), and both orbit on `1`
(`1/16`). -/
theorem two_coins :
    (Finset.univ.filter fun p : (Bool × Bool) × (Bool × Bool) =>
      turnOn11 p.1 ≠ turnOn11 p.2).card = 6 ∧
    (Finset.univ.filter fun p : (Bool × Bool) × (Bool × Bool) =>
      turnOn11 p.1 = true ∧ turnOn11 p.2 = true).card = 1 := by
  decide

/-- Two choices that agree every time, from independent sources, are fixed: they can agree and vary
only through a cause they share. -/
theorem shared_cause {Ω₁ Ω₂ α : Type*} [Nonempty Ω₁] [Nonempty Ω₂] (f : Ω₁ → α) (g : Ω₂ → α)
    (h : ∀ ω₁ ω₂, f ω₁ = g ω₂) : ∃ a, (∀ ω, f ω = a) ∧ ∀ ω, g ω = a := by
  obtain ⟨ω₂⟩ := ‹Nonempty Ω₂›
  obtain ⟨ω₁⟩ := ‹Nonempty Ω₁›
  exact ⟨g ω₂, fun ω => h ω ω₂, fun ω => (h ω₁ ω).symm.trans (h ω₁ ω₂)⟩

end Duet

/-- **T14** (the caller's rule). -/
@[ledger "T14"]
theorem callerRules : Statement.callerRules := by
  obtain ⟨h1, h2, h3⟩ := shares
  refine ⟨h1, h2, h3, fun K _ _ h gx gy => ?_⟩
  have hc : ∀ q : K, cut (q • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
      (1 - q) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) =
      (2 * q - 1) * (h ^ 2 * (gx - gy) / 2) := fun q => (callerCut K h gx gy q).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, h1]
    push_cast
    ring
  · rw [hc, h2]
    push_cast
    ring
  · rw [hc, h3]
    push_cast
    ring

/-- **T14** (one cue). -/
@[ledger "T14"]
theorem oneCue : Statement.oneCue := fun _ R _ _ _ X =>
  ⟨fun w => mask_comm_iff (R := R) X w, mask_comm_all_iff (R := R) X⟩

/-- **T16** (the duet). -/
@[ledger "T16"]
theorem duet : Statement.duet := by
  obtain ⟨h1, h2⟩ := one_cue
  obtain ⟨h3, h4⟩ := two_coins
  exact ⟨h1, h2, h3, h4, fun _ _ _ _ _ f g h => shared_cause f g h⟩

/-! ## Non-vacuity

On a checkerboard of `ℤ²`, written as `ℤ` for the sum of the coordinates mod `2`: the even cells are
invariant under the shift by `2` and not under the shift by `1`.
-/

example : (∀ z : ℤ, z + 2 ∈ {n : ℤ | Even n} ↔ z ∈ {n : ℤ | Even n}) ∧
    ¬ ∀ z : ℤ, z + 1 ∈ {n : ℤ | Even n} ↔ z ∈ {n : ℤ | Even n} := by
  constructor
  · intro z
    simp only [Set.mem_ofPred_eq, Int.even_add]
    simp
  · intro h
    have := h 0
    simp at this

end Artform.Scores
