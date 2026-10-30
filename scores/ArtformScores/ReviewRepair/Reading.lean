import ArtformScores.ReviewRepair.Statements

/-! # Complete observational readings and their closed forms -/

namespace Artform.Scores
open Matrix (SpecialLinearGroup)

/-- The scalar reading obeys the characteristic recurrence. -/
theorem reading_recurrence {S : Type*} [CommRing S]
    (A : SpecialLinearGroup (Fin 2) S) (n : ℕ) :
    (A ^ (n + 2)).1 0 0 = phase A * (A ^ (n + 1)).1 0 0 - (A ^ n).1 0 0 := by
  simpa [Matrix.SpecialLinearGroup.coe_pow, phase] using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M 0 0) (pow_add_two A n)

theorem recurrence_unique {S : Type*} [CommRing S] (t : S) (f g : ℕ → S)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ n, f (n + 2) = t * f (n + 1) - f n)
    (hg : ∀ n, g (n + 2) = t * g (n + 1) - g n) : ∀ n, f n = g n := by
  suffices ∀ n, f n = g n ∧ f (n + 1) = g (n + 1) from fun n => (this n).1
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih => exact ⟨ih.2, by rw [hf, hg, ih.1, ih.2]⟩

/-- All outputs from a unit initial flux determine both phase and reading.
Only ticks 1, 2 and 3 are needed; this works over every commutative ring. -/
theorem reading_complete {S : Type} [CommRing S] (A B : SpecialLinearGroup (Fin 2) S) :
    (phase A = phase B ∧ reading A = reading B) ↔
      ∀ n : ℕ, (A ^ n).1 0 0 = (B ^ n).1 0 0 := by
  constructor
  · rintro ⟨ht, ha⟩ n
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      readingDetermines S A B ht ha n 1
  · intro h
    have h1 : reading A = reading B := by simpa [reading] using h 1
    have h2 := h 2
    have h3 := h 3
    rw [reading_recurrence A 0, reading_recurrence B 0] at h2
    have ha : A.1 0 0 = B.1 0 0 := h1
    simp only [zero_add, pow_one, pow_zero, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, ha] at h2
    rw [reading_recurrence A 1, reading_recurrence B 1] at h3
    rw [reading_recurrence A 0, reading_recurrence B 0] at h3
    simp only [zero_add, pow_one, pow_zero, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, ha] at h3
    refine ⟨?_, h1⟩
    linear_combination (phase A + phase B) * h2 - h3

/-- The oscillatory closed form, with the necessary nonzero sine stated explicitly. -/
theorem reading_trigonometric (A : SpecialLinearGroup (Fin 2) ℝ) (θ : ℝ)
    (ht : phase A = 2 * Real.cos θ) (hs : Real.sin θ ≠ 0) (n : ℕ) :
    (A ^ n).1 0 0 = Real.cos (n * θ) +
      ((A.1 0 0 - A.1 1 1) / 2) * Real.sin (n * θ) / Real.sin θ := by
  let c := (A.1 0 0 - A.1 1 1) / 2 / Real.sin θ
  have htrace : A.1 0 0 + A.1 1 1 = 2 * Real.cos θ := by
    simpa [phase, Matrix.trace_fin_two] using ht
  have h1 : A.1 0 0 = Real.cos θ + c * Real.sin θ := by
    dsimp [c]
    field_simp [hs]
    linear_combination htrace
  have hrec : ∀ k : ℕ,
      Real.cos ((k + 2 : ℕ) * θ) + c * Real.sin ((k + 2 : ℕ) * θ) =
      (2 * Real.cos θ) * (Real.cos ((k + 1 : ℕ) * θ) + c * Real.sin ((k + 1 : ℕ) * θ)) -
        (Real.cos (k * θ) + c * Real.sin (k * θ)) := by
    intro k
    have e2 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e0 : (k : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e2, e0, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub]
    ring
  have h := recurrence_unique (phase A) (fun k => (A ^ k).1 0 0)
    (fun k => Real.cos (k * θ) + c * Real.sin (k * θ))
    (by simp) (by simpa using h1) (reading_recurrence A) (by intro k; rw [ht]; exact hrec k) n
  simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The repeated-root formulas at phase `2` and `-2`, over any commutative ring. -/
theorem reading_repeated_root {S : Type} [CommRing S] (A : SpecialLinearGroup (Fin 2) S)
    (ε : S) (he : ε * ε = 1) (ht : phase A = 2 * ε) (n : ℕ) :
    (A ^ n).1 0 0 = ε ^ n * (1 + (n : S) * (ε * reading A - 1)) := by
  apply recurrence_unique (phase A) (fun k => (A ^ k).1 0 0)
    (fun k => ε ^ k * (1 + (k : S) * (ε * reading A - 1)))
    (by simp) ?_ (reading_recurrence A) ?_ n
  · simp only [pow_one, Nat.cast_one]
    dsimp [reading]
    linear_combination -(A.1 0 0) * he
  · intro k
    rw [ht, pow_add ε k 2, pow_succ ε k]
    simp only [pow_two, he, mul_one]
    push_cast
    linear_combination -2 * ε ^ k *
      (1 + ((k : S) + 1) * (ε * reading A - 1)) * he

/-- **T12** (the complete invariant, closed form and repeated-root cases). -/
@[ledger "T12"]
theorem readingComplete : Statement.readingComplete :=
  ⟨readingDetermines, fun _ _ => reading_complete, reading_trigonometric,
    fun _ _ => reading_repeated_root⟩

/-! ## Non-vacuity -/

/-- The running pull 2 is the oscillatory quarter turn. -/
example : phase (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (tick 2)) =
    2 * Real.cos (Real.pi / 2) ∧ Real.sin (Real.pi / 2) ≠ 0 := by
  simp [phase, tick_mat, Matrix.trace_fin_two]

/-- The running pull 4 uses the repeated eigenvalue `-1`, rather than division by zero. -/
example (n : ℕ) :
    (tick 4 ^ n).1 0 0 = (-1 : ℤ) ^ n * (1 + (n : ℤ) * 2) := by
  have h := reading_repeated_root (tick 4) (-1) (by norm_num)
    (by simp [phase, tick_mat, Matrix.trace_fin_two]) n
  simpa [reading, tick_mat] using h

end Artform.Scores
