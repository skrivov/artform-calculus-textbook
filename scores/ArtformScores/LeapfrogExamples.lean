import ArtformScores.MagicStep
import ArtformScores.LeapfrogPalindromes

/-!
# The class counts of finding 057

The statements of T8 at the dials of the finding's tables. The counts of S3.4 follow from the size
of `⟨-1, ρ⟩`, computed from the explicit `ρ = (1 + q - 2 r) / (1 - q)`, in which `-1` is a power of
`ρ` on every dial of the table. The counts of S3.5 follow at once.
-/

namespace Artform.Scores.Leapfrog

open Matrix (SpecialLinearGroup)

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance fact_prime_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-! ### The curve -/

/-- The curve at `q = 2`, at the point `s = 3` of the line: `x = -4/3` and `λ = -6`. -/
example : (-6 : ℚ) + (-6)⁻¹ = 2 - 2 * (2 - (-4 / 3) - (-4 / 3)⁻¹) := by
  have h := (leapfrogCurve ℚ 2 (by norm_num) (by norm_num)).1 3 (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, -, h3, -⟩ := h
  norm_num at h3 ⊢

/-- Over `x = 1` the line has the two points `s² = q`, here at `q = 4`. -/
example : (4 : ℚ) * (1 - 2) / (2 * (2 - 4)) = 1 := by
  have h := (leapfrogCurve ℚ 4 (by norm_num) (by norm_num)).1 2 (by norm_num) (by norm_num)
    (by norm_num)
  exact h.2.2.2.mpr (by norm_num)

/-! ### The classes -/

/-- A law of the glued classes and a law of the unglued class, of one phase, are not related by
processing. -/
example : ¬ Processed (ungluedLaw (2 : ZMod 7)) (gluedLaw 2 0) := by
  have hq0 : (2 : ZMod 7) ≠ 0 := by decide
  have hq1 : (2 : ZMod 7) ≠ 1 := by decide
  obtain ⟨-, hg, hu, Φ, h1, -, -, -, -, h6, h7⟩ := leapfrogClasses (ZMod 7) 2 hq0 hq0 hq1
  intro hP
  have h := (h1 _ _ hu (hg 0)).mpr hP
  rw [h7, h6 0 (isUnit_rE hq0).unit (by simp)] at h
  exact absurd h (by simp)

/-- The book's tick on the dial `C₇`, at `κ = 1` and `ℓ = 2`, is in the trivial class, and its link
form in the unglued class. -/
example : Processed (companionLaw ((1 : ZMod 7) * 2))
        (realize (([.kick 1, .move 1] : Score (ZMod 7)).map (faceStep 1 2))) ∧
      Processed (ungluedLaw ((1 : ZMod 7) * 2))
        (realize (([.kick 1, .move 1] : Score (ZMod 7)).map (linkStep 1 2))) := by
  obtain ⟨-, h2, -, h4⟩ := leapfrogSchemes (ZMod 7) 1 2 (by decide) (by decide) (by decide)
    [.kick 1, .move 1] (by simp [schemes])
  exact ⟨h2, h4⟩

/-- At a split node, `U` is the group of units of the dial. -/
example : ∃ e : U (4 : ZMod 13) ≃* (ZMod 13)ˣ, ∀ u : U (4 : ZMod 13),
    ((e u : (ZMod 13)ˣ) : ZMod 13) =
      ((u : (Fib (4 : ZMod 13))ˣ) : Fib (4 : ZMod 13)).re +
        ((u : (Fib (4 : ZMod 13))ˣ) : Fib (4 : ZMod 13)).im * 2 := by
  obtain ⟨e, he, -⟩ := leapfrogSplit (ZMod 13) 4 2 (by decide) (by decide) (by decide) (by decide)
  exact ⟨e, he⟩

/-! ### The table of S3.4 -/

/-- The dial `C_7` at `κλ = 2`: `1` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (2 : ZMod 7)))) = 1 + 1 := by
  have hq0 : (2 : ZMod 7) ≠ 0 := by decide
  have hq1 : (2 : ZMod 7) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 7) 2 (by decide) hq0 hq1
  have hs : IsSquare (2 : ZMod 7) := ⟨3, by decide⟩
  have hU := h.2.1 hs
  have hH : Nat.card (gluing (2 : ZMod 7)) = 6 :=
    card_gluing_of_rho hq0 hq1 (⟨4, 2⟩ : Fib (2 : ZMod 7)) (by decide +kernel) 3 6
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_13` at `κλ = 4`: `2` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (4 : ZMod 13)))) = 2 + 1 := by
  have hq0 : (4 : ZMod 13) ≠ 0 := by decide
  have hq1 : (4 : ZMod 13) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 13) 4 (by decide) hq0 hq1
  have hs : IsSquare (4 : ZMod 13) := ⟨2, by decide⟩
  have hU := h.2.1 hs
  have hH : Nat.card (gluing (4 : ZMod 13)) = 6 :=
    card_gluing_of_rho hq0 hq1 (⟨7, 5⟩ : Fib (4 : ZMod 13)) (by decide +kernel) 3 6
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_13` at `κλ = 12`: `3` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (12 : ZMod 13)))) = 3 + 1 := by
  have hq0 : (12 : ZMod 13) ≠ 0 := by decide
  have hq1 : (12 : ZMod 13) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 13) 12 (by decide) hq0 hq1
  have hs : IsSquare (12 : ZMod 13) := ⟨5, by decide⟩
  have hU := h.2.1 hs
  have hH : Nat.card (gluing (12 : ZMod 13)) = 4 :=
    card_gluing_of_rho hq0 hq1 (⟨0, 12⟩ : Fib (12 : ZMod 13)) (by decide +kernel) 2 4
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_17` at `κλ = 16`: `4` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (16 : ZMod 17)))) = 4 + 1 := by
  have hq0 : (16 : ZMod 17) ≠ 0 := by decide
  have hq1 : (16 : ZMod 17) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 17) 16 (by decide) hq0 hq1
  have hs : IsSquare (16 : ZMod 17) := ⟨4, by decide⟩
  have hU := h.2.1 hs
  have hH : Nat.card (gluing (16 : ZMod 17)) = 4 :=
    card_gluing_of_rho hq0 hq1 (⟨0, 16⟩ : Fib (16 : ZMod 17)) (by decide +kernel) 2 4
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_19` at `κλ = 6`: `3` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (6 : ZMod 19)))) = 3 + 1 := by
  have hq0 : (6 : ZMod 19) ≠ 0 := by decide
  have hq1 : (6 : ZMod 19) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 19) 6 (by decide) hq0 hq1
  have hs : IsSquare (6 : ZMod 19) := ⟨5, by decide⟩
  have hU := h.2.1 hs
  have hH : Nat.card (gluing (6 : ZMod 19)) = 6 :=
    card_gluing_of_rho hq0 hq1 (⟨10, 8⟩ : Fib (6 : ZMod 19)) (by decide +kernel) 3 6
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_7` at `κλ = 3`: `1` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (3 : ZMod 7)))) = 1 + 1 := by
  have hq0 : (3 : ZMod 7) ≠ 0 := by decide
  have hq1 : (3 : ZMod 7) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 7) 3 (by decide) hq0 hq1
  have hs : ¬ IsSquare (3 : ZMod 7) := by
    rintro ⟨r, hr⟩
    revert r
    decide
  have hU := h.2.2.1 hs
  have hH : Nat.card (gluing (3 : ZMod 7)) = 8 :=
    card_gluing_of_rho hq0 hq1 (⟨5, 1⟩ : Fib (3 : ZMod 7)) (by decide +kernel) 4 8
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_11` at `κλ = 10`: `3` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (10 : ZMod 11)))) = 3 + 1 := by
  have hq0 : (10 : ZMod 11) ≠ 0 := by decide
  have hq1 : (10 : ZMod 11) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 11) 10 (by decide) hq0 hq1
  have hs : ¬ IsSquare (10 : ZMod 11) := by
    rintro ⟨r, hr⟩
    revert r
    decide
  have hU := h.2.2.1 hs
  have hH : Nat.card (gluing (10 : ZMod 11)) = 4 :=
    card_gluing_of_rho hq0 hq1 (⟨0, 10⟩ : Fib (10 : ZMod 11)) (by decide +kernel) 2 4
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_17` at `κλ = 11`: `3` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (11 : ZMod 17)))) = 3 + 1 := by
  have hq0 : (11 : ZMod 17) ≠ 0 := by decide
  have hq1 : (11 : ZMod 17) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 17) 11 (by decide) hq0 hq1
  have hs : ¬ IsSquare (11 : ZMod 17) := by
    rintro ⟨r, hr⟩
    revert r
    decide
  have hU := h.2.2.1 hs
  have hH : Nat.card (gluing (11 : ZMod 17)) = 6 :=
    card_gluing_of_rho hq0 hq1 (⟨9, 7⟩ : Fib (11 : ZMod 17)) (by decide +kernel) 3 6
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-- The dial `C_19` at `κλ = 18`: `5` glued classes and the unglued one. -/
example : Nat.card (Quotient (processingSetoid (phaseT (18 : ZMod 19)))) = 5 + 1 := by
  have hq0 : (18 : ZMod 19) ≠ 0 := by decide
  have hq1 : (18 : ZMod 19) ≠ 1 := by decide
  have h := leapfrogCount (ZMod 19) 18 (by decide) hq0 hq1
  have hs : ¬ IsSquare (18 : ZMod 19) := by
    rintro ⟨r, hr⟩
    revert r
    decide
  have hU := h.2.2.1 hs
  have hH : Nat.card (gluing (18 : ZMod 19)) = 4 :=
    card_gluing_of_rho hq0 hq1 (⟨0, 18⟩ : Fib (18 : ZMod 19)) (by decide +kernel) 2 4
      (by decide +kernel) (by decide +kernel) (by norm_num)
      (fun m h0 h1 => by interval_cases m <;> decide +kernel)
  rw [h.1, hU, hH, Nat.card_zmod]

/-! ### The palindromes -/

/-- On `C₇` at `κλ = 2`, the companion tick is processed from a palindrome. -/
example : ∃ L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial (ZMod 7)),
    (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 7))) 0 0 =
      (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 7))) 1 1 ∧
    Processed L' (companionLaw (2 : ZMod 7)) :=
  (leapfrogPalindromes (ZMod 7) 2 (by decide) (by decide) (by decide) _
    phase_companionLaw).mpr (Or.inr (Or.inl ⟨1, by simp⟩))

/-- On `C₁₃` at `κλ = 4`, `1 - q = 6²`, and the class of `κ` holds a palindrome. -/
example : ∃ L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial (ZMod 13)),
    (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 13))) 0 0 =
      (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 13))) 1 1 ∧
    Processed L' (gluedLaw (4 : ZMod 13) (-(1 + 6))) :=
  (leapfrogPalindromes (ZMod 13) 4 (by decide) (by decide) (by decide) _
    (phase_gluedLaw _)).mpr (Or.inr (Or.inr ⟨6, by decide, 1, by simp⟩))

/-! ### The magic step -/

/-- The split movers are not in the trivial class. -/
example : ¬ Processed (magicLaw (0 : LaurentPolynomial (ZMod 5))) (magicLaw 1) := by
  obtain ⟨Φ, h1, h2, -, -, -, -⟩ := magicClasses (ZMod 5) (by decide)
  intro hP
  have h := (h1 _ _ (h2 0).1 (h2 1).1).mpr hP
  rw [(h2 0).2, (h2 1).2, map_zero, map_zero, map_one, map_one, ofPair_zero,
    ofPair_inl one_ne_zero one_ne_zero] at h
  exact absurd h (by simp)

/-- The schemes at the magic step on the dial `C₅`, at `κ = 2` and `ℓ = 3`. -/
example : (realize (([.kick 1, .move 1] : Score (ZMod 5)).map (linkStep 2 3)) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 5))).map (atPi (ZMod 5)) ≠ -1 := by
  exact ((magicSchemes (ZMod 5) 2 3 (by decide) (by decide)).1 [.kick 1, .move 1]
    (by simp [schemes])).2.2.2.2

/-- The dial `C_5` at the magic step: `5` classes. -/
example : Nat.card (Quotient (processingSetoid (phaseT (1 : ZMod 5)))) = 5 := by
  rw [magicCount (ZMod 5) (by decide), Nat.card_zmod]

/-- The dial `C_7` at the magic step: `6` classes. -/
example : Nat.card (Quotient (processingSetoid (phaseT (1 : ZMod 7)))) = 6 := by
  rw [magicCount (ZMod 7) (by decide), Nat.card_zmod]

/-- The dial `C_11` at the magic step: `8` classes. -/
example : Nat.card (Quotient (processingSetoid (phaseT (1 : ZMod 11)))) = 8 := by
  rw [magicCount (ZMod 11) (by decide), Nat.card_zmod]

/-- The dial `C_13` at the magic step: `9` classes. -/
example : Nat.card (Quotient (processingSetoid (phaseT (1 : ZMod 13)))) = 9 := by
  rw [magicCount (ZMod 13) (by decide), Nat.card_zmod]

end Artform.Scores.Leapfrog
