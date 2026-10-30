import ArtformScores

/-!
# Independent checks of the nine repaired submissions

These are review witnesses and composition checks, not replacement ledger
statements. Run with `lake env lean scores/review/RepairJudgeChecks.lean`.
-/

namespace Artform.Scores.RepairJudge

/-- The corrected score order gives the intended diagonal, over the same
rationals that separated the old score from its intended law. -/
example :
    let u : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩
    (realize (balancedScore u) : Matrix (Fin 2) (Fin 2) ℚ) = !![2, 0; 0, 1 / 2] := by
  dsimp
  rw [(balancedRule ℚ _ 1).2.2, balanced_mat]
  rfl

/-- The repaired source bracket is the positive time-order commutator. -/
example :
    realizeC [(⟨1, 2, -1⟩ : ChanStep 3 ℚ), ⟨0, 1, -1⟩, ⟨1, 2, 1⟩, ⟨0, 1, 1⟩] =
      (⟨0, 2, 1⟩ : ChanStep 3 ℚ).mat := by
  simpa only [mul_one] using ((steinbergRules' ℚ 3 0 1 2 0 1 1).2.2.2
    (by decide) (by decide) (by decide)).2.1

/-- Zero readings need tick 3 to separate the phases; ticks 1 and 2 alone
agree for these two genuine determinant-one laws. -/
example :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℚ :=
      ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩
    let B : Matrix.SpecialLinearGroup (Fin 2) ℚ :=
      ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two]⟩
    reading A = 0 ∧ reading B = 0 ∧ (A ^ 2).1 0 0 = (B ^ 2).1 0 0 ∧
      (A ^ 3).1 0 0 ≠ (B ^ 3).1 0 0 := by
  decide +kernel

/-- Fairness is necessary on a nondegenerate mode. -/
example (q : ℚ) :
    cut (q • (splitTick true (2 : ℚ) 3 1 : Matrix (Fin 2) (Fin 2) ℚ) +
      (1 - q) • (splitTick false (2 : ℚ) 3 1 : Matrix (Fin 2) (Fin 2) ℚ)) = 0 ↔
      q = 1 / 2 := by
  simpa using callerCutComplete.2 ℚ 2 3 1 q

/-- The all-dials quotient includes both the zero ring and a nonreduced dial. -/
example :
    elementary (LaurentPolynomial (ZMod 1)) =
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial (ZMod 1)) →*
        (LaurentPolynomial (ZMod 1))ˣ).ker ∧
    elementary (LaurentPolynomial (ZMod 49)) =
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial (ZMod 49)) →*
        (LaurentPolynomial (ZMod 49))ˣ).ker :=
  ⟨(indexGroupComplete.2 1 (by decide)).1, (indexGroupComplete.2 49 (by decide)).1⟩

/-- Adjacency with either determinant sign gives a face; the sign quotient
does not leave an orientation gap in the Platonic graph identifications. -/
theorem triangle_of_pm {n : ℕ} (u v w : Klein.State n)
    (huv : Klein.det2 u v = 1 ∨ Klein.det2 u v = -1)
    (huw : Klein.det2 u w = 1 ∨ Klein.det2 u w = -1)
    (hvw : Klein.det2 v w = 1 ∨ Klein.det2 v w = -1) :
    ({Klein.cls u, Klein.cls v, Klein.cls w} : Set (Klein.Cls n)) ∈ Klein.faces n := by
  rcases huv with h | h
  · exact Klein.triangle_is_face h huw hvw
  · have h' : Klein.det2 (-u) v = 1 := by rw [Klein.det2_neg_left, h]; ring
    have hw' : Klein.det2 (-u) w = 1 ∨ Klein.det2 (-u) w = -1 := by
      rw [Klein.det2_neg_left]
      rcases huw with hw | hw
      · right; rw [hw]
      · left; rw [hw]; ring
    simpa only [Klein.cls_neg] using Klein.triangle_is_face h' hw' hvw

/-- The graph models therefore preserve triangular faces, not only edges. -/
example {n N : ℕ} {adj : Fin N → Fin N → Prop} (hm : PrimitiveGraphModel n N adj) :
    ∃ v : Fin N → Klein.State n, (∀ i, Klein.IsPrim (v i)) ∧
      ∀ i j k, adj i j → adj i k → adj j k →
        ({Klein.cls (v i), Klein.cls (v j), Klein.cls (v k)} : Set (Klein.Cls n)) ∈
          Klein.faces n := by
  obtain ⟨v, hp, _, he⟩ := hm
  exact ⟨v, hp, fun i j k hij hik hjk => triangle_of_pm _ _ _
    ((he i j).mp hij) ((he i k).mp hik) ((he j k).mp hjk)⟩

/-- The normalization comparison really implies equality of ideal classes:
the principal factor is nonzero under the theorem's injective base map. -/
example (F : Type) [Field F] (κ ℓ : F) (w : Score F)
    (hk : totalKick w * κ ≠ 0) (B : Type) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (ι : LaurentPolynomial F →+* B) (hi : Function.Injective ι)
    (lam : B)
    (hr : lam * lam - ι (phase (realize (w.map (faceStep κ ℓ)))) * lam + 1 = 0) :
    SameClass
      (Ideal.span {ι ((realize (w.map (linkStep κ ℓ))).1 1 0),
        lam - ι ((realize (w.map (linkStep κ ℓ))).1 0 0)})
      (Ideal.span {ι ((realize (w.map (faceStep κ ℓ))).1 1 0),
        lam - ι ((realize (w.map (faceStep κ ℓ))).1 0 0)}) := by
  have hD : diffDs F ≠ 0 := by
    intro h
    have hT : (LaurentPolynomial.T (-1) : LaurentPolynomial F) = LaurentPolynomial.T 0 := by
      rw [LaurentPolynomial.T_zero]
      exact (sub_eq_zero.mp h).symm
    have h0 := congrArg (fun f : LaurentPolynomial F => f.coeff 0) hT
    simp [LaurentPolynomial.T_apply] at h0
  have hiD : ι (diffDs F) ≠ 0 := by
    intro h
    exact hD (hi (h.trans (map_zero ι).symm))
  refine ⟨1, by simp, ι (diffDs F), mem_nonZeroDivisors_iff_ne_zero.mpr hiD, ?_⟩
  simpa using faceAndLinkNormalization.2 F κ ℓ w hk B ι hi lam hr

/-- A split node has two distinct branches over a small odd field. -/
example : (2 : ZMod 7) * 2 = 4 ∧ (2 : ZMod 7) ≠ -2 ∧
    ∀ u v : ZMod 7, v ^ 2 - 4 * u ^ 2 = (v - 2 * u) * (v + 2 * u) := by
  refine ⟨by decide, by decide, ?_⟩
  intro u v
  ring

end Artform.Scores.RepairJudge
