import ArtformScores.ReviewRepair.Statements

/-! # Determinant quotients, mean-cut zeros and Platonic incidences -/

namespace Artform.Scores
open Matrix (SpecialLinearGroup)
open LaurentPolynomial

/-- **T14** (the mean cut, including degenerate modes). -/
@[ledger "T14"]
theorem callerCutComplete : Statement.callerCutComplete := by
  refine ⟨callerCut, ?_⟩
  intro K _ _ h gx gy q
  rw [(callerCut K h gx gy q).2.2.2]
  have h2 : (2 : K) ≠ 0 := by norm_num
  have hq : 2 * q - 1 = 0 ↔ q = 1 / 2 := by
    constructor
    · intro e; apply (eq_div_iff h2).mpr; linear_combination e
    · intro e; rw [e]; field_simp; ring
  simp only [mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0),
    sub_eq_zero, hq, h2, or_false]

/-- T1 identifies the elementary group with the determinant kernel over any
ring for which every special-linear law has a score. -/
theorem elementary_eq_det_ker {S : Type} [CommRing S]
    (hs : ∀ A : SpecialLinearGroup (Fin 2) S, ∃ w : Score S, realize w = A) :
    elementary S = (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) S →* Sˣ).ker := by
  apply le_antisymm
  · rw [elementary, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    simp
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hdet : g.1.det = 1 := congrArg Units.val hg
    obtain ⟨w, hw⟩ := hs ⟨g.1, hdet⟩
    have hg' : g = ((realize w : SpecialLinearGroup (Fin 2) S) :
        Matrix.GeneralLinearGroup (Fin 2) S) := by
      rw [hw]
      apply Units.ext
      rfl
    rw [hg']
    clear hg' hw
    induction w with
    | nil => rw [realize_nil, map_one]; exact Subgroup.one_mem _
    | cons s w ih =>
      rw [realize_cons, map_mul]
      exact Subgroup.mul_mem _ ih (Subgroup.subset_closure ⟨s, rfl⟩)

/-- **T2** (the determinant quotient over fields and all positive dials). -/
@[ledger "T2"]
theorem indexGroupComplete : Statement.indexGroupComplete :=
  ⟨indexGroup, fun n hn => ⟨elementary_eq_det_ker (everyLawIsAScoreModulus n hn), det_surjective⟩⟩

/-- **T13** (explicit identifications with the three standard Platonic graphs). -/
@[ledger "T13"]
theorem platonicIncidence : Statement.platonicIncidence := by
  refine ⟨platonicSolids, ?_, ?_, ?_⟩
  · refine ⟨![(0, 1), (1, 0), (1, 1), (1, 2)], ?_, ?_, ?_⟩
    · simp only [Klein.IsPrim]; decide +kernel
    · simp only [Klein.IsPrim, ExistsUnique]; decide +kernel
    · decide +kernel
  · refine ⟨![(0, 1), (2, 1), (1, 0), (1, 2), (1, 1), (1, 3)], ?_, ?_, ?_⟩
    · simp only [Klein.IsPrim]; decide +kernel
    · simp only [Klein.IsPrim, ExistsUnique]; decide +kernel
    · simp only [octahedronAdj]; decide +kernel
  · refine ⟨![(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
      (2, 1), (2, 3), (2, 0), (2, 2), (2, 4)], ?_, ?_, ?_⟩
    · simp only [Klein.IsPrim]; decide +kernel
    · simp only [Klein.IsPrim, ExistsUnique]; decide +kernel
    · simp only [icosahedronAdj, icosahedronEdge]; decide +kernel

/-! ## Non-vacuity -/

/-- A nondegenerate rational mode detects the unique fair caller. -/
example (q : ℚ) :
    cut (q • (splitTick true (1 : ℚ) 1 0 : Matrix (Fin 2) (Fin 2) ℚ) +
      (1 - q) • (splitTick false (1 : ℚ) 1 0 : Matrix (Fin 2) (Fin 2) ℚ)) = 0 ↔ q = 1 / 2 := by
  simpa using callerCutComplete.2 ℚ 1 1 0 q

/-- The nilpotent dial `Z/49`, omitted by the field-only quotient statement. -/
example : elementary (LaurentPolynomial (ZMod 49)) =
    (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial (ZMod 49)) →*
      (LaurentPolynomial (ZMod 49))ˣ).ker :=
  (indexGroupComplete.2 49 (by decide)).1

/-- The icosahedron identification supplies every primitive state, not just a count. -/
example : PrimitiveGraphModel 5 12 icosahedronAdj := platonicIncidence.2.2.2

end Artform.Scores
