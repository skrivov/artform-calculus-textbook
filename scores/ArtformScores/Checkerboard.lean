import ArtformScores.Blocking

/-!
# The checkerboard

R6 of the algebra of scores on the ledger's own setting: blocking by a sublattice, and
red-black on the checkerboard of `ℤ²` with the book's face form.
- **The cosets.** For a sublattice `Λ′ ⊂ Λ` and coset representatives `t_i`, the shift `xᵗ`
  times a stencil `f` of `Λ′` lives on the coset of `t`: its coefficient at `a` is `f(a - t)`
  when `a - t ∈ Λ′`, else `0`. So the shifts `x^(t_i)` are independent over `R[Λ′]`, and they
  span, since a monomial `xᵃ` is `x^(a - t_i)` times `x^(t_i)` for the representative of `a`.
- **The checkerboard.** The representatives `0` and `e₁` give the basis `1, x`. The square
  `x² = u v` is a unit of the checkerboard's stencils, so red-black's hypotheses hold.
- **The face form.** `g = 4 - x - 1/x - y - 1/y = 4 - x (1 + 1/u + 1/v + 1/(u v))`, so its
  black part is `-(1 + 1/u + 1/v + 1/(u v))`, whose constant term is `-1`. By R6's red-black
  obstruction, red-black with the half move `M(-λg/2)` is the blocking of no law of the plane
  when `κ² λ ≠ 0`.
-/

namespace Artform.Scores

open AddMonoidAlgebra

section Cosets

variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] (Λ' : AddSubgroup Λ)

theorem algebraMap_sublattice (f : AddMonoidAlgebra R Λ') :
    algebraMap (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) f = mapDomain Λ'.subtype f := rfl

/-- The coefficient of `f xᵗ`, `f` a stencil of the sublattice, at a cell `a` of the coset of
`t`. -/
theorem coeff_smul_single_of_mem (f : AddMonoidAlgebra R Λ') {t a : Λ} (h : a - t ∈ Λ') :
    (f • single t (1 : R)).coeff a = f.coeff ⟨a - t, h⟩ := by
  rw [Algebra.smul_def, algebraMap_sublattice, coeff_mul_single_apply, mul_one, coeff_mapDomain,
    ← sub_eq_add_neg]
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective f.coeff ⟨a - t, h⟩

/-- The coefficient of `f xᵗ` at a cell outside the coset of `t` is `0`. -/
theorem coeff_smul_single_of_not_mem (f : AddMonoidAlgebra R Λ') {t a : Λ} (h : a - t ∉ Λ') :
    (f • single t (1 : R)).coeff a = 0 := by
  rw [Algebra.smul_def, algebraMap_sublattice, coeff_mul_single_apply, mul_one, coeff_mapDomain,
    ← sub_eq_add_neg]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨c, hc⟩
  exact h (hc ▸ c.2)

/-- Shifts by coset representatives are independent over the sublattice's stencils. -/
theorem cosets_linearIndependent {m : ℕ} (t : Fin m → Λ) (ht : ∀ a : Λ, ∃! i, a - t i ∈ Λ') :
    LinearIndependent (AddMonoidAlgebra R Λ') fun i => single (t i) (1 : R) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  rw [← coeff_inj]
  ext ⟨h, hh⟩
  have e := congrArg (fun z : AddMonoidAlgebra R Λ => z.coeff (h + t j)) hc
  simp only [coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply, coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at e
  rw [Finset.sum_eq_single j] at e
  · rw [coeff_smul_single_of_mem Λ' (c j) (by simpa using hh)] at e
    simpa using e
  · intro i _ hij
    refine coeff_smul_single_of_not_mem Λ' (c i) fun hmem => hij ?_
    refine (ht (t j)).unique ?_ (by simp)
    have e2 : t j - t i = h + t j - t i - h := by abel
    rw [e2]
    exact Λ'.sub_mem hmem hh
  · simp

/-- Shifts by coset representatives span the stencils over the sublattice's stencils. -/
theorem cosets_span {m : ℕ} (t : Fin m → Λ) (ht : ∀ a : Λ, ∃! i, a - t i ∈ Λ') :
    ⊤ ≤ Submodule.span (AddMonoidAlgebra R Λ') (Set.range fun i => single (t i) (1 : R)) := by
  rintro z -
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single a r =>
    obtain ⟨i, hi, -⟩ := ht a
    have e : single a r = (single (⟨a - t i, hi⟩ : Λ') r : AddMonoidAlgebra R Λ') •
        single (t i) (1 : R) := by
      rw [Algebra.smul_def, algebraMap_sublattice, mapDomain_single, single_mul_single, mul_one]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The coset basis of the stencils over a sublattice. -/
noncomputable def cosetBasis {m : ℕ} (t : Fin m → Λ) (ht : ∀ a : Λ, ∃! i, a - t i ∈ Λ') :
    Module.Basis (Fin m) (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) :=
  Module.Basis.mk (cosets_linearIndependent Λ' t ht) (cosets_span Λ' t ht)

theorem cosetBasis_apply {m : ℕ} (t : Fin m → Λ) (ht : ∀ a : Λ, ∃! i, a - t i ∈ Λ') (i : Fin m) :
    cosetBasis (R := R) Λ' t ht i = single (t i) 1 :=
  Module.Basis.mk_apply _ _ _

end Cosets

section Checkerboard

variable (R : Type*) [CommRing R]

/-- The checkerboard's coset representatives: `0` (red) and `e₁` (black). -/
def checkerReps : Fin 2 → ℤ × ℤ := ![0, (1, 0)]

theorem checkerReps_unique (a : ℤ × ℤ) : ∃! i, a - checkerReps i ∈ checkerboard := by
  obtain ⟨p, q⟩ := a
  have mem : ∀ c : ℤ × ℤ, c ∈ checkerboard ↔ (c.1 + c.2) % 2 = 0 := fun c => Iff.rfl
  by_cases h : (p + q) % 2 = 0
  · refine ⟨0, by simp [checkerReps, mem, h], fun j hj => ?_⟩
    fin_cases j
    · rfl
    · simp [checkerReps, mem] at hj
      omega
  · refine ⟨1, by simp [checkerReps, mem]; omega, fun j hj => ?_⟩
    fin_cases j
    · simp [checkerReps, mem] at hj
      omega
    · rfl

/-- The checkerboard basis `1, x` of `R[ℤ²]` over `R[Λ′]`. -/
noncomputable def checkerBasis :
    Module.Basis (Fin 2) (AddMonoidAlgebra R checkerboard) (AddMonoidAlgebra R (ℤ × ℤ)) :=
  cosetBasis checkerboard checkerReps checkerReps_unique

theorem checkerBasis_zero : checkerBasis R 0 = 1 := by
  rw [checkerBasis, cosetBasis_apply]
  rfl

theorem checkerBasis_one : checkerBasis R 1 = shiftX R := by
  rw [checkerBasis, cosetBasis_apply]
  rfl

/-- `x² = u v`. -/
theorem shiftX_sq : shiftX R * shiftX R =
    algebraMap (AddMonoidAlgebra R checkerboard) (AddMonoidAlgebra R (ℤ × ℤ))
      (single (cellU + cellV) 1) := by
  rw [shiftX, single_mul_single, mul_one, algebraMap_sublattice, mapDomain_single]
  rfl

theorem isUnit_single_cell (c : checkerboard) : IsUnit (single c (1 : R)) :=
  ⟨⟨single c 1, single (-c) 1, by rw [single_mul_single, mul_one, add_neg_cancel]; rfl,
    by rw [single_mul_single, mul_one, neg_add_cancel]; rfl⟩, rfl⟩

theorem algebraMap_single_cell (c : checkerboard) (r : R) :
    algebraMap (AddMonoidAlgebra R checkerboard) (AddMonoidAlgebra R (ℤ × ℤ)) (single c r) =
      single (c : ℤ × ℤ) r := by
  rw [algebraMap_sublattice, mapDomain_single]
  rfl

/-- The face form's red and black parts. -/
theorem faceStencil_eq : faceStencil R =
    (4 : AddMonoidAlgebra R checkerboard) • checkerBasis R 0 +
      (-(1 + single (-cellU) 1 + single (-cellV) 1 + single (-(cellU + cellV)) 1) :
        AddMonoidAlgebra R checkerboard) • checkerBasis R 1 := by
  rw [checkerBasis_zero, checkerBasis_one, Algebra.smul_def, Algebra.smul_def, mul_one,
    map_ofNat]
  simp only [map_neg, map_add, map_one, algebraMap_single_cell, shiftX, neg_mul, add_mul,
    one_mul, single_mul_single, mul_one]
  have e1 : ((-cellU : checkerboard) : ℤ × ℤ) + (1, 0) = (0, -1) := rfl
  have e2 : ((-cellV : checkerboard) : ℤ × ℤ) + (1, 0) = (0, 1) := rfl
  have e3 : ((-(cellU + cellV) : checkerboard) : ℤ × ℤ) + (1, 0) = (-1, 0) := rfl
  rw [e1, e2, e3, faceStencil]
  abel

/-- The face form's black part, `-(1 + 1/u + 1/v + 1/(u v))`. -/
noncomputable abbrev faceBlack : AddMonoidAlgebra R checkerboard :=
  -(1 + single (-cellU) 1 + single (-cellV) 1 + single (-(cellU + cellV)) 1)

theorem repr_face : (checkerBasis R).repr (faceStencil R) =
    Finsupp.single 0 4 + Finsupp.single 1 (faceBlack R) := by
  rw [faceStencil_eq, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one]

theorem repr_face_red : (checkerBasis R).repr (faceStencil R) 0 = 4 := by
  rw [repr_face]
  simp

theorem repr_face_black : (checkerBasis R).repr (faceStencil R) 1 = faceBlack R := by
  rw [repr_face]
  simp

theorem faceBlack_coeff_zero : (faceBlack R).coeff 0 = -1 := by
  have hu : (-cellU : checkerboard) ≠ 0 := by decide
  have hv : (-cellV : checkerboard) ≠ 0 := by decide
  have huv : (-cellV + -cellU : checkerboard) ≠ 0 := by decide
  simp [faceBlack, one_def, hu, hv, huv]

theorem smul_eq_algebraMap_smul {Λ : Type*} [AddCommGroup Λ] (Λ' : AddSubgroup Λ) (r : R)
    (z : AddMonoidAlgebra R Λ) : r • z = (algebraMap R (AddMonoidAlgebra R Λ') r) • z := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_sublattice]
  congr 1
  simp [AddMonoidAlgebra.coe_algebraMap, mapDomain_single]

/-- The face form's red-black tick, with the half move `M(-ℓ g/2)`, is the blocking of no law of
the plane when `κ² ℓ ≠ 0`. -/
theorem face_not_law [Invertible (2 : R)] (κ ℓ : R) (hκℓ : κ * κ * ℓ ≠ 0) :
    ¬ ∃ T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra R (ℤ × ℤ)),
      block (checkerBasis R) T = redBlackTick (checkerBasis R)
        (algebraMap R (AddMonoidAlgebra R checkerboard) κ) ((-(ℓ * ⅟2)) • faceStencil R) := by
  intro hT
  have hd := isUnit_single_cell R (cellU + cellV)
  have h := (redBlack_of (checkerBasis_zero R) (checkerBasis_one R)
    (by rw [hd.unit_spec]; exact shiftX_sq R) (algebraMap R _ κ)
    ((-(ℓ * ⅟2)) • faceStencil R)).2.2 hT
  rw [smul_eq_algebraMap_smul R checkerboard, map_smul, Finsupp.smul_apply, smul_eq_mul,
    repr_face_black] at h
  have h' : algebraMap R (AddMonoidAlgebra R checkerboard) (κ * κ * (-(ℓ * ⅟2))) *
      faceBlack R = 0 := by
    rw [map_mul, map_mul]
    linear_combination h
  have h0 := congrArg (fun z : AddMonoidAlgebra R checkerboard => z.coeff 0) h'
  simp only [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, coeff_single_zero_mul, faceBlack_coeff_zero, coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h0
  apply hκℓ
  linear_combination 2 * h0 - κ * κ * ℓ * invOf_mul_self (2 : R)

end Checkerboard

/-- **R6** (the cosets). -/
@[ledger "R6"]
theorem cosets : Statement.cosets := fun _ _ _ _ Λ' _ t ht =>
  ⟨cosetBasis Λ' t ht, cosetBasis_apply Λ' t ht⟩

/-- **R6** (red-black on the checkerboard). -/
@[ledger "R6"]
theorem checkerboardRedBlack : Statement.checkerboardRedBlack := fun R _ _ =>
  ⟨checkerBasis R, checkerBasis_zero R, checkerBasis_one R, shiftX_sq R,
    isUnit_single_cell R _, repr_face_red R, repr_face_black R, face_not_law R⟩

/-! ## Non-vacuity

- The line `ℤ`, blocked by its even cells `2ℤ`, on the representatives `0` and `1`.
- The plane over `ℚ`, blocked by the checkerboard: the book's face-form tick blocks as R6 says,
  and red-black with finding 044's `κ = 1/4` and `λ = 1` is the blocking of no law of the plane.
-/

/-- The line blocked by its even cells: `ℚ[x^±1]` has the basis `1, x` over `ℚ[x^±2]`. -/
example : ∃ bs : Module.Basis (Fin 2) (AddMonoidAlgebra ℚ (AddSubgroup.zmultiples (2 : ℤ)))
    (AddMonoidAlgebra ℚ ℤ), bs 0 = 1 ∧ bs 1 = single 1 1 := by
  obtain ⟨bs, hbs⟩ := cosets ℚ ℤ (AddSubgroup.zmultiples 2) 2 ![0, 1] fun a => by
    simp only [Int.mem_zmultiples_iff]
    by_cases h : 2 ∣ a
    · refine ⟨0, by simpa using h, fun j hj => ?_⟩
      fin_cases j
      · rfl
      · simp at hj
        omega
    · refine ⟨1, by simp; omega, fun j hj => ?_⟩
      fin_cases j
      · simp at hj
        omega
      · rfl
  exact ⟨bs, hbs 0, hbs 1⟩

/-- R6 on the book's face-form tick `K(1/4) M(-g)` in the plane, blocked by the checkerboard. -/
example : block (checkerBasis ℚ) (realize
      [Step.kick (algebraMap ℚ (AddMonoidAlgebra ℚ (ℤ × ℤ)) (1 / 4)), Step.move (-faceStencil ℚ)] :
      Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (ℤ × ℤ))) =
    realizePlaced (blockScore (checkerBasis ℚ)
      [Step.kick (algebraMap ℚ (AddMonoidAlgebra ℚ (ℤ × ℤ)) (1 / 4)),
        Step.move (-faceStencil ℚ)]) :=
  blocking _ _ _ (checkerBasis ℚ) _

/-- Red-black on the checkerboard, with finding 044's `κ = 1/4` and `λ = 1` and the half move
`M(-g/2)`, is the blocking of no law of the plane. -/
example : ∃ bs : Module.Basis (Fin 2) (AddMonoidAlgebra ℚ checkerboard)
    (AddMonoidAlgebra ℚ (ℤ × ℤ)), bs 0 = 1 ∧ bs 1 = shiftX ℚ ∧
    ¬ ∃ T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (ℤ × ℤ)),
      block bs T = redBlackTick bs (algebraMap ℚ (AddMonoidAlgebra ℚ checkerboard) (1 / 4))
        ((-((1 : ℚ) * ⅟2)) • faceStencil ℚ) := by
  obtain ⟨bs, h0, h1, -, -, -, -, hno⟩ := checkerboardRedBlack ℚ
  exact ⟨bs, h0, h1, hno (1 / 4) 1 (by norm_num)⟩

end Artform.Scores
