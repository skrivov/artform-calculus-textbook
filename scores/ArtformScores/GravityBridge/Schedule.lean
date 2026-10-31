import ArtformScores.GravityBridge.ScheduleStatements
import ArtformScores.Rules

/-! # Order defects preserve the form but change the endpoint data -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma schedule_defect (a b : ℚ) (x : ℚ × ℚ) :
    scheduleMove b (scheduleKick a x) - scheduleKick a (scheduleMove b x) =
      (a * b * x.1, -a * b * x.2) := by
  ext <;> dsimp [scheduleKick, scheduleMove] <;> ring

lemma schedule_pairing (a b : ℚ) (x y : ℚ × ℚ) :
    (scheduleMove b (scheduleKick a x)).1 * (scheduleMove b (scheduleKick a y)).2 -
      (scheduleMove b (scheduleKick a x)).2 * (scheduleMove b (scheduleKick a y)).1 =
        x.1 * y.2 - x.2 * y.1 ∧
    (scheduleKick a (scheduleMove b x)).1 * (scheduleKick a (scheduleMove b y)).2 -
      (scheduleKick a (scheduleMove b x)).2 * (scheduleKick a (scheduleMove b y)).1 =
        x.1 * y.2 - x.2 * y.1 := by
  constructor <;> dsimp [scheduleKick, scheduleMove] <;> ring

lemma schedule_equal_iff (a b : ℚ) :
    (∀ x, scheduleMove b (scheduleKick a x) = scheduleKick a (scheduleMove b x)) ↔ a * b = 0 := by
  constructor
  · intro h
    have he := congrArg Prod.fst (h (1, 0))
    dsimp [scheduleKick, scheduleMove] at he
    nlinarith
  · intro h x
    apply sub_eq_zero.mp
    rw [schedule_defect, h]
    simp [neg_mul, h]

lemma schedule_boundary_terms (a b : ℚ) (x u : ℚ × ℚ) :
    boundaryPotential (scheduleMove b (scheduleKick a x)) (scheduleMove b (scheduleKick a u)) -
      boundaryPotential x u = kmDerivative a b x u ∧
    boundaryPotential (scheduleKick a (scheduleMove b x)) (scheduleKick a (scheduleMove b u)) -
      boundaryPotential x u = mkDerivative a b x u := by
  constructor <;>
    dsimp [boundaryPotential, scheduleMove, scheduleKick, kmDerivative, mkDerivative] <;> ring

lemma schedule_primitive_variation (a b : ℚ) (x u : ℚ × ℚ) (e : ℚ) :
    kmPrimitive a b (x + e • u) =
      kmPrimitive a b x + e * kmDerivative a b x u + e ^ 2 * kmPrimitive a b u ∧
    mkPrimitive a b (x + e • u) =
      mkPrimitive a b x + e * mkDerivative a b x u + e ^ 2 * mkPrimitive a b u := by
  constructor <;> dsimp [kmPrimitive, mkPrimitive, kmDerivative, mkDerivative] <;> ring

variable {K X W : Type*} [Field K] [AddCommGroup X] [Module K X]

lemma quotient_schedule_iff (N : Submodule K X) (F G : X →ₗ[K] X) :
    N.mkQ.comp F = N.mkQ.comp G ↔ LinearMap.range (F - G) ≤ N := by
  constructor
  · intro h
    rintro n ⟨x, rfl⟩
    have he := LinearMap.congr_fun h x
    have hz : N.mkQ ((F - G) x) = 0 := by simpa [map_sub, sub_eq_zero] using he
    change (Submodule.Quotient.mk ((F - G) x) : X ⧸ N) = 0 at hz
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  · intro h
    apply LinearMap.ext
    intro x
    have hn := h (LinearMap.mem_range_self (F - G) x)
    have hz : N.mkQ ((F - G) x) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hn
    simpa [map_sub, sub_eq_zero] using hz

/-- **GAC:schedule-boundary** (old shear order, symplectic pairing and boundary primitives). -/
@[ledger "GAC:schedule-boundary"]
theorem scheduleLaw : Statement.scheduleLaw := by
  refine ⟨schedule_defect, schedule_equal_iff, schedule_pairing,
    schedule_boundary_terms, schedule_primitive_variation, ?_⟩
  intro K X _ _ _ N F G
  exact quotient_schedule_iff N F G

/-! ## Non-vacuity -/

example (a b : ℚ) (x : ℚ × ℚ) :
    Matrix.mulVec (realize [Step.kick a, Step.move b] : Matrix (Fin 2) (Fin 2) ℚ)
      ![x.1, x.2] = ![(scheduleMove b (scheduleKick a x)).1,
        (scheduleMove b (scheduleKick a x)).2] := by
  ext i
  fin_cases i <;>
    simp [realize, Step.mat, scheduleMove, scheduleKick, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two] <;> ring

example : scheduleMove 1 (scheduleKick 1 (1, 0)) = (2, 1) ∧
    scheduleKick 1 (scheduleMove 1 (1, 0)) = (1, 1) ∧
    kmPrimitive 1 1 (1, 0) = 1 ∧ mkPrimitive 1 1 (1, 0) = 1 / 2 := by
  norm_num [scheduleKick, scheduleMove, kmPrimitive, mkPrimitive]

end

end Artform.Scores.GravityBridge
