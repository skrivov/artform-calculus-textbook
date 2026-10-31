import ArtformScores.Nonabelian.Physical
import ArtformScores.Nonabelian.ProbabilityData

/-! # Normalized curvature measurement after two actual score ticks -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Nonabelian
open Finset

def sourceQ : Raw → ℚ := orbitInclude sourceVector
def outputQ (active : Bool) : Raw → ℚ := orbitInclude (checkedStage active 6)
lemma rawInclusion_vec (v : Fin 11 → ℚ) : rawInclusion.mulVec v=orbitInclude v := by
  funext x
  simp [rawInclusion,Matrix.mulVec,dotProduct,orbitInclude]
lemma raw_action (w : List Gate) (v : Fin 11 → ℚ) :
    (compile w).mulVec (orbitInclude v)=orbitInclude ((compileOrbit w).mulVec v) := by
  rw [← rawInclusion_vec,Matrix.mulVec_mulVec,compile_intertwiner,← Matrix.mulVec_mulVec,
    rawInclusion_vec]
lemma rational_two_ticks (active : Bool) :
    (compile (tickWord active++tickWord active)).mulVec sourceQ=outputQ active := by
  rw [sourceQ,raw_action,two_tick_orbit]
  rfl
lemma orbit_flat : ∀ x, curvature x=1 ↔ orbitSign (orbitIndex x)=1 := by decide +kernel
lemma source_massQ : ∑ x, sourceQ x^2=(3:ℚ) := by
  rw [sourceQ]
  change (∑ x, (sourceVector (orbitIndex x))^2)=3
  rw [sum_orbits (fun i => sourceVector i ^ 2)]
  decide +kernel
lemma output_massQ (active : Bool) : ∑ x, outputQ active x^2=(3:ℚ) := by
  change (∑ x, (checkedStage active 6 (orbitIndex x))^2)=3
  rw [sum_orbits (fun i => checkedStage active 6 i ^ 2)]
  cases active <;> decide +kernel
lemma output_curvedQ (active : Bool) :
    ∑ x, (if curvature x=1 then 0 else outputQ active x^2)=if active then (32:ℚ)/27 else 0 := by
  simp_rw [orbit_flat]
  change (∑ x, if orbitSign (orbitIndex x)=1 then 0 else
    (checkedStage active 6 (orbitIndex x))^2)=_
  rw [sum_orbits (fun i => if orbitSign i=1 then 0 else checkedStage active 6 i ^ 2)]
  cases active <;> decide +kernel

def liftVector {I : Type} (v : I → ℚ) : I → ℂ := fun x => (v x : ℂ)
def scaled (v : Raw → ℚ) : Raw → ℂ := normalizer 1 • liftVector v
def source : Raw → ℂ := scaled sourceQ
def evolved (active : Bool) : Raw → ℂ :=
  (toComplex (compile (tickWord active++tickWord active))).mulVec source

def mass (ψ : Raw → ℂ) : ℝ := ∑ x, Complex.normSq (ψ x)
def curvedMass (ψ : Raw → ℂ) : ℝ :=
  ∑ x, if curvature x=1 then 0 else Complex.normSq (ψ x)
def probability (ψ : Raw → ℂ) : ℝ := curvedMass ψ/mass ψ
lemma normSq_rat (q : ℚ) : Complex.normSq (q : ℂ)=(q:ℝ)^2 := by
  simp [Complex.normSq,pow_two]
lemma normalizer_one_norm : Complex.normSq (normalizer 1)=(1:ℝ)/3 := by
  have h : (3:ℂ)*normalizer 1*normalizer 1=1 := normalizer_square 1
  have hc : (Complex.normSq (normalizer 1):ℂ)=(1:ℂ)/3 := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (normalizer 1)*normalizer 1=(1:ℂ)/3
    rw [normalizer_star]
    linear_combination (1/3)*h
  apply Complex.ofReal_injective
  norm_num at hc ⊢
  exact hc
lemma mass_scaled (v : Raw → ℚ) : mass (scaled v)=(1:ℝ)/3*(∑ x, v x^2 : ℚ) := by
  simp only [mass,scaled,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,liftVector]
  rw [← Finset.mul_sum,normalizer_one_norm]
  simp only [normSq_rat]
  push_cast
  rfl
lemma curved_scaled (v : Raw → ℚ) :
    curvedMass (scaled v)=(1:ℝ)/3*(∑ x, if curvature x=1 then 0 else v x^2 : ℚ) := by
  simp only [curvedMass,scaled,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,liftVector]
  have ht (x : Raw) :
      (if curvature x=1 then 0 else Complex.normSq (normalizer 1)*Complex.normSq (v x : ℂ)) =
      Complex.normSq (normalizer 1)*(if curvature x=1 then 0 else Complex.normSq (v x : ℂ)) := by
    split_ifs <;> simp
  simp_rw [ht]
  rw [← Finset.mul_sum,normalizer_one_norm]
  simp only [normSq_rat]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_cast
lemma complex_vec (M : Matrix Raw Raw ℚ) (v : Raw → ℚ) :
    (toComplex M).mulVec (liftVector v)=liftVector (M.mulVec v) := by
  funext x
  simp [toComplex,liftVector,Matrix.mulVec,dotProduct]
lemma evolved_exact (active : Bool) : evolved active=scaled (outputQ active) := by
  rw [evolved,source,scaled,Matrix.mulVec_smul,complex_vec,rational_two_ticks]
  rfl
lemma source_normalized : mass source=1 := by
  rw [source,mass_scaled,source_massQ]
  norm_num
lemma evolved_normalized (active : Bool) : mass (evolved active)=1 := by
  rw [evolved_exact,mass_scaled,output_massQ]
  norm_num
lemma curvature_probability (active : Bool) :
    probability (evolved active)=if active then (32:ℝ)/81 else 0 := by
  rw [probability,evolved_normalized,div_one,evolved_exact,curved_scaled,output_curvedQ]
  cases active <;> norm_num


lemma source_column : source=inclusion.mulVec (Pi.single 1 (1:ℂ)) := by
  funext x
  rw [inclusion_vec]
  change normalizer 1*(sourceVector (orbitIndex x) : ℂ)=_
  by_cases h : orbitIndex x=1
  · simp [sourceVector,h]
  · simp [sourceVector,h]
lemma source_vacuum : Vacuum source := by
  rw [source_column]
  exact inclusion_vacuum _
lemma evolved_vacuum (active : Bool) : Vacuum (evolved active) :=
  compile_vacuum _ _ source_vacuum

/-- The raw orthogonal projector measuring nontrivial commutator curvature. -/
def curvatureProjector : Matrix Raw Raw ℂ :=
  Matrix.diagonal (fun x => if curvature x=1 then 0 else 1)
lemma curvature_projector_selfadjoint : curvatureProjector.conjTranspose=curvatureProjector := by
  apply Matrix.ext
  intro x y
  by_cases h : x=y
  · subst y
    simp [curvatureProjector,Matrix.conjTranspose_apply,apply_ite]
  · simp [curvatureProjector,Matrix.conjTranspose_apply,h,Ne.symm h]
lemma curvature_projector_square : curvatureProjector*curvatureProjector=curvatureProjector := by
  simp only [curvatureProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> norm_num
lemma curvature_projector_covariant : Covariant curvatureProjector := by
  intro h x y
  have hg : curvature (gauge h x)=1 ↔ curvature x=1 := by
    rw [curvature_gauge]
    simp [conjugate]
  have he : gauge h x=gauge h y ↔ x=y := (gaugeEquiv h).injective.eq_iff
  simp [curvatureProjector,Matrix.diagonal_apply,hg,he]
lemma curvature_measure (ψ : Raw → ℂ) : mass (curvatureProjector.mulVec ψ)=curvedMass ψ := by
  simp only [mass,curvedMass,curvatureProjector,Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp
lemma source_curved : curvedMass source=0 := by
  have h : sourceQ=outputQ false := by simp [sourceQ,outputQ,checked_free]
  rw [source,h,curved_scaled,output_curvedQ]
  norm_num
lemma free_returns_source : evolved false=source := by
  rw [evolved_exact]
  simp [outputQ,sourceQ,checked_free,source]
lemma active_curved_mass : curvedMass (evolved true)=(32:ℝ)/81 := by
  rw [evolved_exact,curved_scaled,output_curvedQ]
  norm_num

/-! ## Non-vacuity -/
example : mass source=1 ∧ Vacuum source ∧ curvedMass source=0 :=
  ⟨source_normalized,source_vacuum,source_curved⟩
example : probability (evolved true)=(32:ℝ)/81 := curvature_probability true
example : probability (evolved false)=0 := curvature_probability false
example : evolved true ≠ source := by
  intro h
  have ht := active_curved_mass
  rw [h,source_curved] at ht
  norm_num at ht


end Artform.Scores.Nonabelian
