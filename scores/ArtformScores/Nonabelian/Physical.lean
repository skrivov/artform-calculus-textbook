import ArtformScores.Nonabelian.Descent

/-! # Normalized physical inclusion and the declared coefficient field -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Nonabelian
open Finset

def toComplex {m n : Type} (M : Matrix m n ℚ) : Matrix m n ℂ := M.map (algebraMap ℚ ℂ)
lemma complex_mul {m n o : Type} [Fintype n] (A : Matrix m n ℚ) (B : Matrix n o ℚ) :
    toComplex (A*B)=toComplex A*toComplex B := Matrix.map_mul
lemma complex_one {n : Type} [DecidableEq n] : toComplex (1 : Matrix n n ℚ)=1 := by
  apply Matrix.ext; intro i j; simp [toComplex,Matrix.one_apply]
lemma complex_star {m n : Type} (A : Matrix m n ℚ) :
    (toComplex A).conjTranspose=toComplex A.transpose := by
  apply Matrix.ext; intro i j; simp [toComplex,Matrix.conjTranspose_apply]
lemma compile_unitary (w : List Gate) :
    (toComplex (compile w)).conjTranspose*toComplex (compile w)=1 := by
  rw [complex_star,← complex_mul,compile_orthogonal,complex_one]

/-- Positive orbit-size normalizers in the declared complex embedding. -/
def normalizer (i : Fin 11) : ℂ := ((Real.sqrt (orbitWeight i : ℝ) : ℂ))⁻¹
lemma normalizer_ne (i : Fin 11) : normalizer i ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast orbit_weight_pos i)
lemma normalizer_star (i : Fin 11) : star (normalizer i)=normalizer i := by simp [normalizer]
lemma normalizer_square (i : Fin 11) : (orbitWeight i : ℂ)*normalizer i*normalizer i=1 := by
  have h : (Real.sqrt (orbitWeight i : ℝ))^2=(orbitWeight i : ℝ) := Real.sq_sqrt (by positivity)
  have hc : (Real.sqrt (orbitWeight i : ℝ) : ℂ)^2=(orbitWeight i : ℂ) := by exact_mod_cast h
  rw [← hc]
  unfold normalizer
  have hn : (Real.sqrt (orbitWeight i : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast orbit_weight_pos i)
  field_simp [hn]

def inclusion : Matrix Raw (Fin 11) ℂ :=
  fun x i => if orbitIndex x=i then normalizer i else 0
lemma inclusion_apply (x : Raw) (i : Fin 11) : inclusion x i=
    (if orbitIndex x=i then normalizer i else 0) := rfl
lemma inclusion_vec (v : Fin 11 → ℂ) (x : Raw) :
    inclusion.mulVec v x=normalizer (orbitIndex x)*v (orbitIndex x) := by
  simp [Matrix.mulVec,dotProduct,inclusion]
lemma inclusion_vacuum (v : Fin 11 → ℂ) : Vacuum (inclusion.mulVec v) := by
  intro h x
  simp only [inclusion_vec,orbit_gauge]
lemma inclusion_complete (ψ : Raw → ℂ) : Vacuum ψ ↔ ∃ v, inclusion.mulVec v=ψ := by
  constructor
  · intro h
    refine ⟨fun i => (normalizer i)⁻¹*ψ (representative i),?_⟩
    funext x
    rw [inclusion_vec]
    have hv := congrFun (vacuum_complete ψ |>.mp h) x
    change ψ (representative (orbitIndex x))=ψ x at hv
    rw [← mul_assoc,mul_inv_cancel₀ (normalizer_ne _),one_mul,hv]
  · rintro ⟨v,rfl⟩
    exact inclusion_vacuum v

lemma inclusion_isometry : inclusion.conjTranspose*inclusion=1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,inclusion]
  have h : ∑ x : Raw, star (if orbitIndex x=i then normalizer i else 0)*
      (if orbitIndex x=j then normalizer j else 0) =
      ∑ k : Fin 11, (orbitWeight k : ℂ)*
        (star (if k=i then normalizer i else 0)*(if k=j then normalizer j else 0)) := by
    simpa only [nsmul_eq_mul] using sum_orbits (fun k =>
      star (if k=i then normalizer i else 0)*(if k=j then normalizer j else 0))
  rw [h]
  by_cases hij : i=j
  · subst j
    simp only [apply_ite,star_zero,ite_mul,zero_mul,mul_zero,
      Finset.sum_ite_eq',mem_univ,ite_true,Matrix.one_apply_eq]
    rw [normalizer_star]
    simpa only [mul_assoc] using normalizer_square i
  · simp [apply_ite,hij,Ne.symm hij]

def normalization : Matrix (Fin 11) (Fin 11) ℂ := Matrix.diagonal normalizer
def inverseNormalization : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.diagonal (fun i => (normalizer i)⁻¹)
lemma normalization_inverse : normalization*inverseNormalization=1 := by
  simp [normalization,inverseNormalization,Matrix.diagonal_mul_diagonal,normalizer_ne]
lemma inverse_normalization : inverseNormalization*normalization=1 :=
  mul_eq_one_comm.mp normalization_inverse
lemma inclusion_factor : inclusion=toComplex rawInclusion*normalization := by
  apply Matrix.ext
  intro x i
  simp [Matrix.mul_diagonal,normalization,rawInclusion,toComplex,inclusion]

def physicalCompile (w : List Gate) : Matrix (Fin 11) (Fin 11) ℂ :=
  inverseNormalization*toComplex (compileOrbit w)*normalization
lemma physical_entry (w : List Gate) (i j : Fin 11) :
    physicalCompile w i j=(normalizer i)⁻¹*(compileOrbit w i j : ℂ)*normalizer j := by
  simp [physicalCompile,inverseNormalization,normalization,Matrix.mul_diagonal,
    Matrix.diagonal_mul,toComplex]
lemma physical_intertwiner (w : List Gate) :
    toComplex (compile w)*inclusion=inclusion*physicalCompile w := by
  have hc := congrArg toComplex (compile_intertwiner w)
  rw [complex_mul,complex_mul] at hc
  rw [inclusion_factor,physicalCompile]
  calc
    _ = (toComplex (compile w)*toComplex rawInclusion)*normalization :=
      (Matrix.mul_assoc _ _ _).symm
    _ = toComplex rawInclusion*toComplex (compileOrbit w)*normalization := by rw [hc]
    _ = _ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc normalization,normalization_inverse,Matrix.one_mul]

lemma physical_compression (w : List Gate) :
    inclusion.conjTranspose*toComplex (compile w)*inclusion=physicalCompile w := by
  rw [Matrix.mul_assoc,physical_intertwiner,← Matrix.mul_assoc,inclusion_isometry,
    Matrix.one_mul]
lemma physical_unitary (w : List Gate) :
    (physicalCompile w).conjTranspose*physicalCompile w=1 := by
  calc
    _ = (inclusion*physicalCompile w).conjTranspose*(inclusion*physicalCompile w) := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc inclusion.conjTranspose,inclusion_isometry,Matrix.one_mul]
    _ = (toComplex (compile w)*inclusion).conjTranspose*(toComplex (compile w)*inclusion) := by
      rw [physical_intertwiner]
    _ = 1 := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (toComplex (compile w)).conjTranspose,
        compile_unitary,Matrix.one_mul,inclusion_isometry]
lemma physical_reverse (w : List Gate) :
    physicalCompile w.reverse=(physicalCompile w).conjTranspose := by
  rw [← physical_compression,compile_inverse,← complex_star,← physical_compression]
  simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]

def gaugeProjector : Matrix Raw Raw ℂ := inclusion*inclusion.conjTranspose
lemma projector_selfadjoint : gaugeProjector.conjTranspose=gaugeProjector := by
  simp [gaugeProjector,Matrix.conjTranspose_mul]
lemma projector_square : gaugeProjector*gaugeProjector=gaugeProjector := by
  simp only [gaugeProjector,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc inclusion.conjTranspose,inclusion_isometry,Matrix.one_mul]
lemma projector_range (ψ : Raw → ℂ) : gaugeProjector.mulVec ψ=ψ ↔ Vacuum ψ := by
  constructor
  · intro h
    rw [← h]
    rw [gaugeProjector,← Matrix.mulVec_mulVec]
    exact inclusion_vacuum _
  · intro h
    obtain ⟨v,rfl⟩ := (inclusion_complete ψ).mp h
    rw [gaugeProjector,← Matrix.mulVec_mulVec,Matrix.mulVec_mulVec v,
      inclusion_isometry,Matrix.one_mulVec]

/-- A sufficient scalar extension, with positive real square-root generators. -/
def physicalScalars : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ),(Real.sqrt 3 : ℂ)}
lemma normalizer_mem (i : Fin 11) : normalizer i ∈ physicalScalars := by
  have h2 : (Real.sqrt 2 : ℂ) ∈ physicalScalars := IntermediateField.subset_adjoin _ _ (by simp)
  have h3 : (Real.sqrt 3 : ℂ) ∈ physicalScalars := IntermediateField.subset_adjoin _ _ (by simp)
  have hw : orbitWeight i=1 ∨ orbitWeight i=2 ∨ orbitWeight i=3 ∨ orbitWeight i=6 := by
    fin_cases i <;> decide
  rcases hw with hw|hw|hw|hw
  · simp [normalizer,hw]
  · simpa only [normalizer,hw,Nat.cast_ofNat] using physicalScalars.inv_mem h2
  · simpa only [normalizer,hw,Nat.cast_ofNat] using physicalScalars.inv_mem h3
  · unfold normalizer
    rw [hw]
    norm_num only [Nat.cast_ofNat]
    rw [show (6:ℝ)=2*3 by norm_num,Real.sqrt_mul (by norm_num)]
    push_cast
    exact physicalScalars.inv_mem (physicalScalars.mul_mem h2 h3)
lemma physical_coefficients (w : List Gate) (i j : Fin 11) :
    physicalCompile w i j ∈ physicalScalars := by
  rw [physical_entry]
  exact physicalScalars.mul_mem
    (physicalScalars.mul_mem (physicalScalars.inv_mem (normalizer_mem i))
      (physicalScalars.algebraMap_mem _)) (normalizer_mem j)


lemma compile_unitary_other (w : List Gate) :
    toComplex (compile w)*(toComplex (compile w)).conjTranspose=1 :=
  mul_eq_one_comm.mp (compile_unitary w)
lemma compile_complex_covariant (w : List Gate) : Covariant (toComplex (compile w)) := by
  intro h x y
  change (compile w (gauge h x) (gauge h y) : ℂ)=(compile w x y : ℂ)
  rw [compile_covariant w h x y]
lemma compile_vacuum (w : List Gate) (ψ : Raw → ℂ) (hψ : Vacuum ψ) :
    Vacuum ((toComplex (compile w)).mulVec ψ) :=
  covariant_vacuum _ (compile_complex_covariant w) ψ hψ
lemma physical_unitary_other (w : List Gate) :
    physicalCompile w*(physicalCompile w).conjTranspose=1 :=
  mul_eq_one_comm.mp (physical_unitary w)

/-! ## Non-vacuity -/
example : Fintype.card Physical=11 := physical_card
example : inclusion.conjTranspose*inclusion=1 := inclusion_isometry
example : physicalCompile (tickWord true) *
    (physicalCompile (tickWord true)).conjTranspose=1 := physical_unitary_other _

end Artform.Scores.Nonabelian
