import ArtformScores.Nonabelian.Statements

/-! # Checked curvature-dependent non-Abelian score claims -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Nonabelian
open Artform

/-- **NQS:geometry** (ordered multiplicative curvature on the actual canvas). -/
@[ledger "NQS:geometry"]
theorem geometry : Statement.geometry := by
  exact ⟨rfl,group_card,raw_card,curvature_word,curvature_gauge,curvature_flat,nonflat_count,
    by decide +kernel,by decide +kernel⟩

/-- **NQS:legal-coherent** (owned batches and coherent execution). -/
@[ledger "NQS:legal-coherent"]
theorem legalCoherent : Statement.legalCoherent := by
  exact ⟨fun e c x => ⟨trivial,rfl,rfl,replacement_apply e c x⟩,
    fun x => ⟨trivial,rfl,rfl,curvature_apply x⟩,
    fun _ _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,
    batch_injective,admitted_electric,admitted_curvature,batch_size,coefficient_reads,
    fun g h x r => ⟨transport_commit g h x r,transport_coefficient g h x r⟩,
    branch_kernel,fun active t x r => (nativeRealizer active).allows t x r,
    fun _ => ⟨rfl,rfl⟩,native_tick,realizer_periodic,native_six,history_compiles,magnetic_off,
    fun _ _ => rfl⟩

/-- **NQS:unitary-score** (full raw inverses and quantum Gauss). -/
@[ledger "NQS:unitary-score"]
theorem unitaryScore : Statement.unitaryScore := by
  refine ⟨compile_append,fun g => ⟨gate_transpose g,gate_square g⟩,?_⟩
  intro w
  refine ⟨compile_unitary w,compile_unitary_other w,?_,compile_complex_covariant w,compile_vacuum w⟩
  rw [compile_inverse,complex_star]

/-- **NQS:physical-carrier** (all eleven orbits with the exact physical normalization). -/
@[ledger "NQS:physical-carrier"]
theorem physicalCarrier : Statement.physicalCarrier := by
  exact ⟨orbit_iff,fun i => ⟨orbit_representative i,orbit_weight_count i,orbit_weight_pos i⟩,
    ⟨physicalEquiv⟩,physical_card,inclusion_gram,inclusion_isometry,inclusion_complete,
    projector_selfadjoint,projector_square,projector_range⟩

/-- **NQS:physical-descent** (all-word unitary descent and scalar membership). -/
@[ledger "NQS:physical-descent"]
theorem physicalDescent : Statement.physicalDescent := by
  exact ⟨normalizer_mem,fun w => ⟨compile_intertwiner w,compileOrbit_weighted w,
    physical_intertwiner w,physical_compression w,physical_unitary w,physical_unitary_other w,
    physical_reverse w,physical_coefficients w⟩⟩

/-- **NQS:two-tick-curvature** (exact normalized curvature sensitivity). -/
@[ledger "NQS:two-tick-curvature"]
theorem twoTickCurvature : Statement.twoTickCurvature := by
  exact ⟨by decide +kernel,rfl,source_column,source_normalized,source_vacuum,source_curved,
    curvature_projector_selfadjoint,curvature_projector_square,curvature_projector_covariant,
    curvature_measure,fun active => ⟨evolved_normalized active,evolved_vacuum active,
      curvature_probability active⟩,free_returns_source⟩

/-! ## Non-vacuity -/
example : curvature (elements 1,elements 2) ≠ 1 := by decide +kernel
example : (batch (.electric false) (table (1,1)) (some 1)).apps.length=1 := rfl
example : (batch (.curvature false) (table (1,1)) (some ())).apps.length=1 := rfl
example : historyAmplitude (tickWord true) (1,1) (1,1)=tick true (1,1) (1,1) :=
  history_compiles _ _ _
example : physicalCompile (tickWord true)*(physicalCompile (tickWord true)).conjTranspose=1 :=
  physical_unitary_other _
example : Fintype.card Physical=11 ∧ inclusion.conjTranspose*inclusion=1 :=
  ⟨physical_card,inclusion_isometry⟩
example : mass source=1 ∧ Vacuum source ∧ curvedMass source=0 :=
  ⟨source_normalized,source_vacuum,source_curved⟩
example : probability (evolved true) ≠ probability (evolved false) := by
  rw [curvature_probability,curvature_probability]
  norm_num
end Artform.Scores.Nonabelian
