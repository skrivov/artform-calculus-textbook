import ArtformScores.Gauge.Statements

/-! # Reviewed gauge score applications -/
set_option autoImplicit false
namespace Artform.Scores.Gauge
open Artform

/-- **GSC:canonical-filter** (actual reversal and a Weyl-conjugation obstruction). -/
@[ledger "GSC:canonical-filter"]
theorem canonicalFilter : Statement.canonicalFilter := by
  exact ⟨fun _ _ P h => matrix_filter P h, fun _ _ f => fixed_iff_laplacian f,
    common_canonical, weyl_commutator, processed_obstruction.1, processed_obstruction.2,
    old_commutes, new_not_commutes, no_processed_conjugacy⟩

/-- **GSC:fixed-word** (two-sided inverse, Gauss, gauge and fixed-source tangent action). -/
@[ledger "GSC:fixed-word"]
theorem fixedWord : Statement.fixedWord := by
  intro K R _ w s φ u v
  exact ⟨run_inverse w s,run_inverse_other w s,fun n => run_defect (w.take n) s,
    run_gauge w φ s,run_perturb w s u,run_canonical w u v,tangent_gauss w u⟩

/-- **GSC:owned-compiler** (atomic local profiles and the padded native macro cycle). -/
@[ledger "GSC:owned-compiler"]
theorem ownedCompiler : Statement.ownedCompiler := by
  intro K R _ w
  exact ⟨realizer_wellPosed w,profile_apply,fun _ => ⟨rfl,rfl⟩,
    fun s n hn => history_prefix w s n hn,history_cycle w,maxwell_word,fieldTick_native⟩

/-- **GSC:c8-receipts** (the actual two C8 receipt policies and their coefficient extension). -/
@[ledger "GSC:c8-receipts"]
theorem c8Receipts : Statement.c8Receipts := by
  exact ⟨χ_standard,q_receipt,q_even,q_zero,q_unit,receipts_distinct,receipt_eighth,q_mem,
    kernel_mem,kinetic_unitary,inverse_kernel⟩

/-- **GSC:coherent-compiler** (phase-aware vacuum words on all raw configurations). -/
@[ledger "GSC:coherent-compiler"]
theorem coherentCompiler : Statement.coherentCompiler := by
  intro K w
  exact ⟨compile_unitary K w,mul_eq_one_comm.mp (compile_unitary K w),compile_inverse K w,
    compile_covariant K w,compile_vacuum K w,compile_mem K w,edge_actual K,vacuum_factor K,
    fun e a x => ⟨trivial,rfl,rfl,translation_apply K e a x,
      fun b => edge_translation K e b a x⟩⟩

/-- **GSM:transverse** (native toroidal Maxwell with divergence-free prescribed current). -/
@[ledger "GSM:transverse"]
theorem transverseBinding : Statement.transverseBinding := by
  exact ⟨fun _ _ a => ⟨div_transverse a,curlStar_transverse a⟩,
    fun _ _ s => embed_gauss s,fun _ _ => embed_injective,native_transverse⟩

/-- **GSM:block-source** (exact direct blocking and the gauge-invariant output map). -/
@[ledger "GSM:block-source"]
theorem blockedSource : Statement.blockedSource := by
  intro R _
  exact ⟨assemble_reads,read_assemble,blocked_tick,curvature_output⟩

/-- **GSM:forced-memory** (sources, preparation and constructive fine reconstruction). -/
@[ledger "GSM:forced-memory"]
theorem forcedMemory : Statement.forcedMemory := by
  intro R _
  exact ⟨sourced_memory,hidden_formula,reconstruction_iff,trajectory_unique,block_period⟩

/-- **GSM:coarse-obstruction** (a native Gauss-valid pair prevents autonomous coarse dynamics). -/
@[ledger "GSM:coarse-obstruction"]
theorem coarseObstruction : Statement.coarseObstruction := by
  exact ⟨coarse_values,coarse_initial,coarse_next,embed_gauss zeroFine,
    embed_gauss oddFine,coarse_not_autonomous⟩

/-! ## Non-vacuity -/

example : LaurentPolynomial.invert (waveVar : LaurentPolynomial (ZMod 8))=waveVar := by
  simp [waveVar,add_comm]
example : weylOp (processed5 a0) * weylOp (processed5 a1) ≠
    weylOp (processed5 a1) * weylOp (processed5 a0) := new_not_commutes

def squareInitial : FieldState oneFace (ZMod 8) := ⟨![1,2,0,0],0,0⟩
def squareCurrent : oneFace.E → ZMod 8 := ![1,0,0,0]

example : fieldTick squareCurrent squareInitial =
    ⟨![7,7,5,5],![2,3,3,3],![7,1,0,0]⟩ := by
  apply FieldState.ext <;> decide +kernel
example : defect (faceKick (K:=oneFace) 0 1 squareInitial)=0 := by decide +kernel
example : defect (FieldState.mk squareInitial.A (Pi.single 0 (3:ZMod 8)) 0) ≠ 0 := by
  decide +kernel
example : history (maxwellWord oneFace squareCurrent) squareInitial
    (law (maxwellWord oneFace squareCurrent)).score.period =
      fieldTick squareCurrent squareInitial := by
  rw [history_cycle,maxwell_word]
example : (profile (.current (K:=oneFace) 0 (1:ZMod 8))).apply (encode squareInitial)=
    encode (source (K:=oneFace) (Pi.single 0 1) squareInitial) := profile_apply _ _

example : q false 1 ≠ q true 1 := receipts_distinct
example (b : Bool) : (q b 1)^8 ≠ 1 := receipt_eighth b
example :
    let w : List (CoherentGate oneFace × Bool) := [(.face 0 false,false),(.move 0 true,false)]
    (compile oneFace w).conjTranspose * compile oneFace w=1 := compile_unitary _ _
example : Vacuum oneFace (fun _ => (1:ℂ)) := by intro _ _; rfl

example : torus.curl (transverse (![0,1,0,0] : Fin 4 → ZMod 8)) (0,0)=1 := by
  decide +kernel
example : embed (tick (![1,2,3,4] : Fin 4 → ZMod 8) zeroFine) ≠ embed zeroFine := by
  intro h
  have he := embed_injective h
  exact (by decide +kernel : tick (![1,2,3,4] : Fin 4 → ZMod 8) zeroFine ≠ zeroFine) he
example : evenForce (![1,2,3,4] : Fin 4 → ZMod 8) ≠ 0 ∧
    oddForce (![1,2,3,4] : Fin 4 → ZMod 8) ≠ 0 := by decide +kernel
example : (localBlock^4) (odd oddFine)=odd oddFine := block_period _
example : coarseRead zeroFine=coarseRead oddFine ∧
    coarseRead (tick 0 zeroFine) ≠ coarseRead (tick 0 oddFine) := ⟨coarse_initial,coarse_next⟩

example : coarseRead zeroFine=(0,0) ∧ coarseRead oddFine=(0,0) ∧
    coarseRead (tick 0 zeroFine)=(0,0) ∧
    coarseRead (tick 0 oddFine)=(0,![7,7]) := by decide +kernel

end Artform.Scores.Gauge
