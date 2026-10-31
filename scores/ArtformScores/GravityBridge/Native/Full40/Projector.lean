import ArtformScores.GravityBridge.Native.Full40.ProjectorStatements
/-! # The coframe Lorentz projector with compatible sources -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
omit [CharZero K] in
lemma gauge_field_add (d : Fin 4 → X) (w v : X → Biv K) :
    gaugeField d (w + v) = gaugeField d w + gaugeField d v := by
  funext x
  apply Prod.ext
  · exact lie_add _ _
  · funext i a
    simp [gaugeField, gaugeConnection]
    ring
omit [CharZero K] in
lemma gauge_field_sub (d : Fin 4 → X) (w v : X → Biv K) :
    gaugeField d (w - v) = gaugeField d w - gaugeField d v := by
  funext x
  apply Prod.ext
  · exact lie_sub _ _
  · funext i a
    simp [gaugeField, gaugeConnection]
    ring
omit [CharZero K] in
lemma gauge_field_zero (d : Fin 4 → X) : gaugeField d (0 : X → Biv K) = 0 := by
  funext x
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gaugeField, lie]
  · funext i a
    simp [gaugeField, gaugeConnection]
lemma lorentz_lie (w : Biv K) : coframeLorentz (lie w) = w := by
  funext a
  fin_cases a <;> simp [coframeLorentz, lie]
omit [CharZero K] in
lemma lorentz_sub (F G : Frame K) : coframeLorentz (F - G) =
    coframeLorentz F - coframeLorentz G := by
  funext a
  fin_cases a <;> simp [coframeLorentz] <;> ring
omit [CharZero K] in
lemma lorentz_zero : coframeLorentz (0 : Frame K) = 0 := by
  funext a
  fin_cases a <;> simp [coframeLorentz]
lemma readout_gauge (d : Fin 4 → X) (w : X → Biv K) :
    lorentzReadout (gaugeField d w) = w := by
  funext x
  exact lorentz_lie (w x)
omit [AddCommGroup X] [CharZero K] in
lemma readout_sub (q p : NativeField X K) : lorentzReadout (q - p) =
    lorentzReadout q - lorentzReadout p := by
  funext x
  exact lorentz_sub _ _
lemma readout_project (d : Fin 4 → X) (q : NativeField X K) :
    lorentzReadout (projectField d q) = 0 := by
  rw [projectField, readout_sub, readout_gauge, sub_self]
lemma project_idempotent (d : Fin 4 → X) (q : NativeField X K) :
    projectField d (projectField d q) = projectField d q := by
  rw [projectField, readout_project, gauge_field_zero, sub_zero]
lemma project_gauge_zero (d : Fin 4 → X) (w : X → Biv K) :
    projectField d (gaugeField d w) = 0 := by
  rw [projectField, readout_gauge, sub_self]
lemma project_fixed_iff (d : Fin 4 → X) (q : NativeField X K) :
    projectField d q = q ↔ lorentzReadout q = 0 := by
  constructor
  · intro h
    rw [← h, readout_project]
  · intro h
    rw [projectField, h, gauge_field_zero, sub_zero]
lemma project_kernel_iff (d : Fin 4 → X) (q : NativeField X K) :
    projectField d q = 0 ↔ ∃ w, q = gaugeField d w := by
  constructor
  · intro h
    exact ⟨lorentzReadout q, sub_eq_zero.mp h⟩
  · rintro ⟨w, rfl⟩
    exact project_gauge_zero d w
lemma source_project_iff (d : Fin 4 → X) (J : NativeField X K →ₗ[K] K) :
    (∀ w, J (gaugeField d w) = 0) ↔ ∀ q, J (projectField d q) = J q := by
  constructor
  · intro h q
    simp only [projectField, map_sub, h, sub_zero]
  · intro h w
    have he := h (gaugeField d w)
    rw [project_gauge_zero, map_zero] at he
    exact he.symm
omit [CharZero K] in
lemma project_preserves_metric (d : Fin 4 → X) (q : NativeField X K)
    (x : X) (i j : Fin 4) : metricVariation (projectField d q x).1 i j =
      metricVariation (q x).1 i j := by
  have hz := lie_metric_kernel (lorentzReadout q x) i j
  change eta i * ((q x).1 i j - lie (lorentzReadout q x) i j) +
    eta j * ((q x).1 j i - lie (lorentzReadout q x) j i) = metricVariation (q x).1 i j
  dsimp [metricVariation] at hz ⊢
  linear_combination -hz
lemma full_force_project [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K) :
    fullForce d kappa (projectField d q) = fullForce d kappa q := by
  classical
  funext a
  change nativeFirstVariation d kappa (projectField d q)
    (fieldCoordinates.symm (Pi.single a 1)) = _
  have hq : projectField d q = q + (-1 : K) • gaugeField d (lorentzReadout q) := by
    simp [projectField, sub_eq_add_neg]
  rw [hq]
  simp only [nativeFirstVariation, native_bilinear_add_left, native_bilinear_add_right,
    native_bilinear_smul_left, native_bilinear_smul_right]
  have hw := complete_mixed_ward d kappa
    (fieldCoordinates.symm (Pi.single a 1)) (lorentzReadout q)
  unfold nativeFirstVariation at hw
  change _ = nativeFirstVariation d kappa q (fieldCoordinates.symm (Pi.single a 1))
  unfold nativeFirstVariation
  linear_combination -hw
lemma native_source_compatible [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K) :
    ∀ w, firstVariationMap d kappa q (gaugeField d w) = 0 := by
  intro w
  exact complete_mixed_ward d kappa q w
/-- **GAC2:coframe-projector-compatible-sources**
(the coframe lorentz projector with compatible sources). -/
@[ledger "GAC2:coframe-projector-compatible-sources"]
theorem projectorLaw : Statement.projectorLaw := by
  intro X K _ _ _
  exact ⟨lorentz_lie,
    readout_gauge,
    readout_project,
    project_idempotent,
    project_gauge_zero,
    project_fixed_iff,
    project_kernel_iff,
    source_project_iff,
    project_preserves_metric,
    full_force_project,
    native_source_compatible⟩
/-! ## Non-vacuity -/
example : coframeLorentz (lie (![1, 2, 3, 4, 5, 6] : Biv ℚ)) = ![1, 2, 3, 4, 5, 6] :=
  lorentz_lie _
example : ∀ w, firstVariationMap (fun _ : Fin 4 => PUnit.unit) (1 / 101)
    constantBoostField (gaugeField (fun _ => PUnit.unit) w) = 0 :=
  native_source_compatible _ _ _
end Artform.Scores.GravityBridge.Native.Full40
