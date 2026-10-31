import ArtformScores.GravityBridge.Native.Full40.WardStatements
/-! # The full original mixed Lorentz Ward identity -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
omit [CharZero K] in
lemma first_wedge_gauge (w : Biv K) (i j : Fin 4) :
    firstWedge (lie w) i j = bivBracket w (wedge (basisVector i) (basisVector j)) := by
  funext a
  fin_cases i <;> fin_cases j <;> fin_cases a <;>
    simp [firstWedge, wedge, basisVector, lie, bivBracket, cross3, boostPart, spatialPart]
lemma native_lu_gauge (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6) :
    nativeLU d (gaugeField d w) x r = bivBracket (w x) (flatComplement r) := by
  simp only [nativeLU, linearComplement, connectionComplement, nativeV, gaugeField,
    gaugeConnection, first_wedge_gauge]
  funext a
  fin_cases a <;>
    simp [flatComplement, bivBracket, cross3, boostPart, spatialPart,
      add_assoc, add_comm (d (faceFirst r)) (d (faceSecond r))] <;> ring
omit [CharZero K] in
lemma native_k_gauge (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6) :
    nativeK d (gaugeField d w) x r = 0 :=
  curvature_gauge_zero d w x (faceFirst r) (faceSecond r)
omit [CharZero K] in
lemma native_theta_gauge (d : Fin 4 → X) (w : X → Biv K) (x : X) (r : Fin 6) :
    nativeTheta d (gaugeField d w) x r = 0 := by
  funext a
  exact torsion_gauge_zero d w x (faceFirst r) (faceSecond r) a
set_option maxHeartbeats 2000000 in
-- Expand the six original bivector components in the mixed ordered plaquette contact.
lemma mixed_curvature_gauge (d : Fin 4 → X) (q : NativeField X K) (w : X → Biv K)
    (x : X) (r : Fin 6) : nativeK d (gaugeCorrection d q w) x r +
      rawPlaquetteContact d q (gaugeField d w) x r +
      rawPlaquetteContact d (gaugeField d w) q x r =
        bivBracket (w x) (nativeK d q x r) := by
  funext a
  fin_cases a <;>
    simp [nativeK, linearCurvature, gaugeCorrection, rawPlaquetteContact, nativeLetters,
      gaugeField, gaugeConnection, bivBracket, cross3, boostPart, spatialPart,
      add_assoc, add_comm (d (faceFirst r)) (d (faceSecond r))] <;> ring
omit [CharZero K] in
lemma star_sub (a b : Biv K) : internalStar (a - b) = internalStar a - internalStar b := by
  funext i
  fin_cases i <;> simp [internalStar] <;> ring
omit [CharZero K] in
lemma biv_pair_sub_right (a b c : Biv K) : bivPair a (b - c) = bivPair a b - bivPair a c := by
  simp [bivPair, mul_sub, Finset.sum_sub_distrib]
omit [CharZero K] in
lemma total_curvature_zero [Fintype X] (d : Fin 4 → X) (q : NativeField X K)
    (r : Fin 6) (C : Biv K) : ∑ x, bivPair C (internalStar (nativeK d q x r)) = 0 := by
  have hs (a : X) (f : X → K) : ∑ x, f (x + a) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.addRight a) f
  simp only [nativeK, linearCurvature, star_sub, biv_pair_sub_right,
    Finset.sum_sub_distrib]
  rw [hs (d (faceSecond r)) (fun x => bivPair C (internalStar ((q x).2 (faceFirst r)))),
    hs (d (faceFirst r)) (fun x => bivPair C (internalStar ((q x).2 (faceSecond r))))]
  ring
lemma mixed_gauge_density (d : Fin 4 → X) (q : NativeField X K) (w : X → Biv K)
    (x : X) (r : Fin 6) :
    bivPair (nativeLU d (gaugeField d w) x r) (internalStar (nativeK d q x r)) +
      bivPair (flatComplement r) (internalStar
        (rawPlaquetteContact d q (gaugeField d w) x r +
         rawPlaquetteContact d (gaugeField d w) q x r)) =
    -bivPair (flatComplement r) (internalStar (nativeK d (gaugeCorrection d q w) x r)) := by
  have hc := mixed_curvature_gauge d q w x r
  have he : rawPlaquetteContact d q (gaugeField d w) x r +
      rawPlaquetteContact d (gaugeField d w) q x r =
      bivBracket (w x) (nativeK d q x r) - nativeK d (gaugeCorrection d q w) x r := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_assoc, add_comm, add_left_comm] using hc
  rw [native_lu_gauge, he, star_sub, biv_pair_sub_right, star_bracket]
  have hi := invariant_biv_pair (w x) (flatComplement r) (internalStar (nativeK d q x r))
  linear_combination hi
lemma complete_mixed_ward [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K) (w : X → Biv K) :
    nativeFirstVariation d kappa q (gaugeField d w) = 0 := by
  rw [direct_first_variation]
  unfold directFirstVariation
  simp only [native_lu_gauge, native_k_gauge, native_theta_gauge]
  have hz : internalStar (0 : Biv K) = 0 := by
    funext i
    fin_cases i <;> simp [internalStar]
  have hp (a : Biv K) : bivPair a 0 = 0 := by simp [bivPair]
  have ht (a : Vec K) : etaPair a 0 = 0 := by simp [etaPair]
  simp only [hz, hp, ht, mul_zero, Finset.sum_const_zero, add_zero]
  have hd (x : X) (r : Fin 6) :
      bivPair (bivBracket (w x) (flatComplement r)) (internalStar (nativeK d q x r)) +
        bivPair (flatComplement r) (internalStar
          (rawPlaquetteContact d q (gaugeField d w) x r +
           rawPlaquetteContact d (gaugeField d w) q x r)) =
      -bivPair (flatComplement r) (internalStar (nativeK d (gaugeCorrection d q w) x r)) := by
    simpa only [native_lu_gauge] using mixed_gauge_density d q w x r
  simp only [hd]
  rw [Finset.sum_comm]
  simp only [Finset.sum_neg_distrib, total_curvature_zero, neg_zero, Finset.sum_const_zero]
lemma full_force_gauge_zero [Fintype X] (d : Fin 4 → X) (kappa : K) (w : X → Biv K) :
    fullForce d kappa (gaugeField d w) = 0 := by
  apply (full_force_zero_iff d kappa _).mpr
  intro p
  rw [first_variation_symmetric]
  exact complete_mixed_ward d kappa p w
omit [CharZero K] in
lemma gauge_field_injective (d : Fin 4 → X) : Function.Injective (gaugeField d (K := K)) := by
  intro w v h
  funext x
  apply lie_injective
  exact congrArg (fun q => (q x).1) h
/-- **GAC2:full-mixed-lorentz-ward**
(the full original mixed lorentz ward identity). -/
@[ledger "GAC2:full-mixed-lorentz-ward"]
theorem wardLaw : Statement.wardLaw := by
  intro X K _ _ _
  exact ⟨first_wedge_gauge,
    native_lu_gauge,
    native_k_gauge,
    native_theta_gauge,
    mixed_curvature_gauge,
    total_curvature_zero,
    mixed_gauge_density,
    complete_mixed_ward,
    full_force_gauge_zero,
    gauge_field_injective⟩
/-! ## Non-vacuity -/
example : (gaugeField gridUnit (fun x => gridPulse x •
    (![1, 0, 0, 0, 0, 0] : Biv ℚ)) 0).1 0 1 = 1 := by
  norm_num [gaugeField, gridPulse, lie]
example : fullForce gridUnit (1 / 101 : ℚ)
    (gaugeField gridUnit (fun x => gridPulse x • ![1, 0, 0, 0, 0, 0])) = 0 :=
  full_force_gauge_zero _ _ _
end Artform.Scores.GravityBridge.Native.Full40
