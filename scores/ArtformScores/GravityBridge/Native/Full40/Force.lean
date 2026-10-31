import ArtformScores.GravityBridge.Native.Full40.ForceStatements
/-! # The original full coordinate force from the complete quadratic action -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
omit [AddCommGroup X] [CharZero K] in
lemma finite_linear_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (L : (J → K) →ₗ[K] K) (z : J → K) :
    L z = ∑ j, z j * L (Pi.single j 1) := by
  classical
  have hz : z = ∑ j, z j • Pi.single j (1 : K) := by
    funext a
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    L z = L (∑ j, z j • Pi.single j (1 : K)) := congrArg L hz
    _ = ∑ j, z j * L (Pi.single j 1) := by simp [map_sum, map_smul]
omit [CharZero K] in
lemma full_force_pairing [Fintype X] (d : Fin 4 → X) (kappa : K) (q p : NativeField X K) :
    nativeFirstVariation d kappa q p = ∑ a, fullForce d kappa q a * fieldCoordinates p a := by
  classical
  have he := finite_linear_expansion
    ((firstVariationMap d kappa q).comp fieldCoordinates.symm.toLinearMap) (fieldCoordinates p)
  simpa [LinearMap.comp_apply, firstVariationMap, fullForce, mul_comm] using he
omit [CharZero K] in
lemma full_force_zero_iff [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K) :
    fullForce d kappa q = 0 ↔ ∀ p, nativeFirstVariation d kappa q p = 0 := by
  classical
  constructor
  · intro h p
    rw [full_force_pairing, h]
    simp
  · intro h
    funext a
    exact h (fieldCoordinates.symm (Pi.single a 1))
omit [CharZero K] in
lemma first_variation_symmetric [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K) : nativeFirstVariation d kappa q p =
      nativeFirstVariation d kappa p q := by
  dsimp [nativeFirstVariation]
  ring
omit [CharZero K] in
lemma full_jacobian_symmetric [Fintype X] (d : Fin 4 → X) (kappa : K) :
    (fullJacobian d kappa).transpose = fullJacobian d kappa := by
  classical
  ext a b
  exact first_variation_symmetric d kappa _ _
omit [CharZero K] in
lemma full_force_matrix [Fintype X] (d : Fin 4 → X) (kappa : K) (q : NativeField X K) :
    fullForce d kappa q = Matrix.mulVec (fullJacobian d kappa) (fieldCoordinates q) := by
  classical
  funext a
  change nativeFirstVariation d kappa q (fieldCoordinates.symm (Pi.single a 1)) =
    ∑ b, fullJacobian d kappa a b * fieldCoordinates q b
  rw [first_variation_symmetric, full_force_pairing]
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun t : K => t * fieldCoordinates q b)
  exact first_variation_symmetric d kappa _ _
omit [CharZero K] in
lemma eta_pair_symmetric (a b : Vec K) : etaPair a b = etaPair b a := by
  simp [etaPair, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma direct_first_variation [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K) : nativeFirstVariation d kappa q p =
      directFirstVariation d kappa q p := by
  have hs (x : X) (r : Fin 6) :
      etaPair (nativeTheta d p x r) (nativeTheta d q x r) =
        etaPair (nativeTheta d q x r) (nativeTheta d p x r) := eta_pair_symmetric _ _
  unfold nativeFirstVariation nativeBilinear directFirstVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_add, biv_pair_add_right, Finset.sum_add_distrib, hs]
  ring
omit [AddCommGroup X] [CharZero K] in
lemma force_row_count [Fintype X] : Fintype.card (X × Coordinate) = 40 * Fintype.card X := by
  rw [Fintype.card_prod, coordinate_count, Nat.mul_comm]
lemma complete_quadratic_real_derivative [Fintype X] (d : Fin 4 → X) (kappa : ℝ)
    (q p : NativeField X ℝ) : HasDerivAt
    (fun epsilon : ℝ => completeQuadratic d kappa (q + epsilon • p))
    (nativeFirstVariation d kappa q p) 0 := by
  have he : (fun epsilon : ℝ => completeQuadratic d kappa (q + epsilon • p)) =
      (fun epsilon : ℝ => completeQuadratic d kappa q +
        epsilon * nativeFirstVariation d kappa q p +
        epsilon ^ 2 * completeQuadratic d kappa p) := by
    funext epsilon
    exact complete_quadratic_variation d kappa epsilon q p
  rw [he]
  convert ((hasDerivAt_const (0 : ℝ) (completeQuadratic d kappa q)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (nativeFirstVariation d kappa q p))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (completeQuadratic d kappa p)) using 1 <;>
    simp
  all_goals rfl
/-- **GAC2:full-coordinate-variational-force**
(the original full coordinate force from the complete quadratic action). -/
@[ledger "GAC2:full-coordinate-variational-force"]
theorem forceLaw : Statement.forceLaw := by
  intro X K _ _ _
  exact ⟨full_force_pairing,
    full_force_zero_iff,
    first_variation_symmetric,
    full_jacobian_symmetric,
    full_force_matrix,
    direct_first_variation,
    force_row_count,
    complete_quadratic_real_derivative⟩
/-! ## Non-vacuity -/
example : nativeFirstVariation (fun _ : Fin 4 => (PUnit.unit : PUnit))
    (1 / 101) constantBoostField constantBoostField = 2 / 101 := by decide +kernel
end Artform.Scores.GravityBridge.Native.Full40
