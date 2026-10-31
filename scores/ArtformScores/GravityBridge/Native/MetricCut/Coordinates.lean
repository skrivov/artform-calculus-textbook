import ArtformScores.GravityBridge.Native.MetricCut.CoordinatesStatements
/-! # The original metric Cauchy organization and exact inverses -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
variable {K : Type*} [Field K] [CharZero K]
open Matrix
omit [CharZero K] in
lemma dot3_add (a b c : SVec K) : dot3 a (b + c) = dot3 a b + dot3 a c := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
omit [CharZero K] in
lemma dot3_smul (a b : SVec K) (t : K) : dot3 a (t • b) = t * dot3 a b := by
  simp [dot3, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma dot3_symm (a b : SVec K) : dot3 a b = dot3 b a := by
  simp [dot3, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma outer3_mul (a b c : SVec K) : outer3 a b *ᵥ c = dot3 b c • a := by
  ext i
  simp [outer3, dot3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma outer3_trace (a b : SVec K) : trace (outer3 a b) = dot3 a b := rfl
omit [CharZero K] in
lemma projector3_k (k : SVec K) (hR : rho2 k ≠ 0) : projector3 k *ᵥ k = 0 := by
  rw [projector3, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outer3_mul]
  change k - (rho2 k)⁻¹ • (rho2 k • k) = 0
  rw [smul_smul, inv_mul_cancel₀ hR, one_smul, sub_self]
omit [CharZero K] in
lemma projector3_trace (k : SVec K) (hR : rho2 k ≠ 0) : trace (projector3 k) = 2 := by
  rw [projector3, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, outer3_trace]
  change (3 : K) - (rho2 k)⁻¹ * rho2 k = 2
  rw [inv_mul_cancel₀ hR]
  ring
omit [CharZero K] in
lemma spatial_gradient_k (j : K) (k u : SVec K) :
    spatialGradient j k u *ᵥ k = j • (dot3 k u • k + rho2 k • u) := by
  rw [spatialGradient, Matrix.smul_mulVec, Matrix.add_mulVec, outer3_mul, outer3_mul,
    dot3_symm u k]
  rfl
omit [CharZero K] in
lemma spatial_gradient_trace (j : K) (k u : SVec K) :
    trace (spatialGradient j k u) = 2 * j * dot3 k u := by
  rw [spatialGradient, Matrix.trace_smul, Matrix.trace_add, outer3_trace, outer3_trace,
    dot3_symm u k]
  ring
omit [CharZero K] in
lemma dot3_sub (a b c : SVec K) : dot3 a (b - c) = dot3 a b - dot3 a c := by
  simp [dot3, mul_sub, Finset.sum_sub_distrib]
omit [CharZero K] in
lemma dot3_self (k : SVec K) : dot3 k k = rho2 k := rfl
lemma coulomb3_compose (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (hj : j ≠ 0) (hR : rho2 k ≠ 0) (hq : q *ᵥ k = 0) :
    coulomb3 j k (spatialCompose j k q s u) = u := by
  have hm : spatialCompose j k q s u *ᵥ k =
      j • (dot3 k u • k + rho2 k • u) := by
    simp [spatialCompose, Matrix.add_mulVec, Matrix.smul_mulVec,
      projector3_k k hR, hq, spatial_gradient_k]
  rw [coulomb3, hm]
  simp only [dot3_smul, dot3_add, dot3_self]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
  field_simp [hj, hR]
  ring
lemma scalar3_compose (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (hR : rho2 k ≠ 0) (hq : q *ᵥ k = 0) (ht : trace q = 0) :
    scalar3 k (spatialCompose j k q s u) = s := by
  have hm : spatialCompose j k q s u *ᵥ k =
      j • (dot3 k u • k + rho2 k • u) := by
    simp [spatialCompose, Matrix.add_mulVec, Matrix.smul_mulVec,
      projector3_k k hR, hq, spatial_gradient_k]
  rw [scalar3, hm]
  simp only [spatialCompose, Matrix.trace_add, Matrix.trace_smul,
    projector3_trace k hR, spatial_gradient_trace, ht, dot3_smul, dot3_add, dot3_self]
  field_simp [hR]
  ring
-- The remainder is the original transverse, trace-free spatial metric.
omit [CharZero K] in
lemma spatial_recompose (j : K) (k : SVec K) (m : SMat K) :
    spatialCompose j k (tt3 j k m) (scalar3 k m) (coulomb3 j k m) = m := by
  unfold spatialCompose tt3
  abel
lemma tt3_transverse (j : K) (k : SVec K) (m : SMat K)
    (hj : j ≠ 0) (hR : rho2 k ≠ 0) : tt3 j k m *ᵥ k = 0 := by
  rw [tt3, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    projector3_k k hR, smul_zero, sub_zero, spatial_gradient_k]
  simp only [coulomb3, dot3_smul, dot3_sub, dot3_self]
  ext i
  simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  field_simp [hj, hR]
  ring
lemma tt3_trace (j : K) (k : SVec K) (m : SMat K)
    (hj : j ≠ 0) (hR : rho2 k ≠ 0) : trace (tt3 j k m) = 0 := by
  rw [tt3, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
    projector3_trace k hR, spatial_gradient_trace]
  simp only [scalar3, coulomb3, dot3_smul, dot3_sub, dot3_self]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring_nf
  field_simp [hj, hR]
  ring
lemma momentum_dot (j : K) (k : SVec K) (m : SMat K) (shift : SVec K)
    (hR : rho2 k ≠ 0) :
    dot3 k (momentum3 j k m shift) = -j * rho2 k * scalar3 k m := by
  simp only [momentum3, dot3_smul, dot3_add, dot3_sub, dot3_self, scalar3]
  field_simp [hR]
  ring
lemma momentum_scalar_return (j : K) (k : SVec K) (m : SMat K) (shift : SVec K)
    (hj2 : j * j = -1) (hR : rho2 k ≠ 0) :
    j * dot3 k (momentum3 j k m shift) / rho2 k = scalar3 k m := by
  rw [momentum_dot j k m shift hR]
  calc
    j * (-j * rho2 k * scalar3 k m) / rho2 k =
        -(j * j) * scalar3 k m := by field_simp
    _ = scalar3 k m := by rw [hj2]; ring
lemma shift_return (j : K) (k : SVec K) (m : SMat K) (shift : SVec K)
    (hj : j ≠ 0) (hj2 : j * j = -1) (hR : rho2 k ≠ 0) :
    (2 / rho2 k) • (momentum3 j k m shift -
      (dot3 k (momentum3 j k m shift) / rho2 k) • k) +
      coulomb3 j k m +
      (j * ((dot3 k shift - dot3 k (coulomb3 j k m)) / (j * rho2 k))) • k =
      shift := by
  have hjSq : j ^ 2 = -1 := by simpa [pow_two] using hj2
  rw [momentum_dot j k m shift hR]
  simp only [momentum3, scalar3, coulomb3, dot3_smul, dot3_sub, dot3_self]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring_nf
  field_simp [hj, hR]
  ring_nf
  simp only [hjSq]
  ring
lemma reconstruct_organize (j : K) (k : SVec K) (x : CauchyData K)
    (hj : j ≠ 0) (hj2 : j * j = -1) (hR : rho2 k ≠ 0) :
    reconstruct j k (organize j k x) = x := by
  cases x
  apply CauchyData.ext
  · simp only [reconstruct, organize]
    rw [mul_div_cancel_left₀ _ hR, spatial_recompose]
  · simp only [reconstruct, organize]
    rw [momentum_scalar_return j k _ _ hj2 hR, spatial_recompose]
  · exact shift_return j k _ _ hj hj2 hR
  · rfl
  · rfl
  · rfl
lemma tt3_compose (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (hj : j ≠ 0) (hR : rho2 k ≠ 0) (hq : q *ᵥ k = 0) (ht : trace q = 0) :
    tt3 j k (spatialCompose j k q s u) = q := by
  rw [tt3, scalar3_compose j k u q s hR hq ht,
    coulomb3_compose j k u q s hj hR hq]
  unfold spatialCompose
  abel
lemma momentum_compose (j : K) (k u b : SVec K) (q : SMat K) (s chi : K)
    (hj2 : j * j = -1) (hR : rho2 k ≠ 0) (hq : q *ᵥ k = 0)
    (ht : trace q = 0) (hb : dot3 k b = 0) :
    momentum3 j k (spatialCompose j k q s u) (b + u + (j * chi) • k) =
      (rho2 k / 2) • b - (j * s) • k := by
  have hjSq : j ^ 2 = -1 := by simpa [pow_two] using hj2
  have hm : spatialCompose j k q s u *ᵥ k =
      j • (dot3 k u • k + rho2 k • u) := by
    simp [spatialCompose, Matrix.add_mulVec, Matrix.smul_mulVec,
      projector3_k k hR, hq, spatial_gradient_k]
  rw [momentum3, hm]
  simp only [spatialCompose, Matrix.trace_add, Matrix.trace_smul,
    projector3_trace k hR, spatial_gradient_trace, ht, dot3_smul, dot3_add, hb,
    dot3_self]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [hjSq]
  ring
omit [CharZero K] in
lemma transverse_part_dot (k w : SVec K) (hR : rho2 k ≠ 0) :
    dot3 k ((2 / rho2 k) • (w - (dot3 k w / rho2 k) • k)) = 0 := by
  simp only [dot3_smul, dot3_sub, dot3_self]
  field_simp
  simp
omit [CharZero K] in
lemma temporal_return (j : K) (k w v : SVec K) (chi : K)
    (hj : j ≠ 0) (hR : rho2 k ≠ 0) :
    (dot3 k ((2 / rho2 k) • (w - (dot3 k w / rho2 k) • k) +
      v + (j * chi) • k) - dot3 k v) / (j * rho2 k) = chi := by
  rw [dot3_add, dot3_add, transverse_part_dot k w hR, dot3_smul, dot3_self]
  field_simp
  ring
lemma organize_reconstruct (j : K) (k : SVec K) (z : Organized K)
    (hj : j ≠ 0) (hj2 : j * j = -1) (hR : rho2 k ≠ 0)
    (hq : z.tt *ᵥ k = 0) (ht : trace z.tt = 0)
    (hp : z.ttVelocity *ᵥ k = 0) (hpt : trace z.ttVelocity = 0) :
    organize j k (reconstruct j k z) = z := by
  have hjSq : j ^ 2 = -1 := by simpa [pow_two] using hj2
  apply Organized.ext
  · exact tt3_compose j k _ _ _ hj hR hq ht
  · exact tt3_compose j k _ _ _ hj hR hp hpt
  · exact coulomb3_compose j k _ _ _ hj hR hq
  · exact coulomb3_compose j k _ _ _ hj hR hp
  · simp only [organize, reconstruct]
    rw [coulomb3_compose j k _ _ _ hj hR hp]
    exact temporal_return j k _ _ _ hj hR
  · rfl
  · rfl
  · rfl
  · simp only [organize, reconstruct]
    rw [scalar3_compose j k _ _ _ hR hq ht]
    field_simp
  · simp only [organize, reconstruct]
    rw [momentum_compose j k _ _ _ _ _ hj2 hR hp hpt (transverse_part_dot _ _ hR)]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring_nf
    simp only [hjSq]
    ring
lemma tt3_symmetric (j : K) (k : SVec K) (m : SMat K)
    (hm : ∀ i l, m i l = m l i) : ∀ i l, tt3 j k m i l = tt3 j k m l i := by
  intro i l
  simp only [tt3, projector3, spatialGradient, outer3, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hil : i = l
  · subst l; rfl
  · simp only [hil, Ne.symm hil, ite_false]
    rw [hm i l]
    ring
omit [CharZero K] in
lemma spatial_compose_symmetric (j : K) (k u : SVec K) (q : SMat K) (s : K)
    (hq : ∀ i l, q i l = q l i) :
    ∀ i l, spatialCompose j k q s u i l = spatialCompose j k q s u l i := by
  intro i l
  simp only [spatialCompose, projector3, spatialGradient, outer3, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hil : i = l
  · subst l; rfl
  · simp only [hil, Ne.symm hil, ite_false]
    rw [hq i l]
    ring
lemma organize_symmetric (j : K) (k : SVec K) (x : CauchyData K)
    (hx : symmetricCauchy x) : symmetricOrganized (organize j k x) :=
  ⟨tt3_symmetric j k x.spatial hx.1, tt3_symmetric j k x.spatialVelocity hx.2⟩
omit [CharZero K] in
lemma reconstruct_symmetric (j : K) (k : SVec K) (z : Organized K)
    (hz : symmetricOrganized z) : symmetricCauchy (reconstruct j k z) :=
  ⟨spatial_compose_symmetric j k _ _ _ hz.1,
    spatial_compose_symmetric j k _ _ _ hz.2⟩
-- This is the fixed physical target; its entries are not free coordinate jets.
/-- **GAC2:metric-cauchy-organization**
(the original metric cauchy organization and exact inverses). -/
@[ledger "GAC2:metric-cauchy-organization"]
theorem coordinatesLaw : Statement.coordinatesLaw := by
  intro K _ _
  exact ⟨coulomb3_compose,
    scalar3_compose,
    tt3_transverse,
    tt3_trace,
    tt3_symmetric,
    spatial_recompose,
    reconstruct_organize,
    organize_reconstruct,
    organize_symmetric,
    reconstruct_symmetric⟩
/-! ## Non-vacuity -/
example : (Complex.I : ℂ) ≠ 0 ∧ Complex.I * Complex.I = -1 ∧
    rho2 (![1, 2, 3] : SVec ℂ) = 14 := by
  norm_num [rho2, dot3, Fin.sum_univ_succ]
-- A nonzero original physical scalar target and all four spacetime rows.
example : let x := fixedN4Target Complex.I (![1, 2, 3] : SVec ℂ) 0 0 1 0
    x.spatial 0 0 = 4 ∧ x.shiftVelocity 2 = -6 * Complex.I ∧
    reconstruct Complex.I ![1, 2, 3] (organize Complex.I ![1, 2, 3] x) = x := by
  dsimp only
  refine ⟨by norm_num [fixedN4Target], by norm_num [fixedN4Target]; ring, ?_⟩
  apply reconstruct_organize
  · exact Complex.I_ne_zero
  · exact Complex.I_mul_I
  · norm_num [rho2, dot3, Fin.sum_univ_succ]
end Artform.Scores.GravityBridge.Native.MetricCut
