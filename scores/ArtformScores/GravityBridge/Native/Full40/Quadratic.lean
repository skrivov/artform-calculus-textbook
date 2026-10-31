import ArtformScores.GravityBridge.Native.Full40.QuadraticStatements
/-! # Complete original flat quadratic variation on periodic fields -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
omit [CharZero K] in
lemma lie_add (a b : Biv K) : lie (a + b) = lie a + lie b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lie] <;> ring
omit [CharZero K] in
lemma lie_smul (c : K) (a : Biv K) : lie (c • a) = c • lie a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lie]
omit [CharZero K] in
lemma bracket_matrix (a b : Biv K) : lie (bivBracket a b) = commutator (lie a) (lie b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lie, bivBracket, cross3, boostPart, spatialPart, commutator] <;> ring
omit [CharZero K] in
lemma bracket_add_left (a b c : Biv K) : bivBracket (a + b) c = bivBracket a c + bivBracket b c 
    := by
  funext i
  fin_cases i <;> simp [bivBracket, cross3, boostPart, spatialPart] <;> ring
omit [CharZero K] in
lemma bracket_add_right (a b c : Biv K) : bivBracket a (b + c) = bivBracket a b + bivBracket a c 
    := by
  funext i
  fin_cases i <;> simp [bivBracket, cross3, boostPart, spatialPart] <;> ring
omit [CharZero K] in
lemma bracket_smul_left (c : K) (a b : Biv K) : bivBracket (c • a) b = c • bivBracket a b := by
  funext i
  fin_cases i <;> simp [bivBracket, cross3, boostPart, spatialPart] <;> ring
omit [CharZero K] in
lemma bracket_smul_right (c : K) (a b : Biv K) : bivBracket a (c • b) = c • bivBracket a b := by
  funext i
  fin_cases i <;> simp [bivBracket, cross3, boostPart, spatialPart] <;> ring
omit [CharZero K] in
lemma star_bracket (a b : Biv K) : internalStar (bivBracket a b) = bivBracket a (internalStar b) 
    := by
  funext i
  fin_cases i <;> simp [internalStar, bivBracket, cross3, boostPart, spatialPart] <;> ring
omit [CharZero K] in
lemma invariant_biv_pair (a b c : Biv K) :
    bivPair (bivBracket a b) c + bivPair b (bivBracket a c) = 0 := by
  simp [bivPair, bivSign, bivBracket, cross3, boostPart, spatialPart, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma first_wedge_add (F G : Frame K) (i j : Fin 4) :
    firstWedge (F + G) i j = firstWedge F i j + firstWedge G i j := by
  funext a
  fin_cases a <;> simp [firstWedge, wedge] <;> ring
omit [CharZero K] in
lemma first_wedge_smul (c : K) (F : Frame K) (i j : Fin 4) :
    firstWedge (c • F) i j = c • firstWedge F i j := by
  funext a
  fin_cases a <;> simp [firstWedge, wedge] <;> ring
omit [CharZero K] in
lemma linear_complement_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    linearComplement d (q + p) x r = linearComplement d q x r + linearComplement d p x r := by
  simp only [linearComplement, Pi.add_apply, Prod.fst_add, first_wedge_add]
  module
omit [CharZero K] in
lemma linear_complement_smul (d : Fin 4 → X) (c : K) (q : NativeField X K)
    (x : X) (r : Fin 6) : linearComplement d (c • q) x r = c • linearComplement d q x r := by
  simp only [linearComplement, Pi.smul_apply, Prod.smul_fst, first_wedge_smul]
  module
omit [CharZero K] in
lemma native_v_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    nativeV d (q + p) x r = nativeV d q x r + nativeV d p x r := by
  simp only [nativeV, Pi.add_apply, Prod.snd_add]
  module
omit [CharZero K] in
lemma native_v_smul (d : Fin 4 → X) (c : K) (q : NativeField X K) (x : X) (r : Fin 6) :
    nativeV d (c • q) x r = c • nativeV d q x r := by
  simp only [nativeV, Pi.smul_apply, Prod.smul_snd]
  module
omit [CharZero K] in
lemma connection_complement_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    connectionComplement d (q + p) x r =
      connectionComplement d q x r + connectionComplement d p x r := by
  simp only [connectionComplement, native_v_add, bracket_add_left, neg_add]
omit [CharZero K] in
lemma connection_complement_smul (d : Fin 4 → X) (c : K) (q : NativeField X K)
    (x : X) (r : Fin 6) :
    connectionComplement d (c • q) x r = c • connectionComplement d q x r := by
  simp only [connectionComplement, native_v_smul, bracket_smul_left, smul_neg]
omit [CharZero K] in
lemma native_k_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    nativeK d (q + p) x r = nativeK d q x r + nativeK d p x r := by
  simp only [nativeK, linearCurvature, Pi.add_apply, Prod.snd_add]
  module
omit [CharZero K] in
lemma native_k_smul (d : Fin 4 → X) (c : K) (q : NativeField X K) (x : X) (r : Fin 6) :
    nativeK d (c • q) x r = c • nativeK d q x r := by
  simp only [nativeK, linearCurvature, Pi.smul_apply, Prod.smul_snd]
  module
omit [CharZero K] in
lemma native_theta_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    nativeTheta d (q + p) x r = nativeTheta d q x r + nativeTheta d p x r := by
  funext a
  simp only [nativeTheta, torsion, Pi.add_apply, Prod.fst_add, Prod.snd_add, lie_add,
    Matrix.add_apply]
  ring
omit [CharZero K] in
lemma native_theta_smul (d : Fin 4 → X) (c : K) (q : NativeField X K) (x : X) (r : Fin 6) :
    nativeTheta d (c • q) x r = c • nativeTheta d q x r := by
  funext a
  simp only [nativeTheta, torsion, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, lie_smul,
    Matrix.smul_apply, smul_eq_mul]
  ring
omit [CharZero K] in
lemma native_letters_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    nativeLetters d (q + p) x r = nativeLetters d q x r + nativeLetters d p x r := by
  funext i a
  fin_cases i <;> simp [nativeLetters] <;> ring
omit [CharZero K] in
lemma native_letters_smul (d : Fin 4 → X) (c : K) (q : NativeField X K) (x : X) (r : Fin 6) :
    nativeLetters d (c • q) x r = c • nativeLetters d q x r := by
  funext i a
  fin_cases i <;> simp [nativeLetters]
omit [CharZero K] in
lemma raw_contact_add_left (d : Fin 4 → X) (q p t : NativeField X K) (x : X) (r : Fin 6) :
    rawPlaquetteContact d (q + p) t x r =
      rawPlaquetteContact d q t x r + rawPlaquetteContact d p t x r := by
  simp only [rawPlaquetteContact, native_letters_add, Pi.add_apply, bracket_add_left]
  module
omit [CharZero K] in
lemma raw_contact_add_right (d : Fin 4 → X) (q p t : NativeField X K) (x : X) (r : Fin 6) :
    rawPlaquetteContact d q (p + t) x r =
      rawPlaquetteContact d q p x r + rawPlaquetteContact d q t x r := by
  simp only [rawPlaquetteContact, native_letters_add, Pi.add_apply, bracket_add_right]
  module
omit [CharZero K] in
lemma raw_contact_smul_left (d : Fin 4 → X) (c : K) (q p : NativeField X K)
    (x : X) (r : Fin 6) :
    rawPlaquetteContact d (c • q) p x r = c • rawPlaquetteContact d q p x r := by
  simp only [rawPlaquetteContact, native_letters_smul, Pi.smul_apply, bracket_smul_left]
  module
omit [CharZero K] in
lemma raw_contact_smul_right (d : Fin 4 → X) (c : K) (q p : NativeField X K)
    (x : X) (r : Fin 6) :
    rawPlaquetteContact d q (c • p) x r = c • rawPlaquetteContact d q p x r := by
  simp only [rawPlaquetteContact, native_letters_smul, Pi.smul_apply, bracket_smul_right]
  module
omit [CharZero K] in
lemma star_add (a b : Biv K) : internalStar (a + b) = internalStar a + internalStar b := by
  funext i
  fin_cases i <;> simp [internalStar, add_comm]
omit [CharZero K] in
lemma star_smul (c : K) (a : Biv K) : internalStar (c • a) = c • internalStar a := by
  funext i
  fin_cases i <;> simp [internalStar]
omit [CharZero K] in
lemma biv_pair_add_left (a b c : Biv K) : bivPair (a + b) c = bivPair a c + bivPair b c := by
  simp [bivPair, mul_add, add_mul, Finset.sum_add_distrib]
omit [CharZero K] in
lemma biv_pair_add_right (a b c : Biv K) : bivPair a (b + c) = bivPair a b + bivPair a c := by
  simp [bivPair, mul_add, Finset.sum_add_distrib]
omit [CharZero K] in
lemma biv_pair_smul_left (c : K) (a b : Biv K) : bivPair (c • a) b = c * bivPair a b := by
  simp [bivPair, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma biv_pair_smul_right (c : K) (a b : Biv K) : bivPair a (c • b) = c * bivPair a b := by
  simp [bivPair, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma eta_pair_add_left (a b c : Vec K) : etaPair (a + b) c = etaPair a c + etaPair b c := by
  simp [etaPair, mul_add, add_mul, Finset.sum_add_distrib]
omit [CharZero K] in
lemma eta_pair_add_right (a b c : Vec K) : etaPair a (b + c) = etaPair a b + etaPair a c := by
  simp [etaPair, mul_add, Finset.sum_add_distrib]
omit [CharZero K] in
lemma eta_pair_smul_left (c : K) (a b : Vec K) : etaPair (c • a) b = c * etaPair a b := by
  simp [etaPair, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma eta_pair_smul_right (c : K) (a b : Vec K) : etaPair a (c • b) = c * etaPair a b := by
  simp [etaPair, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma native_lu_add (d : Fin 4 → X) (q p : NativeField X K) (x : X) (r : Fin 6) :
    nativeLU d (q + p) x r = nativeLU d q x r + nativeLU d p x r := by
  rw [nativeLU, linear_complement_add, connection_complement_add]
  dsimp [nativeLU]
  abel
omit [CharZero K] in
lemma native_lu_smul (d : Fin 4 → X) (c : K) (q : NativeField X K) (x : X) (r : Fin 6) :
    nativeLU d (c • q) x r = c • nativeLU d q x r := by
  rw [nativeLU, linear_complement_smul, connection_complement_smul]
  dsimp [nativeLU]
  module
omit [CharZero K] in
lemma native_bilinear_add_left [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p t : NativeField X K) :
    nativeBilinear d kappa (q + p) t = nativeBilinear d kappa q t + nativeBilinear d kappa p t := by
  simp only [nativeBilinear, native_lu_add, raw_contact_add_left, star_add,
    biv_pair_add_left, biv_pair_add_right, native_theta_add, eta_pair_add_left,
    mul_add, Finset.sum_add_distrib]
  ring
omit [CharZero K] in
lemma native_bilinear_add_right [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p t : NativeField X K) :
    nativeBilinear d kappa q (p + t) = nativeBilinear d kappa q p + nativeBilinear d kappa q t := by
  simp only [nativeBilinear, native_k_add, raw_contact_add_right, star_add,
    biv_pair_add_right, native_theta_add, eta_pair_add_right,
    mul_add, Finset.sum_add_distrib]
  ring
omit [CharZero K] in
lemma native_bilinear_smul_left [Fintype X] (d : Fin 4 → X) (kappa c : K)
    (q p : NativeField X K) :
    nativeBilinear d kappa (c • q) p = c * nativeBilinear d kappa q p := by
  simp only [nativeBilinear, native_lu_smul, raw_contact_smul_left, star_smul,
    biv_pair_smul_left, biv_pair_smul_right, native_theta_smul, eta_pair_smul_left]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring
omit [CharZero K] in
lemma native_bilinear_smul_right [Fintype X] (d : Fin 4 → X) (kappa c : K)
    (q p : NativeField X K) :
    nativeBilinear d kappa q (c • p) = c * nativeBilinear d kappa q p := by
  simp only [nativeBilinear, native_k_smul, raw_contact_smul_right, star_smul,
    biv_pair_smul_right, native_theta_smul, eta_pair_smul_right]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring
omit [CharZero K] in
lemma complete_quadratic_variation [Fintype X] (d : Fin 4 → X) (kappa epsilon : K)
    (q p : NativeField X K) :
    completeQuadratic d kappa (q + epsilon • p) = completeQuadratic d kappa q +
      epsilon * nativeFirstVariation d kappa q p + epsilon ^ 2 * completeQuadratic d kappa p := by
  simp only [completeQuadratic, native_bilinear_add_left, native_bilinear_add_right,
    native_bilinear_smul_left, native_bilinear_smul_right, nativeFirstVariation]
  ring
lemma contact_is_original_reading (d : Fin 4 → X) (q : NativeField X K) (x : X) (r : Fin 6) :
    lie (rawPlaquetteContact d q q x r) =
      curvatureJet (orderedFourJet (fun a => lie (nativeLetters d q x r a))) 2 := by
  rw [ordered_curvature_second]
  simp only [rawPlaquetteContact, lie_smul, lie_add, bracket_matrix, orderedCommutators]
/-- **GAC2:complete-flat-quadratic-variation**
(complete original flat quadratic variation on periodic fields). -/
@[ledger "GAC2:complete-flat-quadratic-variation"]
theorem quadraticLaw : Statement.quadraticLaw := by
  intro X K _ _ _
  exact ⟨bracket_matrix,
    star_bracket,
    invariant_biv_pair,
    native_bilinear_add_left,
    native_bilinear_add_right,
    native_bilinear_smul_left,
    native_bilinear_smul_right,
    complete_quadratic_variation,
    contact_is_original_reading⟩
/-! ## Non-vacuity -/
def constantBoostField : NativeField PUnit ℚ := fun _ =>
  (0, fun i => if i = 0 then ![1, 0, 0, 0, 0, 0] else 0)
example : completeQuadratic (fun _ : Fin 4 => (PUnit.unit : PUnit))
    (1 / 101) constantBoostField = 1 / 101 := by decide +kernel
end Artform.Scores.GravityBridge.Native.Full40
