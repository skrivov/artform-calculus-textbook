import ArtformScores.GravityBridge.Native.Full40.PlaquetteStatements

/-! # Ordered native plaquette through quadratic degree -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma four_jet_first (X : Fin 4 → Matrix4 K) :
    orderedFourJet X 0 = 1 ∧ orderedFourJet X 1 = firstSum X := by
  simp [orderedFourJet, jetProduct, exponentialJet, firstSum, add_assoc, add_comm]
lemma four_jet_second (X : Fin 4 → Matrix4 K) :
    orderedFourJet X 2 =
      (1 / 2 : K) • (X 0 * X 0 + X 1 * X 1 + X 2 * X 2 + X 3 * X 3) +
        orderedPairs X := by
  simp only [orderedFourJet, jetProduct, exponentialJet, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.mul_one, Matrix.one_mul]
  ext i j
  simp [orderedPairs, Matrix.mul_apply, Fin.sum_univ_succ]
  ring
omit [CharZero K] in
lemma inverse_jet_left (J : Jet2 K) (hJ : J 0 = 1) :
    jetProduct (inverseJetAtOne J) J = ![1, 0, 0] := by
  funext i
  fin_cases i
  · simp [jetProduct, inverseJetAtOne, hJ]
  · simp [jetProduct, inverseJetAtOne, hJ]
  · simp [jetProduct, inverseJetAtOne, hJ]
    abel
omit [CharZero K] in
lemma inverse_jet_right (J : Jet2 K) (hJ : J 0 = 1) :
    jetProduct J (inverseJetAtOne J) = ![1, 0, 0] := by
  funext i
  fin_cases i
  · simp [jetProduct, inverseJetAtOne, hJ]
  · simp [jetProduct, inverseJetAtOne, hJ]
  · simp [jetProduct, inverseJetAtOne, hJ]
    abel
lemma ordered_curvature_second (X : Fin 4 → Matrix4 K) :
    curvatureJet (orderedFourJet X) 2 = (-1 / 2 : K) • orderedCommutators X := by
  have h1 := (four_jet_first X).2
  dsimp [curvatureJet, inverseJetAtOne]
  rw [h1, four_jet_second]
  ext i j
  simp [firstSum, orderedPairs, orderedCommutators, commutator,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring
lemma plaquette_curvature_first (Al SlAk SkAl Ak : Matrix4 K) :
    curvatureJet (orderedFourJet (plaquetteLetters Al SlAk SkAl Ak)) 1 =
      SlAk - Ak - (SkAl - Al) := by
  dsimp [curvatureJet, inverseJetAtOne]
  rw [(four_jet_first _).2]
  ext i j
  simp [firstSum, plaquetteLetters]
  ring

/-- **GAC2:native-ordered-plaquette-jet**
(ordered native plaquette through quadratic degree). -/
@[ledger "GAC2:native-ordered-plaquette-jet"]
theorem plaquetteLaw : Statement.plaquetteLaw := by
  intro K _ _
  exact ⟨four_jet_first,
    four_jet_second,
    inverse_jet_left,
    inverse_jet_right,
    ordered_curvature_second,
    plaquette_curvature_first⟩

/-! ## Non-vacuity -/
def jetWitnessA : Matrix4 ℚ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def jetWitnessB : Matrix4 ℚ := !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0]
example : commutator jetWitnessA jetWitnessB 1 2 = 1 ∧
    commutator jetWitnessB jetWitnessA 1 2 = -1 := by decide +kernel

end Artform.Scores.GravityBridge.Native.Full40
