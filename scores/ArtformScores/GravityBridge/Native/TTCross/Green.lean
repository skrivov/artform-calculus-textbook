import ArtformScores.GravityBridge.Native.TTCross.GreenStatements

/-! # Full four-jet scalar current and its prepared pullback -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma complete_four_jet_Green (a : K) (x y : Fin 5 → K) :
    scalarGreen a (nextFour x) (firstFour y) + scalarGreen a (firstFour x) (nextFour y) =
      x 0 * scalarRow a y - scalarRow a x * y 0 := by
  norm_num [scalarGreen, firstFour, nextFour, scalarRow]
  ring

lemma prepared_Green_pullback (a : K) (ha : a ≠ 0) (u v : Fin 2 → K) :
    scalarGreen a (preparedJet a u) (preparedJet a v) =
      -(5 / 2 : K) * (u 0 * v 1 - u 1 * v 0) := by
  norm_num [scalarGreen, preparedJet]
  field_simp
  ring

omit [CharZero K] in
lemma full_Green_source_contact (a : K) (x y : Fin 5 → K) (f g : K)
    (hx : scalarRow a x = f) (hy : scalarRow a y = g) :
    scalarGreen a (nextFour x) (firstFour y) + scalarGreen a (firstFour x) (nextFour y) =
      x 0 * g - f * y 0 := by rw [complete_four_jet_Green, hx, hy]

lemma prepared_source_contact_cancels (a : K) (u v : Fin 2 → K) :
    preparedJet a u 0 * (-2 * a ^ 2 * v 1) - (-2 * a ^ 2 * u 1) * preparedJet a v 0 = 0 := by
  simp only [preparedJet, Matrix.cons_val_zero]
  ring

/-- **GAC2:native-scalar-fourjet-current**
(full four-jet scalar current and its prepared pullback). -/
@[ledger "GAC2:native-scalar-fourjet-current"]
theorem greenLaw : Statement.greenLaw := by
  intro K _ _
  exact ⟨complete_four_jet_Green,
    prepared_Green_pullback,
    full_Green_source_contact,
    prepared_source_contact_cancels⟩

/-! ## Non-vacuity -/
example : scalarGreen (1 : ℚ) (preparedJet 1 ![1, 0]) (preparedJet 1 ![0, 1]) = -5 / 2 := by
  norm_num [scalarGreen, preparedJet]

end Artform.Scores.GravityBridge.Native.TTCross
