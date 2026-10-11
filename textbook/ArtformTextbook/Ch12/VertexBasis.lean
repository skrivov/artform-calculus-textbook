import ArtformTextbook.Ch12.VertexCensus

/-!
# The eight states are a basis

* In the book's order the eight states are independent: each has a coefficient `±1` on an
  occupation table where the other seven vanish (`Vertex.eight_linearIndependent_book`).
* A change of the order of the modes conjugates every creation and annihilation by the diagonal
  matrix of signs `Σ` (Proposition 11.11), so in any order each of the eight states is `±Σ` times
  the same state in the book's order (`Vertex.eight_change`), and the eight stay independent.
* The colourless states of one vertex are spanned by the eight for the cube group and the
  icosahedral group (eight independent invariants in a space of dimension eight), and by the six
  built from `ε` for `SU(3)`, `C₃ × A₅` and Valentiner's group: each of these contains `ω 1`, which
  multiplies the pair by `ω²` and the paired holes by `ω`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open FockCalc Spin

namespace Vertex

/-! ### Independence in the book's order -/

/-- The pivot masks of the eight states: the empty table, `{(1,↑), (1,↓)}`, `{(1,↑), (2,↑), (3,↑)}`,
`{(1,↑), (2,↑), (3,↓)}`, `{(1,↑), (2,↓), (3,↓)}`, `{(1,↓), (2,↓), (3,↓)}`, all but `(1,↑), (1,↓)`,
and all. -/
def pivot : Fin 8 → ℕ := ![0, 3, 21, 37, 41, 42, 60, 63]

theorem pivot_spec : ∀ i j : Fin 8, Vec.sumAt 6 (pivot j) (eightVec i) = 0 ↔ i ≠ j := by
  decide +kernel

theorem eight_linearIndependent_book : LinearIndependent ℂ (eight bookOrd) := by
  have h := Vec.linearIndependent numbering eightVec pivot
    (fun i => by fin_cases i <;> decide) pivot_spec
  convert h using 1
  funext i
  exact eight_eq i

/-! ### A change of order -/

theorem diagonal_mulVec_ket {M : Type*} [Fintype M] [DecidableEq M] (d : Finset M → ℂ)
    (n : Finset M) : Matrix.diagonal d *ᵥ Fock.ket n = d n • Fock.ket n := by
  funext n'
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Fock.ket, Pi.single_apply]
  split_ifs with h
  · rw [h]
  · simp

section Change

variable (ord : LinearOrder (Fin 3 × Fin 2))

/-- The matrix of signs from the book's order to `ord`. -/
noncomputable def sig : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ :=
  Fock.orderSigma bookOrd ord

theorem sig_mul_sig : sig ord * sig ord = 1 := Fock.orderSigma_mul_self _ _

theorem creation_sig (m : Fin 3 × Fin 2) :
    Fock.creation ord m = sig ord * Fock.creation bookOrd m * sig ord := by
  rw [Fock.creation_change bookOrd ord, Fock.orderSigma_inv]
  rfl

theorem annihilation_sig (m : Fin 3 × Fin 2) :
    Fock.annihilation ord m = sig ord * Fock.annihilation bookOrd m * sig ord := by
  rw [Fock.annihilation_change bookOrd ord, Fock.orderSigma_inv]
  rfl

theorem sig_ket_empty : sig ord *ᵥ Fock.ket ∅ = Fock.ket ∅ := by
  rw [sig, Fock.orderSigma, diagonal_mulVec_ket]
  simp [Fock.orderSign]

/-- The sign of the full table under the change of order. -/
noncomputable def sigFull : ℂ := Fock.orderSign bookOrd ord Finset.univ

theorem sig_full : sig ord *ᵥ full = sigFull ord • full := by
  rw [sig, Fock.orderSigma, full, diagonal_mulVec_ket]
  rfl

theorem sigFull_sq : sigFull ord * sigFull ord = 1 :=
  Fock.orderSign_sq bookOrd ord Finset.univ

theorem conj_two (A B : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ) :
    (sig ord * A * sig ord) * (sig ord * B * sig ord) = sig ord * (A * B) * sig ord := by
  have h := sig_mul_sig ord
  calc (sig ord * A * sig ord) * (sig ord * B * sig ord)
      = sig ord * A * (sig ord * sig ord) * B * sig ord := by simp only [mul_assoc]
    _ = sig ord * (A * B) * sig ord := by rw [h, mul_one, mul_assoc (sig ord) A B]

theorem conj_three (A B C : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ) :
    (sig ord * A * sig ord) * (sig ord * B * sig ord) * (sig ord * C * sig ord) =
      sig ord * (A * B * C) * sig ord := by
  rw [conj_two, conj_two]

theorem conj_mulVec_empty (A : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ) :
    (sig ord * A * sig ord) *ᵥ Fock.ket ∅ = sig ord *ᵥ (A *ᵥ Fock.ket ∅) := by
  rw [← Matrix.mulVec_mulVec, sig_ket_empty, ← Matrix.mulVec_mulVec]

theorem conj_mulVec_full (A : Matrix (Finset (Fin 3 × Fin 2)) (Finset (Fin 3 × Fin 2)) ℂ) :
    (sig ord * A * sig ord) *ᵥ full = sigFull ord • (sig ord *ᵥ (A *ᵥ full)) := by
  rw [← Matrix.mulVec_mulVec, sig_full, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

theorem pair_change : pair ord = sig ord *ᵥ pair bookOrd := by
  simp only [pair, creation_sig ord, conj_two, conj_mulVec_empty, Matrix.mulVec_sum]

theorem epsState_change (s₁ s₂ s₃ : Fin 2) :
    epsState ord s₁ s₂ s₃ = sig ord *ᵥ epsState bookOrd s₁ s₂ s₃ := by
  simp only [epsState, creation_sig ord, conj_three, conj_mulVec_empty, Matrix.mulVec_sum,
    Matrix.mulVec_smul]

theorem quartet_change (m : Fin 4) : quartet ord m = sig ord *ᵥ quartet bookOrd m := by
  fin_cases m
  · simp only [quartet, Fin.zero_eta, Matrix.cons_val_zero, creation_sig ord, conj_three,
      conj_mulVec_empty]
  · simp only [quartet, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      epsState_change ord, Matrix.mulVec_smul]
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val, epsState_change ord,
      Matrix.mulVec_smul]
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val, creation_sig ord, conj_three,
      conj_mulVec_empty]

theorem holes_change : holes ord = sigFull ord • (sig ord *ᵥ holes bookOrd) := by
  simp only [holes, annihilation_sig ord, conj_two, conj_mulVec_full, Matrix.mulVec_sum,
    Finset.smul_sum]

theorem full_change : full = sigFull ord • (sig ord *ᵥ full) := by
  rw [sig_full, smul_smul, sigFull_sq, one_smul]

theorem empty_change : empty = sig ord *ᵥ empty := by
  rw [empty, sig_ket_empty]

/-- The sign of each of the eight states under the change of order. -/
noncomputable def eightSign (i : Fin 8) : ℂ := if i = 6 ∨ i = 7 then sigFull ord else 1

/-- In any order each of the eight states is `±Σ` times the same state in the book's order. -/
theorem eight_change (i : Fin 8) :
    eight ord i = eightSign ord i • (sig ord *ᵥ eight bookOrd i) := by
  have h1 : ∀ j : Fin 8, j ≠ 6 → j ≠ 7 → eightSign ord j = 1 := by
    intro j h6 h7
    simp [eightSign, h6, h7]
  have h6 : eightSign ord 6 = sigFull ord := by simp [eightSign]
  have h7 : eightSign ord 7 = sigFull ord := by simp [eightSign]
  fin_cases i
  · change empty = eightSign ord 0 • (sig ord *ᵥ empty)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact empty_change ord
  · change pair ord = eightSign ord 1 • (sig ord *ᵥ pair bookOrd)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact pair_change ord
  · change quartet ord 0 = eightSign ord 2 • (sig ord *ᵥ quartet bookOrd 0)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact quartet_change ord 0
  · change quartet ord 1 = eightSign ord 3 • (sig ord *ᵥ quartet bookOrd 1)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact quartet_change ord 1
  · change quartet ord 2 = eightSign ord 4 • (sig ord *ᵥ quartet bookOrd 2)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact quartet_change ord 2
  · change quartet ord 3 = eightSign ord 5 • (sig ord *ᵥ quartet bookOrd 3)
    rw [h1 _ (by decide) (by decide), one_smul]
    exact quartet_change ord 3
  · change holes ord = eightSign ord 6 • (sig ord *ᵥ holes bookOrd)
    rw [h6]
    exact holes_change ord
  · change full = eightSign ord 7 • (sig ord *ᵥ full)
    rw [h7]
    exact full_change ord

theorem sig_injective : Function.Injective (Matrix.toLin' (sig ord)) := by
  intro a b h
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  have := congrArg (fun v => sig ord *ᵥ v) h
  simpa [Matrix.mulVec_mulVec, sig_mul_sig] using this

theorem eightSign_ne_zero (i : Fin 8) : eightSign ord i ≠ 0 := by
  unfold eightSign
  split_ifs
  · intro h
    have := sigFull_sq ord
    rw [h, zero_mul] at this
    exact zero_ne_one this
  · exact one_ne_zero

/-- In any order of the six modes the eight states are linearly independent. -/
theorem eight_linearIndependent : LinearIndependent ℂ (eight ord) := by
  have h1 := eight_linearIndependent_book.map' (Matrix.toLin' (sig ord))
    (LinearMap.ker_eq_bot.mpr (sig_injective ord))
  have h2 := h1.units_smul fun i => Units.mk0 (eightSign ord i) (eightSign_ne_zero ord i)
  convert h2 using 1
  funext i
  rw [eight_change ord i]
  rfl

end Change

end Vertex

end Artform
