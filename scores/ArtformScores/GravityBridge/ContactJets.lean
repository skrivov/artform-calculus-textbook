import ArtformScores.GravityBridge.ContactJetStatements
import ArtformScores.GravityBridge.Kernels
import ArtformScores.GravityBridge.Native.Preparation

/-! # Source jets retain preparation, measure and input contact terms -/

namespace Artform.Scores.GravityBridge

open Polynomial

noncomputable section

lemma polynomial_processing_jets {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (eX : X ≃ X') (eY : Y ≃ Y') (μ : X → Polynomial ℚ) (ν : Y → Polynomial ℚ)
    (ψ : X → Polynomial ℚ) (a : BoundaryKernel X Y (Polynomial ℚ))
    (φ : Y → Polynomial ℚ) (n : ℕ) (z : ℚ) :
    sourceJet n
      (closedAmplitude (transportFunction eX μ) (transportFunction eY ν)
        (transportFunction eX ψ) (transportKernel eX eY a) (transportFunction eY φ)) z =
      sourceJet n (closedAmplitude μ ν ψ a φ) z := by
  rw [closedAmplitude_transport]


lemma second_product_jet (p q : Polynomial ℚ) (z : ℚ) :
    sourceJet 2 (p * q) z = sourceJet 2 p z * sourceJet 0 q z +
      2 * sourceJet 1 p z * sourceJet 1 q z + sourceJet 0 p z * sourceJet 2 q z := by
  simp [sourceJet, Function.iterate_succ_apply', derivative_mul, derivative_add]
  ring

lemma quadratic_jets (c z : ℚ) :
    sourceJet 0 (C c * X ^ 2) z = c * z ^ 2 ∧
    sourceJet 1 (C c * X ^ 2) z = 2 * c * z ∧
    sourceJet 2 (C c * X ^ 2) z = 2 * c := by
  norm_num [sourceJet, Function.iterate_succ_apply', derivative_mul,
    derivative_pow, derivative_X, derivative_C, eval_mul, eval_pow]
  all_goals (ring_nf; simp)

lemma native_contact_jet (z : ℚ) :
    completeInputPolynomial.eval z =
      Native.completeConnectionAction z (Native.connectionPreparation z) ∧
    connectionInputPolynomial.eval z =
      Native.connectionAction z (Native.connectionPreparation z) ∧
    sourceJet 2 completeInputPolynomial z = -4 / 103 ∧
    sourceJet 2 connectionInputPolynomial z = 8 / 10403 ∧
    sourceJet 2 completeInputPolynomial z - sourceJet 2 connectionInputPolynomial z = -4 / 101 := by
  rw [Native.completeConnectionAction_prepared, Native.connectionAction_prepared]
  have hc : sourceJet 2 completeInputPolynomial z = -4 / 103 := by
    convert (quadratic_jets (-2 / 103) z).2.2 using 1 <;> norm_num [completeInputPolynomial]
  have ht : sourceJet 2 connectionInputPolynomial z = 8 / 10403 := by
    convert (quadratic_jets (4 / 10403) z).2.2 using 1 <;> norm_num [connectionInputPolynomial]
  refine ⟨?_, ?_, hc, ht, ?_⟩
  · simp [completeInputPolynomial]; ring
  · simp [connectionInputPolynomial]; ring
  · rw [hc, ht]; norm_num

/-- **GAC:source-contact-jets** (complete polynomial jets and native contact contribution). -/
@[ledger "GAC:source-contact-jets"]
theorem sourceContactJets : Statement.sourceContactJets := by
  refine ⟨?_, second_product_jet, native_contact_jet⟩
  intro X X' Y Y' _ _ _ _ eX eY μ ν ψ a φ n z
  exact polynomial_processing_jets eX eY μ ν ψ a φ n z

/-! ## Non-vacuity -/

example : sourceJet 0 (0 : Polynomial ℚ) 0 = sourceJet 0 (X ^ 3) 0 ∧
    sourceJet 1 (0 : Polynomial ℚ) 0 = sourceJet 1 (X ^ 3) 0 ∧
    sourceJet 2 (0 : Polynomial ℚ) 0 = sourceJet 2 (X ^ 3) 0 ∧
    (0 : Polynomial ℚ).eval 1 ≠ (X ^ 3 : Polynomial ℚ).eval 1 := by
  norm_num [sourceJet, Function.iterate_succ_apply', derivative_pow]

def polynomialMeasure (i : Fin 2) : Polynomial ℚ := if i = 0 then 1 else X ^ 2

def polynomialSelect : BoundaryKernel Unit (Fin 2) (Polynomial ℚ) :=
  fun _ i => if i = 0 then 1 else 0

example :
    sourceJet 2 (closedAmplitude (fun _ : Unit => (1 : Polynomial ℚ)) polynomialMeasure
      (fun _ => 1) polynomialSelect (fun _ => 1)) 0 = 0 ∧
    sourceJet 2 (closedAmplitude (fun _ : Unit => (1 : Polynomial ℚ)) polynomialMeasure
      (fun _ => 1)
      (transportKernel (Equiv.refl Unit) (Equiv.swap (0 : Fin 2) 1) polynomialSelect)
      (fun _ => 1)) 0 = 2 := by
  norm_num [closedAmplitude, polynomialMeasure, polynomialSelect, transportKernel,
    Fin.sum_univ_two, Equiv.swap_apply_def, sourceJet, Function.iterate_succ_apply',
    derivative_pow]

example : sourceJet 2 completeInputPolynomial (23 / 10) = -4 / 103 :=
  (native_contact_jet (23 / 10)).2.2.1

end

end Artform.Scores.GravityBridge
