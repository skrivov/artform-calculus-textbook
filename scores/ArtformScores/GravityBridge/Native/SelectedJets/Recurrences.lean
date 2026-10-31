import ArtformScores.GravityBridge.Native.SelectedJets.RecurrencesStatements

/-! # Unique coupled selected-jet recurrences for the fixed reference -/

namespace Artform.Scores.GravityBridge.Native.SelectedJets

open Matrix



open Matrix
lemma SelectedJet.ext {x y : SelectedJet} (hy : x.y = y.y)
    (h1 : x.p1 = y.p1) (h2 : x.p2 = y.p2) (h3 : x.n1 = y.n1)
    (h4 : x.n2 = y.n2) : x = y := by
  cases x; cases y; simp_all

lemma principal_both_inverse :
    principal * principalInverse = 1 ∧ principalInverse * principal = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [principal, principalInverse, outerK, hd, dd, k, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

lemma selected_y_unique (y : Vec3) (hy : principal *ᵥ y = (101 / 490 : ℚ) • selectedU) :
    y = selectedJet.y := by
  have h := congrArg (fun z => principalInverse *ᵥ z) hy
  rw [Matrix.mulVec_mulVec, principal_both_inverse.2, Matrix.one_mulVec,
    Matrix.mulVec_smul] at h
  exact h

lemma selected_jet_solves : jetEquations selectedJet := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · change principal *ᵥ ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, principal_both_inverse.1, Matrix.one_mulVec]
  · dsimp only [selectedJet]
    norm_num [dd]
    ring
  · dsimp only [selectedJet]
    ring
  · dsimp only [selectedJet]
    ring

lemma selected_jet_unique (s : SelectedJet) (hs : jetEquations s) : s = selectedJet := by
  have hy := selected_y_unique s.y hs.1
  have ht := selected_jet_solves
  apply SelectedJet.ext hy
  · have h := hs.2.1
    rw [hy] at h
    have ht' := ht.2.1
    norm_num [dd] at h ht'
    linear_combination (10300 / 71407) * (h - ht')
  · have h := hs.2.2.1
    rw [hy] at h
    linear_combination (1 / 7 : ℚ) * (h - ht.2.2.1)
  · exact hs.2.2.2.1.trans (by rw [hy]; exact ht.2.2.2.1.symm)
  · have hn : s.n1 = selectedJet.n1 :=
      hs.2.2.2.1.trans (by rw [hy]; exact ht.2.2.2.1.symm)
    have h := hs.2.2.2.2
    rw [hy, hn] at h
    linear_combination (1 / 14 : ℚ) * (h - ht.2.2.2.2)

/-- **GAC2:selected-jet-coupled-recurrences**
(unique coupled selected-jet recurrences for the fixed reference). -/
@[ledger "GAC2:selected-jet-coupled-recurrences"]
theorem recurrencesLaw : Statement.recurrencesLaw := by
  exact ⟨principal_both_inverse,
    selected_y_unique,
    selected_jet_solves,
    selected_jet_unique⟩

/-! ## Non-vacuity -/

example : jetEquations selectedJet ∧ selectedJet.y 0 ≠ 0 := by
  refine ⟨selected_jet_solves, ?_⟩
  norm_num [selectedJet, principalInverse, outerK, selectedU, k, hd, dd, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.one_apply]

end Artform.Scores.GravityBridge.Native.SelectedJets
