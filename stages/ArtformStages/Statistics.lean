import ArtformStages.TheWalk

/-!
# Statistics

Finding 477 of the research ledger on a layered universe: asked a lowest level, a charge whose
walk has levels of both signs takes the alternating sign. The levels of one charge are finitely
many real numbers `μ₁, …, μ_K`. An occupation gives each level a whole number of charges, any
number with the symmetric sign and `0` or `1` with the alternating sign. Its energy is the sum of
the levels, each counted as often as it is occupied. The sea fills every level below zero once,
and no other.

* `symmetric_no_lowest` (ST1): if some level is below zero, then for every number `M` some
  occupation with the symmetric sign has an energy below `M`.
* `alternating_energy_ge`, `sea_energy` (ST2): every occupation with the alternating sign has an
  energy at least the sum of the levels below zero, and the sea, an occupation with the
  alternating sign, has exactly that energy.
* `walk_level_signs` (ST3): for a coin angle `μ` strictly between `0` and `π / 2` and every wave
  number `k`, the walk's table has a level `e^{-iε}` with `ε` strictly between `0` and `π`, and
  its pair `e^{iε}`.

None of this is new: it is Dirac's sea, read on finitely many levels.
-/

open scoped Real

namespace Artform.Stages

/-- The energy of an occupation `n` of the levels `μ`: the sum of the levels, each counted as
often as it is occupied. -/
def occupationEnergy {K : ℕ} (μ : Fin K → ℝ) (n : Fin K → ℕ) : ℝ := ∑ i, (n i : ℝ) * μ i

/-- An occupation with the alternating sign: `0` or `1` on each level. -/
def IsAlternating {K : ℕ} (n : Fin K → ℕ) : Prop := ∀ i, n i ≤ 1

/-- The sea: the occupation with the alternating sign that fills every level below zero once,
and no other. -/
noncomputable def sea {K : ℕ} (μ : Fin K → ℝ) : Fin K → ℕ := fun i => if μ i < 0 then 1 else 0

/-- **ST1**: with the symmetric sign there is no lowest energy: if some level is below zero, then
for every number `M` some occupation has an energy below `M`. -/
theorem symmetric_no_lowest {K : ℕ} (μ : Fin K → ℝ) (h : ∃ i, μ i < 0) (M : ℝ) :
    ∃ n : Fin K → ℕ, occupationEnergy μ n < M := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨m, hm⟩ := exists_nat_gt (M / μ i)
  refine ⟨fun j => if j = i then m else 0, ?_⟩
  have e : occupationEnergy μ (fun j => if j = i then m else 0) = m * μ i := by
    simp [occupationEnergy]
  rw [e]
  have := (div_lt_iff_of_neg hi).mp hm
  linarith

/-- **ST2**: every occupation with the alternating sign has an energy at least the sum of the
levels below zero. -/
theorem alternating_energy_ge {K : ℕ} (μ : Fin K → ℝ) (n : Fin K → ℕ) (hn : IsAlternating n) :
    ∑ i ∈ Finset.univ.filter (fun i => μ i < 0), μ i ≤ occupationEnergy μ n := by
  rw [Finset.sum_filter, occupationEnergy]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (n i : ℝ) ≤ 1 := by exact_mod_cast hn i
  have h0 : (0 : ℝ) ≤ n i := Nat.cast_nonneg _
  split_ifs with hμ
  · nlinarith
  · push Not at hμ
    exact mul_nonneg h0 hμ

/-- **ST2**: the sea is an occupation with the alternating sign, and its energy is the sum of the
levels below zero. -/
theorem sea_energy {K : ℕ} (μ : Fin K → ℝ) :
    IsAlternating (sea μ) ∧
      occupationEnergy μ (sea μ) = ∑ i ∈ Finset.univ.filter (fun i => μ i < 0), μ i := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold sea
    split_ifs <;> omega
  · rw [Finset.sum_filter, occupationEnergy]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold sea
    split_ifs <;> simp

/-- **ST3**: for a coin angle `μ` strictly between `0` and `π / 2` and every wave number `k`, the
walk's table has a level `e^{-iε}` with `ε` strictly between `0` and `π`, and its pair `e^{iε}`:
read as energies, one above zero and one below. -/
theorem walk_level_signs {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ < π / 2) (k : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < π ∧ IsWalkLevel μ k ε ∧ IsWalkLevel μ k (-ε) := by
  have hc0 : 0 < Real.cos μ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hμ⟩
  have hc1 : Real.cos μ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hμ.le hμ0
    rwa [Real.cos_zero] at this
  have hk1 := Real.cos_le_one k
  have hk0 := Real.neg_one_le_cos k
  have hlo : -1 < Real.cos μ * Real.cos k := by nlinarith
  have hhi : Real.cos μ * Real.cos k < 1 := by nlinarith
  refine ⟨Real.arccos (Real.cos μ * Real.cos k), Real.arccos_pos.mpr hhi,
    Real.arccos_lt_pi.mpr hlo, ?_, ?_⟩
  · rw [walk_level_iff, Real.cos_arccos hlo.le hhi.le]
  · apply walk_levels_pair
    rw [walk_level_iff, Real.cos_arccos hlo.le hhi.le]

end Artform.Stages
