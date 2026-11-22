import ArtformStages.InnerDirection

/-!
# The inner direction at every reach

Finding 475 of the research ledger on a layered universe, its clause ID8: Meyer's theorem at every
finite reach. On the ring of `N` places, with `S` the shift, a table `∑_{j=-r}^{r} a_j S^j` of
reach `r`, the same at every place, on waves of plain numbers, keeps the sum of the squares of
the sizes of every wave exactly when exactly one `a_j` is not `0` and that one has size `1`: it
shifts rigidly by `j` places and turns.

* `ringShiftBy`, `reachTable`: the shift made `j` times, `S^j`, and the table of reach `r`.
* `scalar_reach_unitary_iff` (ID8): the theorem, for every `r` and every `N ≥ 4 r + 1`.
* `reachOne_eq_reachTable`, `scalar_reach_one_of_reach` (ID8 at `r = 1`): the table
  `a S⁻¹ + b + c S` of ID1 is the table of reach 1 with the coefficients `a`, `b` and `c`, and
  ID8 at `r = 1` gives ID1 again.

The proof reads the table's answer `α` to the wave that is `1` at `0`. A table that keeps the sum
of squares keeps the pairing, so the answers to the waves at `0` and at `d` are orthogonal for
`d ≠ 0`. With `m < M` the least and the greatest `j` with `a_j ≠ 0`, the pairing at
`d = M - m` is `conj (a_M) a_m ≠ 0`, because `N ≥ 4 r + 1` keeps the places apart.

None of this is new: it is Meyer's theorem on scalar quantum cellular automata (1996).
-/

open ComplexConjugate

namespace Artform.Stages

section Reach

variable {N : ℕ}

/-- The shift made `j` times, `S^j`: it moves a wave by `j` places. -/
def ringShiftBy (j : ℤ) (ψ : ZMod N → ℂ) : ZMod N → ℂ := fun x => ψ (x - j)

theorem ringShiftBy_one : (ringShiftBy 1 : (ZMod N → ℂ) → ZMod N → ℂ) = ringShift := by
  funext ψ x
  simp [ringShiftBy, ringShift]

theorem ringShiftBy_neg_one :
    (ringShiftBy (-1) : (ZMod N → ℂ) → ZMod N → ℂ) = ringUnshift := by
  funext ψ x
  simp [ringShiftBy, ringUnshift]

/-- A table of reach `r`, the same at every place, on waves of plain numbers:
`∑_{j=-r}^{r} a_j S^j`. -/
def reachTable (r : ℕ) (a : ℤ → ℂ) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  ∑ j ∈ Finset.Icc (-(r : ℤ)) r, a j • ringShiftBy j ψ

theorem reachTable_apply (r : ℕ) (a : ℤ → ℂ) (ψ : ZMod N → ℂ) (x : ZMod N) :
    reachTable r a ψ x = ∑ j ∈ Finset.Icc (-(r : ℤ)) r, a j * ψ (x - j) := by
  simp [reachTable, ringShiftBy, Finset.sum_apply]

theorem reachTable_add (r : ℕ) (a : ℤ → ℂ) (φ ψ : ZMod N → ℂ) :
    reachTable r a (φ + ψ) = reachTable r a φ + reachTable r a ψ := by
  funext x
  simp only [reachTable_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem reachTable_sub (r : ℕ) (a : ℤ → ℂ) (φ ψ : ZMod N → ℂ) :
    reachTable r a (φ - ψ) = reachTable r a φ - reachTable r a ψ := by
  funext x
  simp only [reachTable_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem reachTable_smul (r : ℕ) (a : ℤ → ℂ) (t : ℂ) (ψ : ZMod N → ℂ) :
    reachTable r a (t • ψ) = t • reachTable r a ψ := by
  funext x
  simp only [reachTable_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A table of reach `r` that keeps the sum of squares of every wave keeps the pairing. -/
theorem ringPair_reachTable [NeZero N] {r : ℕ} {a : ℤ → ℂ}
    (h : ∀ ψ : ZMod N → ℂ, ∑ x, ‖reachTable r a ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2)
    (φ ψ : ZMod N → ℂ) :
    ringPair (reachTable r a φ) (reachTable r a ψ) = ringPair φ ψ := by
  have hQ : ∀ f : ZMod N → ℂ, ringPair (reachTable r a f) (reachTable r a f) = ringPair f f :=
    fun f => by rw [ringPair_self, ringPair_self, h]
  have h4 := ringPair_polar (reachTable r a φ) (reachTable r a ψ)
  rw [← reachTable_smul, ← reachTable_add, ← reachTable_add, ← reachTable_sub, ← reachTable_sub,
    hQ, hQ, hQ, hQ, ← ringPair_polar] at h4
  linear_combination h4 / 4

/-- Two whole numbers closer than `N` are one place of the ring only if they are equal. -/
theorem intCast_eq_of_abs_lt {i j : ℤ} (h : |i - j| < N) (e : (i : ZMod N) = (j : ZMod N)) :
    i = j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
  have := Int.eq_zero_of_abs_lt_dvd e (by rwa [abs_sub_comm])
  omega

theorem sum_norm_sq_ringDelta [NeZero N] (p : ZMod N) : ∑ x, ‖ringDelta p x‖ ^ 2 = 1 := by
  simp [ringDelta, apply_ite, Finset.sum_ite_eq']

/-- The answer to the wave at `p` is the answer to the wave at `0`, moved by `p`. -/
theorem reachTable_delta (r : ℕ) (a : ℤ → ℂ) (p x : ZMod N) :
    reachTable r a (ringDelta p) x = reachTable r a (ringDelta 0) (x - p) := by
  simp only [reachTable_apply, ringDelta, sub_right_comm x p, sub_eq_zero]

/-- With `2 r < N`, the answer to the wave at `0` is `a_i` at the place `i`. -/
theorem reachTable_delta_at {r : ℕ} (hN : 2 * r < N) (a : ℤ → ℂ) {i : ℤ}
    (hi : i ∈ Finset.Icc (-(r : ℤ)) r) : reachTable r a (ringDelta 0) (i : ZMod N) = a i := by
  rw [reachTable_apply, Finset.sum_eq_single i]
  · simp [ringDelta]
  · intro j hj hji
    have hne : (i : ZMod N) - (j : ZMod N) ≠ 0 := by
      rw [sub_ne_zero]
      intro e
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      exact hji (intCast_eq_of_abs_lt (by rw [abs_sub_lt_iff]; constructor <;> omega) e).symm
    simp [ringDelta, hne]
  · intro hi'
    exact absurd hi hi'

/-- The answer to the wave at `0` is not `0` only at a place `i` with `a_i ≠ 0`. -/
theorem reachTable_delta_ne_zero {r : ℕ} (a : ℤ → ℂ) {x : ZMod N}
    (hx : reachTable r a (ringDelta 0) x ≠ 0) :
    ∃ i ∈ Finset.Icc (-(r : ℤ)) r, a i ≠ 0 ∧ x = (i : ZMod N) := by
  rw [reachTable_apply] at hx
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  refine ⟨i, hi, fun h0 => hne (by rw [h0, zero_mul]), ?_⟩
  by_contra hxi
  exact hne (by simp [ringDelta, sub_eq_zero, hxi])

/-- **ID8** (Meyer's theorem at every reach). On the ring of `N ≥ 4 r + 1` places the table
`∑_{j=-r}^{r} a_j S^j` keeps the sum of the squares of the sizes of every wave exactly when
exactly one `a_j` is not `0` and that one has size `1`. -/
theorem scalar_reach_unitary_iff [NeZero N] {r : ℕ} (hN : 4 * r + 1 ≤ N) (a : ℤ → ℂ) :
    (∀ ψ : ZMod N → ℂ, ∑ x, ‖reachTable r a ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2) ↔
      ∃ j ∈ Finset.Icc (-(r : ℤ)) r, ‖a j‖ = 1 ∧
        ∀ i ∈ Finset.Icc (-(r : ℤ)) r, i ≠ j → a i = 0 := by
  have hN2 : 2 * r < N := by omega
  constructor
  · intro h
    have h0 := h (ringDelta 0)
    rw [sum_norm_sq_ringDelta] at h0
    set S := (Finset.Icc (-(r : ℤ)) r).filter (fun j => a j ≠ 0) with hSdef
    have memS : ∀ j, j ∈ S ↔ j ∈ Finset.Icc (-(r : ℤ)) r ∧ a j ≠ 0 := fun j => Finset.mem_filter
    have hS : S.Nonempty := by
      by_contra hS
      rw [Finset.not_nonempty_iff_eq_empty] at hS
      have hz : ∀ x : ZMod N, reachTable r a (ringDelta 0) x = 0 := fun x => by
        by_contra hx
        obtain ⟨i, hi, hai, -⟩ := reachTable_delta_ne_zero a hx
        have hiS : i ∈ S := (memS i).mpr ⟨hi, hai⟩
        rw [hS] at hiS
        exact Finset.notMem_empty i hiS
      simp [hz] at h0
    set m := S.min' hS with hmdef
    set M := S.max' hS with hMdef
    have hmS : m ∈ S := S.min'_mem hS
    have hMS : M ∈ S := S.max'_mem hS
    have hm_le : ∀ j ∈ S, m ≤ j := fun j hj => S.min'_le j hj
    have hle_M : ∀ j ∈ S, j ≤ M := fun j hj => S.le_max' j hj
    obtain ⟨hmI, ham⟩ := (memS m).mp hmS
    obtain ⟨hMI, haM⟩ := (memS M).mp hMS
    have hm' := Finset.mem_Icc.mp hmI
    have hM' := Finset.mem_Icc.mp hMI
    have hmM : m = M := by
      by_contra hne
      have hlt : m < M := lt_of_le_of_ne (hm_le M hMS) hne
      have hd0 : (0 : ZMod N) ≠ ((M - m : ℤ) : ZMod N) := by
        intro e
        have := intCast_eq_of_abs_lt (N := N) (i := 0) (j := M - m)
          (by rw [abs_sub_lt_iff]; constructor <;> omega) (by rw [Int.cast_zero]; exact e)
        omega
      have e := ringPair_reachTable h (ringDelta 0) (ringDelta ((M - m : ℤ) : ZMod N))
      rw [ringPair_delta] at e
      simp only [hd0, ↓reduceIte] at e
      have hL : ringPair (reachTable r a (ringDelta 0))
          (reachTable r a (ringDelta ((M - m : ℤ) : ZMod N))) = conj (a M) * a m := by
        unfold ringPair
        rw [Finset.sum_eq_single (M : ZMod N)]
        · rw [reachTable_delta r a ((M - m : ℤ) : ZMod N) (M : ZMod N), Int.cast_sub,
            sub_sub_cancel, reachTable_delta_at hN2 a hMI, reachTable_delta_at hN2 a hmI]
        · intro x _ hxM
          by_contra hx
          obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
          rw [map_ne_zero] at h1
          rw [reachTable_delta] at h2
          obtain ⟨i, hi, hai, rfl⟩ := reachTable_delta_ne_zero a h1
          obtain ⟨j, hj, haj, hj'⟩ := reachTable_delta_ne_zero a h2
          have hiS : i ∈ S := (memS i).mpr ⟨hi, hai⟩
          have hjS : j ∈ S := (memS j).mpr ⟨hj, haj⟩
          have h3 := hm_le i hiS
          have h4 := hle_M i hiS
          have h5 := hm_le j hjS
          have h6 := hle_M j hjS
          have e2 : ((i - (M - m) : ℤ) : ZMod N) = (j : ZMod N) := by
            rw [Int.cast_sub]
            exact hj'
          have := intCast_eq_of_abs_lt (by rw [abs_sub_lt_iff]; constructor <;> omega) e2
          exact hxM (by rw [show i = M by omega])
        · intro hM
          exact absurd (Finset.mem_univ _) hM
      rw [hL] at e
      exact mul_ne_zero ((map_ne_zero _).mpr haM) ham e
    have honly : ∀ i ∈ Finset.Icc (-(r : ℤ)) r, i ≠ m → a i = 0 := fun i hi him => by
      by_contra hai
      have hiS : i ∈ S := (memS i).mpr ⟨hi, hai⟩
      exact him (le_antisymm (by rw [hmM]; exact hle_M i hiS) (hm_le i hiS))
    have hα : ∀ x, reachTable r a (ringDelta 0) x = if x = (m : ZMod N) then a m else 0 :=
      fun x => by
        by_cases hx : x = (m : ZMod N)
        · rw [hx, reachTable_delta_at hN2 a hmI]
          simp
        · simp only [hx, ↓reduceIte]
          by_contra hne
          obtain ⟨i, hi, hai, rfl⟩ := reachTable_delta_ne_zero a hne
          have him : i = m := by
            by_contra him
            exact hai (honly i hi him)
          exact hx (by rw [him])
    have hn : ‖a m‖ ^ 2 = 1 := by
      simp only [hα] at h0
      simpa [apply_ite, Finset.sum_ite_eq'] using h0
    refine ⟨m, hmI, ?_, honly⟩
    have := norm_nonneg (a m)
    nlinarith
  · rintro ⟨j, hj, hnorm, hzero⟩ ψ
    have e : ∀ x, reachTable r a ψ x = a j * ψ (x + -(j : ZMod N)) := fun x => by
      rw [reachTable_apply, Finset.sum_eq_single j, sub_eq_add_neg]
      · intro i hi hij
        rw [hzero i hi hij, zero_mul]
      · intro hj'
        exact absurd hj hj'
    simp only [e]
    exact sum_norm_sq_shift (a j) (by rw [hnorm, one_pow]) _ ψ

/-! ### ID8 at `r = 1` is ID1 -/

/-- The coefficients of the table `a S⁻¹ + b + c S` of ID1, read as a table of reach 1. -/
def reachOneCoeff (a b c : ℂ) : ℤ → ℂ :=
  fun j => if j = -1 then a else if j = 0 then b else if j = 1 then c else 0

/-- The table `a S⁻¹ + b + c S` of ID1 is the table of reach 1 with the coefficients `a`, `b`,
`c`. -/
theorem reachOne_eq_reachTable (a b c : ℂ) :
    (reachOne a b c : (ZMod N → ℂ) → ZMod N → ℂ) = reachTable 1 (reachOneCoeff a b c) := by
  funext ψ x
  have hI : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [reachTable_apply, hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, reachOne_apply]
  simp [reachOneCoeff, sub_eq_add_neg]
  ring

/-- **ID8 at `r = 1`**: with `N ≥ 5`, the theorem at reach 1 gives ID1 again. -/
theorem scalar_reach_one_of_reach [NeZero N] (hN : 5 ≤ N) (a b c : ℂ) :
    (∀ ψ : ZMod N → ℂ, ∑ x, ‖reachOne a b c ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2) ↔
      ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 = 1 ∧ (a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 ∨ b = 0 ∧ c = 0) := by
  rw [reachOne_eq_reachTable, scalar_reach_unitary_iff (by omega)]
  have mem : ∀ j : ℤ, j ∈ Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) ↔ j = -1 ∨ j = 0 ∨ j = 1 :=
    fun j => by
      rw [Finset.mem_Icc]
      omega
  have cm : reachOneCoeff a b c (-1) = a := by simp [reachOneCoeff]
  have c0 : reachOneCoeff a b c 0 = b := by simp [reachOneCoeff]
  have c1 : reachOneCoeff a b c 1 = c := by simp [reachOneCoeff]
  have one_of_sq : ∀ z : ℂ, ‖z‖ ^ 2 = 1 → ‖z‖ = 1 := fun z hz => by
    have := norm_nonneg z
    nlinarith
  constructor
  · rintro ⟨j, hj, hn, hz⟩
    rcases (mem j).mp hj with rfl | rfl | rfl
    · have hb := hz 0 ((mem 0).mpr (by norm_num)) (by norm_num)
      have hc := hz 1 ((mem 1).mpr (by norm_num)) (by norm_num)
      rw [cm] at hn
      rw [c0] at hb
      rw [c1] at hc
      refine ⟨by rw [hn, hb, hc]; norm_num, Or.inr (Or.inr ⟨hb, hc⟩)⟩
    · have ha := hz (-1) ((mem (-1)).mpr (by norm_num)) (by norm_num)
      have hc := hz 1 ((mem 1).mpr (by norm_num)) (by norm_num)
      rw [c0] at hn
      rw [cm] at ha
      rw [c1] at hc
      refine ⟨by rw [hn, ha, hc]; norm_num, Or.inr (Or.inl ⟨ha, hc⟩)⟩
    · have ha := hz (-1) ((mem (-1)).mpr (by norm_num)) (by norm_num)
      have hb := hz 0 ((mem 0).mpr (by norm_num)) (by norm_num)
      rw [c1] at hn
      rw [cm] at ha
      rw [c0] at hb
      refine ⟨by rw [hn, ha, hb]; norm_num, Or.inl ⟨ha, hb⟩⟩
  · rintro ⟨hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨1, (mem 1).mpr (by norm_num), ?_, fun i hi hi1 => ?_⟩
      · rw [c1]
        exact one_of_sq c (by simpa using hn)
      · rcases (mem i).mp hi with rfl | rfl | rfl
        · exact cm
        · exact c0
        · exact absurd rfl hi1
    · refine ⟨0, (mem 0).mpr (by norm_num), ?_, fun i hi hi0 => ?_⟩
      · rw [c0]
        exact one_of_sq b (by simpa using hn)
      · rcases (mem i).mp hi with rfl | rfl | rfl
        · exact cm
        · exact absurd rfl hi0
        · exact c1
    · refine ⟨-1, (mem (-1)).mpr (by norm_num), ?_, fun i hi hi1 => ?_⟩
      · rw [cm]
        exact one_of_sq a (by simpa using hn)
      · rcases (mem i).mp hi with rfl | rfl | rfl
        · exact absurd rfl hi1
        · exact c0
        · exact c1

end Reach

end Artform.Stages
