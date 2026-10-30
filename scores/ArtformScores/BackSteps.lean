import ArtformScores.Extents

/-!
# Back-steps

The rest of the ledger's finding 043 on extents: one back-step (Lemma 3), and the score of
forward kicks and backward moves, which never rings (Theorem S5.3, part 1).
- **One back-step.** Away from the back-step at `x₀`, the two forward predecessors `x` and `c x`
  of `B x` still choose alike. The predecessor of `B x₀` is `c x₀`, which takes `A`, and that of
  `A x₀` is `c⁻¹ x₀`, which takes `B`. The links join `c x₀, c² x₀, …, c⁻¹ x₀` unless one of them
  is broken at the back-step's target, which happens exactly when `(A B)⁻¹ ∈ ⟨c⟩`.
- **The cat map never rings.** With the steps `K` and `M⁻¹`, `c = K⁻¹ M⁻¹` is the inverse of the
  tick, and `c³ = -1`. In `PSL(2, Z/n) = SL(2, Z/n)/{±1}`, `c` has the odd order 3, `|PSL|` is
  even (the quarter turn `S` has order 2), and `L_K` is even: `K` has the order `n`, and for even
  `n` the cycles of `L_K` are the `[PSL : ⟨K⟩]` cosets, an even number, since `S` acts on them
  without fixed points (a conjugate of `S` has trace `0`, a power of `K` the trace `±2`). So
  Rankin's parity excludes an extent. In `SL(2, Z/n)`, `-1 = c³` lies in `⟨c⟩`, and lifting carries
  an extent down to `PSL(2, Z/n)`.
-/

namespace Artform.Scores.Bells

open Equiv

section BackStep

variable {G : Type*} [Group G]

/-- A Rankin link away from the back-step: the two forward predecessors `x` and `c x` of `B x`
choose alike. -/
theorem link_of_ne {A B : G} {σ : Perm G} {x₀ : G}
    (hstep : ∀ x, x ≠ x₀ → σ x = A * x ∨ σ x = B * x) {x : G} (hx : x ≠ x₀)
    (hcx : A⁻¹ * B * x ≠ x₀) (hh : σ x₀ ≠ B * x) :
    σ (A⁻¹ * B * x) = A * (A⁻¹ * B * x) ↔ σ x = A * x := by
  have hAc : A * (A⁻¹ * B * x) = B * x := by group
  constructor
  · intro h
    by_contra hxA
    have hxB := (hstep x hx).resolve_left hxA
    have := σ.injective (h.trans (hAc.trans hxB.symm))
    rw [this] at h
    exact hxA h
  · intro h
    obtain ⟨y, hy⟩ := σ.surjective (B * x)
    have hy0 : y ≠ x₀ := by
      rintro rfl
      exact hh hy
    rcases hstep y hy0 with hyA | hyB
    · have hyc : y = A⁻¹ * B * x := by
        rw [hyA] at hy
        calc y = A⁻¹ * (A * y) := by group
          _ = A⁻¹ * B * x := by rw [hy]; group
      rw [← hyc, hy, ← hAc, hyc]
    · rw [hyB] at hy
      have hyx : y = x := mul_left_cancel hy
      rw [hyx] at hyB
      have hAB : A = B := mul_right_cancel (h.symm.trans hyB)
      rw [← hAB, inv_mul_cancel, one_mul]
      exact h

/-- Lemma 3 for a back-step `A⁻¹`: `A B ∈ ⟨c⟩`. -/
theorem one_back_step_A [Finite G] {A B : G} {σ : Perm G} {x₀ : G}
    (hstep : ∀ x, x ≠ x₀ → σ x = A * x ∨ σ x = B * x) (hback : σ x₀ = A⁻¹ * x₀) :
    A * B ∈ Subgroup.zpowers (A⁻¹ * B) := by
  set c := A⁻¹ * B with hc
  by_contra hAB
  have hAA : A * A ≠ 1 := by
    intro h
    apply hAB
    have hA : A⁻¹ = A := (eq_inv_of_mul_eq_one_left h).symm
    rw [show A * B = c by rw [hc, hA]]
    exact Subgroup.mem_zpowers c
  have hAB1 : A * B ≠ 1 := fun h => hAB (h ▸ Subgroup.one_mem _)
  -- the predecessor of `B x₀` is `c x₀`, which takes `A`
  obtain ⟨y, hy⟩ := σ.surjective (B * x₀)
  have hy0 : y ≠ x₀ := by
    rintro rfl
    rw [hback] at hy
    have h1 : A⁻¹ = B := mul_right_cancel hy
    exact hAB1 (by rw [← h1, mul_inv_cancel])
  have hcy : y = c * x₀ := by
    rcases hstep y hy0 with h | h
    · rw [h] at hy
      calc y = A⁻¹ * (A * y) := by group
        _ = c * x₀ := by rw [hy, hc]; group
    · rw [h] at hy
      exact absurd (mul_left_cancel hy) hy0
  have hcA : σ (c * x₀) = A * (c * x₀) := by
    rw [← hcy, hy, hcy, hc]
    group
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, one_mul] at hcy
    exact hy0 hcy
  -- the predecessor of `A x₀` is `c⁻¹ x₀`, which takes `B`
  obtain ⟨z, hz⟩ := σ.surjective (A * x₀)
  have hz0 : z ≠ x₀ := by
    rintro rfl
    rw [hback] at hz
    have h1 : A⁻¹ = A := mul_right_cancel hz
    exact hAA (by rw [← mul_inv_cancel A, h1])
  have hzc : z = c⁻¹ * x₀ := by
    rcases hstep z hz0 with h | h
    · rw [h] at hz
      exact absurd (mul_left_cancel hz) hz0
    · rw [h] at hz
      calc z = B⁻¹ * (B * z) := by group
        _ = c⁻¹ * x₀ := by rw [hz, hc]; group
  have hcB : σ (c⁻¹ * x₀) ≠ A * (c⁻¹ * x₀) := by
    rw [← hzc, hz]
    intro h
    exact hz0 (mul_left_cancel h).symm
  -- the chain of links from `c x₀` to `c⁻¹ x₀`
  have hord := orderOf_pos c
  have hord2 : 2 ≤ orderOf c := by
    by_contra h
    push Not at h
    exact hc1 (orderOf_eq_one_iff.mp (by omega))
  have hpow_ne : ∀ k, 0 < k → k < orderOf c → c ^ k * x₀ ≠ x₀ := by
    intro k hk1 hk2 h
    have h1 : c ^ k = 1 := mul_eq_right.mp h
    exact absurd (orderOf_le_of_pow_eq_one hk1 h1) (by omega)
  have hchain : ∀ k, 1 ≤ k → k < orderOf c → σ (c ^ k * x₀) = A * (c ^ k * x₀) := by
    intro k hk1 hk2
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hcA
      · have hprev := ih hk (by omega)
        have hl := link_of_ne hstep (x := c ^ k * x₀) (hpow_ne k hk (by omega))
          (by
            rw [← hc, ← mul_assoc, ← pow_succ']
            exact hpow_ne (k + 1) (by omega) hk2)
          (by
            intro h
            rw [hback] at h
            apply hAB
            have h2 : A⁻¹ = B * c ^ k := by
              have := congrArg (· * x₀⁻¹) h
              simpa [mul_assoc] using this
            have h3 : A * B = (c ^ k)⁻¹ := by
              rw [eq_inv_iff_mul_eq_one]
              calc A * B * c ^ k = A * (B * c ^ k) := by group
                _ = 1 := by rw [← h2, mul_inv_cancel]
            rw [h3]
            exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
        rw [← hc, ← mul_assoc, ← pow_succ'] at hl
        exact hl.mpr hprev
  have hlast := hchain (orderOf c - 1) (by omega) (by omega)
  have hinv : c ^ (orderOf c - 1) = c⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hord, pow_orderOf_eq_one]
  rw [hinv] at hlast
  exact hcB hlast

/-- Lemma 3 for a back-step `B⁻¹`: `B A ∈ ⟨c⟩`. -/
theorem one_back_step_B [Finite G] {A B : G} {σ : Perm G} {x₀ : G}
    (hstep : ∀ x, x ≠ x₀ → σ x = A * x ∨ σ x = B * x) (hback : σ x₀ = B⁻¹ * x₀) :
    B * A ∈ Subgroup.zpowers (A⁻¹ * B) := by
  have := one_back_step_A (A := B) (B := A) (fun x hx => (hstep x hx).symm) hback
  rwa [show B⁻¹ * A = (A⁻¹ * B)⁻¹ by group, Subgroup.zpowers_inv] at this

end BackStep

section CatMap

open Matrix (SpecialLinearGroup)

variable {n : ℕ}

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)

theorem mem_pmOne_iff (g : SLn) : g ∈ pmOne n ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/-- The kick `K = K(1)`. -/
abbrev Kn (n : ℕ) : SpecialLinearGroup (Fin 2) (ZMod n) := (Step.kick (1 : ZMod n)).sl

/-- The back-move `M⁻¹ = M(1)`, the inverse of the leapfrog's move `M = M(-1)`. -/
abbrev Mn (n : ℕ) : SpecialLinearGroup (Fin 2) (ZMod n) := (Step.move (1 : ZMod n)).sl

theorem catC_mat : (((Kn n)⁻¹ * Mn n : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) =
    !![1, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  simp only [Kn, Mn, Step.coe_sl, Step.mat, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- `c = K⁻¹ M⁻¹ = (M K)⁻¹`, the inverse of the tick, has `c³ = -1`. -/
theorem catC_cube : ((Kn n)⁻¹ * Mn n) ^ 3 = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, catC_mat, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, pow_succ, pow_succ, pow_one, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem Kn_pow (j : ℕ) : (((Kn n) ^ j : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) =
    !![1, 0; (j : ZMod n), 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    simp only [Kn, Step.coe_sl, Step.mat, Matrix.mul_fin_two]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

theorem two_ne_zero_of (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp this)
  omega

theorem Kn_pow_mem_iff (hn : 3 ≤ n) (j : ℕ) : Kn n ^ j ∈ pmOne n ↔ n ∣ j := by
  rw [mem_pmOne_iff]
  constructor
  · rintro (h | h)
    · have e := congrArg (fun g : SLn => (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0) h
      simp only [Kn_pow, Matrix.SpecialLinearGroup.coe_one] at e
      simpa using (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using e)
    · have e := congrArg (fun g : SLn => (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0) h
      simp only [Kn_pow, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at e
      exfalso
      apply two_ne_zero_of hn
      have : (1 : ZMod n) = -1 := by simpa using e
      linear_combination this
  · intro h
    left
    apply Subtype.ext
    rw [Kn_pow, (ZMod.natCast_eq_zero_iff _ _).mpr h, Matrix.SpecialLinearGroup.coe_one]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

local notation "PSLn" => SpecialLinearGroup (Fin 2) (ZMod n) ⧸ pmOne n

theorem catMap_mat : ((Mn n * Kn n : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = !![2, 1; 1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [Kn, Mn, Step.coe_sl, Step.mat, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [one_add_one_eq_two]

theorem orderOf_catC_PSL (hn : 3 ≤ n) : orderOf (((Kn n)⁻¹ * Mn n : SLn) : PSLn) = 3 := by
  have : Fact (1 < n) := ⟨by omega⟩
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, catC_cube, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  · rw [Ne, QuotientGroup.eq_one_iff, mem_pmOne_iff]
    rintro (h | h) <;>
    · have e := congrArg (fun g : SLn => (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 1) h
      simp only [catC_mat] at e
      simp at e

theorem orderOf_Kn_PSL (hn : 3 ≤ n) : orderOf ((Kn n : SLn) : PSLn) = n := by
  have hiff : ∀ j : ℕ, ((Kn n : SLn) : PSLn) ^ j = 1 ↔ n ∣ j := fun j => by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Kn_pow_mem_iff hn]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hiff n).mpr dvd_rfl))
    ((hiff _).mp (pow_orderOf_eq_one _))

/-- The quarter turn `S = [[0, -1], [1, 0]]`, with `S² = -1`. -/
def Sn (n : ℕ) : SpecialLinearGroup (Fin 2) (ZMod n) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem Sn_sq : Sn n ^ 2 = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sn, sq, Matrix.mul_apply, Fin.sum_univ_two]

theorem orderOf_Sn_PSL (hn : 3 ≤ n) : orderOf ((Sn n : SLn) : PSLn) = 2 := by
  have : Fact (1 < n) := ⟨by omega⟩
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, Sn_sq, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  · rw [Ne, QuotientGroup.eq_one_iff, mem_pmOne_iff]
    rintro (h | h) <;>
    · have e := congrArg (fun g : SLn => (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0) h
      simp [Sn] at e

/-- `S̄` is conjugate to no power of `K̄`: their traces are `0` and `±2`. -/
theorem Sn_not_conj (hn : 3 ≤ n) (x : SLn) (k : ℕ) :
    ((x⁻¹ * Sn n * x : SLn) : PSLn) ≠ ((Kn n ^ k : SLn) : PSLn) := by
  intro h
  rw [QuotientGroup.eq, mem_pmOne_iff] at h
  have htrS : ((x⁻¹ * Sn n * x : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)).trace = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul]
    simp [Sn, Matrix.trace_fin_two]
  have htrK : ((Kn n ^ k : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)).trace = 2 := by
    rw [Kn_pow, Matrix.trace_fin_two_of]
    norm_num [one_add_one_eq_two]
  rcases h with h | h
  · have heq : x⁻¹ * Sn n * x = Kn n ^ k := inv_mul_eq_one.mp h
    rw [heq, htrK] at htrS
    exact two_ne_zero_of hn htrS
  · have heq : Kn n ^ k = x⁻¹ * Sn n * x * -1 := inv_mul_eq_iff_eq_mul.mp h
    rw [mul_neg_one] at heq
    rw [heq, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, htrS, neg_zero] at htrK
    exact two_ne_zero_of hn htrK.symm

/-- The index of `⟨K̄⟩` is even: `S̄` acts on its cosets without fixed points. -/
theorem index_Kn_even (hn : 3 ≤ n) [NeZero n] :
    Even (Subgroup.zpowers ((Kn n : SLn) : PSLn)).index := by
  set U := Subgroup.zpowers ((Kn n : SLn) : PSLn)
  set H := Subgroup.zpowers ((Sn n : SLn) : PSLn)
  have hp : IsPGroup 2 H :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_Sn_PSL hn, pow_one])
  have hfix : IsEmpty (MulAction.fixedPoints H (PSLn ⧸ U)) := by
    refine ⟨fun ⟨q, hq⟩ => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hq ⟨_, Subgroup.mem_zpowers ((Sn n : SLn) : PSLn)⟩
    have hS : (((Sn n : SLn) : PSLn))⁻¹ = ((Sn n : SLn) : PSLn) := by
      rw [inv_eq_iff_mul_eq_one, ← sq]
      have h2 := pow_orderOf_eq_one ((Sn n : SLn) : PSLn)
      rwa [orderOf_Sn_PSL hn] at h2
    rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mul_inv_rev,
      hS] at h1
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr h1)
    apply Sn_not_conj hn x k
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hk,
      QuotientGroup.mk_pow]
  have h2 := hp.card_modEq_card_fixedPoints (PSLn ⧸ U)
  have h0 : Nat.card (MulAction.fixedPoints H (PSLn ⧸ U)) = 0 := Nat.card_of_isEmpty
  rw [h0] at h2
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp h2)

theorem mulLeft_pow_apply {G : Type*} [Group G] (g : G) (j : ℕ) (x : G) :
    ((Equiv.mulLeft g) ^ j) x = g ^ j * x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, ih]
    change g * (g ^ j * x) = _
    rw [← mul_assoc, ← pow_succ']

/-- `L_K̄` is even on `PSL(2, Z/n)`: `n` odd, or `n` even and an even number of `n`-cycles. -/
theorem sign_mulLeft_Kn (hn : 3 ≤ n) [NeZero n] [Fintype PSLn] [DecidableEq PSLn] :
    Perm.sign (Equiv.mulLeft ((Kn n : SLn) : PSLn)) = 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · have hK1 : ((Kn n : SLn) : PSLn) ≠ 1 := by
      intro h
      have := orderOf_Kn_PSL hn
      rw [h, orderOf_one] at this
      omega
    have hper : ∀ x, Equiv.mulLeft ((Kn n : SLn) : PSLn) x ≠ x →
        ∀ j : ℕ, (Equiv.mulLeft ((Kn n : SLn) : PSLn) ^ j) x = x ↔ n ∣ j := by
      intro x _ j
      rw [mulLeft_pow_apply, mul_eq_right, ← orderOf_dvd_iff_pow_eq_one, orderOf_Kn_PSL hn]
    obtain ⟨m, hm, hs⟩ := sign_of_period _ n hper
    have hsupp : (Equiv.mulLeft ((Kn n : SLn) : PSLn)).support.card = Fintype.card PSLn := by
      rw [← Finset.card_univ]
      congr 1
      ext x
      simp [Perm.mem_support, hK1]
    have hidx := Subgroup.card_mul_index (Subgroup.zpowers ((Kn n : SLn) : PSLn))
    rw [Nat.card_zpowers, orderOf_Kn_PSL hn, Nat.card_eq_fintype_card, ← hsupp, ← hm,
      mul_comm] at hidx
    have hmi : m = (Subgroup.zpowers ((Kn n : SLn) : PSLn)).index :=
      (Nat.eq_of_mul_eq_mul_right (by omega) hidx).symm
    obtain ⟨t, ht⟩ := index_Kn_even hn
    obtain ⟨u, hu⟩ := heven
    rw [hs, hmi, ht, hu, (show u + u + 1 = 2 * u + 1 by ring), pow_succ, pow_mul, neg_one_sq,
      one_pow, one_mul]
    exact Even.neg_one_pow ⟨t, rfl⟩
  · exact sign_mulLeft_of_odd (by rw [orderOf_Kn_PSL hn]; exact hodd)

/-- Rankin's parity with a given sign of `L_A`. -/
theorem no_extent_of_sign {G : Type*} [Group G] [Fintype G] [DecidableEq G] {A B : G}
    (hA : Perm.sign (Equiv.mulLeft A) = 1) (hc : Odd (orderOf (A⁻¹ * B)))
    (hG : 2 ∣ Fintype.card G) (σ : Perm G) : ¬ IsExtent A B σ := by
  intro hσ
  obtain ⟨m, -, hs⟩ := rankin_sign hσ.1
  obtain ⟨t, ht⟩ := hc
  rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul, neg_one_sq, one_pow, one_pow,
    mul_one, hA] at hs
  have he := extent_sign hσ
  rw [hs] at he
  obtain ⟨u, hu⟩ := hG
  rw [hu, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at he
  exact absurd he (by decide)

theorem two_dvd_card_PSLn (hn : 3 ≤ n) [NeZero n] [Fintype PSLn] : 2 ∣ Fintype.card PSLn := by
  have := orderOf_dvd_card (x := ((Sn n : SLn) : PSLn))
  rwa [orderOf_Sn_PSL hn] at this

/-- Kicks with back-moves never ring on `PSL(2, Z/n)`. -/
theorem cat_PSL (hn : 3 ≤ n) (σ : Perm PSLn) :
    ¬ IsExtent ((Kn n : SLn) : PSLn) ((Mn n : SLn) : PSLn) σ := by
  classical
  have : NeZero n := ⟨by omega⟩
  let _ : Fintype PSLn := Fintype.ofFinite _
  refine no_extent_of_sign (sign_mulLeft_Kn hn) ?_ (two_dvd_card_PSLn hn) σ
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, orderOf_catC_PSL hn]
  decide

/-- Kicks with back-moves never ring on `SL(2, Z/n)`: `-1 = c³` lifts an extent to `PSL`. -/
theorem cat_SL (hn : 3 ≤ n) (σ : Perm SLn) : ¬ IsExtent (Kn n) (Mn n) σ := by
  have : NeZero n := ⟨by omega⟩
  intro hσ
  have hN : pmOne n ≤ Subgroup.zpowers ((Kn n)⁻¹ * Mn n) := by
    intro g hg
    rcases (mem_pmOne_iff g).mp hg with rfl | rfl
    · exact Subgroup.one_mem _
    · rw [← catC_cube]
      exact Subgroup.npow_mem_zpowers _ _
  obtain ⟨σ', hσ', -⟩ := extent_lift hN hσ
  exact cat_PSL hn σ' hσ'

end CatMap

end Artform.Scores.Bells

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

/-- **T15** (one back-step). -/
@[ledger "T15"]
theorem oneBackStep : Statement.oneBackStep := fun _ _ _ _ _ _ _ hstep =>
  ⟨Bells.one_back_step_A hstep, Bells.one_back_step_B hstep⟩

/-- **T15** (kicks with back-moves never ring). -/
@[ledger "T15"]
theorem catMapNeverRings : Statement.catMapNeverRings := fun _ hn =>
  ⟨Bells.catMap_mat, Bells.cat_SL hn, Bells.cat_PSL hn⟩

/-! ## Non-vacuity

- One back-step excluded: on `ℤ/6` with the steps `+1` and `+4`, `c = 3` generates `{0, 3}`, which
  does not hold `1 + 4 = 5`, so no permutation steps forward everywhere but once.
- The cat map on `Z/6`, where `n` is even: neither `SL(2, Z/6)` nor `PSL(2, Z/6)` has an extent
  under `K` and `M⁻¹`.
-/

/-- `ℤ/6`, written multiplicatively, with the steps `A = +1` and `B = +4`. -/
abbrev Z6 := Multiplicative (ZMod 6)

theorem z6_not_mem : (Multiplicative.ofAdd (1 : ZMod 6) * Multiplicative.ofAdd 4 : Z6) ∉
    Subgroup.zpowers ((Multiplicative.ofAdd (1 : ZMod 6))⁻¹ * Multiplicative.ofAdd 4) := by
  intro h
  have hord : orderOf ((Multiplicative.ofAdd (1 : ZMod 6))⁻¹ * Multiplicative.ofAdd 4 : Z6) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at h
  revert h
  decide

/-- No permutation of `ℤ/6` steps forward by `+1` or `+4` everywhere but at one element. -/
example : ¬ ∃ (σ : Equiv.Perm Z6) (x₀ : Z6),
    (∀ x, x ≠ x₀ → σ x = Multiplicative.ofAdd 1 * x ∨ σ x = Multiplicative.ofAdd 4 * x) ∧
    (σ x₀ = (Multiplicative.ofAdd 1)⁻¹ * x₀ ∨ σ x₀ = (Multiplicative.ofAdd 4)⁻¹ * x₀) := by
  rintro ⟨σ, x₀, hstep, hback | hback⟩
  · exact z6_not_mem ((oneBackStep Z6 _ _ σ x₀ hstep).1 hback)
  · have := (oneBackStep Z6 _ _ σ x₀ hstep).2 hback
    rw [mul_comm] at this
    exact z6_not_mem this

/-- The cat map on `Z/6`: no extent of `SL(2, Z/6)` or of `PSL(2, Z/6)` under `K` and `M⁻¹`. -/
example : (∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod 6)),
      ¬ Bells.IsExtent (Step.kick (1 : ZMod 6)).sl (Step.move (1 : ZMod 6)).sl σ) ∧
    ∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod 6) ⧸ Bells.pmOne 6),
      ¬ Bells.IsExtent
        ((Step.kick (1 : ZMod 6)).sl : SpecialLinearGroup (Fin 2) (ZMod 6) ⧸ Bells.pmOne 6)
        ((Step.move (1 : ZMod 6)).sl : SpecialLinearGroup (Fin 2) (ZMod 6) ⧸ Bells.pmOne 6) σ :=
  (catMapNeverRings 6 (by norm_num)).2

end Artform.Scores
