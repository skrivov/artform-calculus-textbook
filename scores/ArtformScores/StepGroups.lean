import ArtformScores.Runs
import ArtformScores.StepOrders

/-!
# The step groups of one mode

The ledger's finding 037, Theorem Q: the one-mode tick has finite order exactly at the pulls
`μ = 1, 2, 3`; the step group `Σ_μ` lies in `Γ¹(μ)`, with equality exactly when `μ ≤ 4`, and has
the indices `1, 3, 8, 12` and then infinite index; it is free exactly when `μ ≥ 4`.
- **The descent.** For `μ ≤ 4`, Euclid's algorithm with the quotients in `μ ℤ` on the first column
  reaches `c = 0`. The only stall is `μ = 4` with `|a| = 2 |c|`, where `a` and `b` are even.
- **The gap.** For `μ ≥ 5`, a nonempty alternating word in powers of `K` and `M` sends `(9, 4)` into
  the ping-pong sets, which do not hold it. So no nonzero power of the parabolic law that fixes
  `(9, 4)` lies in `Σ_μ`.
- **Freeness.** Mathlib's ping-pong lemma, on the cones `|x| < 2 |y|` and `|x| > 2 |y|`.
-/

namespace Artform.Scores.StepGroup

open Matrix (SpecialLinearGroup)

local notation "SL2Z" => SpecialLinearGroup (Fin 2) ℤ

theorem Kz_coe : (Kz : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := rfl

theorem Mz_coe (μ : ℤ) : (Mz μ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -μ; 0, 1] := rfl

theorem Kz_zpow (k : ℤ) : ((Kz ^ k : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; k, 1] := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, Kz_coe, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | pred k ih =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv,
      Kz_coe, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem Mz_zpow (μ k : ℤ) : ((Mz μ ^ k : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![1, -(k * μ); 0, 1] := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, Mz_coe, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  | pred k ih =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv,
      Mz_coe, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

/-- The entries of `K^k g`. -/
theorem Kz_zpow_mul (k : ℤ) (g : SL2Z) :
    (Kz ^ k * g).1 0 0 = g.1 0 0 ∧ (Kz ^ k * g).1 0 1 = g.1 0 1 ∧
    (Kz ^ k * g).1 1 0 = g.1 1 0 + k * g.1 0 0 ∧ (Kz ^ k * g).1 1 1 = g.1 1 1 + k * g.1 0 1 := by
  have h : (Kz ^ k * g).1 = !![1, 0; k, 1] * g.1 := by
    rw [← Kz_zpow]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The entries of `M^k g`. -/
theorem Mz_zpow_mul (μ k : ℤ) (g : SL2Z) :
    (Mz μ ^ k * g).1 0 0 = g.1 0 0 - k * μ * g.1 1 0 ∧
    (Mz μ ^ k * g).1 0 1 = g.1 0 1 - k * μ * g.1 1 1 ∧
    (Mz μ ^ k * g).1 1 0 = g.1 1 0 ∧ (Mz μ ^ k * g).1 1 1 = g.1 1 1 := by
  have h : (Mz μ ^ k * g).1 = !![1, -(k * μ); 0, 1] * g.1 := by
    rw [← Mz_zpow]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

theorem det_entries (g : SL2Z) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

theorem ext_entries {g h : SL2Z} (h1 : g.1 0 0 = h.1 0 0) (h2 : g.1 0 1 = h.1 0 1)
    (h3 : g.1 1 0 = h.1 1 0) (h4 : g.1 1 1 = h.1 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Rounding: some multiple of `m` lies within `|m| / 2` of `a`. -/
theorem exists_round (a m : ℤ) (hm : m ≠ 0) : ∃ k : ℤ, 2 * |a - k * m| ≤ |m| := by
  have h0 := Int.emod_nonneg a hm
  have h1 := Int.emod_lt_abs a hm
  have h2 := Int.mul_ediv_add_emod a m
  by_cases h : 2 * (a % m) ≤ |m|
  · refine ⟨a / m, ?_⟩
    have : a - a / m * m = a % m := by linarith [mul_comm m (a / m)]
    rw [this, abs_of_nonneg h0]
    exact h
  · rcases abs_cases m with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩
    · refine ⟨a / m + 1, ?_⟩
      have : a - (a / m + 1) * m = a % m - m := by nlinarith [mul_comm m (a / m)]
      rw [this, abs_of_nonpos (by omega)]
      omega
    · refine ⟨a / m - 1, ?_⟩
      have : a - (a / m - 1) * m = a % m + m := by nlinarith [mul_comm m (a / m)]
      rw [this, abs_of_nonpos (by omega)]
      omega

section Descent

variable (μ : ℕ)

/-- `g` is in the step group up to sign. -/
def PM (g : SL2Z) : Prop := g ∈ stepGroup μ ∨ -g ∈ stepGroup μ

theorem Kz_mem : Kz ∈ stepGroup μ := Subgroup.subset_closure (by simp)

theorem Mz_mem : Mz μ ∈ stepGroup μ := Subgroup.subset_closure (by simp)

variable {μ}

theorem PM.of_Kz {g : SL2Z} (k : ℤ) (h : PM μ (Kz ^ k * g)) : PM μ g := by
  have hk := Subgroup.zpow_mem _ (Kz_mem μ) (-k)
  rcases h with h | h
  · left
    have := Subgroup.mul_mem _ hk h
    simpa using this
  · right
    have := Subgroup.mul_mem _ hk h
    rw [mul_neg] at this
    simpa using this

theorem PM.of_Mz {g : SL2Z} (k : ℤ) (h : PM μ (Mz μ ^ k * g)) : PM μ g := by
  have hk := Subgroup.zpow_mem _ (Mz_mem μ) (-k)
  rcases h with h | h
  · left
    have := Subgroup.mul_mem _ hk h
    simpa using this
  · right
    have := Subgroup.mul_mem _ hk h
    rw [mul_neg] at this
    simpa using this

/-- With `c = 0`, a law is `±M^j`. -/
theorem PM_of_c_zero {g : SL2Z} (hc : g.1 1 0 = 0) (hb : (μ : ℤ) ∣ g.1 0 1) : PM μ g := by
  have hdet := det_entries g
  rw [hc, mul_zero, sub_zero] at hdet
  obtain ⟨t, ht⟩ := hb
  have hmem : ∀ j : ℤ, Mz μ ^ j ∈ stepGroup μ := fun j => Subgroup.zpow_mem _ (Mz_mem μ) j
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have : g = Mz μ ^ (-t) := by
      apply ext_entries <;> rw [Mz_zpow] <;> simp [h1, h2, ht, hc, mul_comm]
    rw [this]
    exact hmem _
  · right
    have : -g = Mz μ ^ t := by
      apply ext_entries <;> rw [Mz_zpow, Matrix.SpecialLinearGroup.coe_neg] <;>
        simp [h1, h2, ht, hc, mul_comm]
    rw [this]
    exact hmem _

/-- The descent: for `μ ≤ 4`, every law with `μ ∣ b` is in the step group up to sign. -/
theorem descent (hμ1 : 1 ≤ μ) (hμ4 : μ ≤ 4) (n : ℕ) (g : SL2Z)
    (hn : (g.1 0 0).natAbs + (g.1 1 0).natAbs ≤ n) (hb : (μ : ℤ) ∣ g.1 0 1) : PM μ g := by
  induction n generalizing g with
  | zero =>
    have ha : g.1 0 0 = 0 := by omega
    have hc : g.1 1 0 = 0 := by omega
    exact PM_of_c_zero hc hb
  | succ n ih =>
    by_cases hc : g.1 1 0 = 0
    · exact PM_of_c_zero hc hb
    have hμ0 : (μ : ℤ) ≠ 0 := by positivity
    have hμabs : |(μ : ℤ)| = μ := abs_of_nonneg (by positivity)
    have hcabs : 0 < |g.1 1 0| := abs_pos.mpr hc
    by_cases ha : g.1 0 0 = 0
    · -- `a = 0`: then `μ = 1`, and two steps reach `c = 0`
      have hdet := det_entries g
      rw [ha, zero_mul, zero_sub] at hdet
      have hbu : IsUnit (g.1 0 1) := by
        apply IsUnit.of_mul_eq_one (-(g.1 1 0))
        linarith
      have hμu : IsUnit (μ : ℤ) := isUnit_of_dvd_unit hb hbu
      have hμone : (μ : ℤ) = 1 := by
        rcases Int.isUnit_iff.mp hμu with h | h
        · exact h
        · omega
      have hcu : g.1 1 0 = 1 ∨ g.1 1 0 = -1 := by
        have : IsUnit (g.1 1 0) := by
          apply IsUnit.of_mul_eq_one (-(g.1 0 1))
          linarith
        exact Int.isUnit_iff.mp this
      set c := g.1 1 0 with hcdef
      apply PM.of_Mz c
      apply PM.of_Kz c
      apply PM_of_c_zero
      · obtain ⟨-, -, h3, -⟩ := Kz_zpow_mul c (Mz μ ^ c * g)
        obtain ⟨h4, -, h5, -⟩ := Mz_zpow_mul μ c g
        rw [h3, h4, h5, ha, hμone]
        rcases hcu with h | h <;> rw [h] <;> norm_num
      · rw [hμone]
        exact one_dvd _
    · by_cases h1 : (μ : ℤ) * |g.1 1 0| < 2 * |g.1 0 0|
      · -- divide `a` by `μ c`
        obtain ⟨k, hk⟩ := exists_round (g.1 0 0) (μ * g.1 1 0) (mul_ne_zero hμ0 hc)
        rw [abs_mul, hμabs] at hk
        apply PM.of_Mz k
        obtain ⟨h4, h5, h6, -⟩ := Mz_zpow_mul μ k g
        apply ih
        · rw [h4, h6]
          have : |g.1 0 0 - k * μ * g.1 1 0| < |g.1 0 0| := by
            rw [show k * μ * g.1 1 0 = k * (μ * g.1 1 0) by ring]
            linarith
          have h7 := Int.natAbs_lt_iff_sq_lt.mpr (sq_lt_sq.mpr (by simpa using this))
          omega
        · rw [h5]
          exact dvd_sub hb (Dvd.intro_left (k * g.1 1 1) (by ring))
      · by_cases h2 : |g.1 0 0| < 2 * |g.1 1 0|
        · -- divide `c` by `a`
          obtain ⟨k, hk⟩ := exists_round (g.1 1 0) (-(g.1 0 0)) (neg_ne_zero.mpr ha)
          rw [abs_neg] at hk
          apply PM.of_Kz k
          obtain ⟨h4, h5, h6, -⟩ := Kz_zpow_mul k g
          apply ih
          · rw [h4, h6]
            have : |g.1 1 0 + k * g.1 0 0| < |g.1 1 0| := by
              rw [show g.1 1 0 + k * g.1 0 0 = g.1 1 0 - k * -(g.1 0 0) by ring]
              linarith
            have h7 := Int.natAbs_lt_iff_sq_lt.mpr (sq_lt_sq.mpr (by simpa using this))
            omega
          · rw [h5]
            exact hb
        · -- the stall is impossible: `a` and `b` are even
          exfalso
          push Not at h1 h2
          have hμ4' : (μ : ℤ) = 4 := by
            by_contra hne
            have : (μ : ℤ) ≤ 3 := by omega
            nlinarith
          rw [hμ4'] at h1 hb
          have hac : |g.1 0 0| = 2 * |g.1 1 0| := by linarith
          have haeven : (2 : ℤ) ∣ g.1 0 0 := by
            rcases abs_cases (g.1 0 0) with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
              rcases abs_cases (g.1 1 0) with ⟨h4, -⟩ | ⟨h4, -⟩ <;> rw [h3, h4] at hac
            · exact ⟨g.1 1 0, by linarith⟩
            · exact ⟨-(g.1 1 0), by linarith⟩
            · exact ⟨-(g.1 1 0), by linarith⟩
            · exact ⟨g.1 1 0, by linarith⟩
          have hbeven : (2 : ℤ) ∣ g.1 0 1 := dvd_trans (by norm_num) hb
          have hdet := det_entries g
          have : (2 : ℤ) ∣ 1 := by
            rw [← hdet]
            exact dvd_sub (Dvd.dvd.mul_right haeven _) (Dvd.dvd.mul_right hbeven _)
          norm_num at this

end Descent

section Upper

variable {μ : ℕ}

theorem Kz_mem_upper : Kz ∈ gammaUpper μ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Step.mat]

theorem Mz_mem_upper : Mz μ ∈ gammaUpper μ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Step.mat]

theorem stepGroup_le_upper : stepGroup μ ≤ gammaUpper μ := by
  rw [stepGroup, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Kz_mem_upper
  · exact Mz_mem_upper

/-- `-1` lies in the step group at `μ = 1` and `μ = 2`, a power of the tick. -/
theorem neg_one_mem_one : (-1 : SL2Z) ∈ stepGroup (1 : ℕ) := by
  have h : (Mz ((1 : ℕ) : ℤ) * Kz) ^ 3 = -1 := by decide +kernel
  rw [← h]
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Mz_mem _) (Kz_mem _)) _

theorem neg_one_mem_two : (-1 : SL2Z) ∈ stepGroup (2 : ℕ) := by
  have h : (Mz ((2 : ℕ) : ℤ) * Kz) ^ 2 = -1 := by decide +kernel
  rw [← h]
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Mz_mem _) (Kz_mem _)) _

/-- For `μ ≤ 4` the step group is all of `Γ¹(μ)`. -/
theorem upper_le_stepGroup (hμ1 : 1 ≤ μ) (hμ4 : μ ≤ 4) : gammaUpper μ ≤ stepGroup μ := by
  intro g hg
  have hb : (μ : ℤ) ∣ g.1 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hg.2.1
  rcases descent hμ1 hμ4 _ g le_rfl hb with h | h
  · exact h
  · -- both `g` and `-g` lie in `Γ¹(μ)`: so `μ ∣ 2`
    have hneg := stepGroup_le_upper h
    have h1 := hg.1
    have h2 := hneg.1
    have h3 : ((-(g.1 0 0) : ℤ) : ZMod μ) = 1 := by
      have : (-g).1 0 0 = -(g.1 0 0) := by simp [Matrix.SpecialLinearGroup.coe_neg]
      rwa [this] at h2
    have h4 : ((2 : ℤ) : ZMod μ) = 0 := by
      push_cast at h1 h3 ⊢
      rw [h1] at h3
      linear_combination -h3
    have h5 : (μ : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h4
    have h6 : μ ∣ 2 := by exact_mod_cast h5
    have h7 : μ = 1 ∨ μ = 2 := (Nat.dvd_prime Nat.prime_two).mp h6
    have hneg1 : (-1 : SL2Z) ∈ stepGroup μ := by
      rcases h7 with rfl | rfl
      · exact neg_one_mem_one
      · exact neg_one_mem_two
    have := Subgroup.mul_mem _ hneg1 h
    simpa using this

/-! The gap: for `μ ≥ 5` a vector with `2|y| ≤ |x|` and `2|x| ≤ μ|y|` lies between the ping-pong
sets. An alternating word sends `(9, 4)` into the sets, so it cannot fix it. -/

variable {G : Type*} [Group G]

/-- A nonempty alternating word in powers of `K` and `M`. `true`: the last-applied letter is `K`. -/
inductive Alt (K M : G) : Bool → G → Prop
  | startK (a : ℤ) (ha : a ≠ 0) : Alt K M true (K ^ a)
  | startM (b : ℤ) (hb : b ≠ 0) : Alt K M false (M ^ b)
  | stepK (a : ℤ) (ha : a ≠ 0) {g : G} (h : Alt K M false g) : Alt K M true (K ^ a * g)
  | stepM (b : ℤ) (hb : b ≠ 0) {g : G} (h : Alt K M true g) : Alt K M false (M ^ b * g)

variable {K M : G}

/-- A power of `K` on an element that is `1` or a word. -/
theorem alt_mulK (c : ℤ) {g : G} (h : g = 1 ∨ Alt K M true g ∨ Alt K M false g) :
    K ^ c * g = 1 ∨ Alt K M true (K ^ c * g) ∨ Alt K M false (K ^ c * g) := by
  by_cases hc : c = 0
  · subst hc
    simpa using h
  rcases h with rfl | h | h
  · right; left
    simpa using Alt.startK c hc
  · cases h with
    | startK a ha =>
      rw [← zpow_add]
      by_cases hs : c + a = 0
      · left
        rw [hs, zpow_zero]
      · right; left
        exact Alt.startK _ hs
    | stepK a ha h' =>
      rw [← mul_assoc, ← zpow_add]
      by_cases hs : c + a = 0
      · right; right
        rw [hs, zpow_zero, one_mul]
        exact h'
      · right; left
        exact Alt.stepK _ hs h'
  · right; left
    exact Alt.stepK c hc h

/-- A power of `M` on an element that is `1` or a word. -/
theorem alt_mulM (c : ℤ) {g : G} (h : g = 1 ∨ Alt K M true g ∨ Alt K M false g) :
    M ^ c * g = 1 ∨ Alt K M true (M ^ c * g) ∨ Alt K M false (M ^ c * g) := by
  by_cases hc : c = 0
  · subst hc
    simpa using h
  rcases h with rfl | h | h
  · right; right
    simpa using Alt.startM c hc
  · right; right
    exact Alt.stepM c hc h
  · cases h with
    | startM a ha =>
      rw [← zpow_add]
      by_cases hs : c + a = 0
      · left
        rw [hs, zpow_zero]
      · right; right
        exact Alt.startM _ hs
    | stepM a ha h' =>
      rw [← mul_assoc, ← zpow_add]
      by_cases hs : c + a = 0
      · right; left
        rw [hs, zpow_zero, one_mul]
        exact h'
      · right; right
        exact Alt.stepM _ hs h'

/-- Every element of `⟨K, M⟩` is `1` or an alternating word. -/
theorem alt_of_mem {g : G} (hg : g ∈ Subgroup.closure {K, M}) :
    g = 1 ∨ Alt K M true g ∨ Alt K M false g := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ ih =>
    rcases hx with rfl | rfl
    · simpa using alt_mulK 1 ih
    · simpa using alt_mulM 1 ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | rfl
    · simpa using alt_mulK (-1) ih
    · simpa using alt_mulM (-1) ih

/-- The action of a law on a vector. -/
def act (g : SL2Z) (x y : ℤ) : ℤ × ℤ := (g.1 0 0 * x + g.1 0 1 * y, g.1 1 0 * x + g.1 1 1 * y)

theorem act_mul (g h : SL2Z) (x y : ℤ) :
    act (g * h) x y = act g (act h x y).1 (act h x y).2 := by
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Prod.mk.injEq]
  constructor <;> ring

theorem act_Kz_zpow (a x y : ℤ) : act (Kz ^ a) x y = (x, y + a * x) := by
  simp only [act, Kz_zpow]
  simp [add_comm]

theorem act_Mz_zpow (μ b x y : ℤ) : act (Mz μ ^ b) x y = (x - b * μ * y, y) := by
  simp only [act, Mz_zpow]
  simp
  ring

theorem abs_lin {a : ℤ} (ha : a ≠ 0) (x y : ℤ) : |x| - |y| ≤ |y + a * x| := by
  have h1 : |a * x| ≤ |y + a * x| + |y| := by
    have := abs_add_le (y + a * x) (-y)
    rwa [show y + a * x + -y = a * x by ring, abs_neg] at this
  have h2 : |x| ≤ |a * x| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs ha)
  linarith

variable {μ₀ : ℤ}

/-- The ping-pong for `μ ≥ 4`: `K^a` carries `X_M` into `X_K`. -/
theorem K_into (hμ : 4 ≤ μ₀) {a x y : ℤ} (ha : a ≠ 0) (h : μ₀ * |y| < 2 * |x|) :
    |x| < 2 * |y + a * x| := by
  have h1 := abs_lin ha x y
  have h2 : 4 * |y| ≤ μ₀ * |y| := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
  linarith

/-- The ping-pong for `μ ≥ 4`: `M^b` carries `X_K` into `X_M`. -/
theorem M_into (hμ : 4 ≤ μ₀) {b x y : ℤ} (hb : b ≠ 0) (h : |x| < 2 * |y|) :
    μ₀ * |y| < 2 * |x - b * μ₀ * y| := by
  have hb' : -b * μ₀ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hb) (by omega)
  have h2 : μ₀ ≤ |-b * μ₀| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ μ₀ by omega)]
    exact le_mul_of_one_le_left (by omega) (Int.one_le_abs hb)
  have h3 : |-b * μ₀ * y| = |-b * μ₀| * |y| := abs_mul _ _
  have h6 : |-b * μ₀| * |y| - |x| ≤ |x + -b * μ₀ * y| := by
    have := abs_add_le (x + -b * μ₀ * y) (-x)
    rw [show x + -b * μ₀ * y + -x = -b * μ₀ * y by ring, abs_neg, h3] at this
    linarith
  rw [show x + -b * μ₀ * y = x - b * μ₀ * y by ring] at h6
  have h7 : μ₀ * |y| ≤ |-b * μ₀| * |y| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have h8 : 0 < |y| := by
    have := abs_nonneg x
    omega
  nlinarith

/-- For `μ ≥ 5`, an alternating word sends `(9, 4)` into the ping-pong sets. -/
theorem alt_act (hμ : 5 ≤ μ₀) {b : Bool} {g : SL2Z} (h : Alt Kz (Mz μ₀) b g) :
    (b = true → |(act g 9 4).1| < 2 * |(act g 9 4).2|) ∧
    (b = false → μ₀ * |(act g 9 4).2| < 2 * |(act g 9 4).1|) := by
  have hμ4 : 4 ≤ μ₀ := by omega
  induction h with
  | startK a ha =>
    refine ⟨fun _ => ?_, by simp⟩
    rw [act_Kz_zpow]
    have := abs_lin ha 9 4
    norm_num at this ⊢
    omega
  | startM c hc =>
    refine ⟨by simp, fun _ => ?_⟩
    rw [act_Mz_zpow]
    simp only
    have h1 : (4 : ℤ) * μ₀ - 9 ≤ |9 - c * μ₀ * 4| := by
      have h3 : μ₀ ≤ |c| * μ₀ := le_mul_of_one_le_left (by omega) (Int.one_le_abs hc)
      have h4 := abs_add_le (9 - c * μ₀ * 4) (-9)
      rw [show (9 : ℤ) - c * μ₀ * 4 + -9 = c * μ₀ * 4 * -1 by ring, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ μ₀ by omega)] at h4
      norm_num at h4
      linarith
    norm_num
    linarith
  | stepK a ha _ ih =>
    refine ⟨fun _ => ?_, by simp⟩
    rw [act_mul, act_Kz_zpow]
    exact K_into hμ4 ha (ih.2 rfl)
  | stepM c hc _ ih =>
    refine ⟨by simp, fun _ => ?_⟩
    rw [act_mul, act_Mz_zpow]
    exact M_into hμ4 hc (ih.1 rfl)

/-- For `μ ≥ 5`, only `1` in the step group fixes `(9, 4)`. -/
theorem fix_eq_one (hμ : 5 ≤ μ₀) {g : SL2Z} (hg : g ∈ stepGroup μ₀)
    (hfix : act g 9 4 = (9, 4)) : g = 1 := by
  rcases alt_of_mem hg with h | h | h
  · exact h
  · have := (alt_act hμ h).1 rfl
    rw [hfix] at this
    norm_num at this
  · have := (alt_act hμ h).2 rfl
    rw [hfix] at this
    norm_num at this
    omega

/-- A parabolic element that fixes `(9, 4)`. -/
def parab : SL2Z := ⟨!![-35, 81; -16, 37], by rw [Matrix.det_fin_two_of]; norm_num⟩

theorem parab_pow (k : ℕ) : ((parab ^ k : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![1 - 36 * (k : ℤ), 81 * k; -16 * k, 1 + 36 * k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    change _ * !![-35, 81; -16, 37] = _
    rw [Matrix.mul_fin_two]
    push_cast
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem parab_pow_act (k : ℕ) : act (parab ^ k) 9 4 = (9, 4) := by
  simp only [act, parab_pow]
  simp
  constructor <;> ring

theorem parab_pow_ne (k : ℕ) (hk : k ≠ 0) : parab ^ k ≠ 1 := by
  intro h
  have : ((parab ^ k : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (1 : SL2Z).1 0 1 := by rw [h]
  rw [parab_pow] at this
  have h2 : (81 : ℤ) * k = 0 := by simpa using this
  exact hk (by omega)

/-- For `μ ≥ 5` no nonzero power of the parabolic element lies in the step group. -/
theorem parab_pow_not_mem (hμ : 5 ≤ μ₀) (k : ℕ) (hk : k ≠ 0) : parab ^ k ∉ stepGroup μ₀ :=
  fun hmem => parab_pow_ne k hk (fix_eq_one hμ hmem (parab_pow_act k))

/-- For `μ ≥ 5` the step group has infinite index. -/
theorem index_eq_zero (hμ : 5 ≤ μ₀) : (stepGroup μ₀).index = 0 := by
  rw [Subgroup.index, Nat.card_eq_zero]
  right
  let f : ℕ → SL2Z ⧸ stepGroup μ₀ := fun k => ((parab ^ k : SL2Z) : SL2Z ⧸ stepGroup μ₀)
  refine Infinite.of_injective f ?_
  intro j k hjk
  by_contra hne
  wlog hlt : j < k generalizing j k
  · exact this hjk.symm (Ne.symm hne) (by omega)
  have hmem := QuotientGroup.eq.mp hjk
  rw [show (parab ^ j)⁻¹ * parab ^ k = parab ^ (k - j) by
    rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]] at hmem
  exact parab_pow_not_mem hμ (k - j) (by omega) hmem

/-- For `μ ≥ 5` the step group is not `Γ¹(μ)`: the `μ`-th power of the parabolic element is in
`Γ¹(μ)`. -/
theorem stepGroup_ne_upper {μ : ℕ} (hμ : 5 ≤ μ) : stepGroup μ ≠ gammaUpper μ := by
  intro e
  have hmem : parab ^ μ ∈ gammaUpper μ := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [parab_pow] <;> simp
  rw [← e] at hmem
  exact parab_pow_not_mem (μ₀ := μ) (by omega) μ (by omega) hmem

end Upper

section Index

variable {μ : ℕ}

/-- The first row of a law on the dial `Z/μ`. -/
def rowOf (μ : ℕ) (g : SL2Z) : ZMod μ × ZMod μ := ((g.1 0 0 : ZMod μ), (g.1 0 1 : ZMod μ))

/-- A primitive row: its entries generate the unit ideal. -/
def Prim (μ : ℕ) : Set (ZMod μ × ZMod μ) := {p | ∃ a b : ZMod μ, a * p.1 + b * p.2 = 1}

theorem mem_upper_of_row {g : SL2Z} (h1 : ((g.1 0 0 : ℤ) : ZMod μ) = 1)
    (h2 : ((g.1 0 1 : ℤ) : ZMod μ) = 0) : g ∈ gammaUpper μ := by
  refine ⟨h1, h2, ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod μ) (det_entries g)
  push_cast at this
  rw [h1, h2] at this
  simpa using this

theorem rowOf_mul_of_mem {h : SL2Z} (hh : h ∈ gammaUpper μ) (g : SL2Z) :
    rowOf μ (h * g) = rowOf μ g := by
  obtain ⟨h1, h2, -⟩ := hh
  simp only [rowOf, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Int.cast_add, Int.cast_mul, h1, h2]
  simp

theorem rowOf_eq_iff (g g' : SL2Z) : rowOf μ g = rowOf μ g' ↔ g' * g⁻¹ ∈ gammaUpper μ := by
  constructor
  · intro e
    simp only [rowOf, Prod.mk.injEq] at e
    have hdet := congrArg (Int.cast : ℤ → ZMod μ) (det_entries g)
    push_cast at hdet
    apply mem_upper_of_row
    · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      push_cast
      rw [← e.1, ← e.2]
      linear_combination hdet
    · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      push_cast
      rw [← e.1, ← e.2]
      ring
  · intro h
    have := rowOf_mul_of_mem h g
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem rowOf_mem_prim (g : SL2Z) : rowOf μ g ∈ Prim μ := by
  refine ⟨(g.1 1 1 : ZMod μ), -(g.1 1 0 : ZMod μ), ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod μ) (det_entries g)
  push_cast at this
  simp only [rowOf]
  linear_combination this

/-- The reduction of `SL(2, ℤ)` onto `SL(2, Z/μ)`: the kick and the move lift. -/
theorem map_surjective [NeZero μ] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod μ))) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← Bells.closure_KM (n := μ), Subgroup.closure_le]
  rintro x (rfl | rfl)
  · refine ⟨Kz, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Step.mat, Bells.Kp]
  · refine ⟨Mz 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Step.mat, Bells.Mp]

theorem exists_rowOf [NeZero μ] {p : ZMod μ × ZMod μ} (hp : p ∈ Prim μ) : ∃ g, rowOf μ g = p := by
  obtain ⟨a, b, hab⟩ := hp
  let g₀ : SpecialLinearGroup (Fin 2) (ZMod μ) :=
    ⟨!![p.1, p.2; -b, a], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩
  obtain ⟨g, hg⟩ := map_surjective (μ := μ) g₀
  refine ⟨g, ?_⟩
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 2) (ZMod μ) => x.1 0 0) hg
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin 2) (ZMod μ) => x.1 0 1) hg
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast] at h1 h2
  exact Prod.ext h1 h2

/-- The index of `Γ¹(μ)` is the number of primitive rows. -/
theorem index_upper [NeZero μ] : (gammaUpper μ).index = Nat.card (Prim μ) := by
  rw [Subgroup.index, ← Nat.card_congr
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (gammaUpper μ))]
  let φ : Quotient (QuotientGroup.rightRel (gammaUpper μ)) → Prim μ :=
    Quotient.lift (fun g => ⟨rowOf μ g, rowOf_mem_prim g⟩) (by
      intro a b hab
      apply Subtype.ext
      exact (rowOf_eq_iff a b).mpr (QuotientGroup.rightRel_apply.mp hab))
  refine Nat.card_congr (Equiv.ofBijective φ ⟨?_, ?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    intro hxy
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr ((rowOf_eq_iff a b).mp (congrArg Subtype.val hxy))
  · rintro ⟨p, hp⟩
    obtain ⟨g, hg⟩ := exists_rowOf hp
    exact ⟨Quotient.mk _ g, Subtype.ext hg⟩

theorem card_prim [NeZero μ] : Nat.card (Prim μ) =
    (Finset.univ.filter fun p : ZMod μ × ZMod μ => ∃ a b : ZMod μ, a * p.1 + b * p.2 = 1).card := by
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  congr 2
  ext p
  simp [Prim]

/-- The indices `1`, `3`, `8`, `12` of the step groups at the pulls `1`, `2`, `3`, `4`. -/
theorem index_small : (gammaUpper 1).index = 1 ∧ (gammaUpper 2).index = 3 ∧
    (gammaUpper 3).index = 8 ∧ (gammaUpper 4).index = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [index_upper, card_prim] <;> decide +kernel

end Index

section Free

open scoped Pointwise Function

/-- The ping-pong for two cyclic groups, from Mathlib's lemma for free products. -/
theorem free_of_ping_pong {G α : Type*} [Group G] [MulAction G α] (a : Fin 2 → G)
    (X : Fin 2 → Set α) (hne : ∀ i, (X i).Nonempty) (hdisj : Pairwise (Disjoint on X))
    (hpp : ∀ i j, i ≠ j → ∀ k : ℤ, k ≠ 0 → a i ^ k • X j ⊆ X i) :
    Function.Injective (FreeGroup.lift a) := by
  have hlift : FreeGroup.lift a =
      (Monoid.CoprodI.lift fun i => FreeGroup.lift fun _ : Unit => a i).comp
        (@freeGroupEquivCoprodI (Fin 2)).toMonoidHom := by
    ext i
    simp
  rw [hlift, MonoidHom.coe_comp]
  refine Function.Injective.comp ?_ (MulEquiv.injective _)
  refine Monoid.CoprodI.lift_injective_of_ping_pong _ (Or.inr ⟨0, ?_⟩) X hne hdisj ?_
  · have : Infinite (FreeGroup Unit) :=
      Infinite.of_injective _ FreeGroup.freeGroupUnitEquivInt.symm.injective
    exact le_trans (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3)).le)
      (Cardinal.aleph0_le_mk _)
  · intro i j hij h hh
    have hk : FreeGroup.freeGroupUnitEquivInt h ≠ 0 := by
      intro e
      apply hh
      have := FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h
      rw [e] at this
      rw [← this]
      simp [FreeGroup.freeGroupUnitEquivInt]
    have hval : FreeGroup.lift (fun _ : Unit => a i) h =
        a i ^ FreeGroup.freeGroupUnitEquivInt h := by
      conv_lhs => rw [← FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h]
      simp [FreeGroup.freeGroupUnitEquivInt]
    rw [hval]
    exact hpp i j hij _ hk

/-- The law acting on the plane. -/
abbrev vecAction : MulAction (SpecialLinearGroup (Fin 2) ℝ) (Fin 2 → ℝ) where
  smul g v := g.1.mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.1 h.1).symm

/-- The kick over the reals. -/
abbrev KR : SpecialLinearGroup (Fin 2) ℝ := (Step.kick (1 : ℝ)).sl

/-- The move over the reals, at the pull `μ`. -/
abbrev MR (μ : ℝ) : SpecialLinearGroup (Fin 2) ℝ := (Step.move (-μ)).sl

theorem KR_zpow (k : ℤ) : ((KR ^ k : SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![1, 0; (k : ℝ), 1] := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih]
    change _ * !![1, 0; 1, 1] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | pred k ih =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv]
    change _ * Matrix.adjugate !![1, 0; 1, 1] = _
    rw [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem MR_zpow (μ : ℝ) (k : ℤ) : ((MR μ ^ k : SpecialLinearGroup (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = !![1, -((k : ℝ) * μ); 0, 1] := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih]
    change _ * !![1, -μ; 0, 1] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  | pred k ih =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv]
    change _ * Matrix.adjugate !![1, -μ; 0, 1] = _
    rw [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem abs_lin_real {a : ℝ} (ha : 1 ≤ |a|) (x y : ℝ) : |x| - |y| ≤ |y + a * x| := by
  have h1 : |a * x| ≤ |y + a * x| + |y| := by
    have := abs_add_le (y + a * x) (-y)
    rwa [show y + a * x + -y = a * x by ring, abs_neg] at this
  have h2 : |x| ≤ |a * x| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) ha
  linarith

/-- The ping-pong of two cyclic groups on two sets. -/
theorem free_of_ping_pong₂ {G α : Type*} [Group G] [MulAction G α] (a b : G) (X Y : Set α)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hd : Disjoint X Y)
    (h1 : ∀ k : ℤ, k ≠ 0 → a ^ k • Y ⊆ X) (h2 : ∀ k : ℤ, k ≠ 0 → b ^ k • X ⊆ Y) :
    Function.Injective (FreeGroup.lift ![a, b]) := by
  refine free_of_ping_pong ![a, b] ![X, Y] (Fin.forall_fin_two.mpr ⟨hX, hY⟩) ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hd
    · exact hd.symm
    · exact absurd rfl hij
  · intro i j hij k hk
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h1 k hk
    · exact h2 k hk
    · exact absurd rfl hij

/-- Over the reals, for every `μ ≥ 4`, the kick and the move generate a free group (Sanov at
`μ = 4`, Brenner beyond). -/
theorem free_real {μ : ℝ} (hμ : 4 ≤ μ) : Function.Injective (FreeGroup.lift ![KR, MR μ]) := by
  let _ := vecAction
  refine free_of_ping_pong₂ (α := Fin 2 → ℝ) KR (MR μ) {v | |v 0| < 2 * |v 1|}
    {v | 2 * |v 1| < |v 0|} ⟨![0, 1], by simp⟩ ⟨![1, 0], by simp⟩ ?_ ?_ ?_
  · rw [Set.disjoint_iff]
    rintro v ⟨h1, h2⟩
    have h1' : |v 0| < 2 * |v 1| := h1
    have h2' : 2 * |v 1| < |v 0| := h2
    linarith
  · rintro k hk _ ⟨v, hv, rfl⟩
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hv' : 2 * |v 1| < |v 0| := hv
    change |((KR ^ k : SpecialLinearGroup (Fin 2) ℝ).1.mulVec v) 0| <
      2 * |((KR ^ k : SpecialLinearGroup (Fin 2) ℝ).1.mulVec v) 1|
    rw [KR_zpow, Matrix.mulVec_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have h3 := abs_lin_real hk1 (v 0) (v 1)
    rw [show (1 : ℝ) * v 0 + 0 * v 1 = v 0 by ring,
      show (k : ℝ) * v 0 + 1 * v 1 = v 1 + k * v 0 by ring]
    linarith
  · rintro k hk _ ⟨v, hv, rfl⟩
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hv' : |v 0| < 2 * |v 1| := hv
    change 2 * |((MR μ ^ k : SpecialLinearGroup (Fin 2) ℝ).1.mulVec v) 1| <
      |((MR μ ^ k : SpecialLinearGroup (Fin 2) ℝ).1.mulVec v) 0|
    rw [MR_zpow, Matrix.mulVec_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show (0 : ℝ) * v 0 + 1 * v 1 = v 1 by ring,
      show (1 : ℝ) * v 0 + -((k : ℝ) * μ) * v 1 = v 0 + (-((k : ℝ) * μ)) * v 1 by ring]
    have hkμ : (4 : ℝ) ≤ |-((k : ℝ) * μ)| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (show 0 ≤ μ by linarith)]
      nlinarith
    have h3 := abs_add_le (v 0 + (-((k : ℝ) * μ)) * v 1) (-(v 0))
    rw [show v 0 + (-((k : ℝ) * μ)) * v 1 + -(v 0) = (-((k : ℝ) * μ)) * v 1 by ring, abs_neg,
      abs_mul] at h3
    have h4 : 4 * |v 1| ≤ |-((k : ℝ) * μ)| * |v 1| :=
      mul_le_mul_of_nonneg_right hkμ (abs_nonneg _)
    linarith

/-- The reduction of integer laws to real laws. -/
theorem map_lift_eq (μ : ℤ) (w : FreeGroup (Fin 2)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (FreeGroup.lift ![Kz, Mz μ] w) =
      FreeGroup.lift ![KR, MR μ] w := by
  have hK : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) Kz = KR := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Step.mat]
  have hM : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (Mz μ) = MR μ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Step.mat]
  have h : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp (FreeGroup.lift ![Kz, Mz μ]) =
      FreeGroup.lift ![KR, MR μ] := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i
    · change Matrix.SpecialLinearGroup.map _ (FreeGroup.lift _ (FreeGroup.of 0)) =
        FreeGroup.lift _ (FreeGroup.of 0)
      rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      exact hK
    · change Matrix.SpecialLinearGroup.map _ (FreeGroup.lift _ (FreeGroup.of 1)) =
        FreeGroup.lift _ (FreeGroup.of 1)
      rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      exact hM
  exact DFunLike.congr_fun h w

/-- Over the integers, for every `μ ≥ 4`, the kick and the move generate a free group. -/
theorem free_int {μ : ℤ} (hμ : 4 ≤ μ) : Function.Injective (FreeGroup.lift ![Kz, Mz μ]) := by
  intro v w hvw
  apply free_real (μ := (μ : ℝ)) (by exact_mod_cast hμ)
  rw [← map_lift_eq, ← map_lift_eq, hvw]

/-- A word that is not `1`, whose law is `(M K)^n`. -/
theorem not_free_of_pow {μ : ℤ} {n : ℕ} (hn : n ≠ 0) (h : (Mz μ * Kz) ^ n = 1) :
    ¬ Function.Injective (FreeGroup.lift ![Kz, Mz μ]) := by
  intro hinj
  let x : FreeGroup (Fin 2) := FreeGroup.of 1 * FreeGroup.of 0
  have hx : FreeGroup.lift ![Kz, Mz μ] (x ^ n) = 1 := by
    rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    simpa using h
  have h1 : x ^ n = 1 := hinj (hx.trans (map_one _).symm)
  let φ : FreeGroup (Fin 2) →* Multiplicative ℤ :=
    FreeGroup.lift fun _ => Multiplicative.ofAdd 1
  have h2 := congrArg φ h1
  rw [map_pow, map_mul, map_one] at h2
  simp only [φ, FreeGroup.lift_apply_of] at h2
  have h3 := congrArg Multiplicative.toAdd h2
  simp at h3
  omega

end Free

section Orders

theorem tick_eq (μ : ℤ) : tick μ = Mz μ * Kz := by
  simp [tick, realize]

/-- The tick's powers and its phase: `T² = t T - 1`. -/
theorem tick_sq_mat (μ : ℤ) : (!![1 - μ, -μ; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 =
    (2 - μ) • !![1 - μ, -μ; 1, 1] - 1 := by
  rw [sq, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The trace of a power of the tick. -/
def traceSeq (μ : ℤ) (n : ℕ) : ℤ :=
  Matrix.trace ((!![1 - μ, -μ; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ n)

theorem traceSeq_rec (μ : ℤ) (n : ℕ) :
    traceSeq μ (n + 2) = (2 - μ) * traceSeq μ (n + 1) - traceSeq μ n := by
  simp only [traceSeq]
  rw [show n + 2 = n + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc, ← sq, tick_sq_mat, mul_sub,
    mul_one, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, ← pow_succ, smul_eq_mul]

theorem traceSeq_zero (μ : ℤ) : traceSeq μ 0 = 2 := by
  simp [traceSeq]

theorem traceSeq_one (μ : ℤ) : traceSeq μ 1 = 2 - μ := by
  simp [traceSeq, Matrix.trace_fin_two]
  ring

/-- For `μ ≥ 5` the traces of the powers grow strictly in size. -/
theorem traceSeq_grow {μ : ℤ} (hμ : 5 ≤ μ) (n : ℕ) :
    |traceSeq μ n| + 1 ≤ |traceSeq μ (n + 1)| := by
  induction n with
  | zero =>
    rw [traceSeq_zero, traceSeq_one, abs_of_nonpos (show 2 - μ ≤ 0 by omega)]
    norm_num
    omega
  | succ n ih =>
    rw [traceSeq_rec]
    set a := traceSeq μ (n + 1)
    set b := traceSeq μ n
    have h1 : |(2 - μ)| = μ - 2 := by
      rw [abs_of_nonpos (by omega)]
      ring
    have h2 : |(2 - μ) * a| ≤ |(2 - μ) * a - b| + |b| := by
      have := abs_add_le ((2 - μ) * a - b) b
      rwa [sub_add_cancel] at this
    rw [abs_mul, h1] at h2
    have h3 : 3 * |a| ≤ (μ - 2) * |a| := mul_le_mul_of_nonneg_right (by omega) (abs_nonneg _)
    have h4 := abs_nonneg b
    linarith

/-- For `μ ≥ 5` the tick has infinite order: the traces of its powers are not `2`. -/
theorem tick_pow_ne {μ : ℤ} (hμ : 5 ≤ μ) (k : ℕ) (hk : 0 < k) : tick μ ^ k ≠ 1 := by
  rw [Ne, tick_pow_eq_one_iff]
  intro h
  have hgt : 3 ≤ |traceSeq μ k| := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h0 : ∀ m, 2 ≤ |traceSeq μ m| := by
      intro m
      induction m with
      | zero => rw [traceSeq_zero]; norm_num
      | succ m ih => have := traceSeq_grow hμ m; omega
    have := traceSeq_grow hμ j
    have := h0 j
    omega
  have h2 : traceSeq μ k = 2 := by
    simp only [traceSeq, h]
    simp
  rw [h2] at hgt
  norm_num at hgt

/-- For `μ = 0` the tick is the kick. -/
theorem tick_zero_pow (n : ℕ) :
    ((tick 0 ^ n : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (n : ℤ), 1] := by
  have h : tick 0 = Kz := by
    rw [tick_eq]
    have : Mz 0 = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Step.mat]
    rw [this, one_mul]
  rw [h]
  have := Kz_zpow n
  simpa using this

/-- For `μ = 4` the powers of the tick grow linearly. -/
theorem tick_four_pow' (n : ℕ) : ((tick 4 ^ n : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
    (-1 : ℤ) ^ n • !![1 + 2 * (n : ℤ), 4 * n; -n, 1 - 2 * n] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, tick_mat, ← tick_four_pow n]
  norm_num

/-- The tick has finite order exactly at the pulls `μ = 1, 2, 3`. -/
theorem finite_order_iff (μ : ℕ) : IsOfFinOrder (tick μ) ↔ μ = 1 ∨ μ = 2 ∨ μ = 3 := by
  have hstep := stepOrders
  rw [Statement.stepOrders] at hstep
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩, h4⟩ := hstep
  constructor
  · intro h
    obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    by_contra hne
    push Not at hne
    rcases Nat.lt_or_ge μ 5 with hlt | hge
    · interval_cases μ
      · -- `μ = 0`: the `(1, 0)` entry of `T^k` is `k`
        have e := tick_zero_pow k
        rw [show ((0 : ℕ) : ℤ) = 0 by rfl, hpow] at *
        have := congrFun (congrFun e 1) 0
        simp at this
        omega
      · exact hne.1 rfl
      · exact hne.2.1 rfl
      · exact hne.2.2 rfl
      · exact h4 k hk hpow
    · exact tick_pow_ne (μ := μ) (by exact_mod_cast hge) k hk hpow
  · rintro (rfl | rfl | rfl)
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by norm_num, h1⟩
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h2⟩
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩

theorem growth_rel {μ : ℝ} (hμ : 5 ≤ μ) :
    1 < growth μ ∧ growth μ + (growth μ)⁻¹ = μ - 2 := by
  have hΔ : 0 ≤ μ ^ 2 - 4 * μ := by nlinarith
  have hsq := Real.sq_sqrt hΔ
  have hnn := Real.sqrt_nonneg (μ ^ 2 - 4 * μ)
  have h1 : 1 < growth μ := by
    unfold growth
    linarith
  refine ⟨h1, ?_⟩
  have h0 : growth μ ≠ 0 := by linarith
  field_simp
  unfold growth
  nlinarith

/-- For `μ ≥ 5` the trace of `T^n` is `(-ρ)^n + (-ρ)^(-n)`: the tick grows by `ρ` per tick. -/
theorem trace_growth {μ : ℕ} (hμ : 5 ≤ μ) (n : ℕ) :
    (traceSeq μ n : ℝ) = (-growth μ) ^ n + ((-growth μ)⁻¹) ^ n := by
  obtain ⟨h1, h2⟩ := growth_rel (μ := μ) (by exact_mod_cast hμ)
  set ρ := growth μ with hρ
  have h0 : ρ ≠ 0 := by linarith
  have hrec : ∀ k, (-ρ) ^ (k + 2) + ((-ρ)⁻¹) ^ (k + 2) =
      (2 - (μ : ℝ)) * ((-ρ) ^ (k + 1) + ((-ρ)⁻¹) ^ (k + 1)) - ((-ρ) ^ k + ((-ρ)⁻¹) ^ k) := by
    intro k
    have ht : (2 - (μ : ℝ)) = -ρ + (-ρ)⁻¹ := by
      rw [inv_neg]
      linarith
    rw [ht]
    have hne : -ρ ≠ 0 := neg_ne_zero.mpr h0
    have hrr : -ρ * (-ρ)⁻¹ = 1 := mul_inv_cancel₀ hne
    linear_combination (-((-ρ) ^ k + ((-ρ)⁻¹) ^ k)) * hrr
  induction n using Nat.twoStepInduction with
  | zero => simp [traceSeq_zero]; norm_num
  | one =>
    rw [traceSeq_one]
    push_cast
    rw [pow_one, pow_one, inv_neg]
    linarith
  | more k ih1 ih2 =>
    rw [traceSeq_rec]
    push_cast
    rw [ih1, ih2, hrec]

end Orders

end Artform.Scores.StepGroup

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open StepGroup

/-- **T13** (Theorem Q, part 1: the tick's orders and growth). -/
@[ledger "T13"]
theorem tickGrowth : Statement.tickGrowth := by
  refine ⟨finite_order_iff, tick_zero_pow, tick_four_pow', fun μ hμ => ?_⟩
  refine ⟨(growth_rel (μ := μ) (by exact_mod_cast hμ)).1, fun n => ?_⟩
  have := trace_growth hμ n
  rw [Matrix.SpecialLinearGroup.coe_pow, tick_mat]
  exact this

/-- **T13** (Theorem Q, part 2: the step groups). -/
@[ledger "T13"]
theorem stepGroups : Statement.stepGroups := by
  obtain ⟨h1, h2, h3, h4⟩ := index_small
  have heq : ∀ μ : ℕ, 1 ≤ μ → μ ≤ 4 → stepGroup μ = gammaUpper μ := fun μ h h' =>
    le_antisymm stepGroup_le_upper (upper_le_stepGroup h h')
  refine ⟨fun μ hμ => ⟨stepGroup_le_upper, fun e => ?_, heq μ hμ⟩, ?_, ?_, ?_, ?_,
    fun μ hμ => index_eq_zero hμ, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  · by_contra hne
    exact stepGroup_ne_upper (by omega) e
  · rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, heq 1 (by norm_num) (by norm_num)]
    exact h1
  · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, heq 2 (by norm_num) (by norm_num)]
    exact h2
  · rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, heq 3 (by norm_num) (by norm_num)]
    exact h3
  · rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, heq 4 (by norm_num) (by norm_num)]
    exact h4

/-- **T13** (Theorem Q, part 3: freeness). -/
@[ledger "T13"]
theorem stepGroupsFree : Statement.stepGroupsFree := by
  refine ⟨fun μ hμ => free_real hμ,
    fun μ hμ => ⟨fun hinj => ?_, fun h => free_int (by exact_mod_cast h)⟩⟩
  by_contra hlt
  have hcases : μ = 1 ∨ μ = 2 ∨ μ = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · refine not_free_of_pow (n := 6) (by norm_num) ?_ hinj
    rw [← tick_eq]
    exact stepOrders.1.1
  · refine not_free_of_pow (n := 4) (by norm_num) ?_ hinj
    rw [← tick_eq]
    exact stepOrders.2.1.1
  · refine not_free_of_pow (n := 3) (by norm_num) ?_ hinj
    rw [← tick_eq]
    exact stepOrders.2.2.1.1

/-! ## Non-vacuity

The fifth power of the parabolic law is an element of `Γ¹(5)` outside `Σ_5`.
-/

example : parab ^ 5 ∈ gammaUpper 5 ∧ parab ^ 5 ∉ stepGroup ((5 : ℕ) : ℤ) := by
  refine ⟨?_, parab_pow_not_mem (by norm_num) 5 (by norm_num)⟩
  change (((parab ^ 5).1 0 0 : ℤ) : ZMod 5) = 1 ∧ (((parab ^ 5).1 0 1 : ℤ) : ZMod 5) = 0 ∧
    (((parab ^ 5).1 1 1 : ℤ) : ZMod 5) = 1
  decide +kernel

end Artform.Scores
