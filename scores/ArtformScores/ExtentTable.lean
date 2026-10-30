import ArtformScores.Certificates.Extents

/-!
# The table of extents

The rest of the ledger's finding 043: the table of forward extents (Theorem S5.3, part 3), the
fewest back-steps (Theorem S5.4), and the two squares.
- **No extent.** Rankin's parity, when `c` has odd order and `L_K` is even, or lifting when
  `-1 ∈ ⟨c⟩`.
- **Some run.** A checked word (`Certificates/Extents.lean`).
- **Few back-steps.** The balance and a small computation with `c` and the offsets.
- **The exact count.** By Rankin's links, an extent is a choice on the cosets of `⟨c⟩`. A table
  numbers the cosets, and the kernel tries every choice, walking from `1` until the walk comes back.
-/

namespace Artform.Scores.Bells

open Equiv
open Matrix (SpecialLinearGroup)

section Sign

variable {G : Type*} [Group G]

/-- The sign of a left multiplication: one cycle of length `ord g` for each coset of `⟨g⟩`. -/
theorem sign_mulLeft_eq [Fintype G] [DecidableEq G] {g : G} (hg : g ≠ 1) :
    Perm.sign (Equiv.mulLeft g) = ((-1) ^ (orderOf g + 1)) ^ (Subgroup.zpowers g).index := by
  have hper : ∀ x, Equiv.mulLeft g x ≠ x → ∀ j : ℕ,
      (Equiv.mulLeft g ^ j) x = x ↔ orderOf g ∣ j := by
    intro x _ j
    rw [mulLeft_pow_apply, mul_eq_right, orderOf_dvd_iff_pow_eq_one]
  obtain ⟨m, hm, hs⟩ := sign_of_period _ (orderOf g) hper
  have hsupp : (Equiv.mulLeft g).support.card = Fintype.card G := by
    rw [← Finset.card_univ]
    congr 1
    ext x
    simp [Perm.mem_support, hg]
  have hidx := Subgroup.card_mul_index (Subgroup.zpowers g)
  rw [Nat.card_zpowers, Nat.card_eq_fintype_card, ← hsupp, ← hm, mul_comm] at hidx
  have hmi : m = (Subgroup.zpowers g).index :=
    (Nat.eq_of_mul_eq_mul_right (orderOf_pos g) hidx).symm
  rw [hs, hmi]

end Sign

section Forward

variable {n : ℕ}

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)
local notation "PSLn" => SpecialLinearGroup (Fin 2) (ZMod n) ⧸ pmOne n

theorem orderOf_Kn_SL : orderOf (Kn n) = n := by
  have h : ∀ j : ℕ, Kn n ^ j = 1 ↔ n ∣ j := by
    intro j
    rw [← ZMod.natCast_eq_zero_iff]
    constructor
    · intro e
      have : ((Kn n ^ j : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0 =
          ((1 : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0 := by rw [e]
      rw [Kn_pow, Matrix.SpecialLinearGroup.coe_one] at this
      simpa using this
    · intro e
      apply Subtype.ext
      rw [Kn_pow, e, Matrix.SpecialLinearGroup.coe_one]
      ext i k
      fin_cases i <;> fin_cases k <;> simp
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((h n).mpr dvd_rfl))
    ((h _).mp (pow_orderOf_eq_one _))

theorem card_pmOne (hn : 3 ≤ n) : Nat.card (pmOne n) = 2 := by
  have : Fact (1 < n) := ⟨by omega⟩
  rw [pmOne, Nat.card_zpowers]
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    simp
  · intro e
    have := congrArg (fun g : SLn => (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0) e
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply two_ne_zero_of hn
    linear_combination -this

/-- `L_K` is even on `SL(2, Z/n)`: its cycles are twice as many as on `PSL(2, Z/n)`. -/
theorem sign_mulLeft_Kn_SL (hn : 3 ≤ n) [NeZero n] :
    Perm.sign (Equiv.mulLeft (Kn n)) = 1 := by
  have hK1 : Kn n ≠ 1 := by
    intro h
    have := orderOf_Kn_SL (n := n)
    rw [h, orderOf_one] at this
    omega
  rw [sign_mulLeft_eq hK1]
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers (Kn n))
  have h2 := Subgroup.card_mul_index (Subgroup.zpowers ((Kn n : SLn) : PSLn))
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pmOne n)
  rw [card_pmOne hn] at h3
  rw [Nat.card_zpowers, orderOf_Kn_SL] at h1
  rw [Nat.card_zpowers, orderOf_Kn_PSL hn] at h2
  rw [h3, ← h2, mul_assoc] at h1
  have h4 := Nat.eq_of_mul_eq_mul_left (by omega) h1
  rw [h4, mul_comm, pow_mul, Int.units_sq, one_pow]

theorem two_dvd_card_SLn (hn : 3 ≤ n) [NeZero n] : 2 ∣ Fintype.card SLn := by
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pmOne n)
  rw [card_pmOne hn, Nat.card_eq_fintype_card] at h3
  exact ⟨_, h3.trans (mul_comm _ _)⟩

variable [NeZero n]

theorem odd_order_of_period {G : Type*} [Group G] {x : G} {m : ℕ} (hm : Odd m) (h : x ^ m = 1) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h)

/-- No forward extent of `PSL(2, Z/n)` when `c` has an odd period there. -/
theorem no_forward_PSL (hn : 3 ≤ n) {m : ℕ} (hm : Odd m)
    (h : codePSL n (iterC (nextQuad n) m (oneQuad n)) = codePSL n (oneQuad n)) (σ : Perm PSLn) :
    ¬ IsExtent ((Kn n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ := by
  classical
  let _ : Fintype PSLn := Fintype.ofFinite _
  refine no_extent_of_sign (sign_mulLeft_Kn hn) ?_ (two_dvd_card_PSLn hn) σ
  rw [← encSL_one] at h
  exact odd_order_of_period hm ((modelPSL n).pow_period h)

/-- No forward extent of `SL(2, Z/n)` when `c` has an odd period there. -/
theorem no_forward_SL (hn : 3 ≤ n) {m : ℕ} (hm : Odd m)
    (h : codeQuad n (iterC (nextQuad n) m (oneQuad n)) = codeQuad n (oneQuad n)) (σ : Perm SLn) :
    ¬ IsExtent (Kn n) (Mp n) σ := by
  classical
  refine no_extent_of_sign (sign_mulLeft_Kn_SL hn) ?_ (two_dvd_card_SLn hn) σ
  rw [← encSL_one] at h
  exact odd_order_of_period hm ((modelSL n).pow_period h)

/-- No forward extent of `SL(2, Z/n)` when `-1 ∈ ⟨c⟩` and `PSL(2, Z/n)` has none. -/
theorem no_forward_SL_of_lift {m : ℕ}
    (h : codeQuad n (iterC (nextQuad n) m (oneQuad n)) = codeQuad n (negQuad n (oneQuad n)))
    (hP : ∀ σ : Perm PSLn, ¬ IsExtent ((Kn n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ)
    (σ : Perm SLn) : ¬ IsExtent (Kn n) (Mp n) σ := by
  intro hσ
  rw [← encSL_one, ← encSL_neg] at h
  have hc := (modelSL n).pow_of_code (g := 1) (h := -1) h
  simp only [mul_one, MonoidHom.id_apply] at hc
  have hN : pmOne n ≤ Subgroup.zpowers ((Kn n)⁻¹ * Mp n) := by
    intro g hg
    rcases (mem_pmOne_iff g).mp hg with rfl | rfl
    · exact Subgroup.one_mem _
    · rw [← hc]
      exact Subgroup.npow_mem_zpowers _ _
  obtain ⟨σ', hσ', -⟩ := extent_lift hN hσ
  exact hP σ' hσ'

end Forward

section Fewest

variable {G₀ G S : Type*} [Group G₀] [Group G] [Finite G] {A₀ B₀ : G₀} {π : G₀ →* G}

/-- Two back-steps are the fewest: no extent, the offsets outside `⟨c⟩`, and a checked word with
two back letters. -/
theorem Model.fewest_two (M : Model S A₀ B₀ π) (hgen : Subgroup.closure {π A₀, π B₀} = ⊤)
    (hext : ∀ σ, ¬ IsExtent (π A₀) (π B₀) σ) (h1 : (π A₀)⁻¹ ≠ π A₀) (h2 : (π A₀)⁻¹ ≠ π B₀)
    (h3 : (π B₀)⁻¹ ≠ π A₀) (h4 : (π B₀)⁻¹ ≠ π B₀) (hAB : π A₀ ≠ π B₀) {P N w : ℕ} (hP : 0 < P)
    (hN : 0 < N) (hper : M.code (iterC M.next P (M.enc 1)) = M.code (M.enc 1))
    (hoff : checkOffsets M.next M.code P (M.enc 1) = true)
    (hcheck : checkRun M.next M.code (digits N w) (M.enc 1) = true)
    (hcount : (digits N w).countP (2 ≤ ·) = 2) : FewestBack (π A₀) (π B₀) 2 := by
  obtain ⟨hZ1, hZ2⟩ := M.offsets_of_check hP hper hoff
  refine fewestBack_two hext (fun σ hσ => not_one_back hAB hZ1 hZ2 hσ) ?_
  obtain ⟨σ, hσ, hc⟩ := M.run_of_check hgen hN hcheck h1 h2 h3 h4
  exact ⟨σ, hσ, hc.trans hcount⟩

/-- At least three back-steps, if any: the offsets and the pairs of offsets miss `⟨c⟩`. -/
theorem Model.not_few (M : Model S A₀ B₀ π) (hAB : π A₀ ≠ π B₀) {P : ℕ} (hP : 0 < P)
    (hper : M.code (iterC M.next P (M.enc 1)) = M.code (M.enc 1))
    (hoff : checkOffsets M.next M.code P (M.enc 1) = true)
    (hpair : checkPairs M.next M.code P (M.enc 1) = true) {σ : Perm G}
    (hσ : IsRun (π A₀) (π B₀) σ) :
    (backSteps (π A₀) (π B₀) σ).ncard ≠ 1 ∧ (backSteps (π A₀) (π B₀) σ).ncard ≠ 2 := by
  obtain ⟨hZ1, hZ2⟩ := M.offsets_of_check hP hper hoff
  exact ⟨not_one_back hAB hZ1 hZ2 hσ, M.not_two_back_of_check hP hAB hper hoff hpair hσ⟩

/-- An extent is a run with no back-steps, so zero is the fewest. -/
theorem fewest_zero {A B : G} (h : ∃ σ, IsExtent A B σ) : FewestBack A B 0 := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨⟨σ, ⟨fun x => ?_, hσ.2⟩, ?_⟩, fun _ _ => Nat.zero_le _⟩
  · rcases hσ.1 x with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [Set.ncard_eq_zero (Set.toFinite _)]
    ext x
    simp only [backSteps, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    intro hx
    exact (hσ.1 x).resolve_left hx

end Fewest

section Table

variable {n : ℕ} [NeZero n]

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)
local notation "PSLn" => SpecialLinearGroup (Fin 2) (ZMod n) ⧸ pmOne n

theorem fewest_two_SL (hn : 3 ≤ n) (hext : ∀ σ : Perm SLn, ¬ IsExtent (Kp n) (Mp n) σ)
    {P N w : ℕ} (hP : 0 < P) (hN : 0 < N)
    (hper : codeQuad n (iterC (nextQuad n) P (oneQuad n)) = codeQuad n (oneQuad n))
    (hoff : checkOffsets (nextQuad n) (codeQuad n) P (oneQuad n) = true)
    (hcheck : checkRun (nextQuad n) (codeQuad n) (digits N w) (oneQuad n) = true)
    (hcount : (digits N w).countP (2 ≤ ·) = 2) : FewestBack (Kp n) (Mp n) 2 := by
  rw [← encSL_one] at hper hoff hcheck
  obtain ⟨h1, h2, h3, h4, hAB⟩ := genuine_SL hn
  exact (modelSL n).fewest_two (π := MonoidHom.id _) closure_KM hext h1 h2 h3 h4 hAB hP hN hper
    hoff hcheck hcount

theorem fewest_two_PSL (hn : 3 ≤ n)
    (hext : ∀ σ : Perm PSLn, ¬ IsExtent ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ)
    {P N w : ℕ} (hP : 0 < P) (hN : 0 < N)
    (hper : codePSL n (iterC (nextQuad n) P (oneQuad n)) = codePSL n (oneQuad n))
    (hoff : checkOffsets (nextQuad n) (codePSL n) P (oneQuad n) = true)
    (hcheck : checkRun (nextQuad n) (codePSL n) (digits N w) (oneQuad n) = true)
    (hcount : (digits N w).countP (2 ≤ ·) = 2) :
    FewestBack ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) 2 := by
  rw [← encSL_one] at hper hoff hcheck
  obtain ⟨h1, h2, h3, h4, hAB⟩ := genuine_PSL hn
  exact (modelPSL n).fewest_two closure_KM_PSL hext h1 h2 h3 h4 hAB hP hN hper hoff hcheck hcount

theorem not_few_SL (hn : 3 ≤ n) {P : ℕ} (hP : 0 < P)
    (hper : codeQuad n (iterC (nextQuad n) P (oneQuad n)) = codeQuad n (oneQuad n))
    (hoff : checkOffsets (nextQuad n) (codeQuad n) P (oneQuad n) = true)
    (hpair : checkPairs (nextQuad n) (codeQuad n) P (oneQuad n) = true) {σ : Perm SLn}
    (hσ : IsRun (Kp n) (Mp n) σ) :
    (backSteps (Kp n) (Mp n) σ).ncard ≠ 1 ∧ (backSteps (Kp n) (Mp n) σ).ncard ≠ 2 := by
  rw [← encSL_one] at hper hoff hpair
  exact (modelSL n).not_few (π := MonoidHom.id _) (genuine_SL hn).2.2.2.2 hP hper hoff hpair hσ

theorem not_few_PSL (hn : 3 ≤ n) {P : ℕ} (hP : 0 < P)
    (hper : codePSL n (iterC (nextQuad n) P (oneQuad n)) = codePSL n (oneQuad n))
    (hoff : checkOffsets (nextQuad n) (codePSL n) P (oneQuad n) = true)
    (hpair : checkPairs (nextQuad n) (codePSL n) P (oneQuad n) = true) {σ : Perm PSLn}
    (hσ : IsRun ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ) :
    (backSteps ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ).ncard ≠ 1 ∧
      (backSteps ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ).ncard ≠ 2 := by
  rw [← encSL_one] at hper hoff hpair
  exact (modelPSL n).not_few (genuine_PSL hn).2.2.2.2 hP hper hoff hpair hσ

/-- A checked word of `PSL(2, Z/n)` with its back letters for back-steps. -/
theorem run_PSL (hn : 3 ≤ n) {N w : ℕ} (hN : 0 < N)
    (hcheck : checkRun (nextQuad n) (codePSL n) (digits N w) (oneQuad n) = true) :
    ∃ σ, IsRun ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ ∧
      (backSteps ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ).ncard =
        (digits N w).countP (2 ≤ ·) := by
  rw [← encSL_one] at hcheck
  obtain ⟨h1, h2, h3, h4, -⟩ := genuine_PSL hn
  exact (modelPSL n).run_of_check closure_KM_PSL hN hcheck h1 h2 h3 h4

end Table

section Count

/-! ## The exact count of extents

Rankin's links make an extent a choice on the cosets `⟨c⟩ x`: the permutation `choicePerm` of a
bitmask `S`, with a table `cid` that numbers the cosets. So the extents are counted by trying every
mask, each time walking from `1` until the walk first comes back. -/

variable {G : Type*} [Group G] {A B : G}

/-- The map of the choice `S`: `B x` where the bit of the coset of `x` is set, and `A x`
elsewhere. -/
def choiceMap (A B : G) (cid : G → ℕ) (S : ℕ) (x : G) : G :=
  if S.testBit (cid x) = true then B * x else A * x

theorem choiceMap_injective {cid : G → ℕ} (hc : ∀ x, cid (A⁻¹ * B * x) = cid x) (S : ℕ) :
    Function.Injective (choiceMap A B cid S) := by
  intro x y hxy
  have key : ∀ {x y : G}, S.testBit (cid x) = true → ¬ S.testBit (cid y) = true →
      B * x ≠ A * y := by
    intro x y hx hy e
    apply hy
    have : y = A⁻¹ * B * x := by
      rw [mul_assoc, e]
      group
    rw [this, hc]
    exact hx
  unfold choiceMap at hxy
  split_ifs at hxy with hx hy hy
  · exact mul_left_cancel hxy
  · exact absurd hxy (key hx hy)
  · exact absurd hxy.symm (key hy hx)
  · exact mul_left_cancel hxy

variable [Finite G]

/-- The permutation of the choice `S`. -/
noncomputable def choicePerm {cid : G → ℕ} (hc : ∀ x, cid (A⁻¹ * B * x) = cid x) (S : ℕ) : Perm G :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (choiceMap_injective hc S))

@[simp] theorem choicePerm_apply {cid : G → ℕ} (hc : ∀ x, cid (A⁻¹ * B * x) = cid x) (S : ℕ)
    (x : G) : choicePerm hc S x = choiceMap A B cid S x := rfl

open scoped Classical in
/-- The extents are the choices whose permutation is an extent. -/
theorem ncard_extents_eq (hAB : A ≠ B) {cid : G → ℕ} {m : ℕ} (hlt : ∀ x, cid x < m)
    (hc : ∀ x, cid (A⁻¹ * B * x) = cid x)
    (hsep : ∀ x y, cid x = cid y → ∃ k : ℕ, y = (A⁻¹ * B) ^ k * x)
    (hsurj : ∀ i < m, ∃ x, cid x = i) :
    {σ : Perm G | IsExtent A B σ}.ncard =
      ((Finset.range (2 ^ m)).filter fun S => IsExtent A B (choicePerm hc S)).card := by
  have hinj : Set.InjOn (choicePerm hc)
      ((Finset.range (2 ^ m)).filter fun S => IsExtent A B (choicePerm hc S) : Finset ℕ) := by
    intro S hS S' hS' e
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hS hS'
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < m
    · obtain ⟨x, rfl⟩ := hsurj i hi
      have hx := congrArg (fun σ : Perm G => σ x) e
      simp only [choicePerm_apply, choiceMap] at hx
      by_cases h1 : S.testBit (cid x) = true <;> by_cases h2 : S'.testBit (cid x) = true
      · rw [h1, h2]
      · simp only [h1, h2, ↓reduceIte] at hx
        exact absurd (mul_right_cancel hx).symm hAB
      · simp only [h1, h2, ↓reduceIte] at hx
        exact absurd (mul_right_cancel hx) hAB
      · simp only [Bool.not_eq_true] at h1 h2
        rw [h1, h2]
    · have hm : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hS.1 hm),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hS'.1 hm)]
  rw [← Set.ncard_coe_finset, ← hinj.ncard_image]
  congr 1
  ext σ
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_range]
  constructor
  · intro hσ
    let f : Fin m → Bool := fun i => decide (∃ x, cid x = i ∧ σ x ≠ A * x)
    have hS := Nat.ofBits_lt_two_pow f
    have hlink : ∀ x, ∀ k : ℕ, σ ((A⁻¹ * B) ^ k * x) = A * ((A⁻¹ * B) ^ k * x) ↔ σ x = A * x := by
      intro x k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← ih]
        have := choice_link hσ.1 ((A⁻¹ * B) ^ (k + 1) * x)
        rw [show (A⁻¹ * B)⁻¹ * ((A⁻¹ * B) ^ (k + 1) * x) = (A⁻¹ * B) ^ k * x by
          rw [pow_succ', mul_assoc, inv_mul_cancel_left]] at this
        exact this.symm
    have heq : choicePerm hc (Nat.ofBits f) = σ := by
      ext x
      simp only [choicePerm_apply, choiceMap, Nat.testBit_ofBits_lt f (cid x) (hlt x), f,
        decide_eq_true_eq]
      split_ifs with h
      · obtain ⟨y, hy, hyA⟩ := h
        obtain ⟨k, rfl⟩ := hsep y x hy
        have hA : σ ((A⁻¹ * B) ^ k * y) ≠ A * ((A⁻¹ * B) ^ k * y) := by
          rw [Ne, hlink]
          exact hyA
        exact ((hσ.1 _).resolve_left hA).symm
      · push Not at h
        exact (h x rfl).symm
    exact ⟨Nat.ofBits f, ⟨hS, by rw [heq]; exact hσ⟩, heq⟩
  · rintro ⟨S, ⟨-, hS⟩, rfl⟩
    exact hS

/-- A permutation with the steps of an extent is one exactly when its walk from `1` first comes back
after `|G|` steps. -/
theorem isExtent_iff_return {σ : Perm G} (hsteps : ∀ x, σ x = A * x ∨ σ x = B * x) {k : ℕ}
    (hG : Nat.card G = k + 1) :
    IsExtent A B σ ↔ (∀ j < k, (σ ^ (j + 1)) 1 ≠ 1) ∧ (σ ^ (k + 1)) 1 = 1 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hG' : Fintype.card G = k + 1 := by rw [← Nat.card_eq_fintype_card, hG]
  constructor
  · rintro ⟨-, htrans⟩
    -- the minimal period of `1`
    set p := Function.minimalPeriod σ 1 with hp
    have hper : (1 : G) ∈ Function.periodicPts σ := by
      refine Function.mem_periodicPts.mpr ?_
      obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite σ)
      refine ⟨n, hn, ?_⟩
      rw [Function.IsPeriodicPt, Function.IsFixedPt, Perm.iterate_eq_pow, h]
      rfl
    have hp0 : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hper
    have hmod : ∀ l : ℕ, (σ ^ (l % p)) 1 = (σ ^ l) 1 := by
      intro l
      have := Function.iterate_mod_minimalPeriod_eq (f := σ) (x := 1) (n := l)
      rwa [Perm.iterate_eq_pow, Perm.iterate_eq_pow] at this
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := 1)
    have hcard : p = k + 1 := by
      apply le_antisymm
      · have : (Finset.range p).card ≤ Fintype.card G :=
          Finset.card_le_card_of_injOn (fun l => σ^[l] 1) (fun _ _ => Finset.mem_univ _)
            (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e)
        simpa [hG'] using this
      · have hcov : (Finset.univ : Finset G) ⊆ (Finset.range p).image fun l => (σ ^ l) 1 := by
          intro y _
          obtain ⟨l, hl⟩ := htrans 1 y
          exact Finset.mem_image.mpr ⟨l % p, Finset.mem_range.mpr (Nat.mod_lt _ hp0),
            by rw [hmod, hl]⟩
        have := (Finset.card_le_card hcov).trans Finset.card_image_le
        simpa [hG'] using this
    have hkp : (σ ^ (k + 1)) 1 = 1 := by
      rw [← hcard, ← Perm.iterate_eq_pow]
      exact Function.isPeriodicPt_minimalPeriod σ 1
    refine ⟨fun j hj e => ?_, hkp⟩
    have hle : p ≤ j + 1 := by
      apply Function.IsPeriodicPt.minimalPeriod_le (by omega)
      rw [Function.IsPeriodicPt, Function.IsFixedPt, Perm.iterate_eq_pow]
      exact e
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨hsteps, ?_⟩
    have hinj : Set.InjOn (fun l => (σ ^ l) (1 : G)) (Finset.range (k + 1) : Finset ℕ) := by
      have hlt : ∀ a b : ℕ, a < b → b < k + 1 → (σ ^ a) (1 : G) ≠ (σ ^ b) 1 := by
        intro a b hab hb e
        have hsplit : (σ ^ b) (1 : G) = (σ ^ a) ((σ ^ (b - a)) 1) := by
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
        rw [hsplit] at e
        have := (σ ^ a).injective e
        apply h1 (b - a - 1) (by omega)
        rw [show b - a - 1 + 1 = b - a by omega]
        exact this.symm
      intro a ha b hb e
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with h | h | h
      · exact absurd e (hlt a b h hb)
      · exact h
      · exact absurd e.symm (hlt b a h ha)
    have himg : (Finset.range (k + 1)).image (fun l => (σ ^ l) (1 : G)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, Finset.card_range, hG']
    have hmem : ∀ x : G, ∃ a < k + 1, (σ ^ a) (1 : G) = x := by
      intro x
      have : x ∈ (Finset.range (k + 1)).image (fun l => (σ ^ l) (1 : G)) := by
        rw [himg]
        exact Finset.mem_univ _
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp this
      exact ⟨a, Finset.mem_range.mp ha, rfl⟩
    intro x y
    obtain ⟨a, ha, rfl⟩ := hmem x
    obtain ⟨b, -, rfl⟩ := hmem y
    refine ⟨b + (k + 1 - a), ?_⟩
    rw [← Perm.mul_apply, ← pow_add, show b + (k + 1 - a) + a = b + (k + 1) by omega, pow_add,
      Perm.mul_apply, h2]

/-- A numbering of the cosets of `⟨c⟩`: `|G| = ord c · m` makes it one to one. -/
theorem sep_of_count {c : G} {cid : G → ℕ} {m : ℕ} (hlt : ∀ x, cid x < m)
    (hinv : ∀ x, cid (c * x) = cid x) (hsurj : ∀ i < m, ∃ x, cid x = i)
    (hcount : orderOf c * m = Nat.card G) (x y : G) (hxy : cid x = cid y) :
    ∃ k : ℕ, y = c ^ k * x := by
  have hpow : ∀ (k : ℕ) (x : G), cid (c ^ k * x) = cid x := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, hinv, ih]
  let Z := Subgroup.zpowers c
  let Q := Quotient (QuotientGroup.rightRel Z)
  have hrel : ∀ a b : G, QuotientGroup.rightRel Z a b → ∃ k : ℕ, b = c ^ k * a := by
    intro a b hab
    rw [QuotientGroup.rightRel_apply, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff] at hab
    obtain ⟨k, hk⟩ := hab
    exact ⟨k, by rw [hk]; group⟩
  let φ : Q → Fin m := Quotient.lift (fun a => ⟨cid a, hlt a⟩) (by
    intro a b hab
    obtain ⟨k, rfl⟩ := hrel a b hab
    exact Fin.ext (hpow k a).symm)
  have hφ : Function.Surjective φ := by
    intro i
    obtain ⟨a, ha⟩ := hsurj i i.2
    exact ⟨Quotient.mk _ a, Fin.ext ha⟩
  have hcardQ : Nat.card Q = m := by
    have h1 : Nat.card Q = Z.index :=
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Z)
    have h2 := Subgroup.card_mul_index Z
    rw [Nat.card_zpowers, ← hcount, ← h1] at h2
    exact Nat.eq_of_mul_eq_mul_left (orderOf_pos c) h2
  have hbij := hφ.bijective_of_nat_card_le (by rw [hcardQ, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  have hq : (Quotient.mk _ x : Q) = Quotient.mk _ y := hbij.1 (Fin.ext hxy)
  exact hrel x y (Quotient.exact hq)

end Count

section CountCheck

variable {St : Type*} (next : ℕ → St → St) (code : St → ℕ)

/-- The number of the coset at a code, four bits of the table. -/
def cidAt (table c : ℕ) : ℕ := (table >>> (4 * c)) % 16

/-- The step of the choice `S` on states. -/
def choiceNext (table S : ℕ) (x : St) : St :=
  if S.testBit (cidAt table (code x)) = true then next 1 x else next 0 x

/-- The walk of the choice `S` first reaches the code `start` after exactly `k + 1` steps. -/
def fullFrom (table S start : ℕ) : ℕ → St → Bool
  | 0, x => code (choiceNext next code table S x) == start
  | k + 1, x => code (choiceNext next code table S x) != start &&
      fullFrom table S start k (choiceNext next code table S x)

/-- The number of masks `lo + i`, `i < 2 ^ j`, whose walk from `x₀` is full. -/
def countPow (table start k₀ : ℕ) (x₀ : St) : ℕ → ℕ → ℕ
  | 0, lo => if fullFrom next code table lo start k₀ x₀ = true then 1 else 0
  | j + 1, lo => countPow table start k₀ x₀ j lo + countPow table start k₀ x₀ j (lo + 2 ^ j)

/-- A check along a walk: the table numbers below `m`, is constant under `c`, and hits every
number. -/
def cosetPass (table m : ℕ) : List ℕ → St → ℕ → Bool
  | [], _, hits => hits == 2 ^ m - 1
  | s :: w, x, hits =>
    decide (cidAt table (code x) < m) &&
      cidAt table (code (stepC next x)) == cidAt table (code x) &&
      cosetPass table m w (next s x) (hits ||| 1 <<< cidAt table (code x))

theorem countPow_eq (table start k₀ : ℕ) (x₀ : St) (j lo : ℕ) :
    countPow next code table start k₀ x₀ j lo =
      ((Finset.range (2 ^ j)).filter
        fun i => fullFrom next code table (lo + i) start k₀ x₀ = true).card := by
  induction j generalizing lo with
  | zero =>
    simp only [countPow, pow_zero, Finset.range_one, Finset.filter_singleton, add_zero]
    split_ifs <;> simp
  | succ j ih =>
    rw [countPow, ih, ih, pow_succ, mul_two, Finset.card_filter, Finset.card_filter,
      Finset.card_filter, Finset.sum_range_add]
    simp only [add_assoc]

variable {G₀ G : Type*} [Group G₀] [Group G] {A₀ B₀ : G₀} {π : G₀ →* G}

namespace Model

variable (M : Model St A₀ B₀ π)

theorem cosetPass_spec {table m : ℕ} (w : List ℕ) (g : G₀) (hits : ℕ)
    (h : cosetPass M.next M.code table m w (M.enc g) hits = true) :
    (∀ y ∈ visits A₀ B₀ w g, cidAt table (M.code (M.enc y)) < m ∧
      cidAt table (M.code (M.enc (A₀⁻¹ * B₀ * y))) = cidAt table (M.code (M.enc y))) ∧
    ∀ i < m, hits.testBit i = true ∨
      ∃ y ∈ visits A₀ B₀ w g, cidAt table (M.code (M.enc y)) = i := by
  induction w generalizing g hits with
  | nil =>
    simp only [cosetPass, beq_iff_eq] at h
    subst h
    refine ⟨by simp [visits], fun i hi => Or.inl ?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    simpa using hi
  | cons s w ih =>
    simp only [cosetPass, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [enc_stepC] at h2
    rw [M.hnext] at h3
    obtain ⟨h4, h5⟩ := ih _ _ h3
    refine ⟨?_, fun i hi => ?_⟩
    · intro y hy
      rw [visits, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨h1, h2⟩
      · exact h4 y hy
    · rcases h5 i hi with h6 | ⟨y, hy, hyi⟩
      · rw [testBit_or_shift] at h6
        rcases h6 with h6 | rfl
        · exact Or.inl h6
        · exact Or.inr ⟨g, by simp [visits], rfl⟩
      · exact Or.inr ⟨y, by rw [visits, List.mem_cons]; exact Or.inr hy, hyi⟩

theorem choiceNext_enc (table S : ℕ) (g : G₀) :
    choiceNext M.next M.code table S (M.enc g) = M.enc
      ((if S.testBit (cidAt table (M.code (M.enc g))) = true then B₀ else A₀) * g) := by
  rw [choiceNext]
  split_ifs
  · exact M.hnext 1 g
  · exact M.hnext 0 g

variable [Finite G]

/-- The exact count of the extents, from a checked word and a checked table of cosets. -/
theorem ncard_extents (hsurj : Function.Surjective π) (hgen : Subgroup.closure {π A₀, π B₀} = ⊤)
    (hAB : π A₀ ≠ π B₀) {k w table m ord C : ℕ}
    (hcheck : checkRun M.next M.code (digits (k + 1) w) (M.enc 1) = true)
    (hpass : cosetPass M.next M.code table m (digits (k + 1) w) (M.enc 1) 0 = true)
    (hord : orderOf ((π A₀)⁻¹ * π B₀) = ord) (hm : ord * m = k + 1)
    (hcount : countPow M.next M.code table (M.code (M.enc 1)) k (M.enc 1) m 0 = C) :
    {σ : Equiv.Perm G | IsExtent (π A₀) (π B₀) σ}.ncard = C := by
  classical
  have hw := digits_ne_nil (Nat.succ_pos k) w
  obtain ⟨-, -, hall⟩ := walk_of_check M.next M.code M.hnext M.hcode hgen hw hcheck
  have hcard : Nat.card G = k + 1 := M.card_of_check hgen (Nat.succ_pos k) hcheck
  have hvis := map_visits π A₀ B₀ (digits (k + 1) w) 1
  rw [map_one] at hvis
  have hcover : ∀ x : G, ∃ z ∈ visits A₀ B₀ (digits (k + 1) w) 1, π z = x := by
    intro x
    have := hall x
    rw [← hvis, List.mem_map] at this
    exact this
  obtain ⟨hs1, hs2⟩ := M.cosetPass_spec _ _ _ hpass
  let cid : G → ℕ := fun x => cidAt table (M.code (M.enc (Function.surjInv hsurj x)))
  have hcid : ∀ g : G₀, cid (π g) = cidAt table (M.code (M.enc g)) := by
    intro g
    change cidAt table (M.code (M.enc (Function.surjInv hsurj (π g)))) = _
    rw [(M.hcode _ _).mpr (Function.surjInv_eq hsurj (π g))]
  have hlt : ∀ x, cid x < m := by
    intro x
    obtain ⟨z, hz, rfl⟩ := hcover x
    rw [hcid]
    exact (hs1 z hz).1
  have hc : ∀ x, cid ((π A₀)⁻¹ * π B₀ * x) = cid x := by
    intro x
    obtain ⟨z, hz, rfl⟩ := hcover x
    have := (hs1 z hz).2
    rw [← hcid, ← hcid] at this
    simpa only [map_mul, map_inv] using this
  have hsurj' : ∀ i < m, ∃ x, cid x = i := by
    intro i hi
    rcases hs2 i hi with h | ⟨y, -, hy⟩
    · simp at h
    · exact ⟨π y, by rw [hcid, hy]⟩
  have hsep := sep_of_count hlt hc hsurj' (by rw [hord, hm, hcard])
  rw [ncard_extents_eq hAB hlt hc hsep hsurj', ← hcount, countPow_eq]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_range, zero_add, and_congr_right_iff]
  intro _
  have hsteps : ∀ x, choicePerm hc S x = π A₀ * x ∨ choicePerm hc S x = π B₀ * x := by
    intro x
    simp only [choicePerm_apply, choiceMap]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  rw [isExtent_iff_return hsteps hcard]
  -- the walk on states
  have hwalk : ∀ (j : ℕ) (g : G₀), fullFrom M.next M.code table S (M.code (M.enc 1)) j (M.enc g) =
      true ↔ (∀ i < j, ((choicePerm hc S) ^ (i + 1)) (π g) ≠ 1) ∧
        ((choicePerm hc S) ^ (j + 1)) (π g) = 1 := by
    have hstep : ∀ g : G₀, ∃ h : G₀, choiceNext M.next M.code table S (M.enc g) = M.enc h ∧
        π h = choicePerm hc S (π g) := by
      intro g
      refine ⟨_, M.choiceNext_enc table S g, ?_⟩
      simp only [choicePerm_apply, choiceMap, hcid]
      split_ifs <;> simp
    intro j
    induction j with
    | zero =>
      intro g
      obtain ⟨h, he, hπ⟩ := hstep g
      rw [fullFrom, he, beq_iff_eq, M.hcode, map_one, hπ]
      simp
    | succ j ih =>
      intro g
      obtain ⟨h, he, hπ⟩ := hstep g
      rw [fullFrom, he, Bool.and_eq_true, bne_iff_ne, ne_eq, M.hcode, map_one, ih, hπ]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨fun i hi => ?_, by rw [pow_succ, Perm.mul_apply]; exact h2⟩
        cases i with
        | zero => simpa using h0
        | succ i =>
          rw [pow_succ, Perm.mul_apply]
          exact h1 i (by omega)
      · rintro ⟨h1, h2⟩
        refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, ?_⟩
        · have := h1 (i + 1) (by omega)
          rwa [pow_succ, Perm.mul_apply] at this
        · rwa [pow_succ, Perm.mul_apply] at h2
  rw [hwalk]
  simp

end Model

end CountCheck

section Certified

open Cert

/-! ## The forward extents -/

theorem none4 : (∀ σ, ¬ IsExtent (leapK 4) (leapM 4) σ) ∧ ∀ σ, ¬ IsExtent (barK 4) (barM 4) σ :=
  ⟨no_forward_SL (by norm_num) (m := 3) (by decide) (by decide +kernel),
    no_forward_PSL (by norm_num) (m := 3) (by decide) (by decide +kernel)⟩

theorem none5 : (∀ σ, ¬ IsExtent (leapK 5) (leapM 5) σ) ∧ ∀ σ, ¬ IsExtent (barK 5) (barM 5) σ := by
  have h : ∀ σ, ¬ IsExtent (barK 5) (barM 5) σ :=
    no_forward_PSL (by norm_num) (m := 5) (by decide) (by decide +kernel)
  exact ⟨no_forward_SL_of_lift (m := 5) (by decide +kernel) h, h⟩

theorem none10 :
    (∀ σ, ¬ IsExtent (leapK 10) (leapM 10) σ) ∧ ∀ σ, ¬ IsExtent (barK 10) (barM 10) σ := by
  have h : ∀ σ, ¬ IsExtent (barK 10) (barM 10) σ :=
    no_forward_PSL (by norm_num) (m := 15) (by decide) (by decide +kernel)
  exact ⟨no_forward_SL_of_lift (m := 15) (by decide +kernel) h, h⟩

theorem none11 :
    (∀ σ, ¬ IsExtent (leapK 11) (leapM 11) σ) ∧ ∀ σ, ¬ IsExtent (barK 11) (barM 11) σ :=
  ⟨no_forward_SL (by norm_num) (m := 5) (by decide) (by decide +kernel),
    no_forward_PSL (by norm_num) (m := 5) (by decide) (by decide +kernel)⟩

theorem none13 :
    (∀ σ, ¬ IsExtent (leapK 13) (leapM 13) σ) ∧ ∀ σ, ¬ IsExtent (barK 13) (barM 13) σ := by
  have h : ∀ σ, ¬ IsExtent (barK 13) (barM 13) σ :=
    no_forward_PSL (by norm_num) (m := 7) (by decide) (by decide +kernel)
  exact ⟨no_forward_SL_of_lift (m := 7) (by decide +kernel) h, h⟩

theorem some3 : (∃ σ, IsExtent (leapK 3) (leapM 3) σ) ∧ ∃ σ, IsExtent (barK 3) (barM 3) σ :=
  ⟨extent_SL (N := 24) (w := wordSL3) (by norm_num) (by decide +kernel) (by decide +kernel),
    extent_PSL (N := 12) (w := wordPSL3) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

theorem some6 : (∃ σ, IsExtent (leapK 6) (leapM 6) σ) ∧ ∃ σ, IsExtent (barK 6) (barM 6) σ :=
  ⟨extent_SL (N := 144) (w := wordSL6) (by norm_num) (by decide +kernel) (by decide +kernel),
    extent_PSL (N := 72) (w := wordPSL6) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

theorem some7 : (∃ σ, IsExtent (leapK 7) (leapM 7) σ) ∧ ∃ σ, IsExtent (barK 7) (barM 7) σ :=
  ⟨extent_SL (N := 336) (w := wordSL7) (by norm_num) (by decide +kernel) (by decide +kernel),
    extent_PSL (N := 168) (w := wordPSL7) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

theorem some9 : (∃ σ, IsExtent (leapK 9) (leapM 9) σ) ∧ ∃ σ, IsExtent (barK 9) (barM 9) σ :=
  ⟨extent_SL (N := 648) (w := wordSL9) (by norm_num) (by decide +kernel) (by decide +kernel),
    extent_PSL (N := 324) (w := wordPSL9) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

theorem some12 : (∃ σ, IsExtent (leapK 12) (leapM 12) σ) ∧ ∃ σ, IsExtent (barK 12) (barM 12) σ :=
  ⟨extent_SL (N := 1152) (w := wordSL12) (by norm_num) (by decide +kernel) (by decide +kernel),
    extent_PSL (N := 576) (w := wordPSL12) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-! ## The fewest back-steps -/

theorem fewest4 : FewestBack (leapK 4) (leapM 4) 2 ∧ FewestBack (barK 4) (barM 4) 2 :=
  ⟨fewest_two_SL (by norm_num) none4.1 (P := 3) (N := 48) (w := wordSL4) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    fewest_two_PSL (by norm_num) none4.2 (P := 3) (N := 24) (w := wordPSL4) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem fewest5 : FewestBack (leapK 5) (leapM 5) 2 ∧ FewestBack (barK 5) (barM 5) 2 :=
  ⟨fewest_two_SL (by norm_num) none5.1 (P := 10) (N := 120) (w := wordSL5) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    fewest_two_PSL (by norm_num) none5.2 (P := 5) (N := 60) (w := wordPSL5) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem fewest10 : FewestBack (leapK 10) (leapM 10) 2 ∧ FewestBack (barK 10) (barM 10) 2 :=
  ⟨fewest_two_SL (by norm_num) none10.1 (P := 30) (N := 720) (w := wordSL10) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    fewest_two_PSL (by norm_num) none10.2 (P := 15) (N := 360) (w := wordPSL10) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem fewest13 : FewestBack (leapK 13) (leapM 13) 2 ∧ FewestBack (barK 13) (barM 13) 2 :=
  ⟨fewest_two_SL (by norm_num) none13.1 (P := 14) (N := 2184) (w := wordSL13) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    fewest_two_PSL (by norm_num) none13.2 (P := 7) (N := 1092) (w := wordPSL13) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem notFew8 : (∀ σ, IsRun (leapK 8) (leapM 8) σ →
      (backSteps (leapK 8) (leapM 8) σ).ncard ≠ 1 ∧ (backSteps (leapK 8) (leapM 8) σ).ncard ≠ 2) ∧
    ∀ σ, IsRun (barK 8) (barM 8) σ →
      (backSteps (barK 8) (barM 8) σ).ncard ≠ 1 ∧ (backSteps (barK 8) (barM 8) σ).ncard ≠ 2 :=
  ⟨fun _ hσ => not_few_SL (by norm_num) (P := 6) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hσ,
    fun _ hσ => not_few_PSL (by norm_num) (P := 6) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hσ⟩

theorem notFew11 : (∀ σ, IsRun (leapK 11) (leapM 11) σ →
      (backSteps (leapK 11) (leapM 11) σ).ncard ≠ 1 ∧
      (backSteps (leapK 11) (leapM 11) σ).ncard ≠ 2) ∧
    ∀ σ, IsRun (barK 11) (barM 11) σ →
      (backSteps (barK 11) (barM 11) σ).ncard ≠ 1 ∧
      (backSteps (barK 11) (barM 11) σ).ncard ≠ 2 :=
  ⟨fun _ hσ => not_few_SL (by norm_num) (P := 5) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hσ,
    fun _ hσ => not_few_PSL (by norm_num) (P := 5) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hσ⟩

/-- A run with neither one back-step nor two, of a group with no extent, has three or more. -/
theorem three_le {G : Type*} [Group G] [Finite G] {A B : G} (hext : ∀ σ, ¬ IsExtent A B σ)
    {σ : Perm G} (hσ : IsRun A B σ)
    (h : (backSteps A B σ).ncard ≠ 1 ∧ (backSteps A B σ).ncard ≠ 2) :
    3 ≤ (backSteps A B σ).ncard := by
  have h0 : (backSteps A B σ).ncard ≠ 0 := fun e => hext σ (hσ.isExtent e)
  omega

theorem threeBack8 :
    ∃ σ, IsRun (barK 8) (barM 8) σ ∧ (backSteps (barK 8) (barM 8) σ).ncard = 3 := by
  obtain ⟨σ, hσ, hc⟩ := run_PSL (n := 8) (N := 192) (w := wordPSL8) (by norm_num) (by norm_num)
    (by decide +kernel)
  exact ⟨σ, hσ, hc.trans (by decide +kernel)⟩

end Certified

section Counts

open Cert

/-! ## The exact counts -/

variable {n : ℕ} [NeZero n]

/-- The count of the extents of `SL(2, Z/n)`. -/
theorem count_SL (hn : 2 ≤ n) {k w table m ord C : ℕ}
    (hcheck : checkRun (nextQuad n) (codeQuad n) (digits (k + 1) w) (oneQuad n) = true)
    (hpass : cosetPass (nextQuad n) (codeQuad n) table m (digits (k + 1) w) (oneQuad n) 0 = true)
    (hper : codeQuad n (iterC (nextQuad n) ord (oneQuad n)) = codeQuad n (oneQuad n))
    (hord : notPow (nextQuad n) (codeQuad n) (oneQuad n) (ord - 1)
      (stepC (nextQuad n) (oneQuad n)) = true) (hord0 : 0 < ord) (hm : ord * m = k + 1)
    (hcount : countPow (nextQuad n) (codeQuad n) table (codeQuad n (oneQuad n)) k (oneQuad n) m 0 =
      C) : (extentsSL n).ncard = C := by
  rw [← encSL_one] at hcheck hpass hper hord hcount
  exact (modelSL n).ncard_extents (π := MonoidHom.id _) Function.surjective_id closure_KM
    (Kp_ne_Mp hn) hcheck hpass ((modelSL n).orderOf_of_check hord0 hper hord) hm hcount

/-- The count of the extents of `PSL(2, Z/n)`. -/
theorem count_PSL (hn : 2 ≤ n) {k w table m ord C : ℕ}
    (hcheck : checkRun (nextQuad n) (codePSL n) (digits (k + 1) w) (oneQuad n) = true)
    (hpass : cosetPass (nextQuad n) (codePSL n) table m (digits (k + 1) w) (oneQuad n) 0 = true)
    (hper : codePSL n (iterC (nextQuad n) ord (oneQuad n)) = codePSL n (oneQuad n))
    (hord : notPow (nextQuad n) (codePSL n) (oneQuad n) (ord - 1)
      (stepC (nextQuad n) (oneQuad n)) = true) (hord0 : 0 < ord) (hm : ord * m = k + 1)
    (hcount : countPow (nextQuad n) (codePSL n) table (codePSL n (oneQuad n)) k (oneQuad n) m 0 =
      C) : (extentsPSL n).ncard = C := by
  rw [← encSL_one] at hcheck hpass hper hord hcount
  exact (modelPSL n).ncard_extents (QuotientGroup.mk'_surjective _) closure_KM_PSL
    (barK_ne_barM hn) hcheck hpass ((modelPSL n).orderOf_of_check hord0 hper hord) hm hcount

theorem countSL2 : (extentsSL 2).ncard = 2 :=
  count_SL (by norm_num) (k := 5) (w := wordSL2) (table := cosetsSL2) (m := 2) (ord := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

theorem countPSL2 : (extentsPSL 2).ncard = 2 :=
  count_PSL (by norm_num) (k := 5) (w := wordPSL2) (table := cosetsPSL2) (m := 2) (ord := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

theorem countSL3 : (extentsSL 3).ncard = 16 :=
  count_SL (by norm_num) (k := 23) (w := wordSL3) (table := cosetsSL3) (m := 6) (ord := 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

theorem countPSL3 : (extentsPSL 3).ncard = 16 :=
  count_PSL (by norm_num) (k := 11) (w := wordPSL3) (table := cosetsPSL3) (m := 6) (ord := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

theorem countSL6 : (extentsSL 6).ncard = 768 :=
  count_SL (by norm_num) (k := 143) (w := wordSL6) (table := cosetsSL6) (m := 12) (ord := 12)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

theorem countPSL6 : (extentsPSL 6).ncard = 768 :=
  count_PSL (by norm_num) (k := 71) (w := wordPSL6) (table := cosetsPSL6) (m := 12) (ord := 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by norm_num) (by decide +kernel)

end Counts

section TwoSquares

/-! ## The two squares -/

/-- A permutation of the six corners on natural numbers. -/
abbrev Six := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The letters `L`, `R`, `L⁻¹`, `R⁻¹` on the corners. -/
def tabOf : ℕ → ℕ → ℕ
  | 0, i => [1, 2, 3, 0, 4, 5].getD i 0
  | 1, i => [0, 4, 1, 3, 5, 2].getD i 0
  | 2, i => [3, 0, 1, 2, 4, 5].getD i 0
  | _, i => [0, 2, 5, 3, 1, 4].getD i 0

/-- A letter on a permutation of the corners. -/
def nextSix (s : ℕ) : Six → Six
  | (a, b, c, d, e, f) =>
    (tabOf s a, tabOf s b, tabOf s c, tabOf s d, tabOf s e, tabOf s f)

/-- The code of a permutation of the corners: its values as digits in base `6`. -/
def codeSix : Six → ℕ
  | (a, b, c, d, e, f) => ((((a * 6 + b) * 6 + c) * 6 + d) * 6 + e) * 6 + f

/-- The state of an element of the group of the two squares. -/
def encSix (g : twoSquares) : Six :=
  ((g.1 0).val, (g.1 1).val, (g.1 2).val, (g.1 3).val, (g.1 4).val, (g.1 5).val)

/-- The identity. -/
def oneSix : Six := (0, 1, 2, 3, 4, 5)

theorem encSix_one : encSix 1 = oneSix := rfl

theorem tab_spec (s : ℕ) (j : Fin 6) : ((letter turnL turnR s).1 j).val = tabOf s j.val := by
  match s with
  | 0 => revert j; decide
  | 1 => revert j; decide
  | 2 => revert j; decide
  | s + 3 =>
    change ((turnR⁻¹).1 j).val = [0, 2, 5, 3, 1, 4].getD j.val 0
    revert j
    decide

theorem nextSix_enc (s : ℕ) (g : twoSquares) :
    nextSix s (encSix g) = encSix (letter turnL turnR s * g) := by
  simp only [nextSix, encSix, ← tab_spec]
  rfl

theorem codeSix_inj {g h : twoSquares} (e : codeSix (encSix g) = codeSix (encSix h)) : g = h := by
  simp only [codeSix, encSix] at e
  have hd : ∀ (g : twoSquares) (i : Fin 6), (g.1 i).val < 6 := fun g i => (g.1 i).isLt
  obtain ⟨e1, e6⟩ := digit_eq (hd g 5) (hd h 5) e
  obtain ⟨e2, e5⟩ := digit_eq (hd g 4) (hd h 4) e1
  obtain ⟨e3, e4⟩ := digit_eq (hd g 3) (hd h 3) e2
  obtain ⟨e7, e8⟩ := digit_eq (hd g 2) (hd h 2) e3
  obtain ⟨e9, e10⟩ := digit_eq (hd g 1) (hd h 1) e7
  have e11 : (g.1 0).val = (h.1 0).val := by omega
  apply Subtype.ext
  ext i
  fin_cases i
  · exact e11
  · exact e10
  · exact e8
  · exact e4
  · exact e5
  · exact e6

/-- The computation in the group of the two squares. -/
def modelSquares : Model Six turnL turnR (MonoidHom.id twoSquares) where
  next := nextSix
  code := codeSix
  enc := encSix
  hnext := nextSix_enc
  hcode g h := by
    simp only [MonoidHom.id_apply]
    exact ⟨codeSix_inj, fun e => by rw [e]⟩

theorem closure_turns : Subgroup.closure {turnL, turnR} = ⊤ := by
  have hset : ({turnL, turnR} : Set twoSquares) =
      ((↑) : twoSquares → Perm (Fin 6)) ⁻¹' {squareL, squareR} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
    rfl
  rw [hset]
  exact Subgroup.closure_closure_coe_preimage

theorem square_order : orderOf turnL = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := turnL)
    (by intro e; have := congrArg Subtype.val e; revert this; decide)
    (by apply Subtype.ext; decide)
  simpa using h

theorem card_squares : Nat.card twoSquares = 120 :=
  modelSquares.card_of_check (π := MonoidHom.id _) closure_turns (N := 120) (w := Cert.wordSquares)
    (by norm_num) (by
      change checkRun nextSix codeSix (digits 120 Cert.wordSquares) oneSix = true
      decide +kernel)

theorem no_extent_squares (σ : Perm twoSquares) : ¬ IsExtent turnL turnR σ := by
  classical
  let _ : Fintype twoSquares := Fintype.ofFinite _
  have hL1 : turnL ≠ 1 := by
    intro e
    have := congrArg Subtype.val e
    revert this
    decide
  have hidx := Subgroup.card_mul_index (Subgroup.zpowers turnL)
  rw [Nat.card_zpowers, square_order, card_squares] at hidx
  have hi : (Subgroup.zpowers turnL).index = 30 := by omega
  refine no_extent_of_sign ?_ ?_ ?_ σ
  · rw [sign_mulLeft_eq hL1, square_order, hi]
    decide
  · apply odd_order_of_period (m := 3) (by decide)
    apply Subtype.ext
    decide
  · rw [← Nat.card_eq_fintype_card, card_squares]
    norm_num

theorem fewest_squares : FewestBack turnL turnR 2 := by
  refine modelSquares.fewest_two (π := MonoidHom.id _) closure_turns no_extent_squares
    ?_ ?_ ?_ ?_ ?_ (P := 3) (N := 120) (w := Cert.wordSquares) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · intro e; have := congrArg Subtype.val e; revert this; decide
  · intro e; have := congrArg Subtype.val e; revert this; decide
  · intro e; have := congrArg Subtype.val e; revert this; decide
  · intro e; have := congrArg Subtype.val e; revert this; decide
  · intro e; have := congrArg Subtype.val e; revert this; decide
  · change codeSix (iterC nextSix 3 oneSix) = codeSix oneSix
    decide +kernel
  · change checkOffsets nextSix codeSix 3 oneSix = true
    decide +kernel
  · change checkRun nextSix codeSix (digits 120 Cert.wordSquares) oneSix = true
    decide +kernel
  · decide +kernel

end TwoSquares

end Artform.Scores.Bells

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open Bells

/-- **T15** (the balance of back-steps). -/
@[ledger "T15"]
theorem backStepBalance : Statement.backStepBalance := by
  intro G _ _ A B σ O hAB hO
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hb := balance hAB σ O.toFinset (by simpa using hO)
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card', Set.toFinset_inter,
    Set.toFinset_inter]
  convert hb using 2
  · ext x; simp
  · ext x; simp

/-- **T15** (the two squares). -/
@[ledger "T15"]
theorem twoSquaresBackTurns : Statement.twoSquaresBackTurns := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_, fewest_squares⟩
  · apply orderOf_eq_prime
    · apply Subtype.ext; decide
    · intro e; have := congrArg Subtype.val e; revert this; decide
  · apply orderOf_eq_prime
    · apply Subtype.ext; decide
    · intro e; have := congrArg Subtype.val e; revert this; decide
  · apply orderOf_eq_prime
    · apply Subtype.ext; decide
    · intro e; have := congrArg Subtype.val e; revert this; decide

/-- **T15** (the fewest back-steps). -/
@[ledger "T15"]
theorem fewestBackSteps : Statement.fewestBackSteps := by
  refine ⟨?_, ?_, ?_, ?_, ?_, threeBack8⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fewest_zero some3.1, fewest_zero some3.2⟩
    · exact ⟨fewest_zero some6.1, fewest_zero some6.2⟩
    · exact ⟨fewest_zero some7.1, fewest_zero some7.2⟩
    · exact ⟨fewest_zero some9.1, fewest_zero some9.2⟩
    · exact ⟨fewest_zero some12.1, fewest_zero some12.2⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact fewest4
    · exact fewest5
    · exact fewest10
    · exact fewest13
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact notFew8
    · exact notFew11
  · exact fun σ hσ => three_le none11.1 hσ (notFew11.1 σ hσ)
  · exact fun σ hσ => three_le none11.2 hσ (notFew11.2 σ hσ)

/-- **T15** (the table of forward extents). -/
@[ledger "T15"]
theorem forwardExtentTable : Statement.forwardExtentTable := by
  refine ⟨countSL2, countPSL2, countSL3, countPSL3, countSL6, countPSL6, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    have key : ∀ {n : ℕ}, ((∀ σ, ¬ IsExtent (leapK n) (leapM n) σ) ∧
        ∀ σ, ¬ IsExtent (barK n) (barM n) σ) → extentsSL n = ∅ ∧ extentsPSL n = ∅ :=
      fun h => ⟨Set.eq_empty_of_forall_notMem h.1, Set.eq_empty_of_forall_notMem h.2⟩
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact key none4
    · exact key none5
    · exact key none10
    · exact key none11
    · exact key none13
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    have key : ∀ {n : ℕ}, ((∃ σ, IsExtent (leapK n) (leapM n) σ) ∧
        ∃ σ, IsExtent (barK n) (barM n) σ) → (extentsSL n).Nonempty ∧ (extentsPSL n).Nonempty :=
      fun h => ⟨h.1, h.2⟩
    rcases hn with rfl | rfl | rfl
    · exact key some7
    · exact key some9
    · exact key some12

/-! ## Non-vacuity

The table and the fewest back-steps are statements about given groups, and each clause holds by a
checked word or a computation; `FewestBack` asserts a run. The balance on `ℤ/3`:
-/

/-- `ℤ/3`, written multiplicatively, with the steps `A = +1` and `B = +2`. -/
abbrev Z3 := Multiplicative (ZMod 3)

theorem z3_backSteps : backSteps (Multiplicative.ofAdd 1 : Z3) (Multiplicative.ofAdd 2)
    (1 : Equiv.Perm Z3) = Set.univ := by
  ext x
  simp only [backSteps, Equiv.Perm.one_apply, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  revert x
  decide

/-- The balance on `ℤ/3`: the identity has three back-steps, and `B v` is the target of a back-step
for all three `v`. -/
example : ((Set.univ : Set Z3) ∩ backSteps (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 2)
      (1 : Equiv.Perm Z3)).ncard = 3 ∧
    (Set.univ ∩ {v : Z3 | (1 : Equiv.Perm Z3)⁻¹ (Multiplicative.ofAdd 2 * v) ∈
      backSteps (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 2)
        (1 : Equiv.Perm Z3)}).ncard = 3 := by
  have h3 : (Set.univ : Set Z3).ncard = 3 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    rfl
  have h1 : ((Set.univ : Set Z3) ∩ backSteps (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 2)
      (1 : Equiv.Perm Z3)).ncard = 3 := by
    rw [z3_backSteps, Set.inter_self, h3]
  refine ⟨h1, ?_⟩
  rw [← backStepBalance Z3 _ _ _ _ (by decide) (by simp)]
  exact h1

end Artform.Scores
