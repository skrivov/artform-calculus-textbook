import ArtformScores.BackSteps
import ArtformScores.CRT

/-!
# Runs: back-steps and checked words

The tools for the rest of the ledger's finding 043, Theorems S5.3 and S5.4.
- **The balance.** For any permutation `σ` of a finite group, every `y = B v` has one predecessor:
  `c v` by `A`, `v` by `B`, or a back-step. Summed over a union `O` of cosets of `⟨c⟩`, this says
  that the back-steps in `O` are as many as the `v ∈ O` with `B v` the target of a back-step. So a
  back-step's offset `B⁻¹ σ(x) x⁻¹` must carry the coset of `x` to the coset of a back-step, which
  excludes one back-step, or two, by a small computation. Lemma 3 of the ledger is the first case.
- **Checked words.** A run is given as a word in the letters `A`, `B`, `A⁻¹`, `B⁻¹`, packed into a
  natural number. `checkRun` follows it on natural numbers: `Model` says how to compute in a group,
  a quotient of `G₀`. The kernel runs the check, a mask of the codes seen, quickly.
- **The instances.** `SL(2, Z/n)` and `PSL(2, Z/n)` under the leapfrog's `K` and `M`, which generate
  `SL(2, Z/n)` by T1.
-/

namespace Artform.Scores.Bells

open Equiv

section Balance

variable {G : Type*} [Group G]

open scoped Classical in
/-- **The balance.** For any permutation `σ` of a finite group, and any union `O` of cosets `⟨c⟩ x`,
`c = A⁻¹ B`, the back-steps in `O` are as many as the `v ∈ O` with `B v` the target of a
back-step. -/
theorem balance {A B : G} (hAB : A ≠ B) (σ : Perm G) (O : Finset G)
    (hO : ∀ v, A⁻¹ * B * v ∈ O ↔ v ∈ O) :
    (O.filter fun x => x ∈ backSteps A B σ).card =
      (O.filter fun v => σ⁻¹ (B * v) ∈ backSteps A B σ).card := by
  set c := A⁻¹ * B with hc
  have hc1 : ∀ v, c * v ≠ v := by
    intro v h
    have : c = 1 := by simpa using h
    apply hAB
    rw [hc, inv_mul_eq_one] at this
    exact this
  have hcne : c ≠ 1 := fun h => hc1 1 (by simp [h])
  set a : G → ℕ := fun x => if σ x = A * x then 1 else 0 with ha
  set b : G → ℕ := fun x => if σ x = B * x then 1 else 0 with hb
  have h1 : ∀ x, a x + b x + (if x ∈ backSteps A B σ then 1 else 0) = 1 := by
    intro x
    simp only [ha, hb, backSteps, Set.mem_ofPred_eq]
    by_cases hA : σ x = A * x
    · have hB : σ x ≠ B * x := fun hB => hAB (mul_right_cancel (hA.symm.trans hB))
      simp [hA, hAB]
    · by_cases hB : σ x = B * x <;> simp [hA, hB, hAB.symm]
  have hAc : ∀ v, A * (c * v) = B * v := by
    intro v
    rw [hc]
    group
  have h2 : ∀ v, a (c * v) + b v + (if σ⁻¹ (B * v) ∈ backSteps A B σ then 1 else 0) = 1 := by
    intro v
    set z := σ⁻¹ (B * v) with hz
    have hσz : σ z = B * v := by simp [hz]
    have hzz : ∀ y, σ y = B * v ↔ y = z := by
      intro y
      rw [hz, Perm.eq_inv_iff_eq]
    simp only [ha, hb, backSteps, Set.mem_ofPred_eq]
    rw [hAc, hzz, hzz]
    by_cases hcz : c * v = z
    · have hvz : v ≠ z := fun h => hc1 v (hcz.trans h.symm)
      have : σ z = A * z := by rw [hσz, ← hcz, hAc]
      simp [hcz, hvz, this, hAB]
    · by_cases hvz : v = z
      · have : σ z = B * z := by rw [hσz, hvz]
        simp [hvz, this, hAB.symm, hcne]
      · have h3 : σ z ≠ A * z := by
          intro h
          apply hcz
          rw [hσz] at h
          have := h.symm.trans (hAc v).symm
          exact (mul_left_cancel this).symm
        have h4 : σ z ≠ B * z := by
          intro h
          apply hvz
          rw [hσz] at h
          exact mul_left_cancel h
        simp [hcz, hvz, h3, h4]
  have hsum : ∑ v ∈ O, a (c * v) = ∑ v ∈ O, a v :=
    Finset.sum_bij (fun v _ => c * v) (fun v hv => (hO v).mpr hv)
      (fun _ _ _ _ h => mul_left_cancel h)
      (fun y hy => ⟨c⁻¹ * y, (hO _).mp (by simpa using hy), by simp⟩) (fun _ _ => rfl)
  have s1 : ∑ v ∈ O, (a v + b v + (if v ∈ backSteps A B σ then 1 else 0)) = O.card := by
    rw [Finset.sum_congr rfl fun x _ => h1 x]
    simp
  have s2 : ∑ v ∈ O, (a (c * v) + b v + (if σ⁻¹ (B * v) ∈ backSteps A B σ then 1 else 0)) =
      O.card := by
    rw [Finset.sum_congr rfl fun x _ => h2 x]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at s1 s2
  rw [hsum] at s2
  rw [Finset.card_filter, Finset.card_filter]
  omega

/-- Every back-step `x₀` is balanced by the target of a back-step `x`, with
`B⁻¹ σ(x) x₀⁻¹ ∈ ⟨c⟩`. -/
theorem exists_break [Finite G] {A B : G} (hAB : A ≠ B) (σ : Perm G) {x₀ : G}
    (hx₀ : x₀ ∈ backSteps A B σ) :
    ∃ x ∈ backSteps A B σ, B⁻¹ * σ x * x₀⁻¹ ∈ Subgroup.zpowers (A⁻¹ * B) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  set Z := Subgroup.zpowers (A⁻¹ * B) with hZ
  set O : Finset G := Finset.univ.filter fun v => v * x₀⁻¹ ∈ Z with hOdef
  have hO : ∀ v, A⁻¹ * B * v ∈ O ↔ v ∈ O := by
    intro v
    simp only [hOdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_assoc]
    exact Subgroup.mul_mem_cancel_left _ (Subgroup.mem_zpowers _)
  have hb := balance hAB σ O hO
  have hmem : x₀ ∈ O.filter fun x => x ∈ backSteps A B σ := by
    simp only [hOdef, Finset.mem_filter, Finset.mem_univ, true_and, mul_inv_cancel]
    exact ⟨Subgroup.one_mem _, hx₀⟩
  have hpos : 0 < (O.filter fun v => σ⁻¹ (B * v) ∈ backSteps A B σ).card := by
    rw [← hb]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  simp only [hOdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨_, hv.2, ?_⟩
  simpa using hv.1

variable {A B : G}

/-- A back-step of a run has the offset `B⁻¹ A⁻¹` or `B⁻¹ B⁻¹`. -/
theorem offset_of_run {σ : Perm G} (hstep : ∀ x, σ x = A * x ∨ σ x = B * x ∨ σ x = A⁻¹ * x ∨
    σ x = B⁻¹ * x) {x : G} (hx : x ∈ backSteps A B σ) :
    B⁻¹ * σ x * x⁻¹ = B⁻¹ * A⁻¹ ∨ B⁻¹ * σ x * x⁻¹ = B⁻¹ * B⁻¹ := by
  rcases hstep x with h | h | h | h
  · exact absurd h hx.1
  · exact absurd h hx.2
  · left
    rw [h]
    group
  · right
    rw [h]
    group

variable [Finite G]

/-- A run with no back-steps is an extent. -/
theorem IsRun.isExtent {σ : Perm G} (hσ : IsRun A B σ) (h : (backSteps A B σ).ncard = 0) :
    IsExtent A B σ := by
  refine ⟨fun x => ?_, hσ.2⟩
  have he : backSteps A B σ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp h
  by_contra hx
  push Not at hx
  have : x ∈ backSteps A B σ := hx
  rw [he] at this
  exact this

/-- One back-step needs an offset in `⟨c⟩`. -/
theorem not_one_back (hAB : A ≠ B) (h1 : B⁻¹ * A⁻¹ ∉ Subgroup.zpowers (A⁻¹ * B))
    (h2 : B⁻¹ * B⁻¹ ∉ Subgroup.zpowers (A⁻¹ * B)) {σ : Perm G} (hσ : IsRun A B σ) :
    (backSteps A B σ).ncard ≠ 1 := by
  intro hc
  obtain ⟨x₀, hX⟩ := Set.ncard_eq_one.mp hc
  have hx₀ : x₀ ∈ backSteps A B σ := by rw [hX]; rfl
  obtain ⟨x, hx, hm⟩ := exists_break hAB σ hx₀
  rw [hX] at hx
  obtain rfl : x = x₀ := hx
  rcases offset_of_run hσ.1 hx₀ with h | h <;> rw [h] at hm
  · exact h1 hm
  · exact h2 hm

/-- Two back-steps need a product `g₀ m g₁ ∈ ⟨c⟩` of two offsets and an element `m` of `⟨c⟩`, or
an offset in `⟨c⟩`. -/
theorem not_two_back (hAB : A ≠ B) (h1 : B⁻¹ * A⁻¹ ∉ Subgroup.zpowers (A⁻¹ * B))
    (h2 : B⁻¹ * B⁻¹ ∉ Subgroup.zpowers (A⁻¹ * B))
    (h3 : ∀ g₀ ∈ ({B⁻¹ * A⁻¹, B⁻¹ * B⁻¹} : Set G), ∀ g₁ ∈ ({B⁻¹ * A⁻¹, B⁻¹ * B⁻¹} : Set G),
      ∀ m ∈ Subgroup.zpowers (A⁻¹ * B), g₀ * m * g₁ ∉ Subgroup.zpowers (A⁻¹ * B))
    {σ : Perm G} (hσ : IsRun A B σ) : (backSteps A B σ).ncard ≠ 2 := by
  intro hc
  obtain ⟨x₀, x₁, -, hX⟩ := Set.ncard_eq_two.mp hc
  have hx₀ : x₀ ∈ backSteps A B σ := by rw [hX]; simp
  have hx₁ : x₁ ∈ backSteps A B σ := by rw [hX]; simp
  have hD : ∀ {x}, x ∈ backSteps A B σ →
      B⁻¹ * σ x * x⁻¹ ∈ ({B⁻¹ * A⁻¹, B⁻¹ * B⁻¹} : Set G) := fun hx => offset_of_run hσ.1 hx
  have hnot : ∀ {x}, x ∈ backSteps A B σ →
      B⁻¹ * σ x * x⁻¹ ∉ Subgroup.zpowers (A⁻¹ * B) := by
    intro x hx
    rcases offset_of_run hσ.1 hx with h | h <;> rw [h]
    · exact h1
    · exact h2
  obtain ⟨x, hx, hm⟩ := exists_break hAB σ hx₀
  obtain ⟨y, hy, hn⟩ := exists_break hAB σ hx₁
  have hxx : x = x₀ ∨ x = x₁ := by rw [hX] at hx; simpa using hx
  have hyy : y = x₀ ∨ y = x₁ := by rw [hX] at hy; simpa using hy
  rcases hxx with rfl | rfl
  · exact hnot hx₀ hm
  rcases hyy with rfl | rfl
  · refine h3 _ (hD hx₀) _ (hD hx₁) _ (Subgroup.inv_mem _ hm) ?_
    convert hn using 1
    group
  · exact hnot hx₁ hn

end Balance

section Walk

variable {G : Type*} [Group G]

/-- A letter of a word: `0, 1, 2, 3` are the steps `A`, `B`, `A⁻¹`, `B⁻¹`. -/
def letter (A B : G) : ℕ → G
  | 0 => A
  | 1 => B
  | 2 => A⁻¹
  | _ => B⁻¹

/-- The elements that a word visits from `x`, before each of its steps. -/
def visits (A B : G) : List ℕ → G → List G
  | [], _ => []
  | s :: w, x => x :: visits A B w (letter A B s * x)

/-- Where a word ends. -/
def walkEnd (A B : G) : List ℕ → G → G
  | [], x => x
  | s :: w, x => walkEnd A B w (letter A B s * x)

@[simp] theorem length_visits (A B : G) (w : List ℕ) (x : G) :
    (visits A B w x).length = w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih => simp [visits, ih]

theorem letter_mul_getElem (A B : G) (w : List ℕ) (x : G) (i : ℕ) (hi : i < w.length) :
    letter A B w[i] * (visits A B w x)[i]'(by simpa using hi) =
      if h : i + 1 < w.length then (visits A B w x)[i + 1]'(by simpa using h)
      else walkEnd A B w x := by
  induction w generalizing x i with
  | nil => simp at hi
  | cons s w ih =>
    cases i with
    | zero =>
      cases w with
      | nil => simp [visits, walkEnd]
      | cons t w => simp [visits]
    | succ i =>
      have hi' : i < w.length := by simpa using hi
      have := ih (letter A B s * x) i hi'
      simpa [visits, walkEnd] using this

theorem letter_cases (A B : G) (s : ℕ) :
    letter A B s = A ∨ letter A B s = B ∨ letter A B s = A⁻¹ ∨ letter A B s = B⁻¹ := by
  match s with
  | 0 => simp [letter]
  | 1 => simp [letter]
  | 2 => simp [letter]
  | _ + 3 => simp [letter]

/-- A closed walk through all of `G` makes a run. -/
theorem exists_run {A B : G} {w : List ℕ} (hw : w ≠ []) (hnd : (visits A B w 1).Nodup)
    (hend : walkEnd A B w 1 = 1) (hall : ∀ x, x ∈ visits A B w 1) :
    ∃ σ : Perm G, (∀ x y, ∃ k : ℕ, (σ ^ k) x = y) ∧
      ∀ (i : ℕ) (hi : i < w.length), σ ((visits A B w 1)[i]'(by simpa using hi)) =
        letter A B w[i] * (visits A B w 1)[i]'(by simpa using hi) := by
  classical
  have hlen : 0 < (visits A B w 1).length := by
    simpa using List.length_pos_iff.mpr hw
  have hhead : (visits A B w 1)[0]'hlen = 1 := by
    cases w with
    | nil => exact absurd rfl hw
    | cons s w => rfl
  refine ⟨(visits A B w 1).formPerm, ?_, ?_⟩
  · intro x y
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall y)
    refine ⟨j + ((visits A B w 1).length - i), ?_⟩
    rw [List.formPerm_pow_apply_getElem _ hnd]
    congr 1
    rw [show i + (j + ((visits A B w 1).length - i)) = j + (visits A B w 1).length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · intro i hi
    rw [List.formPerm_apply_getElem _ hnd, letter_mul_getElem]
    simp only [length_visits]
    split_ifs with h
    · simp only [Nat.mod_eq_of_lt h]
    · have : i + 1 = w.length := by omega
      simp only [this, Nat.mod_self]
      rw [hend]
      simpa using hhead

theorem card_filter_getElem (w : List ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun i : Fin w.length => p w[i.1] = true).card = w.countP p := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [Finset.card_filter] at ih ⊢
    have h : ∑ i : Fin (s :: w).length, (if p (s :: w)[i.1] = true then 1 else 0) =
        (if p s = true then 1 else 0) + ∑ i : Fin w.length, (if p w[i.1] = true then 1 else 0) :=
      Fin.sum_univ_succ (n := w.length) _
    rw [h, ih, List.countP_cons, add_comm]

/-- The back-steps of the run of a word are its back letters. -/
theorem ncard_backSteps_of_walk [Finite G] {A B : G} {w : List ℕ} {σ : Perm G}
    (hnd : (visits A B w 1).Nodup) (hall : ∀ x, x ∈ visits A B w 1)
    (hσ : ∀ (i : ℕ) (hi : i < w.length), σ ((visits A B w 1)[i]'(by simpa using hi)) =
        letter A B w[i] * (visits A B w 1)[i]'(by simpa using hi))
    (h1 : A⁻¹ ≠ A) (h2 : A⁻¹ ≠ B) (h3 : B⁻¹ ≠ A) (h4 : B⁻¹ ≠ B) :
    (backSteps A B σ).ncard = w.countP (2 ≤ ·) := by
  classical
  have hiff : ∀ (i : ℕ) (hi : i < w.length),
      (visits A B w 1)[i]'(by simpa using hi) ∈ backSteps A B σ ↔ 2 ≤ w[i] := by
    intro i hi
    simp only [backSteps, Set.mem_ofPred_eq]
    rw [hσ i hi]
    simp only [ne_eq, mul_left_inj]
    match hs : w[i] with
    | 0 => simp [letter]
    | 1 => simp [letter]
    | 2 => simp [letter, h1, h2]
    | s + 3 => simp [letter, h3, h4]
  have himg : backSteps A B σ = (fun i : Fin w.length => (visits A B w 1)[i.1]'(by simp)) ''
      {i | 2 ≤ w[i.1]} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
      have hi' : i < w.length := by simpa using hi
      exact ⟨⟨i, hi'⟩, (hiff i hi').mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hiff i.1 i.2).mpr hi
  have hinj : Function.Injective (fun i : Fin w.length => (visits A B w 1)[i.1]'(by simp)) := by
    intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hij)
  rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  simpa using card_filter_getElem w (fun s => decide (2 ≤ s))

/-- In a finite group, a set that holds `1` and is closed under left multiplication by generators
is everything. -/
theorem mem_of_closure [Finite G] {A B : G} (hgen : Subgroup.closure {A, B} = ⊤) {V : Set G}
    (h1 : 1 ∈ V) (hA : ∀ v ∈ V, A * v ∈ V) (hB : ∀ v ∈ V, B * v ∈ V) (x : G) : x ∈ V := by
  have key : ∀ g ∈ Subgroup.closure ({A, B} : Set G), ∀ v ∈ V, g * v ∈ V := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hA
      · exact hB
    | one => simp
    | mul a b _ _ iha ihb =>
      intro v hv
      rw [mul_assoc]
      exact iha _ (ihb v hv)
    | inv a _ iha =>
      intro v hv
      have hpow : ∀ k : ℕ, a ^ k * v ∈ V := by
        intro k
        induction k with
        | zero => simpa using hv
        | succ k ih =>
          rw [pow_succ', mul_assoc]
          exact iha _ ih
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        apply mul_left_cancel (a := a)
        rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      rw [hinv]
      exact hpow _
  have := key x (by rw [hgen]; trivial) 1 h1
  simpa using this

end Walk

section Check

/-! ## The checker

A word is checked on codes, by natural-number arithmetic that the kernel runs quickly. `pass1`
follows the word and refuses a state whose code is in the mask of the states before it. `pass2` asks
that both forward steps from every visited state lead into the final mask. -/

variable {S : Type*} (next : ℕ → S → S) (code : S → ℕ)

/-- The digits of a word, packed in base 4. -/
def digits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | N + 1, w => w % 4 :: digits N (w / 4)

theorem digits_ne_nil {N : ℕ} (hN : 0 < N) (w : ℕ) : digits N w ≠ [] := by
  cases N with
  | zero => omega
  | succ N => simp [digits]

@[simp] theorem length_digits (N w : ℕ) : (digits N w).length = N := by
  induction N generalizing w with
  | zero => rfl
  | succ N ih => simp [digits, ih]

/-- Packs chunks of `64` letters, the first chunk first. -/
def pack : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + 2 ^ 128 * pack cs

theorem testBit_or_shift (mask k j : ℕ) :
    (mask ||| 1 <<< k).testBit j = true ↔ mask.testBit j = true ∨ j = k := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr_right eq_comm

/-- The first pass: the state after the word, and the mask of the visited states. -/
def pass1 : List ℕ → S → ℕ → Option (S × ℕ)
  | [], x, mask => some (x, mask)
  | s :: w, x, mask =>
    if mask.testBit (code x) then none else pass1 w (next s x) (mask ||| 1 <<< code x)

/-- The second pass. -/
def pass2 (mask : ℕ) : List ℕ → S → Bool
  | [], _ => true
  | s :: w, x =>
    mask.testBit (code (next 0 x)) && mask.testBit (code (next 1 x)) &&
      pass2 mask w (next s x)

/-- The certificate check of a word from the state `x₀`. -/
def checkRun (word : List ℕ) (x₀ : S) : Bool :=
  match pass1 next code word x₀ 0 with
  | none => false
  | some (x, mask) => code x == code x₀ && pass2 next code mask word x₀

variable {G₀ G : Type*} [Group G₀] [Group G] {A₀ B₀ : G₀} {π : G₀ →* G} {enc : G₀ → S}

theorem map_letter (π : G₀ →* G) (A₀ B₀ : G₀) (s : ℕ) :
    π (letter A₀ B₀ s) = letter (π A₀) (π B₀) s := by
  match s with
  | 0 => rfl
  | 1 => rfl
  | 2 => simp [letter]
  | _ + 3 => simp [letter]

theorem map_visits (π : G₀ →* G) (A₀ B₀ : G₀) (w : List ℕ) (g : G₀) :
    (visits A₀ B₀ w g).map π = visits (π A₀) (π B₀) w (π g) := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp [visits, ih, map_letter]

theorem map_walkEnd (π : G₀ →* G) (A₀ B₀ : G₀) (w : List ℕ) (g : G₀) :
    π (walkEnd A₀ B₀ w g) = walkEnd (π A₀) (π B₀) w (π g) := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp [walkEnd, ih, map_letter]

theorem pass1_spec (hnext : ∀ s g, next s (enc g) = enc (letter A₀ B₀ s * g)) (w : List ℕ)
    (g : G₀) (mask : ℕ) (out : S × ℕ) (h : pass1 next code w (enc g) mask = some out) :
    out.1 = enc (walkEnd A₀ B₀ w g) ∧
    (∀ j, out.2.testBit j = true ↔
      mask.testBit j = true ∨ ∃ y ∈ visits A₀ B₀ w g, j = code (enc y)) ∧
    (∀ y ∈ visits A₀ B₀ w g, mask.testBit (code (enc y)) = false) ∧
    (visits A₀ B₀ w g).Pairwise (fun y z => code (enc z) ≠ code (enc y)) := by
  induction w generalizing g mask with
  | nil =>
    simp only [pass1, Option.some.injEq] at h
    subst h
    simp [visits, walkEnd]
  | cons s w ih =>
    simp only [pass1] at h
    split_ifs at h with hb
    rw [hnext] at h
    obtain ⟨h1, h2, h3, h4⟩ := ih _ _ h
    have hb' : mask.testBit (code (enc g)) = false := by simpa using hb
    refine ⟨h1, ?_, ?_, ?_⟩
    · intro j
      rw [h2, testBit_or_shift]
      simp only [visits, List.mem_cons, exists_eq_or_imp]
      tauto
    · intro y hy
      rw [visits, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hb'
      · have := h3 y hy
        have h5 := (testBit_or_shift mask (code (enc g)) (code (enc y))).not.mp (by simp [this])
        simpa using (not_or.mp h5).1
    · rw [visits, List.pairwise_cons]
      refine ⟨fun z hz => ?_, h4⟩
      have := h3 z hz
      have h5 := (testBit_or_shift mask (code (enc g)) (code (enc z))).not.mp (by simp [this])
      exact (not_or.mp h5).2

theorem pass2_spec (hnext : ∀ s g, next s (enc g) = enc (letter A₀ B₀ s * g)) (mask : ℕ)
    (w : List ℕ) (g : G₀) (h : pass2 next code mask w (enc g) = true) :
    ∀ y ∈ visits A₀ B₀ w g,
      mask.testBit (code (enc (A₀ * y))) = true ∧ mask.testBit (code (enc (B₀ * y))) = true := by
  induction w generalizing g with
  | nil => simp [visits]
  | cons s w ih =>
    simp only [pass2, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hrest⟩ := h
    rw [hnext] at ha hb hrest
    intro y hy
    rw [visits, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨ha, hb⟩
    · exact ih _ hrest y hy

/-- A certificate gives a closed walk of `G` through all of `G`, one element at a time. -/
theorem walk_of_check [Finite G]
    (hnext : ∀ s g, next s (enc g) = enc (letter A₀ B₀ s * g))
    (hcode : ∀ g h, code (enc g) = code (enc h) ↔ π g = π h)
    (hgen : Subgroup.closure {π A₀, π B₀} = ⊤) {w : List ℕ} (hw : w ≠ [])
    (hcheck : checkRun next code w (enc 1) = true) :
    (visits (π A₀) (π B₀) w 1).Nodup ∧ walkEnd (π A₀) (π B₀) w 1 = 1 ∧
      ∀ x, x ∈ visits (π A₀) (π B₀) w 1 := by
  rw [checkRun] at hcheck
  split at hcheck
  · exact absurd hcheck (by simp)
  rename_i x mask hp
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2, h3, h4⟩ := pass1_spec next code hnext w 1 0 (x, mask) hp
  have hvis := map_visits π A₀ B₀ w 1
  rw [map_one] at hvis
  have hend : walkEnd (π A₀) (π B₀) w 1 = 1 := by
    have := map_walkEnd π A₀ B₀ w 1
    rw [map_one] at this
    rw [← this, ← map_one π]
    apply (hcode _ _).mp
    rw [← (show x = _ from h1)]
    simpa using hcheck.1
  refine ⟨?_, hend, ?_⟩
  · rw [← hvis, List.Nodup, List.pairwise_map]
    refine h4.imp ?_
    intro y z hyz hne
    exact hyz ((hcode z y).mpr hne.symm)
  · have hclosed : ∀ y ∈ visits A₀ B₀ w 1, ∀ C ∈ ({A₀, B₀} : Set G₀),
        π C * π y ∈ visits (π A₀) (π B₀) w 1 := by
      intro y hy C hC
      have hspec := pass2_spec next code hnext mask w 1 hcheck.2 y hy
      have hbit : mask.testBit (code (enc (C * y))) = true := by
        rcases hC with rfl | rfl
        · exact hspec.1
        · exact hspec.2
      have := (h2 _).mp hbit
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at this
      obtain ⟨z, hz, hmem⟩ := this
      have heq := (hcode _ _).mp hmem
      rw [map_mul] at heq
      rw [heq, ← hvis]
      exact List.mem_map_of_mem hz
    have hmem : ∀ v ∈ {x | x ∈ visits (π A₀) (π B₀) w 1}, ∀ C ∈ ({A₀, B₀} : Set G₀),
        π C * v ∈ {x | x ∈ visits (π A₀) (π B₀) w 1} := by
      intro v hv C hC
      rw [Set.mem_ofPred_eq, ← hvis, List.mem_map] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      exact hclosed y hy C hC
    refine mem_of_closure hgen (V := {x | x ∈ visits (π A₀) (π B₀) w 1}) ?_
      (fun v hv => hmem v hv A₀ (by simp)) (fun v hv => hmem v hv B₀ (by simp))
    cases w with
    | nil => exact absurd rfl hw
    | cons s w => simp [visits]

end Check

section Model

/-- A way to compute with a group `G`, a quotient of `G₀` by the map `π`, on states: `enc`
computes the state of an element of `G₀`, `next` follows a letter, and `code` names the image of
a state in `G`. -/
structure Model (S : Type*) {G₀ G : Type*} [Group G₀] [Group G] (A₀ B₀ : G₀) (π : G₀ →* G) where
  next : ℕ → S → S
  code : S → ℕ
  enc : G₀ → S
  hnext : ∀ s g, next s (enc g) = enc (letter A₀ B₀ s * g)
  hcode : ∀ g h, code (enc g) = code (enc h) ↔ π g = π h

variable {S : Type*} {G₀ G : Type*} [Group G₀] [Group G] {A₀ B₀ : G₀} {π : G₀ →* G}

/-- The step by `c = A⁻¹ B` on states. -/
def stepC (next : ℕ → S → S) (x : S) : S := next 2 (next 1 x)

/-- The offset `B⁻¹ A⁻¹` on states. -/
def offA (next : ℕ → S → S) (x : S) : S := next 3 (next 2 x)

/-- The offset `B⁻¹ B⁻¹` on states. -/
def offB (next : ℕ → S → S) (x : S) : S := next 3 (next 3 x)

/-- The power `c^k` applied to a state. -/
def iterC (next : ℕ → S → S) : ℕ → S → S
  | 0, x => x
  | k + 1, x => iterC next k (stepC next x)

/-- The state `y` is not `c^k p`, up to the kernel of `π`, for any `k < N`. -/
def notPow (next : ℕ → S → S) (code : S → ℕ) (y : S) : ℕ → S → Bool
  | 0, _ => true
  | N + 1, p => code p != code y && notPow next code y N (stepC next p)

/-- The check that the offsets are not in `⟨c⟩`: `N` is a period of `c`. -/
def checkOffsets (next : ℕ → S → S) (code : S → ℕ) (N : ℕ) (x₀ : S) : Bool :=
  notPow next code (offA next x₀) N x₀ && notPow next code (offB next x₀) N x₀

/-- The check on `g₀ c^i g₁` for `i < M`, from the state `p` of `g₁`. -/
def checkPairsFrom (next : ℕ → S → S) (code : S → ℕ) (N : ℕ) (x₀ : S) : ℕ → S → Bool
  | 0, _ => true
  | M + 1, p =>
    notPow next code (offA next p) N x₀ && notPow next code (offB next p) N x₀ &&
      checkPairsFrom next code N x₀ M (stepC next p)

/-- The check that no `g₀ c^i g₁` lies in `⟨c⟩`, `g₀` and `g₁` offsets. -/
def checkPairs (next : ℕ → S → S) (code : S → ℕ) (N : ℕ) (x₀ : S) : Bool :=
  checkPairsFrom next code N x₀ N (offA next x₀) &&
    checkPairsFrom next code N x₀ N (offB next x₀)

variable (M : Model S A₀ B₀ π)

namespace Model

theorem enc_stepC (g : G₀) : stepC M.next (M.enc g) = M.enc (A₀⁻¹ * B₀ * g) := by
  rw [stepC, M.hnext, M.hnext, mul_assoc]
  rfl

theorem enc_offA (g : G₀) : offA M.next (M.enc g) = M.enc (B₀⁻¹ * A₀⁻¹ * g) := by
  rw [offA, M.hnext, M.hnext, mul_assoc]
  rfl

theorem enc_offB (g : G₀) : offB M.next (M.enc g) = M.enc (B₀⁻¹ * B₀⁻¹ * g) := by
  rw [offB, M.hnext, M.hnext, mul_assoc]
  rfl

theorem enc_iterC (k : ℕ) (g : G₀) :
    iterC M.next k (M.enc g) = M.enc ((A₀⁻¹ * B₀) ^ k * g) := by
  induction k generalizing g with
  | zero => simp [iterC]
  | succ k ih =>
    rw [iterC, enc_stepC, ih, pow_succ]
    simp only [mul_assoc]

/-- A power of `c` from a computation: `π(c^k g) = π h` when their codes agree. -/
theorem pow_of_code {k : ℕ} {g h : G₀}
    (e : M.code (iterC M.next k (M.enc g)) = M.code (M.enc h)) :
    π ((A₀⁻¹ * B₀) ^ k * g) = π h := by
  rw [enc_iterC] at e
  exact (M.hcode _ _).mp e

theorem notPow_spec (x : G₀) (N : ℕ) (g : G₀)
    (h : notPow M.next M.code (M.enc x) N (M.enc g) = true) :
    ∀ k < N, π x ≠ π ((A₀⁻¹ * B₀) ^ k * g) := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    simp only [notPow, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro k hk he
    cases k with
    | zero =>
      apply h.1
      rw [M.hcode, he]
      simp
    | succ k =>
      rw [enc_stepC] at h
      apply ih _ h.2 k (by omega)
      rw [he, pow_succ, mul_assoc]

/-- `N` is a period of `π c`. -/
theorem pow_period {N : ℕ} (hper : M.code (iterC M.next N (M.enc 1)) = M.code (M.enc 1)) :
    ((π A₀)⁻¹ * π B₀) ^ N = 1 := by
  have := M.pow_of_code hper
  simpa using this

/-- `π x` is no power of `π c`, when `N` is a period of `π c`. -/
theorem not_mem_of_notPow [Finite G] {x : G₀} {N : ℕ} (hN : 0 < N)
    (hper : M.code (iterC M.next N (M.enc 1)) = M.code (M.enc 1))
    (h : notPow M.next M.code (M.enc x) N (M.enc 1) = true) :
    π x ∉ Subgroup.zpowers ((π A₀)⁻¹ * π B₀) := by
  intro hmem
  have hpow := M.pow_period hper
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  apply M.notPow_spec x N 1 h (k % N) (Nat.mod_lt _ hN)
  rw [mul_one, map_pow, map_mul, map_inv, ← hk]
  conv_lhs => rw [← Nat.div_add_mod k N, pow_add, pow_mul, hpow, one_pow, one_mul]

theorem checkPairsFrom_spec {N : ℕ} (K : ℕ) (g : G₀)
    (h : checkPairsFrom M.next M.code N (M.enc 1) K (M.enc g) = true) :
    ∀ i < K, notPow M.next M.code (M.enc (B₀⁻¹ * A₀⁻¹ * ((A₀⁻¹ * B₀) ^ i * g))) N
        (M.enc 1) = true ∧
      notPow M.next M.code (M.enc (B₀⁻¹ * B₀⁻¹ * ((A₀⁻¹ * B₀) ^ i * g))) N
        (M.enc 1) = true := by
  induction K generalizing g with
  | zero => simp
  | succ K ih =>
    simp only [checkPairsFrom, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hrest⟩ := h
    rw [enc_stepC] at hrest
    rw [enc_offA] at ha
    rw [enc_offB] at hb
    intro i hi
    cases i with
    | zero => simpa using ⟨ha, hb⟩
    | succ i =>
      have := ih _ hrest i (by omega)
      rw [pow_succ]
      simpa only [mul_assoc] using this

/-- The offsets are not in `⟨c⟩`. -/
theorem offsets_of_check [Finite G] {N : ℕ} (hN : 0 < N)
    (hper : M.code (iterC M.next N (M.enc 1)) = M.code (M.enc 1))
    (h1 : checkOffsets M.next M.code N (M.enc 1) = true) :
    (π B₀)⁻¹ * (π A₀)⁻¹ ∉ Subgroup.zpowers ((π A₀)⁻¹ * π B₀) ∧
      (π B₀)⁻¹ * (π B₀)⁻¹ ∉ Subgroup.zpowers ((π A₀)⁻¹ * π B₀) := by
  rw [checkOffsets, Bool.and_eq_true, enc_offA, enc_offB, mul_one, mul_one] at h1
  constructor
  · have := M.not_mem_of_notPow hN hper h1.1
    simpa only [map_mul, map_inv] using this
  · have := M.not_mem_of_notPow hN hper h1.2
    simpa only [map_mul, map_inv] using this

/-- The check on pairs of offsets excludes two back-steps. -/
theorem not_two_back_of_check [Finite G] {N : ℕ} (hN : 0 < N) (hAB : π A₀ ≠ π B₀)
    (hper : M.code (iterC M.next N (M.enc 1)) = M.code (M.enc 1))
    (h1 : checkOffsets M.next M.code N (M.enc 1) = true)
    (h2 : checkPairs M.next M.code N (M.enc 1) = true)
    {σ : Equiv.Perm G} (hσ : IsRun (π A₀) (π B₀) σ) :
    (backSteps (π A₀) (π B₀) σ).ncard ≠ 2 := by
  obtain ⟨hZ1, hZ2⟩ := M.offsets_of_check hN hper h1
  refine not_two_back hAB hZ1 hZ2 ?_ hσ
  rw [checkPairs, Bool.and_eq_true, enc_offA, enc_offB, mul_one, mul_one] at h2
  have hpow := M.pow_period hper
  have key : ∀ g₁ : G₀, (∀ i < N, notPow M.next M.code
      (M.enc (B₀⁻¹ * A₀⁻¹ * ((A₀⁻¹ * B₀) ^ i * g₁))) N (M.enc 1) = true ∧
      notPow M.next M.code (M.enc (B₀⁻¹ * B₀⁻¹ * ((A₀⁻¹ * B₀) ^ i * g₁))) N
        (M.enc 1) = true) →
      ∀ g₀ ∈ ({(π B₀)⁻¹ * (π A₀)⁻¹, (π B₀)⁻¹ * (π B₀)⁻¹} : Set G),
      ∀ m ∈ Subgroup.zpowers ((π A₀)⁻¹ * π B₀),
        g₀ * m * π g₁ ∉ Subgroup.zpowers ((π A₀)⁻¹ * π B₀) := by
    intro g₁ hg₁ g₀ hg₀ m hm
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hm
    obtain ⟨k, rfl⟩ := hm
    have hk : ((π A₀)⁻¹ * π B₀) ^ k = ((π A₀)⁻¹ * π B₀) ^ (k % N) := by
      conv_lhs => rw [← Nat.div_add_mod k N, pow_add, pow_mul, hpow, one_pow, one_mul]
    rw [hk]
    obtain ⟨ha, hb⟩ := hg₁ (k % N) (Nat.mod_lt _ hN)
    have ha' := M.not_mem_of_notPow hN hper ha
    have hb' := M.not_mem_of_notPow hN hper hb
    simp only [map_mul, map_inv, map_pow] at ha' hb'
    rcases hg₀ with rfl | rfl
    · simpa only [mul_assoc] using ha'
    · simpa only [mul_assoc] using hb'
  intro g₀ hg₀ g₁ hg₁ m hm
  rcases hg₁ with rfl | rfl
  · have := key (B₀⁻¹ * A₀⁻¹) (M.checkPairsFrom_spec N _ h2.1) g₀ hg₀ m hm
    simpa only [map_mul, map_inv] using this
  · have := key (B₀⁻¹ * B₀⁻¹) (M.checkPairsFrom_spec N _ h2.2) g₀ hg₀ m hm
    simpa only [map_mul, map_inv] using this

/-- The order of `π c`, from its powers. -/
theorem orderOf_of_check {N : ℕ} (hN : 0 < N)
    (hper : M.code (iterC M.next N (M.enc 1)) = M.code (M.enc 1))
    (h : notPow M.next M.code (M.enc 1) (N - 1) (stepC M.next (M.enc 1)) = true) :
    orderOf ((π A₀)⁻¹ * π B₀) = N := by
  rw [orderOf_eq_iff hN]
  refine ⟨M.pow_period hper, fun m hm hm0 e => ?_⟩
  rw [enc_stepC, mul_one] at h
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  apply M.notPow_spec 1 (N - 1) _ h j (by omega)
  rw [map_one, map_mul, map_pow, map_mul, map_inv, ← pow_succ, e]

/-- A checked word of forward letters is an extent. -/
theorem extent_of_check [Finite G] (hgen : Subgroup.closure {π A₀, π B₀} = ⊤) {N w : ℕ}
    (hN : 0 < N) (hcheck : checkRun M.next M.code (digits N w) (M.enc 1) = true)
    (hf : (digits N w).all (· < 2) = true) : ∃ σ, IsExtent (π A₀) (π B₀) σ := by
  obtain ⟨hnd, hend, hall⟩ :=
    walk_of_check M.next M.code M.hnext M.hcode hgen (digits_ne_nil hN w) hcheck
  obtain ⟨σ, htrans, hσ⟩ := exists_run (digits_ne_nil hN w) hnd hend hall
  refine ⟨σ, fun x => ?_, htrans⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
  have hi' : i < (digits N w).length := by simpa using hi
  rw [hσ i hi']
  have hlt : (digits N w)[i] < 2 := by
    have := List.all_eq_true.mp hf _ (List.getElem_mem hi')
    simpa using this
  match hs : (digits N w)[i], hlt with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- A checked word is a run with its back letters for back-steps, and the group has as many
elements as the word has letters. -/
theorem run_of_check [Finite G] (hgen : Subgroup.closure {π A₀, π B₀} = ⊤) {N w : ℕ}
    (hN : 0 < N) (hcheck : checkRun M.next M.code (digits N w) (M.enc 1) = true)
    (h1 : (π A₀)⁻¹ ≠ π A₀) (h2 : (π A₀)⁻¹ ≠ π B₀) (h3 : (π B₀)⁻¹ ≠ π A₀)
    (h4 : (π B₀)⁻¹ ≠ π B₀) :
    ∃ σ, IsRun (π A₀) (π B₀) σ ∧
      (backSteps (π A₀) (π B₀) σ).ncard = (digits N w).countP (2 ≤ ·) := by
  obtain ⟨hnd, hend, hall⟩ :=
    walk_of_check M.next M.code M.hnext M.hcode hgen (digits_ne_nil hN w) hcheck
  obtain ⟨σ, htrans, hσ⟩ := exists_run (digits_ne_nil hN w) hnd hend hall
  refine ⟨σ, ⟨fun x => ?_, htrans⟩, ncard_backSteps_of_walk hnd hall hσ h1 h2 h3 h4⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
  have hi' : i < (digits N w).length := by simpa using hi
  rw [hσ i hi']
  rcases letter_cases (π A₀) (π B₀) (digits N w)[i] with h | h | h | h <;> simp [h]

/-- The order of the group, from a checked word. -/
theorem card_of_check [Finite G] (hgen : Subgroup.closure {π A₀, π B₀} = ⊤) {N w : ℕ}
    (hN : 0 < N) (hcheck : checkRun M.next M.code (digits N w) (M.enc 1) = true) :
    Nat.card G = N := by
  classical
  obtain ⟨hnd, -, hall⟩ :=
    walk_of_check M.next M.code M.hnext M.hcode hgen (digits_ne_nil hN w) hcheck
  let _ : Fintype G := Fintype.ofFinite G
  have huniv : (visits (π A₀) (π B₀) (digits N w) 1).toFinset = Finset.univ := by
    ext x
    simp [hall x]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← huniv, List.toFinset_card_of_nodup hnd,
    length_visits, length_digits]

end Model

end Model

section Fewest

variable {G : Type*} [Group G] [Finite G] {A B : G}

/-- The fewest back-steps when there is no extent, and no run with one back-step. -/
theorem fewestBack_two (hext : ∀ σ, ¬ IsExtent A B σ)
    (hone : ∀ σ, IsRun A B σ → (backSteps A B σ).ncard ≠ 1)
    (hrun : ∃ σ, IsRun A B σ ∧ (backSteps A B σ).ncard = 2) : FewestBack A B 2 := by
  refine ⟨hrun, fun σ hσ => ?_⟩
  have h0 : (backSteps A B σ).ncard ≠ 0 := fun h => hext σ (hσ.isExtent h)
  have h1 := hone σ hσ
  omega

end Fewest

open Matrix (SpecialLinearGroup)

section Quad

/-- A two-by-two matrix over `Z/n` on natural numbers. -/
abbrev Quad := ℕ × ℕ × ℕ × ℕ

/-- The letters `K`, `M`, `K⁻¹`, `M⁻¹` on the rows of a matrix. -/
def nextQuad (n : ℕ) : ℕ → Quad → Quad
  | 0, (a, b, c, d) => (a, b, (a + c) % n, (b + d) % n)
  | 1, (a, b, c, d) => ((a + (n - 1) * c) % n, (b + (n - 1) * d) % n, c, d)
  | 2, (a, b, c, d) => (a, b, (c + (n - 1) * a) % n, (d + (n - 1) * b) % n)
  | _, (a, b, c, d) => ((a + c) % n, (b + d) % n, c, d)

/-- The code of a matrix: its entries as digits in base `n`. -/
def codeQuad (n : ℕ) : Quad → ℕ
  | (a, b, c, d) => ((a * n + b) * n + c) * n + d

/-- The matrix `-x`. -/
def negQuad (n : ℕ) : Quad → Quad
  | (a, b, c, d) => ((n - a) % n, (n - b) % n, (n - c) % n, (n - d) % n)

/-- The identity. -/
def oneQuad (n : ℕ) : Quad := (1 % n, 0, 0, 1 % n)

/-- The code of a matrix up to sign, for `PSL(2, Z/n)`. -/
def codePSL (n : ℕ) (x : Quad) : ℕ := min (codeQuad n x) (codeQuad n (negQuad n x))

variable {n : ℕ}

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)

/-- The state of a matrix. -/
def encSL (g : SpecialLinearGroup (Fin 2) (ZMod n)) : Quad :=
  ((g.1 0 0).val, (g.1 0 1).val, (g.1 1 0).val, (g.1 1 1).val)

theorem val_sub_eq [NeZero n] (a c : ZMod n) : (a - c).val = (a.val + (n - 1) * c.val) % n := by
  have hn : 1 ≤ n := NeZero.one_le
  have : a - c = ((a.val + (n - 1) * c.val : ℕ) : ZMod n) := by
    push_cast [Nat.cast_sub hn]
    simp
    ring
  rw [this, ZMod.val_natCast]

theorem Kp_coe : ((Kp n : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = !![1, 0; 1, 1] := rfl

theorem Mp_coe : ((Mp n : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = !![1, -1; 0, 1] := rfl

theorem Kp_inv_coe : (((Kp n)⁻¹ : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = !![1, 0; -1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Kp_coe, Matrix.adjugate_fin_two_of]
  simp

theorem Mp_inv_coe : (((Mp n)⁻¹ : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = !![1, 1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Mp_coe, Matrix.adjugate_fin_two_of]
  simp

theorem Kp_entries (g : SLn) : (Kp n * g).1 0 0 = g.1 0 0 ∧ (Kp n * g).1 0 1 = g.1 0 1 ∧
    (Kp n * g).1 1 0 = g.1 0 0 + g.1 1 0 ∧ (Kp n * g).1 1 1 = g.1 0 1 + g.1 1 1 := by
  have h : (Kp n * g).1 = !![1, 0; 1, 1] * g.1 := by
    rw [← Kp_coe]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two]

theorem Mp_entries (g : SLn) : (Mp n * g).1 0 0 = g.1 0 0 - g.1 1 0 ∧
    (Mp n * g).1 0 1 = g.1 0 1 - g.1 1 1 ∧
    (Mp n * g).1 1 0 = g.1 1 0 ∧ (Mp n * g).1 1 1 = g.1 1 1 := by
  have h : (Mp n * g).1 = !![1, -1; 0, 1] * g.1 := by
    rw [← Mp_coe]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

theorem Kp_inv_entries (g : SLn) : ((Kp n)⁻¹ * g).1 0 0 = g.1 0 0 ∧
    ((Kp n)⁻¹ * g).1 0 1 = g.1 0 1 ∧
    ((Kp n)⁻¹ * g).1 1 0 = g.1 1 0 - g.1 0 0 ∧ ((Kp n)⁻¹ * g).1 1 1 = g.1 1 1 - g.1 0 1 := by
  have h : ((Kp n)⁻¹ * g).1 = !![1, 0; -1, 1] * g.1 := by
    rw [← Kp_inv_coe]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

theorem Mp_inv_entries (g : SLn) : ((Mp n)⁻¹ * g).1 0 0 = g.1 0 0 + g.1 1 0 ∧
    ((Mp n)⁻¹ * g).1 0 1 = g.1 0 1 + g.1 1 1 ∧
    ((Mp n)⁻¹ * g).1 1 0 = g.1 1 0 ∧ ((Mp n)⁻¹ * g).1 1 1 = g.1 1 1 := by
  have h : ((Mp n)⁻¹ * g).1 = !![1, 1; 0, 1] * g.1 := by
    rw [← Mp_inv_coe]
    rfl
  simp [h, Matrix.mul_apply, Fin.sum_univ_two]

theorem nextQuad_enc [NeZero n] (s : ℕ) (g : SLn) :
    nextQuad n s (encSL g) = encSL (letter (Kp n) (Mp n) s * g) := by
  match s with
  | 0 =>
    obtain ⟨h1, h2, h3, h4⟩ := Kp_entries g
    simp only [nextQuad, encSL, letter, h1, h2, h3, h4, ZMod.val_add]
  | 1 =>
    obtain ⟨h1, h2, h3, h4⟩ := Mp_entries g
    simp only [nextQuad, encSL, letter, h1, h2, h3, h4, val_sub_eq]
  | 2 =>
    obtain ⟨h1, h2, h3, h4⟩ := Kp_inv_entries g
    simp only [nextQuad, encSL, letter, h1, h2, h3, h4, val_sub_eq]
  | s + 3 =>
    obtain ⟨h1, h2, h3, h4⟩ := Mp_inv_entries g
    simp only [nextQuad, encSL, letter, h1, h2, h3, h4, ZMod.val_add]

theorem digit_eq {n x x' d d' : ℕ} (hd : d < n) (hd' : d' < n) (h : x * n + d = x' * n + d') :
    x = x' ∧ d = d' := by
  have hn : 0 < n := by omega
  have e1 : d = d' := by
    have h1 := congrArg (· % n) h
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] using h1
  subst e1
  exact ⟨Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h), rfl⟩

theorem encSL_inj [NeZero n] {g h : SLn} (e : encSL g = encSL h) : g = h := by
  simp only [encSL, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective n e1
  · exact ZMod.val_injective n e2
  · exact ZMod.val_injective n e3
  · exact ZMod.val_injective n e4

theorem code_enc_inj [NeZero n] {g h : SLn}
    (e : codeQuad n (encSL g) = codeQuad n (encSL h)) : g = h := by
  apply encSL_inj
  simp only [codeQuad, encSL] at e
  obtain ⟨e1, e4⟩ := digit_eq (ZMod.val_lt _) (ZMod.val_lt _) e
  obtain ⟨e2, e3⟩ := digit_eq (ZMod.val_lt _) (ZMod.val_lt _) e1
  obtain ⟨e5, e6⟩ := digit_eq (ZMod.val_lt _) (ZMod.val_lt _) e2
  simp only [encSL, e3, e4, e5, e6]

theorem encSL_one : encSL (1 : SLn) = oneQuad n := by
  simp only [encSL, oneQuad, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
    ZMod.val_one_eq_one_mod]
  simp [ZMod.val_zero]

theorem encSL_neg [NeZero n] (g : SLn) : encSL (-g) = negQuad n (encSL g) := by
  simp only [encSL, negQuad, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ZMod.neg_val']

/-- The computation in `SL(2, Z/n)`. -/
def modelSL (n : ℕ) [NeZero n] : Model Quad (Kp n) (Mp n)
    (MonoidHom.id (SpecialLinearGroup (Fin 2) (ZMod n))) where
  next := nextQuad n
  code := codeQuad n
  enc := encSL
  hnext := nextQuad_enc
  hcode g h := by
    simp only [MonoidHom.id_apply]
    exact ⟨code_enc_inj, fun e => by rw [e]⟩

theorem mk_eq_iff (g h : SLn) :
    (QuotientGroup.mk' (pmOne n)) g = (QuotientGroup.mk' (pmOne n)) h ↔ g = h ∨ g = -h := by
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pmOne_iff]
  constructor
  · rintro (e | e)
    · left
      exact (inv_mul_eq_one.mp e)
    · right
      have := inv_mul_eq_iff_eq_mul.mp e
      rw [mul_neg_one] at this
      rw [this, neg_neg]
  · rintro (rfl | rfl)
    · left
      simp
    · right
      rw [← neg_one_mul, mul_inv_rev]
      simp

/-- The computation in `PSL(2, Z/n)`, on matrices up to sign. -/
def modelPSL (n : ℕ) [NeZero n] : Model Quad (Kp n) (Mp n) (QuotientGroup.mk' (pmOne n)) where
  next := nextQuad n
  code := codePSL n
  enc := encSL
  hnext := nextQuad_enc
  hcode g h := by
    rw [mk_eq_iff]
    simp only [codePSL, ← encSL_neg]
    constructor
    · intro e
      have hg : codeQuad n (encSL g) = min (codeQuad n (encSL g)) (codeQuad n (encSL (-g))) ∨
          codeQuad n (encSL (-g)) = min (codeQuad n (encSL g)) (codeQuad n (encSL (-g))) := by
        rcases le_total (codeQuad n (encSL g)) (codeQuad n (encSL (-g))) with hl | hl
        · exact Or.inl (min_eq_left hl).symm
        · exact Or.inr (min_eq_right hl).symm
      have hh : codeQuad n (encSL h) = min (codeQuad n (encSL h)) (codeQuad n (encSL (-h))) ∨
          codeQuad n (encSL (-h)) = min (codeQuad n (encSL h)) (codeQuad n (encSL (-h))) := by
        rcases le_total (codeQuad n (encSL h)) (codeQuad n (encSL (-h))) with hl | hl
        · exact Or.inl (min_eq_left hl).symm
        · exact Or.inr (min_eq_right hl).symm
      rw [← e] at hh
      rcases hg with hg | hg <;> rcases hh with hh | hh
      · exact Or.inl (code_enc_inj (hg.trans hh.symm))
      · exact Or.inr (code_enc_inj (hg.trans hh.symm))
      · right
        rw [← neg_neg g, code_enc_inj (hg.trans hh.symm)]
      · left
        have := code_enc_inj (hg.trans hh.symm)
        rw [← neg_neg g, this, neg_neg]
    · rintro (rfl | rfl)
      · rfl
      · rw [neg_neg, min_comm]

end Quad

section Generation

variable {n : ℕ}

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)

theorem Mp_pow (j : ℕ) : ((Mp n ^ j : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) =
    !![1, -(j : ZMod n); 0, 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, Mp_coe, Matrix.mul_fin_two]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

theorem step_mem_closure [NeZero n] (s : Step (ZMod n)) :
    s.sl ∈ Subgroup.closure {Kp n, Mp n} := by
  cases s with
  | kick f =>
    have h : (Step.kick f).sl = Kp n ^ f.val := by
      apply Subtype.ext
      rw [show ((Kp n ^ f.val : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) = _ from Kn_pow _]
      simp [Step.coe_sl, Step.mat]
    rw [h]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  | move f =>
    have h : (Step.move f).sl = Mp n ^ (-f).val := by
      apply Subtype.ext
      rw [Mp_pow]
      simp [Step.coe_sl, Step.mat]
    rw [h]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

/-- The kick `K` and the move `M` generate `SL(2, Z/n)`, by T1. -/
theorem closure_KM [NeZero n] : Subgroup.closure {Kp n, Mp n} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  let C : ZMod n →+* LaurentPolynomial (ZMod n) := LaurentPolynomial.C
  let ev : LaurentPolynomial (ZMod n) →+* ZMod n := LaurentPolynomial.eval₂ (RingHom.id _) 1
  obtain ⟨w, hw⟩ := everyLawIsAScoreModulus n (NeZero.ne n) (Matrix.SpecialLinearGroup.map C g)
  have hev : ∀ r, ev (C r) = r := fun r => LaurentPolynomial.eval₂_C _ _ r
  have hg : realize (w.map (Step.map ev)) = g := by
    rw [realize_map, hw]
    apply Subtype.ext
    ext i j
    simp [hev]
  rw [← hg]
  generalize w.map (Step.map ev) = v
  induction v with
  | nil => exact Subgroup.one_mem _
  | cons s v ih =>
    rw [realize_cons]
    exact Subgroup.mul_mem _ ih (step_mem_closure s)

theorem closure_KM_PSL [NeZero n] :
    Subgroup.closure
      {QuotientGroup.mk' (pmOne n) (Kp n), QuotientGroup.mk' (pmOne n) (Mp n)} = ⊤ := by
  rw [← Set.image_pair, ← MonoidHom.map_closure, closure_KM]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

end Generation

section Genuine

variable {n : ℕ}

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)
local notation "π" => QuotientGroup.mk' (pmOne n)

theorem two_ne_zero_of' (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := two_ne_zero_of hn

theorem neg_one_ne_zero_of (hn : 3 ≤ n) : (-1 : ZMod n) ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  simp

/-- An element is not `±1` when an off-diagonal entry is not zero. -/
theorem not_pm_of_entry {g : SLn} {i j : Fin 2} (hij : i ≠ j) (h : g.1 i j ≠ 0) :
    g ≠ 1 ∧ g ≠ -1 := by
  constructor
  · rintro rfl
    apply h
    simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]
  · rintro rfl
    apply h
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne hij]

theorem mk_ne_of_entry {g h : SLn} {i j : Fin 2} (hij : i ≠ j) (he : (h⁻¹ * g).1 i j ≠ 0) :
    π g ≠ π h := by
  intro e
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq, mem_pmOne_iff]
    at e
  obtain ⟨h1, h2⟩ := not_pm_of_entry hij he
  rcases e with e | e
  · exact h1 e
  · exact h2 e

/-- The kick and the move differ in `PSL(2, Z/n)`, `n ≥ 2`. -/
theorem barK_ne_barM (hn : 2 ≤ n) : π (Kp n) ≠ π (Mp n) := by
  have : Fact (1 < n) := ⟨by omega⟩
  apply mk_ne_of_entry (i := 0) (j := 1) (by decide)
  obtain ⟨-, h, -, -⟩ := Mp_inv_entries (Kp n)
  rw [h, Kp_coe]
  simp

/-- The kick and the move differ in `SL(2, Z/n)`, `n ≥ 2`. -/
theorem Kp_ne_Mp (hn : 2 ≤ n) : Kp n ≠ Mp n := fun e => barK_ne_barM hn (by rw [e])

variable (hn : 3 ≤ n)

include hn

theorem genuine_PSL : (π (Kp n))⁻¹ ≠ π (Kp n) ∧ (π (Kp n))⁻¹ ≠ π (Mp n) ∧
    (π (Mp n))⁻¹ ≠ π (Kp n) ∧ (π (Mp n))⁻¹ ≠ π (Mp n) ∧ π (Kp n) ≠ π (Mp n) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h2 := two_ne_zero_of hn
  have h2' : (-1 + -1 : ZMod n) ≠ 0 := by
    intro h
    apply h2
    linear_combination -h
  have h3 : (1 + 1 : ZMod n) ≠ 0 := by
    intro h
    apply h2
    linear_combination h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_inv]
    apply mk_ne_of_entry (i := 1) (j := 0) (by decide)
    obtain ⟨-, -, h, -⟩ := Kp_inv_entries (Kp n)⁻¹
    rw [h, Kp_inv_coe]
    simpa [sub_eq_add_neg] using h2'
  · rw [← map_inv]
    apply mk_ne_of_entry (i := 0) (j := 1) (by decide)
    obtain ⟨-, h, -, -⟩ := Mp_inv_entries (Kp n)⁻¹
    rw [h, Kp_inv_coe]
    simp
  · rw [← map_inv]
    apply mk_ne_of_entry (i := 0) (j := 1) (by decide)
    obtain ⟨-, h, -, -⟩ := Kp_inv_entries (Mp n)⁻¹
    rw [h, Mp_inv_coe]
    simp
  · rw [← map_inv]
    apply mk_ne_of_entry (i := 0) (j := 1) (by decide)
    obtain ⟨-, h, -, -⟩ := Mp_inv_entries (Mp n)⁻¹
    rw [h, Mp_inv_coe]
    simpa using h3
  · exact barK_ne_barM (by omega)

/-- The same in `SL(2, Z/n)`. -/
theorem genuine_SL : (Kp n)⁻¹ ≠ Kp n ∧ (Kp n)⁻¹ ≠ Mp n ∧ (Mp n)⁻¹ ≠ Kp n ∧ (Mp n)⁻¹ ≠ Mp n ∧
    Kp n ≠ Mp n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := genuine_PSL hn
  refine ⟨fun e => h1 ?_, fun e => h2 ?_, fun e => h3 ?_, fun e => h4 ?_, fun e => h5 ?_⟩
  · rw [← map_inv, e]
  · rw [← map_inv, e]
  · rw [← map_inv, e]
  · rw [← map_inv, e]
  · rw [e]

end Genuine

section Fewest2

variable {n : ℕ} [NeZero n]

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)
local notation "PSLn" => SpecialLinearGroup (Fin 2) (ZMod n) ⧸ pmOne n

/-- A checked word is a forward extent of `SL(2, Z/n)`. -/
theorem extent_SL {N w : ℕ} (hN : 0 < N)
    (h : checkRun (nextQuad n) (codeQuad n) (digits N w) (oneQuad n) = true)
    (hf : (digits N w).all (· < 2) = true) : ∃ σ : Perm SLn, IsExtent (Kp n) (Mp n) σ := by
  rw [← encSL_one] at h
  exact (modelSL n).extent_of_check (π := MonoidHom.id _) closure_KM hN h hf

/-- A checked word is a forward extent of `PSL(2, Z/n)`. -/
theorem extent_PSL {N w : ℕ} (hN : 0 < N)
    (h : checkRun (nextQuad n) (codePSL n) (digits N w) (oneQuad n) = true)
    (hf : (digits N w).all (· < 2) = true) :
    ∃ σ : Perm PSLn, IsExtent ((Kp n : SLn) : PSLn) ((Mp n : SLn) : PSLn) σ := by
  rw [← encSL_one] at h
  exact (modelPSL n).extent_of_check closure_KM_PSL hN h hf

end Fewest2

end Artform.Scores.Bells
