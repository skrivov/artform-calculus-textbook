import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import ArtformTextbook.Ch11.Statements.Occupation
import ArtformTextbook.Ch11.Blocks

/-!
# Many particles on the cells (Propositions 11.11 and 11.12)

* **The sign rule.** From Definition 11.10 the creations anticommute,
  `a†_m a†_{m'} = -a†_{m'} a†_m`, and `a_m a†_{m'} + a†_{m'} a_m = δ_{mm'}`
  (`creation_mul_creation`, `annihilation_mul_creation_add`); the annihilation is the adjoint
  of the creation, and the ascending product of the creations of the occupied modes applied to
  the empty table is the basis table (`crProd_sort_mulVec_vacuum`).
* **Second quantization.** Reordering a product of anticommuting factors changes it by one sign,
  the same for the creations and for the transformed creations (`perm_sign`), and a product with
  a repeated factor vanishes. Hence `Γ(W)` transforms every creation in any product of
  creations applied to the empty table (`secondQuant_mulVec_crProd`), which gives
  `Γ(W) a†_m = (Σ_{m'} W_{m'm} a†_{m'}) Γ(W)`, `Γ(W₂) Γ(W₁) = Γ(W₂ W₁)` and `Γ(1) = 1`.
* **Unitarity.** The pairing of two products of creations of one-quark states applied to the
  empty table depends only on the pairings of the states (`coeffPairing_crvProd_map`), by
  moving each annihilation to the right with the anticommutation relation; a unitary `W` keeps
  those pairings.
* **Change of order.** With `σ(n) = (-1)^{number of pairs of occupied modes in opposite order}`,
  the sign rule of the new order is that of the old one times `σ(n + 1_m) σ(n)`
  (`neg_one_pow_precCount_change`), which says that `Σ = diag σ` conjugates every creation and
  annihilation.
-/


namespace Artform

namespace Fock

open scoped Matrix ComplexConjugate

open Blocks

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem mulVec_ket (A : Matrix (Finset M) (Finset M) ℂ) (n : Finset M) :
    A *ᵥ ket n = fun n' => A n' n := by
  rw [ket, Matrix.mulVec_single_one]
  rfl

theorem ext_ket {A B : Matrix (Finset M) (Finset M) ℂ} (h : ∀ n, A *ᵥ ket n = B *ᵥ ket n) :
    A = B := by
  ext n' n
  have := congrFun (h n) n'
  rwa [mulVec_ket, mulVec_ket] at this

section Signs

variable (ord : LinearOrder M)

omit [Fintype M] in
theorem precCount_insert_of_lt {a : M} {n : Finset M} (ha : a ∉ n) {m : M} (h : ord.lt a m) :
    precCount ord (insert a n) m = precCount ord n m + 1 := by
  let := ord
  unfold precCount
  rw [Finset.filter_insert, ite_eq_left h,
    Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.mp h').1)]

omit [Fintype M] in
theorem precCount_insert_of_not_lt {a : M} {n : Finset M} {m : M} (h : ¬ ord.lt a m) :
    precCount ord (insert a n) m = precCount ord n m := by
  let := ord
  unfold precCount
  rw [Finset.filter_insert, ite_eq_right h]

omit [Fintype M] in
theorem precCount_insert_self (m : M) (n : Finset M) :
    precCount ord (insert m n) m = precCount ord n m := by
  let := ord
  unfold precCount
  rw [Finset.filter_insert]
  simp

omit [Fintype M] in
theorem precCount_erase_self (m : M) (n : Finset M) :
    precCount ord (n.erase m) m = precCount ord n m := by
  let := ord
  unfold precCount
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp

end Signs

theorem creation_mulVec_ket (ord : LinearOrder M) (m : M) (n : Finset M) :
    creation ord m *ᵥ ket n =
      if m ∈ n then 0 else (-1 : ℂ) ^ precCount ord n m • ket (insert m n) := by
  rw [mulVec_ket]
  funext n'
  by_cases hm : m ∈ n
  · simp [creation, hm]
  · simp [creation, hm, ket, Pi.single_apply]

theorem annihilation_mulVec_ket (ord : LinearOrder M) (m : M) (n : Finset M) :
    annihilation ord m *ᵥ ket n =
      if m ∈ n then (-1 : ℂ) ^ precCount ord n m • ket (n.erase m) else 0 := by
  rw [mulVec_ket]
  funext n'
  by_cases hm : m ∈ n
  · simp [annihilation, hm, ket, Pi.single_apply]
  · simp [annihilation, hm]

theorem creation_mulVec_ket_of_mem {ord : LinearOrder M} {m : M} {n : Finset M} (h : m ∈ n) :
    creation ord m *ᵥ ket n = 0 := by
  simp [creation_mulVec_ket, h]

theorem creation_mulVec_ket_of_notMem {ord : LinearOrder M} {m : M} {n : Finset M}
    (h : m ∉ n) :
    creation ord m *ᵥ ket n = (-1 : ℂ) ^ precCount ord n m • ket (insert m n) := by
  simp [creation_mulVec_ket, h]

theorem annihilation_mulVec_ket_of_mem {ord : LinearOrder M} {m : M} {n : Finset M}
    (h : m ∈ n) :
    annihilation ord m *ᵥ ket n = (-1 : ℂ) ^ precCount ord n m • ket (n.erase m) := by
  simp [annihilation_mulVec_ket, h]

theorem annihilation_mulVec_ket_of_notMem {ord : LinearOrder M} {m : M} {n : Finset M}
    (h : m ∉ n) : annihilation ord m *ᵥ ket n = 0 := by
  simp [annihilation_mulVec_ket, h]

/-- Creations anticommute: `a†_m a†_{m'} = -a†_{m'} a†_m`. -/
theorem creation_mul_creation (ord : LinearOrder M) (m m' : M) :
    creation ord m * creation ord m' = -(creation ord m' * creation ord m) := by
  apply ext_ket
  intro n
  rw [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hm' : m' ∈ n
  · rw [creation_mulVec_ket_of_mem hm', Matrix.mulVec_zero]
    by_cases hm : m ∈ n
    · rw [creation_mulVec_ket_of_mem hm, Matrix.mulVec_zero, neg_zero]
    · rw [creation_mulVec_ket_of_notMem hm, Matrix.mulVec_smul,
        creation_mulVec_ket_of_mem (Finset.mem_insert_of_mem hm'), smul_zero, neg_zero]
  · by_cases hm : m ∈ n
    · rw [creation_mulVec_ket_of_mem hm, Matrix.mulVec_zero, neg_zero,
        creation_mulVec_ket_of_notMem hm', Matrix.mulVec_smul,
        creation_mulVec_ket_of_mem (Finset.mem_insert_of_mem hm), smul_zero]
    · by_cases hmm : m = m'
      · subst hmm
        rw [creation_mulVec_ket_of_notMem hm, Matrix.mulVec_smul,
          creation_mulVec_ket_of_mem (Finset.mem_insert_self m n), smul_zero, neg_zero]
      · have h1 : m ∉ insert m' n := by simp [hmm, hm]
        have h2 : m' ∉ insert m n := by simp [Ne.symm hmm, hm']
        rw [creation_mulVec_ket_of_notMem hm', Matrix.mulVec_smul,
          creation_mulVec_ket_of_notMem h1, creation_mulVec_ket_of_notMem hm,
          Matrix.mulVec_smul, creation_mulVec_ket_of_notMem h2, Finset.insert_comm,
          smul_smul, smul_smul, ← neg_smul]
        congr 1
        let := ord
        rcases lt_or_gt_of_ne hmm with hlt | hlt
        · rw [precCount_insert_of_not_lt ord (not_lt_of_gt hlt),
            precCount_insert_of_lt ord hm hlt, pow_succ]
          ring
        · rw [precCount_insert_of_lt ord hm' hlt,
            precCount_insert_of_not_lt ord (not_lt_of_gt hlt), pow_succ]
          ring

omit [Fintype M] in
theorem precCount_erase_of_lt (ord : LinearOrder M) {a : M} {n : Finset M} (ha : a ∈ n) {m : M}
    (h : ord.lt a m) : precCount ord n m = precCount ord (n.erase a) m + 1 := by
  conv_lhs => rw [← Finset.insert_erase ha]
  exact precCount_insert_of_lt ord (Finset.notMem_erase a n) h

omit [Fintype M] in
theorem precCount_erase_of_not_lt (ord : LinearOrder M) {a : M} {n : Finset M} (ha : a ∈ n)
    {m : M} (h : ¬ ord.lt a m) : precCount ord n m = precCount ord (n.erase a) m := by
  conv_lhs => rw [← Finset.insert_erase ha]
  exact precCount_insert_of_not_lt ord h

/-- `a_m a†_{m'} + a†_{m'} a_m = δ_{mm'}`. -/
theorem annihilation_mul_creation_add (ord : LinearOrder M) (m m' : M) :
    annihilation ord m * creation ord m' + creation ord m' * annihilation ord m =
      if m = m' then 1 else 0 := by
  apply ext_ket
  intro n
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hmm : m = m'
  · subst hmm
    rw [ite_eq_left rfl, Matrix.one_mulVec]
    by_cases hm : m ∈ n
    · rw [creation_mulVec_ket_of_mem hm, Matrix.mulVec_zero, zero_add,
        annihilation_mulVec_ket_of_mem hm, Matrix.mulVec_smul,
        creation_mulVec_ket_of_notMem (Finset.notMem_erase m n), Finset.insert_erase hm,
        precCount_erase_self, smul_smul, ← pow_add, ← two_mul, pow_mul]
      simp
    · rw [annihilation_mulVec_ket_of_notMem hm, Matrix.mulVec_zero, add_zero,
        creation_mulVec_ket_of_notMem hm, Matrix.mulVec_smul,
        annihilation_mulVec_ket_of_mem (Finset.mem_insert_self m n),
        Finset.erase_insert hm, precCount_insert_self, smul_smul, ← pow_add, ← two_mul,
        pow_mul]
      simp
  · rw [ite_eq_right hmm, Matrix.zero_mulVec]
    by_cases hm' : m' ∈ n
    · rw [creation_mulVec_ket_of_mem hm', Matrix.mulVec_zero, zero_add]
      by_cases hm : m ∈ n
      · rw [annihilation_mulVec_ket_of_mem hm, Matrix.mulVec_smul,
          creation_mulVec_ket_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hmm, hm'⟩), smul_zero]
      · rw [annihilation_mulVec_ket_of_notMem hm, Matrix.mulVec_zero]
    · by_cases hm : m ∈ n
      · have h1 : m ∈ insert m' n := Finset.mem_insert_of_mem hm
        have h2 : m' ∉ n.erase m := fun h => hm' (Finset.mem_of_mem_erase h)
        rw [creation_mulVec_ket_of_notMem hm', Matrix.mulVec_smul,
          annihilation_mulVec_ket_of_mem h1, annihilation_mulVec_ket_of_mem hm,
          Matrix.mulVec_smul, creation_mulVec_ket_of_notMem h2, smul_smul, smul_smul,
          Finset.erase_insert_of_ne (Ne.symm hmm), ← add_smul]
        apply smul_eq_zero_of_left
        let := ord
        rcases lt_or_gt_of_ne hmm with hlt | hlt
        · rw [precCount_insert_of_not_lt ord (not_lt_of_gt hlt),
            precCount_erase_of_lt ord hm hlt, pow_succ]
          ring
        · rw [precCount_insert_of_lt ord hm' hlt,
            precCount_erase_of_not_lt ord hm (not_lt_of_gt hlt), pow_succ]
          ring
      · rw [annihilation_mulVec_ket_of_notMem hm, Matrix.mulVec_zero, add_zero,
          creation_mulVec_ket_of_notMem hm', Matrix.mulVec_smul,
          annihilation_mulVec_ket_of_notMem (fun h => hm ((Finset.mem_insert.mp h).resolve_left
            hmm)), smul_zero]

theorem annihilation_mulVec_vacuum (ord : LinearOrder M) (m : M) :
    annihilation ord m *ᵥ ket ∅ = 0 :=
  annihilation_mulVec_ket_of_notMem (Finset.notMem_empty m)

omit [Fintype M] in
/-- The annihilation is the adjoint of the creation. -/
theorem conjTranspose_creation (ord : LinearOrder M) (m : M) :
    (creation ord m)ᴴ = annihilation ord m := by
  ext n' n
  simp only [Matrix.conjTranspose_apply, creation, annihilation, Matrix.of_apply]
  by_cases h : m ∈ n ∧ n' = n.erase m
  · obtain ⟨hm, rfl⟩ := h
    rw [ite_eq_left ⟨Finset.notMem_erase m n, (Finset.insert_erase hm).symm⟩, ite_eq_left ⟨hm, rfl⟩,
      precCount_erase_self]
    simp
  · rw [ite_eq_right h, ite_eq_right]
    · simp
    · rintro ⟨h1, rfl⟩
      exact h ⟨Finset.mem_insert_self m n', (Finset.erase_insert h1).symm⟩

/-- The product of creations `a†_{m₁} a†_{m₂} ⋯ a†_{m_k}` of a list of modes. -/
def crProd (ord : LinearOrder M) (L : List M) : Matrix (Finset M) (Finset M) ℂ :=
  (L.map (creation ord)).prod

/-- The product of transformed creations along a list of modes. -/
def trProd (ord : LinearOrder M) (W : Matrix M M ℂ) (L : List M) :
    Matrix (Finset M) (Finset M) ℂ :=
  (L.map (transformedCreation ord W)).prod

omit [Fintype M] [DecidableEq M] in
theorem precCount_eq_zero_of_forall_lt (ord : LinearOrder M) {a : M} {s : Finset M}
    (h : ∀ x ∈ s, ord.lt a x) : precCount ord s a = 0 := by
  let := ord
  unfold precCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxa
  exact lt_asymm hxa (h x hx)

/-- In ascending order the product of creations of the occupied modes is the basis table:
`a†_{m₁} ⋯ a†_{m_k} |0⟩ = |n⟩`. -/
theorem crProd_sort_mulVec_vacuum (ord : LinearOrder M) (n : Finset M) :
    crProd ord (letI := ord; n.sort) *ᵥ ket ∅ = ket n := by
  let := ord
  induction n using Finset.induction_on_min with
  | empty => simp [crProd]
  | insert a s ha ih =>
    have ha' : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sort_insert _ (fun b hb => (ha b hb).le) ha', crProd, List.map_cons, List.prod_cons,
      ← Matrix.mulVec_mulVec]
    erw [ih]
    rw [creation_mulVec_ket_of_notMem ha', precCount_eq_zero_of_forall_lt ord ha, pow_zero,
      one_smul]

theorem secondQuant_mulVec_ket (ord : LinearOrder M) (W : Matrix M M ℂ) (n : Finset M) :
    secondQuant ord W *ᵥ ket n = trProd ord W (letI := ord; n.sort) *ᵥ ket ∅ := by
  rw [mulVec_ket]
  rfl

omit [Fintype M] [DecidableEq M] in
theorem eq_zero_of_eq_neg {X : Matrix (Finset M) (Finset M) ℂ} (h : X = -X) : X = 0 := by
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel X
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem transformedCreation_mul (ord : LinearOrder M) (W : Matrix M M ℂ) (m m' : M) :
    transformedCreation ord W m * transformedCreation ord W m' =
      -(transformedCreation ord W m' * transformedCreation ord W m) := by
  have key : ∀ a b, (W a m * W b m') • (creation ord a * creation ord b) =
      -((W b m' * W a m) • (creation ord b * creation ord a)) := by
    intro a b
    rw [creation_mul_creation ord a b, smul_neg, mul_comm (W a m)]
  simp only [transformedCreation, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, key,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/-- Reordering a product of anticommuting factors changes it by a sign, the same for two
families of factors. -/
theorem perm_sign {L₁ L₂ : List M} (h : L₁.Perm L₂)
    (f g : M → Matrix (Finset M) (Finset M) ℂ)
    (hf : ∀ x y, f x * f y = -(f y * f x)) (hg : ∀ x y, g x * g y = -(g y * g x)) :
    ∃ s : ℂ, (L₁.map f).prod = s • (L₂.map f).prod ∧ (L₁.map g).prod = s • (L₂.map g).prod := by
  induction h with
  | nil => exact ⟨1, by simp, by simp⟩
  | cons x _ ih =>
    obtain ⟨s, h1, h2⟩ := ih
    exact ⟨s, by simp [h1], by simp [h2]⟩
  | swap x y l =>
    refine ⟨-1, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul,
        one_smul]
    · simp only [List.map_cons, List.prod_cons, ← mul_assoc, hg y x, neg_mul, neg_smul,
        one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨s, h1, h2⟩ := ih₁
    obtain ⟨t, h3, h4⟩ := ih₂
    exact ⟨s * t, by rw [h1, h3, smul_smul], by rw [h2, h4, smul_smul]⟩

omit [Fintype M] [DecidableEq M] in
/-- A list with a repeated mode is a rearrangement of one that starts with that mode twice. -/
theorem exists_perm_cons_cons {L : List M} (h : ¬ L.Nodup) :
    ∃ (x : M) (L' : List M), L.Perm (x :: x :: L') := by
  classical
  rw [List.nodup_iff_count_le_one] at h
  push Not at h
  obtain ⟨x, hx⟩ := h
  have hx1 : x ∈ L := List.count_pos_iff.mp (by omega)
  have hx2 : x ∈ L.erase x := by
    rw [← List.count_pos_iff, List.count_erase_self]
    omega
  exact ⟨x, (L.erase x).erase x,
    (List.perm_cons_erase hx1).trans ((List.perm_cons_erase hx2).cons x)⟩

/-- `Γ(W)` transforms every creation in any product of creations applied to the empty table,
`Γ(W) a†_{m₁} ⋯ a†_{m_k} |0⟩ = (Σ_{m'} W_{m'm₁} a†_{m'}) ⋯ (Σ_{m'} W_{m'm_k} a†_{m'}) |0⟩`. -/
theorem secondQuant_mulVec_crProd (ord : LinearOrder M) (W : Matrix M M ℂ) (L : List M) :
    secondQuant ord W *ᵥ (crProd ord L *ᵥ ket ∅) = trProd ord W L *ᵥ ket ∅ := by
  by_cases hL : L.Nodup
  · let := ord
    have hperm : L.Perm (L.toFinset.sort) := List.perm_of_nodup_nodup_toFinset_eq hL
      (Finset.sort_nodup _ _) (by rw [Finset.sort_toFinset])
    obtain ⟨s, h1, h2⟩ := perm_sign hperm (creation ord) (transformedCreation ord W)
      (creation_mul_creation ord) (transformedCreation_mul ord W)
    rw [crProd, h1, Matrix.smul_mulVec, ← crProd]
    erw [crProd_sort_mulVec_vacuum ord L.toFinset]
    have h2' : trProd ord W L = s • trProd ord W L.toFinset.sort := h2
    rw [Matrix.mulVec_smul, secondQuant_mulVec_ket, h2', Matrix.smul_mulVec]
  · obtain ⟨x, L', hperm⟩ := exists_perm_cons_cons hL
    obtain ⟨s, h1, h2⟩ := perm_sign hperm (creation ord) (transformedCreation ord W)
      (creation_mul_creation ord) (transformedCreation_mul ord W)
    have hc : creation ord x * creation ord x = 0 :=
      eq_zero_of_eq_neg (creation_mul_creation ord x x)
    have ht : transformedCreation ord W x * transformedCreation ord W x = 0 :=
      eq_zero_of_eq_neg (transformedCreation_mul ord W x x)
    rw [crProd, h1, trProd, h2]
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hc, ht, zero_mul, smul_zero,
      Matrix.zero_mulVec, Matrix.mulVec_zero]

/-- `Γ(W) a†_m = (Σ_{m'} W_{m'm} a†_{m'}) Γ(W)`. -/
theorem secondQuant_mul_creation (ord : LinearOrder M) (W : Matrix M M ℂ) (m : M) :
    secondQuant ord W * creation ord m = transformedCreation ord W m * secondQuant ord W := by
  apply ext_ket
  intro n
  have h1 : creation ord m *ᵥ ket n = crProd ord (m :: (letI := ord; n.sort)) *ᵥ ket ∅ := by
    rw [crProd, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ← crProd,
      crProd_sort_mulVec_vacuum]
  rw [← Matrix.mulVec_mulVec, h1, secondQuant_mulVec_crProd, ← Matrix.mulVec_mulVec,
    secondQuant_mulVec_ket, trProd, trProd, List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

theorem secondQuant_mul_transformedCreation (ord : LinearOrder M) (W₁ W₂ : Matrix M M ℂ)
    (m : M) :
    secondQuant ord W₂ * transformedCreation ord W₁ m =
      transformedCreation ord (W₂ * W₁) m * secondQuant ord W₂ := by
  rw [transformedCreation, Finset.mul_sum]
  simp_rw [mul_smul_comm, secondQuant_mul_creation, transformedCreation, Finset.sum_mul,
    smul_mul_assoc, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm (W₁ b m)]

theorem secondQuant_mul_trProd (ord : LinearOrder M) (W₁ W₂ : Matrix M M ℂ) (L : List M) :
    secondQuant ord W₂ * trProd ord W₁ L = trProd ord (W₂ * W₁) L * secondQuant ord W₂ := by
  induction L with
  | nil => simp [trProd]
  | cons a L ih =>
    simp only [trProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [← mul_assoc, secondQuant_mul_transformedCreation, mul_assoc, ih, mul_assoc]

theorem secondQuant_mulVec_vacuum (ord : LinearOrder M) (W : Matrix M M ℂ) :
    secondQuant ord W *ᵥ ket ∅ = ket ∅ := by
  rw [secondQuant_mulVec_ket]
  simp [trProd]

/-- `Γ(W₂) Γ(W₁) = Γ(W₂ W₁)`. -/
theorem secondQuant_mul (ord : LinearOrder M) (W₁ W₂ : Matrix M M ℂ) :
    secondQuant ord W₂ * secondQuant ord W₁ = secondQuant ord (W₂ * W₁) := by
  apply ext_ket
  intro n
  rw [← Matrix.mulVec_mulVec, secondQuant_mulVec_ket, Matrix.mulVec_mulVec,
    secondQuant_mul_trProd, ← Matrix.mulVec_mulVec, secondQuant_mulVec_vacuum,
    secondQuant_mulVec_ket]

theorem transformedCreation_one (ord : LinearOrder M) (m : M) :
    transformedCreation ord 1 m = creation ord m := by
  simp [transformedCreation, Matrix.one_apply]

/-- `Γ(1) = 1`. -/
theorem secondQuant_one (ord : LinearOrder M) : secondQuant ord (1 : Matrix M M ℂ) = 1 := by
  apply ext_ket
  intro n
  rw [secondQuant_mulVec_ket, Matrix.one_mulVec]
  have h : ∀ L, trProd ord 1 L = crProd ord L := fun L => by
    rw [trProd, crProd, show transformedCreation ord (1 : Matrix M M ℂ) = creation ord from
      funext (transformedCreation_one ord)]
  rw [h, crProd_sort_mulVec_vacuum]

theorem secondQuant_mul_inv (ord : LinearOrder M) {W : Matrix M M ℂ} (hW : IsUnit W) :
    secondQuant ord W * secondQuant ord W⁻¹ = 1 := by
  rw [secondQuant_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det W).mp hW),
    secondQuant_one]

theorem secondQuant_inv (ord : LinearOrder M) {W : Matrix M M ℂ} (hW : IsUnit W) :
    (secondQuant ord W)⁻¹ = secondQuant ord W⁻¹ :=
  Matrix.inv_eq_right_inv (secondQuant_mul_inv ord hW)

/-- `Γ(W) a†_m Γ(W)⁻¹ = Σ_{m'} W_{m'm} a†_{m'}` for an invertible `W`. -/
theorem secondQuant_conj_creation (ord : LinearOrder M) {W : Matrix M M ℂ} (hW : IsUnit W)
    (m : M) :
    secondQuant ord W * creation ord m * (secondQuant ord W)⁻¹ =
      transformedCreation ord W m := by
  rw [secondQuant_mul_creation, mul_assoc, secondQuant_inv ord hW, secondQuant_mul_inv ord hW,
    mul_one]

section Unitary

/-- The creation of a one-quark state `v`: `a†(v) = Σ_m v_m a†_m`. -/
def crv (ord : LinearOrder M) (v : M → ℂ) : Matrix (Finset M) (Finset M) ℂ :=
  ∑ m, v m • creation ord m

/-- The annihilation of a one-quark state `u`: `a(u) = Σ_m conj(u_m) a_m`. -/
def anv (ord : LinearOrder M) (u : M → ℂ) : Matrix (Finset M) (Finset M) ℂ :=
  ∑ m, conj (u m) • annihilation ord m

/-- A product of creations of one-quark states. -/
def crvProd (ord : LinearOrder M) (vs : List (M → ℂ)) : Matrix (Finset M) (Finset M) ℂ :=
  (vs.map (crv ord)).prod

theorem conjTranspose_crv (ord : LinearOrder M) (v : M → ℂ) : (crv ord v)ᴴ = anv ord v := by
  simp [crv, anv, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, conjTranspose_creation]

theorem anv_mul_crv_add (ord : LinearOrder M) (u v : M → ℂ) :
    anv ord u * crv ord v + crv ord v * anv ord u = coeffPairing u v • 1 := by
  have h1 : anv ord u * crv ord v =
      ∑ a, ∑ b, (conj (u a) * v b) • (annihilation ord a * creation ord b) := by
    simp only [anv, crv, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    exact Finset.sum_comm
  have h2 : crv ord v * anv ord u =
      ∑ a, ∑ b, (conj (u a) * v b) • (creation ord b * annihilation ord a) := by
    simp only [anv, crv, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm (v b)]
  rw [h1, h2, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, annihilation_mul_creation_add, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [coeffPairing, Finset.sum_smul]

theorem anv_mulVec_vacuum (ord : LinearOrder M) (u : M → ℂ) : anv ord u *ᵥ ket ∅ = 0 := by
  simp [anv, Matrix.sum_mulVec, Matrix.smul_mulVec, annihilation_mulVec_vacuum]

theorem creation_mulVec_apply_empty (ord : LinearOrder M) (m : M) (x : Finset M → ℂ) :
    (creation ord m *ᵥ x) ∅ = 0 := by
  simp only [Matrix.mulVec, dotProduct, creation, Matrix.of_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [ite_eq_right fun h => Finset.insert_ne_empty m k h.2.symm, zero_mul]

theorem crv_mulVec_apply_empty (ord : LinearOrder M) (v : M → ℂ) (x : Finset M → ℂ) :
    (crv ord v *ᵥ x) ∅ = 0 := by
  simp [crv, Matrix.sum_mulVec, Matrix.smul_mulVec, creation_mulVec_apply_empty]

theorem crvProd_mulVec_vacuum_empty (ord : LinearOrder M) (vs : List (M → ℂ)) :
    (crvProd ord vs *ᵥ ket ∅) ∅ = if vs = [] then 1 else 0 := by
  cases vs with
  | nil => simp [crvProd, ket]
  | cons v vs =>
    rw [crvProd, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      crv_mulVec_apply_empty]
    simp

omit [DecidableEq M] in
theorem coeffPairing_mulVec_left (A : Matrix (Finset M) (Finset M) ℂ) (x y : Finset M → ℂ) :
    coeffPairing (A *ᵥ x) y = coeffPairing x (Aᴴ *ᵥ y) := by
  rw [coeffPairing_eq_dotProduct, coeffPairing_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec]

omit [DecidableEq M] in
theorem coeffPairing_sum_right {ι : Type*} (s : Finset ι) (x : Finset M → ℂ)
    (f : ι → Finset M → ℂ) : coeffPairing x (∑ i ∈ s, f i) = ∑ i ∈ s, coeffPairing x (f i) := by
  simp only [coeffPairing, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- `a(u) a†(v₀) ⋯ a†(v_{k-1}) |0⟩ = Σ_j (-1)^j ⟨u, v_j⟩ a†(v₀) ⋯ (omit j) ⋯ |0⟩`. -/
theorem anv_mulVec_crvProd (ord : LinearOrder M) (u : M → ℂ) (vs : List (M → ℂ)) :
    anv ord u *ᵥ (crvProd ord vs *ᵥ ket ∅) =
      ∑ j ∈ Finset.range vs.length,
        ((-1) ^ j * coeffPairing u (vs.getD j 0)) • (crvProd ord (vs.eraseIdx j) *ᵥ ket ∅) := by
  induction vs with
  | nil => simp [crvProd, anv_mulVec_vacuum]
  | cons v vs ih =>
    have h : anv ord u * crv ord v = coeffPairing u v • 1 - crv ord v * anv ord u := by
      rw [← anv_mul_crv_add ord u v, add_sub_cancel_right]
    rw [crvProd, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      h, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← crvProd, ih, Matrix.smul_mulVec,
      Matrix.one_mulVec, List.length_cons, Finset.sum_range_succ', Matrix.mulVec_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ, pow_zero, one_mul, pow_succ, Matrix.mulVec_smul]
    rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show crvProd ord (v :: vs.eraseIdx j) =
        crv ord v * (List.map (crv ord) (vs.eraseIdx j)).prod from rfl,
      ← Matrix.mulVec_mulVec, ← neg_smul]
    congr 1
    ring

/-- The pairing of two products of creations applied to the empty table is unchanged when every
one-quark state is moved by a matrix `U` that keeps the pairing. -/
theorem coeffPairing_crvProd_map (ord : LinearOrder M) (U : Matrix M M ℂ) (hU : star U * U = 1)
    (us vs : List (M → ℂ)) :
    coeffPairing (crvProd ord (us.map (U *ᵥ ·)) *ᵥ ket ∅)
        (crvProd ord (vs.map (U *ᵥ ·)) *ᵥ ket ∅) =
      coeffPairing (crvProd ord us *ᵥ ket ∅) (crvProd ord vs *ᵥ ket ∅) := by
  have hpair : ∀ u v : M → ℂ, coeffPairing (U *ᵥ u) (U *ᵥ v) = coeffPairing u v := fun u v => by
    rw [coeffPairing_mulVec, hU, Matrix.one_mulVec]
  have expand : ∀ (w : M → ℂ) (ws ys : List (M → ℂ)),
      coeffPairing (crvProd ord (w :: ws) *ᵥ ket ∅) (crvProd ord ys *ᵥ ket ∅) =
        ∑ j ∈ Finset.range ys.length, ((-1) ^ j * coeffPairing w (ys.getD j 0)) *
          coeffPairing (crvProd ord ws *ᵥ ket ∅) (crvProd ord (ys.eraseIdx j) *ᵥ ket ∅) := by
    intro w ws ys
    rw [show crvProd ord (w :: ws) = crv ord w * crvProd ord ws from rfl,
      ← Matrix.mulVec_mulVec, coeffPairing_mulVec_left, conjTranspose_crv, anv_mulVec_crvProd,
      coeffPairing_sum_right]
    simp only [coeffPairing_smul_right]
  induction us generalizing vs with
  | nil =>
    simp only [List.map_nil]
    rw [show crvProd ord [] = 1 from rfl, Matrix.one_mulVec, ket, coeffPairing_single_left,
      coeffPairing_single_left, ← ket, crvProd_mulVec_vacuum_empty, crvProd_mulVec_vacuum_empty]
    simp
  | cons u us ih =>
    rw [List.map_cons, expand, expand, List.length_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [List.eraseIdx_map, ih, ← Matrix.mulVec_zero U, List.getD_map, hpair,
      Matrix.mulVec_zero]

theorem transformedCreation_eq_crv (ord : LinearOrder M) (W : Matrix M M ℂ) (m : M) :
    transformedCreation ord W m = crv ord (W *ᵥ Pi.single m 1) := by
  rw [transformedCreation, crv, Matrix.mulVec_single_one]
  rfl

theorem trProd_eq_crvProd (ord : LinearOrder M) (W : Matrix M M ℂ) (L : List M) :
    trProd ord W L = crvProd ord ((L.map fun m => Pi.single m 1).map (W *ᵥ ·)) := by
  rw [trProd, crvProd, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun m _ => transformedCreation_eq_crv ord W m

theorem crvProd_map_single (ord : LinearOrder M) (L : List M) :
    crvProd ord (L.map fun m => Pi.single m 1) = crProd ord L := by
  rw [crvProd, crProd, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp [crv, Pi.single_apply]

theorem coeffPairing_ket_left (n : Finset M) (ψ : Finset M → ℂ) :
    coeffPairing (ket n) ψ = ψ n :=
  coeffPairing_single_left n ψ

/-- For a unitary `W`, `Γ(W)` is unitary: the pairing of `Γ(W)|n⟩` and `Γ(W)|n'⟩` is that of
`|n⟩` and `|n'⟩`, because `W` keeps the pairing of one-quark states. -/
theorem secondQuant_mem_unitaryGroup (ord : LinearOrder M) {W : Matrix M M ℂ}
    (hW : W ∈ Matrix.unitaryGroup M ℂ) :
    secondQuant ord W ∈ Matrix.unitaryGroup (Finset M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hW ⊢
  ext n n'
  have key := coeffPairing_crvProd_map ord W hW
    ((letI := ord; n.sort).map fun m => Pi.single m 1)
    ((letI := ord; n'.sort).map fun m => Pi.single m 1)
  rw [← trProd_eq_crvProd, ← trProd_eq_crvProd, ← secondQuant_mulVec_ket,
    ← secondQuant_mulVec_ket, crvProd_map_single, crvProd_map_single, crProd_sort_mulVec_vacuum,
    crProd_sort_mulVec_vacuum, coeffPairing_mulVec, coeffPairing_ket_left,
    coeffPairing_ket_left, mulVec_ket] at key
  exact key.trans (by rw [ket, Pi.single_apply, Matrix.one_apply])

end Unitary

section Vertex

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [DecidableEq C] in
theorem kron_one_mul (g₁ g₂ : Matrix C C ℂ) :
    Matrix.kroneckerMap (· * ·) g₂ (1 : Matrix S S ℂ) * Matrix.kroneckerMap (· * ·) g₁ 1 =
      Matrix.kroneckerMap (· * ·) (g₂ * g₁) 1 := by
  rw [← Matrix.mul_kronecker_mul, one_mul]

theorem transformedCreation_kron (ord : LinearOrder (C × S)) (g : Matrix C C ℂ) (c : C) (s : S) :
    transformedCreation ord (Matrix.kroneckerMap (· * ·) g (1 : Matrix S S ℂ)) (c, s) =
      ∑ c', g c' c • creation ord (c', s) := by
  rw [transformedCreation, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c' _ => ?_
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_smul]

theorem isUnit_kron (g : GL C ℂ) :
    IsUnit (Matrix.kroneckerMap (· * ·) (g : Matrix C C ℂ) (1 : Matrix S S ℂ)) := by
  refine ⟨⟨Matrix.kroneckerMap (· * ·) (g : Matrix C C ℂ) 1,
    Matrix.kroneckerMap (· * ·) ((g⁻¹ : GL C ℂ) : Matrix C C ℂ) 1, ?_, ?_⟩, rfl⟩
  · rw [kron_one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  · rw [kron_one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]

theorem kron_one_mem_unitaryGroup {g : Matrix C C ℂ} (hg : g ∈ Matrix.unitaryGroup C ℂ) :
    Matrix.kroneckerMap (· * ·) g (1 : Matrix S S ℂ) ∈ Matrix.unitaryGroup (C × S) ℂ :=
  Matrix.kronecker_mem_unitary hg (one_mem _)

end Vertex

section OrderChange

open Classical in
/-- The sign `σ(n)` of an occupation table under a change of order: minus one to the number of
pairs of occupied modes that the two orders put in opposite order. -/
noncomputable def orderSign (ord₁ ord₂ : LinearOrder M) (n : Finset M) : ℂ :=
  ∏ a ∈ n, ∏ b ∈ n, if ord₁.lt b a ∧ ord₂.lt a b then -1 else 1

omit [Fintype M] [DecidableEq M] in
open Classical in
theorem neg_one_pow_precCount (ord : LinearOrder M) (n : Finset M) (m : M) :
    (-1 : ℂ) ^ precCount ord n m = ∏ b ∈ n, if ord.lt b m then -1 else 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, precCount]

omit [Fintype M] [DecidableEq M] in
theorem orderSign_sq (ord₁ ord₂ : LinearOrder M) (n : Finset M) :
    orderSign ord₁ ord₂ n * orderSign ord₁ ord₂ n = 1 := by
  classical
  rw [orderSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  split_ifs <;> norm_num

omit [Fintype M] [DecidableEq M] in
theorem orderSign_eq_one_or (ord₁ ord₂ : LinearOrder M) (n : Finset M) :
    orderSign ord₁ ord₂ n = 1 ∨ orderSign ord₁ ord₂ n = -1 := by
  classical
  have hmul : ∀ x y : ℂ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → (x * y = 1 ∨ x * y = -1) := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> norm_num
  refine Finset.prod_induction _ (fun x => x = 1 ∨ x = -1) hmul (Or.inl rfl) fun a _ => ?_
  refine Finset.prod_induction _ (fun x => x = 1 ∨ x = -1) hmul (Or.inl rfl) fun b _ => ?_
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

omit [Fintype M] in
open Classical in
theorem orderSign_insert (ord₁ ord₂ : LinearOrder M) {m : M} {n : Finset M} (hm : m ∉ n) :
    orderSign ord₁ ord₂ (insert m n) = orderSign ord₁ ord₂ n *
      ((∏ b ∈ n, if ord₁.lt b m ∧ ord₂.lt m b then -1 else 1) *
        ∏ a ∈ n, if ord₁.lt m a ∧ ord₂.lt a m then -1 else 1) := by
  have hmm : ¬ (ord₁.lt m m ∧ ord₂.lt m m) := fun h => by
    let := ord₁
    exact lt_irrefl m h.1
  simp only [orderSign, Finset.prod_insert hm, hmm, ite_false, one_mul, Finset.prod_mul_distrib]
  ring

omit [Fintype M] in
/-- The sign rule in the new order is the sign rule in the old one times `σ(n + 1_m) σ(n)`. -/
theorem neg_one_pow_precCount_change (ord₁ ord₂ : LinearOrder M) {m : M} {n : Finset M}
    (hm : m ∉ n) :
    (-1 : ℂ) ^ precCount ord₂ n m =
      orderSign ord₁ ord₂ (insert m n) * orderSign ord₁ ord₂ n * (-1) ^ precCount ord₁ n m := by
  classical
  have asymm₁ : ∀ x y, ord₁.lt x y → ¬ ord₁.lt y x := fun x y h => by
    let := ord₁
    exact lt_asymm h
  have asymm₂ : ∀ x y, ord₂.lt x y → ¬ ord₂.lt y x := fun x y h => by
    let := ord₂
    exact lt_asymm h
  have tri₁ : ∀ x y : M, x ≠ y → ord₁.lt x y ∨ ord₁.lt y x := fun x y h => by
    let := ord₁
    exact lt_or_gt_of_ne h
  have tri₂ : ∀ x y : M, x ≠ y → ord₂.lt x y ∨ ord₂.lt y x := fun x y h => by
    let := ord₂
    exact lt_or_gt_of_ne h
  set X : ℂ := (∏ b ∈ n, if ord₁.lt b m ∧ ord₂.lt m b then -1 else 1) *
    ∏ a ∈ n, if ord₁.lt m a ∧ ord₂.lt a m then -1 else 1 with hX
  have hpt : (-1 : ℂ) ^ precCount ord₂ n m = X * (-1) ^ precCount ord₁ n m := by
    rw [hX, neg_one_pow_precCount, neg_one_pow_precCount, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hbm : b ≠ m := fun h => hm (h ▸ hb)
    rcases tri₁ b m hbm with h1 | h1 <;> rcases tri₂ b m hbm with h2 | h2 <;>
      simp [h1, h2, asymm₁ _ _ h1, asymm₂ _ _ h2]
  rw [orderSign_insert ord₁ ord₂ hm, ← hX, hpt]
  linear_combination (-(X * (-1) ^ precCount ord₁ n m)) * orderSign_sq ord₁ ord₂ n

/-- The diagonal matrix `Σ` of the signs `σ(n)`. -/
noncomputable def orderSigma (ord₁ ord₂ : LinearOrder M) : Matrix (Finset M) (Finset M) ℂ :=
  Matrix.diagonal (orderSign ord₁ ord₂)

theorem orderSigma_mul_self (ord₁ ord₂ : LinearOrder M) :
    orderSigma ord₁ ord₂ * orderSigma ord₁ ord₂ = 1 := by
  rw [orderSigma, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext n
  exact orderSign_sq ord₁ ord₂ n

theorem orderSigma_inv (ord₁ ord₂ : LinearOrder M) :
    (orderSigma ord₁ ord₂)⁻¹ = orderSigma ord₁ ord₂ :=
  Matrix.inv_eq_left_inv (orderSigma_mul_self ord₁ ord₂)

theorem conj_orderSigma_apply (ord₁ ord₂ : LinearOrder M) (A : Matrix (Finset M) (Finset M) ℂ)
    (n' n : Finset M) :
    (orderSigma ord₁ ord₂ * A * (orderSigma ord₁ ord₂)⁻¹) n' n =
      orderSign ord₁ ord₂ n' * A n' n * orderSign ord₁ ord₂ n := by
  rw [orderSigma_inv, orderSigma, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem creation_change (ord₁ ord₂ : LinearOrder M) (m : M) :
    creation ord₂ m =
      orderSigma ord₁ ord₂ * creation ord₁ m * (orderSigma ord₁ ord₂)⁻¹ := by
  ext n' n
  rw [conj_orderSigma_apply]
  simp only [creation, Matrix.of_apply]
  by_cases h : m ∉ n ∧ n' = insert m n
  · obtain ⟨hm, rfl⟩ := h
    simp only [hm, not_false_eq_true, true_and, ite_true]
    rw [neg_one_pow_precCount_change ord₁ ord₂ hm]
    ring
  · simp [h]

theorem annihilation_change (ord₁ ord₂ : LinearOrder M) (m : M) :
    annihilation ord₂ m =
      orderSigma ord₁ ord₂ * annihilation ord₁ m * (orderSigma ord₁ ord₂)⁻¹ := by
  ext n' n
  rw [conj_orderSigma_apply]
  simp only [annihilation, Matrix.of_apply]
  by_cases h : m ∈ n ∧ n' = n.erase m
  · obtain ⟨hm, rfl⟩ := h
    simp only [hm, true_and, ite_true]
    have hne := Finset.notMem_erase m n
    rw [← precCount_erase_self ord₂, ← precCount_erase_self ord₁,
      neg_one_pow_precCount_change ord₁ ord₂ hne, Finset.insert_erase hm]
    ring
  · simp [h]

theorem build_change (ord₁ ord₂ : LinearOrder M) (P : FreeAlgebra ℂ (M ⊕ M)) :
    build ord₂ P = orderSigma ord₁ ord₂ * build ord₁ P * (orderSigma ord₁ ord₂)⁻¹ := by
  have hinv : orderSigma ord₁ ord₂ * (orderSigma ord₁ ord₂)⁻¹ = 1 := by
    rw [orderSigma_inv, orderSigma_mul_self]
  have hinv' : (orderSigma ord₁ ord₂)⁻¹ * orderSigma ord₁ ord₂ = 1 := by
    rw [orderSigma_inv, orderSigma_mul_self]
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one, Matrix.smul_mul, hinv]
  | grade1 x =>
    cases x with
    | inl m => simp only [build, FreeAlgebra.lift_ι_apply, Sum.elim_inl, creation_change ord₁ ord₂]
    | inr m =>
      simp only [build, FreeAlgebra.lift_ι_apply, Sum.elim_inr, annihilation_change ord₁ ord₂]
  | mul a b ha hb =>
    rw [map_mul, map_mul, ha, hb]
    calc orderSigma ord₁ ord₂ * build ord₁ a * (orderSigma ord₁ ord₂)⁻¹ *
          (orderSigma ord₁ ord₂ * build ord₁ b * (orderSigma ord₁ ord₂)⁻¹)
        = orderSigma ord₁ ord₂ * build ord₁ a *
            ((orderSigma ord₁ ord₂)⁻¹ * orderSigma ord₁ ord₂) * build ord₁ b *
              (orderSigma ord₁ ord₂)⁻¹ := by noncomm_ring
      _ = _ := by rw [hinv', mul_one, mul_assoc (orderSigma ord₁ ord₂)]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, mul_add, add_mul]

/-- `a†_m a_m` is the diagonal matrix of the occupation numbers `n_m`, in any order. -/
theorem creation_mul_annihilation (ord : LinearOrder M) (m : M) :
    creation ord m * annihilation ord m = Matrix.diagonal (fun n => if m ∈ n then 1 else 0) := by
  apply ext_ket
  intro n
  rw [← Matrix.mulVec_mulVec, ket, Matrix.diagonal_mulVec_single, ← ket]
  by_cases hm : m ∈ n
  · rw [annihilation_mulVec_ket_of_mem hm, Matrix.mulVec_smul,
      creation_mulVec_ket_of_notMem (Finset.notMem_erase m n), Finset.insert_erase hm,
      precCount_erase_self, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp [hm, ket]
  · rw [annihilation_mulVec_ket_of_notMem hm, Matrix.mulVec_zero]
    simp [hm]

end OrderChange

end Fock

/-- **Proposition 11.11** (the order is a presentation). Changing the order of the modes
conjugates every creation and every annihilation by one diagonal matrix `Σ` of signs, the same
for all of them. Every operator built from them is conjugated by `Σ`, every occupation number
`n_m = a†_m a_m` is unchanged, and every report, which reads squared sizes of coefficients on
basis states, is unchanged. -/
@[book "prop:mt-order-witness"]
theorem mtOrderWitness : Statement.mtOrderWitness := by
  intro M _ _ ord₁ ord₂
  refine ⟨Fock.orderSigma ord₁ ord₂, ⟨Fock.orderSign ord₁ ord₂,
    Fock.orderSign_eq_one_or ord₁ ord₂, rfl⟩, Fock.creation_change ord₁ ord₂,
    Fock.annihilation_change ord₁ ord₂, Fock.build_change ord₁ ord₂,
    fun m => ⟨Fock.creation_mul_annihilation ord₁ m, Fock.creation_mul_annihilation ord₂ m⟩,
    fun P n' n => ?_⟩
  rw [Fock.build_change ord₁ ord₂, Fock.conj_orderSigma_apply, norm_mul, norm_mul]
  have h1 : ∀ k, ‖Fock.orderSign ord₁ ord₂ k‖ = 1 := fun k => by
    rcases Fock.orderSign_eq_one_or ord₁ ord₂ k with h | h <;> simp [h]
  rw [h1, h1, one_mul, mul_one]

/-- **Proposition 11.12** (second quantization is a homomorphism).
`Γ(g₂) Γ(g₁) = Γ(g₂ g₁)`, and `Γ(g) a†_{cs} Γ(g)⁻¹ = Σ_{c'} g_{c'c} a†_{c's}`. For a unitary
`g`, `Γ(g)` is unitary. -/
@[book "prop:mt-gamma"]
theorem mtGamma : Statement.mtGamma := by
  intro C S _ _ _ _ ord
  refine ⟨fun g₁ g₂ => ?_, fun g c s => ?_, fun g hg => ?_⟩
  · simp only [Fock.vertexGamma]
    rw [Fock.secondQuant_mul, Fock.kron_one_mul]
  · simp only [Fock.vertexGamma]
    rw [Fock.secondQuant_conj_creation ord (Fock.isUnit_kron g), Fock.transformedCreation_kron]
  · exact Fock.secondQuant_mem_unitaryGroup ord (Fock.kron_one_mem_unitaryGroup hg)

/-! ## Non-vacuity -/

section NonVacuity

open scoped Matrix

/-- The book's figure for the sign rule, three modes ordered `1 < 2 < 3` (here `0 < 1 < 2`):
the word `a†_2 a†_1 a†_3` acting on the empty table gives `-|111⟩`. -/
example : Fock.creation (inferInstance : LinearOrder (Fin 3)) 1 *ᵥ
    (Fock.creation inferInstance 0 *ᵥ (Fock.creation inferInstance 2 *ᵥ Fock.ket ∅)) =
      -Fock.ket {0, 1, 2} := by
  have h1 : Fock.precCount (inferInstance : LinearOrder (Fin 3)) ∅ 2 = 0 := by decide
  have h2 : Fock.precCount (inferInstance : LinearOrder (Fin 3)) (insert 2 ∅) 0 = 0 := by
    decide
  have h3 : Fock.precCount (inferInstance : LinearOrder (Fin 3)) (insert 0 (insert 2 ∅)) 1 = 1 :=
    by decide
  have hs : (insert 1 (insert 0 (insert 2 ∅)) : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [Fock.creation_mulVec_ket_of_notMem (by decide)]
  simp only [Matrix.mulVec_smul]
  rw [Fock.creation_mulVec_ket_of_notMem (by decide)]
  simp only [Matrix.mulVec_smul]
  rw [Fock.creation_mulVec_ket_of_notMem (by decide), h1, h2, h3, hs]
  simp

/-- Proposition 11.11 on the three colour modes of one vertex: the order `1 < 2 < 3` and the
reversed order `3 < 2 < 1` meet its hypotheses. -/
example : ∃ Sig : Matrix (Finset (Fin 3)) (Finset (Fin 3)) ℂ,
    ∀ m, Fock.creation (LinearOrder.lift' (OrderDual.toDual : Fin 3 → (Fin 3)ᵒᵈ)
      OrderDual.toDual.injective) m = Sig * Fock.creation inferInstance m * Sig⁻¹ := by
  obtain ⟨Sig, -, h, -⟩ := mtOrderWitness (Fin 3) inferInstance
    (LinearOrder.lift' (OrderDual.toDual : Fin 3 → (Fin 3)ᵒᵈ) OrderDual.toDual.injective)
  exact ⟨Sig, h⟩

/-- Proposition 11.12 on one vertex with three colours and one slot, the modes in lexicographic
order: the unitary matrix `-1` meets the hypothesis of the last part. -/
example : Fock.vertexGamma
    (LinearOrder.lift' (toLex : Fin 3 × Fin 1 → Lex (Fin 3 × Fin 1)) toLex.injective)
    (-1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.unitaryGroup (Finset (Fin 3 × Fin 1)) ℂ :=
  (mtGamma (Fin 3) (Fin 1) _).2.2 _ (by rw [Matrix.mem_unitaryGroup_iff']; simp)

end NonVacuity

end Artform
