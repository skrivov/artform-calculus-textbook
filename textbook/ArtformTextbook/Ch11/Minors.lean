import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ArtformTextbook.Ch11.Occupation

/-!
# The coefficients of a second quantization are minors

For a matrix `W` on the modes, the coefficient of `Γ(W)` from the occupation table with occupied
modes `m₁ < ⋯ < m_k` to the one with occupied modes `m'₁ < ⋯ < m'_k` is the minor of `W` with rows
`m'₁, …, m'_k` and columns `m₁, …, m_k` (`Fock.secondQuant_apply_eq_det`), the formula of
Proposition 11.17. It is proved by induction on the occupied modes, expanding the determinant
along its first column: `Γ(W)|n⟩ = (Σ_b W_{b m₁} a†_b) Γ(W)|n - m₁⟩`, and `a†_b` puts the sign
`(-1)^i` on the occupation table whose `i`-th mode is `b`.

Consequences used in Section 11.5:
* `Γ(W)` keeps the number of quarks, and more generally the number of quarks with each value of a
  label `f` of the modes that `W` does not mix (`Fock.secondQuant_apply_eq_zero_of_labels`);
* the sum of the diagonal coefficients of `Γ(W)` over the tables with `k` quarks is the sum of
  the principal `k × k` minors of `W`, the coefficient of `z^k` in `det(1 + z W)`
  (`Fock.sum_powersetCard_secondQuant_diag`), and the trace of `Γ(W)` is `det(1 + W)`
  (`Fock.trace_secondQuant`).
-/

namespace Artform

namespace Fock

open scoped Matrix

open Polynomial

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The coefficient of `a†_m x` on the table `n'`: `(-1)^{p(n' - m, m)} x(n' - m)` if `m ∈ n'`,
and `0` otherwise. -/
theorem creation_mulVec_apply (ord : LinearOrder M) (m : M) (x : Finset M → ℂ) (n' : Finset M) :
    (creation ord m *ᵥ x) n' =
      if m ∈ n' then (-1) ^ precCount ord (n'.erase m) m * x (n'.erase m) else 0 := by
  simp only [Matrix.mulVec, dotProduct, creation, Matrix.of_apply, ite_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single (n'.erase m)]
    · rw [ite_eq_left ⟨Finset.notMem_erase m n', (Finset.insert_erase h).symm⟩]
    · intro n _ hn
      rw [ite_eq_right]
      rintro ⟨h1, rfl⟩
      exact hn (Finset.erase_insert h1).symm
    · simp
  · refine Finset.sum_eq_zero fun n _ => ?_
    rw [ite_eq_right]
    rintro ⟨_, rfl⟩
    exact h (Finset.mem_insert_self _ _)

omit [Fintype M] in
/-- The `i`-th occupied mode of a table, in ascending order, is preceded by `i` occupied modes. -/
theorem precCount_orderEmbOfFin (ord : LinearOrder M) (s : Finset M) {k : ℕ} (h : s.card = k)
    (i : Fin k) :
    precCount ord (s.erase (@Finset.orderEmbOfFin M ord s k h i))
      (@Finset.orderEmbOfFin M ord s k h i) = i := by
  let := ord
  unfold precCount
  have key : (s.erase (s.orderEmbOfFin h i)).filter (· < s.orderEmbOfFin h i) =
      (Finset.Iio i).map (s.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨-, hx⟩, hlt⟩
      have hr : x ∈ Set.range (s.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (s.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hlt := (s.orderEmbOfFin h).lt_iff_lt.mpr hj
      exact ⟨⟨hlt.ne, Finset.orderEmbOfFin_mem s h j⟩, hlt⟩
  rw [key, Finset.card_map, Fin.card_Iio]

omit [Fintype M] in
/-- Removing the `i`-th mode: the ascending enumeration of the remaining modes skips `i`. -/
theorem orderEmbOfFin_succAbove (ord : LinearOrder M) (s : Finset M) {k : ℕ}
    (h : s.card = k + 1) (i : Fin (k + 1))
    (h' : (s.erase (@Finset.orderEmbOfFin M ord s (k + 1) h i)).card = k) :
    (fun j => @Finset.orderEmbOfFin M ord s (k + 1) h (i.succAbove j)) =
      @Finset.orderEmbOfFin M ord _ k h' := by
  let := ord
  refine Finset.orderEmbOfFin_unique h' (fun j => ?_) ?_
  · rw [Finset.mem_erase]
    exact ⟨fun he => Fin.succAbove_ne i j ((s.orderEmbOfFin h).injective he),
      Finset.orderEmbOfFin_mem s h _⟩
  · exact (s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i)

omit [Fintype M] in
/-- Adding a least mode `a`: it is the first in ascending order, and the others follow. -/
theorem orderEmbOfFin_insert_zero (ord : LinearOrder M) {a : M} {s : Finset M}
    (ha : ∀ x ∈ s, ord.lt a x) {k : ℕ} (h : (insert a s).card = k + 1) :
    @Finset.orderEmbOfFin M ord (insert a s) (k + 1) h 0 = a := by
  let := ord
  rw [show (0 : Fin (k + 1)) = ⟨0, Nat.succ_pos k⟩ from rfl, Finset.orderEmbOfFin_zero]
  refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self a s)) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact le_rfl
  · exact (ha y hy).le

omit [Fintype M] in
theorem orderEmbOfFin_insert_succ (ord : LinearOrder M) {a : M} {s : Finset M}
    (ha : ∀ x ∈ s, ord.lt a x) {k : ℕ} (h : (insert a s).card = k + 1) (h' : s.card = k) :
    (fun j => @Finset.orderEmbOfFin M ord (insert a s) (k + 1) h j.succ) =
      @Finset.orderEmbOfFin M ord s k h' := by
  let := ord
  refine Finset.orderEmbOfFin_unique h' (fun j => ?_) ?_
  · have hmem := Finset.orderEmbOfFin_mem (insert a s) h j.succ
    rcases Finset.mem_insert.mp hmem with he | hs
    · exfalso
      have hlt := (Finset.orderEmbOfFin (insert a s) h).strictMono (Fin.succ_pos j)
      rw [orderEmbOfFin_insert_zero ord ha h, he] at hlt
      exact lt_irrefl a hlt
    · exact hs
  · exact (Finset.orderEmbOfFin (insert a s) h).strictMono.comp (Fin.strictMono_succ)

theorem secondQuant_empty_empty (ord : LinearOrder M) (W : Matrix M M ℂ) :
    secondQuant ord W ∅ ∅ = 1 := by
  have := congrFun (secondQuant_mulVec_vacuum ord W) ∅
  rwa [mulVec_ket, ket, Pi.single_eq_same] at this

/-- **The minor formula** (Proposition 11.17). The coefficient of `Γ(W)` from the table with
occupied modes `m₁ < ⋯ < m_k` to the table with occupied modes `m'₁ < ⋯ < m'_k` is the minor of
`W` with rows `m'₁, …, m'_k` and columns `m₁, …, m_k`. -/
theorem secondQuant_apply_eq_det (ord : LinearOrder M) (W : Matrix M M ℂ) (n : Finset M) :
    ∀ (k : ℕ) (n' : Finset M) (hn : n.card = k) (hn' : n'.card = k),
      secondQuant ord W n' n =
        (W.submatrix (@Finset.orderEmbOfFin M ord n' k hn')
          (@Finset.orderEmbOfFin M ord n k hn)).det := by
  let := ord
  induction n using Finset.induction_on_min with
  | empty =>
    intro k n' hn hn'
    rw [Finset.card_empty] at hn
    subst hn
    obtain rfl : n' = ∅ := Finset.card_eq_zero.mp hn'
    rw [secondQuant_empty_empty, Matrix.det_fin_zero]
  | insert a s ha ih =>
    intro k n' hn hn'
    have ha' : a ∉ s := fun h => lt_irrefl a (ha a h)
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨s.card, by rw [← hn, Finset.card_insert_of_notMem ha']⟩
    have hs : s.card = k := by
      rw [Finset.card_insert_of_notMem ha'] at hn
      omega
    -- `Γ(W)|insert a s⟩ = (Σ_b W_{ba} a†_b) Γ(W)|s⟩`
    have hstep : secondQuant ord W *ᵥ ket (insert a s) =
        transformedCreation ord W a *ᵥ (secondQuant ord W *ᵥ ket s) := by
      rw [secondQuant_mulVec_ket, secondQuant_mulVec_ket,
        Finset.sort_insert _ (fun b hb => (ha b hb).le) ha', trProd, List.map_cons,
        List.prod_cons, ← Matrix.mulVec_mulVec]
      rfl
    have hL : secondQuant ord W n' (insert a s) =
        ∑ i : Fin (k + 1), W (n'.orderEmbOfFin hn' i) a * (-1) ^ (i : ℕ) *
          secondQuant ord W (n'.erase (n'.orderEmbOfFin hn' i)) s := by
      have h1 : secondQuant ord W n' (insert a s) =
          (transformedCreation ord W a *ᵥ (secondQuant ord W *ᵥ ket s)) n' := by
        rw [← hstep, mulVec_ket]
      rw [h1, transformedCreation, Matrix.sum_mulVec, Finset.sum_apply]
      simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, creation_mulVec_apply,
        mul_ite, mul_zero]
      have key : ∀ f : M → ℂ, ∑ b ∈ n', f b = ∑ i : Fin (k + 1), f (n'.orderEmbOfFin hn' i) := by
        intro f
        conv_lhs => rw [← Finset.map_orderEmbOfFin_univ n' hn']
        rw [Finset.sum_map]
        rfl
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, key]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [precCount_orderEmbOfFin ord n' hn' i, mulVec_ket]
      ring
    have hR := Matrix.det_succ_column_zero
      (W.submatrix (n'.orderEmbOfFin hn') ((insert a s).orderEmbOfFin hn))
    rw [hL, hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcard : (n'.erase (n'.orderEmbOfFin hn' i)).card = k := by
      rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem n' hn' i), hn']
      rfl
    rw [ih k _ hs hcard, Matrix.submatrix_apply, orderEmbOfFin_insert_zero ord ha hn,
      Matrix.submatrix_submatrix]
    have e1 := orderEmbOfFin_succAbove ord n' hn' i hcard
    have e2 := orderEmbOfFin_insert_succ ord ha hn hs
    simp only [Function.comp_def]
    rw [e1, e2]
    ring

/-- Expanding along the least occupied mode: for `a` below every mode of `s`,
`Γ(W)_{n', s ∪ {a}} = Σ_{b ∈ n'} W_{ba} (-1)^{p(n' - b, b)} Γ(W)_{n' - b, s}`. -/
theorem secondQuant_insert_apply (ord : LinearOrder M) (W : Matrix M M ℂ) {a : M} {s : Finset M}
    (ha : ∀ x ∈ s, ord.lt a x) (n' : Finset M) :
    secondQuant ord W n' (insert a s) =
      ∑ b ∈ n', W b a * ((-1) ^ precCount ord (n'.erase b) b *
        secondQuant ord W (n'.erase b) s) := by
  let := ord
  have ha' : a ∉ s := fun h => lt_irrefl a (ha a h)
  have hstep : secondQuant ord W *ᵥ ket (insert a s) =
      transformedCreation ord W a *ᵥ (secondQuant ord W *ᵥ ket s) := by
    rw [secondQuant_mulVec_ket, secondQuant_mulVec_ket,
      Finset.sort_insert _ (fun b hb => (ha b hb).le) ha', trProd, List.map_cons,
      List.prod_cons, ← Matrix.mulVec_mulVec]
    rfl
  have h1 : secondQuant ord W n' (insert a s) =
      (transformedCreation ord W a *ᵥ (secondQuant ord W *ᵥ ket s)) n' := by
    rw [← hstep, mulVec_ket]
  rw [h1, transformedCreation, Matrix.sum_mulVec, Finset.sum_apply]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, creation_mulVec_apply,
    mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mulVec_ket]

/-- The number of occupied modes of `n` with the label `b`. -/
def labelCount {β : Type*} [DecidableEq β] (f : M → β) (n : Finset M) (b : β) : ℕ :=
  (n.filter fun m => f m = b).card

omit [Fintype M] in
theorem labelCount_erase {β : Type*} [DecidableEq β] (f : M → β) {n : Finset M} {m : M}
    (hm : m ∈ n) (b : β) :
    labelCount f n b = labelCount f (n.erase m) b + if f m = b then 1 else 0 := by
  unfold labelCount
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hm, h⟩)]
    have : 0 < (n.filter fun m => f m = b).card :=
      Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, h⟩⟩
    omega
  · rw [Finset.erase_eq_of_notMem (s := n.filter fun x => f x = b) (a := m)
      (fun h' => h (Finset.mem_filter.mp h').2), add_zero]

omit [Fintype M] in
theorem labelCount_insert {β : Type*} [DecidableEq β] (f : M → β) {s : Finset M} {a : M}
    (ha : a ∉ s) (b : β) :
    labelCount f (insert a s) b = labelCount f s b + if f a = b then 1 else 0 := by
  rw [labelCount_erase f (Finset.mem_insert_self a s) b, Finset.erase_insert ha]

/-- `Γ(W)` keeps the number of quarks with each value of a label `f` of the modes that `W` does
not mix: if `W_{m'm} = 0` whenever `f m' ≠ f m`, then `Γ(W)_{n'n} = 0` unless `n'` and `n` have
as many occupied modes as each other with every label. -/
theorem secondQuant_apply_eq_zero_of_labels (ord : LinearOrder M) {β : Type*} [DecidableEq β]
    (f : M → β)
    {W : Matrix M M ℂ} (hW : ∀ m' m, f m' ≠ f m → W m' m = 0) (n : Finset M) :
    ∀ n' : Finset M, secondQuant ord W n' n ≠ 0 → ∀ b, labelCount f n' b = labelCount f n b := by
  let := ord
  induction n using Finset.induction_on_min with
  | empty =>
    intro n' hn' b
    by_contra hne
    apply hn'
    have hne' : n' ≠ ∅ := by
      rintro rfl
      exact hne rfl
    have h := congrFun (secondQuant_mulVec_vacuum ord W) n'
    rw [mulVec_ket, ket, Pi.single_apply, ite_eq_right hne'] at h
    exact h
  | insert a s ha ih =>
    intro n' hn' b
    have ha' : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [secondQuant_insert_apply ord W ha n'] at hn'
    obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
    have hWc : W c a ≠ 0 := left_ne_zero_of_mul hne
    have hfc : f c = f a := by
      by_contra h
      exact hWc (hW c a h)
    have hG : secondQuant ord W (n'.erase c) s ≠ 0 :=
      right_ne_zero_of_mul (right_ne_zero_of_mul hne)
    rw [labelCount_erase f hc b, ih (n'.erase c) hG b, labelCount_insert f ha' b, hfc]

/-- A diagonal coefficient of `Γ(W)` is a principal minor of `W`, indexed by the occupied
modes. -/
theorem secondQuant_diag_eq_det (ord : LinearOrder M) (W : Matrix M M ℂ) (n : Finset M) :
    secondQuant ord W n n = (W.submatrix (Subtype.val : n → M) Subtype.val).det := by
  let := ord
  rw [secondQuant_apply_eq_det ord W n n.card n rfl rfl,
    ← Matrix.det_submatrix_equiv_self (n.orderIsoOfFin rfl).toEquiv
      (W.submatrix (Subtype.val : n → M) Subtype.val), Matrix.submatrix_submatrix]
  rfl

/-- The sum of the diagonal coefficients of `Γ(W)` over the tables with `k` quarks is the sum of
the principal `k × k` minors of `W`: the coefficient of `z^k` in `det(1 + z W)`. -/
theorem sum_powersetCard_secondQuant_diag (ord : LinearOrder M) (W : Matrix M M ℂ) (k : ℕ) :
    ∑ n ∈ Finset.powersetCard k Finset.univ, secondQuant ord W n n =
      (1 + (X : ℂ[X]) • W.map C).det.coeff k := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact Finset.sum_congr rfl fun n _ => secondQuant_diag_eq_det ord W n

/-- The trace of `Γ(W)` is `det(1 + W)`. -/
theorem trace_secondQuant (ord : LinearOrder M) (W : Matrix M M ℂ) :
    (secondQuant ord W).trace = (1 + W).det := by
  set P : ℂ[X] := (1 + (X : ℂ[X]) • W.map C).det with hP
  have hcoeff : ∀ k, P.coeff k = ∑ n ∈ Finset.powersetCard k Finset.univ, secondQuant ord W n n :=
    fun k => (sum_powersetCard_secondQuant_diag ord W k).symm
  have hdeg : P.natDegree < Fintype.card M + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
    rw [hcoeff, Finset.powersetCard_eq_empty.mpr (by rwa [Finset.card_univ]), Finset.sum_empty]
  have heval : P.eval 1 = (1 + W).det := by
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← heval, Polynomial.eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one, hcoeff]
  rw [Matrix.trace]
  simp only [Matrix.diag]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
    (t := Finset.range (Fintype.card M + 1))
    (fun n _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ n)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ext n
  simp [Finset.mem_powersetCard]

end Fock

end Artform
