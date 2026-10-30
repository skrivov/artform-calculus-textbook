import ArtformScores.Bells

/-!
# Extents

T15 of the algebra of scores, the extents of finding 043. An extent of a group `G` under two
steps `A` and `B` is a run `x → A x` or `x → B x` through every element and back: a peal of
all the rows, a Hamiltonian cycle of the Cayley digraph.
- **Rankin's links.** The two possible predecessors of a vertex are `A⁻¹ z` and
  `B⁻¹ z = c⁻¹ A⁻¹ z`, `c = A⁻¹ B`, and exactly one of them steps to it. So the choice of step
  at `w` and at `c⁻¹ w` agree: it is constant on each coset `⟨c⟩ x`.
- **Rankin's parity.** Then `σ = L_A τ`, where `τ` is `L_c` on the cosets that take `B`, so all
  of its cycles have length `ord c`, and `sign σ = sign L_A · ((-1)^(ord c + 1))^m`. An extent is
  one `|G|`-cycle, of sign `(-1)^(|G| + 1)`.
- **Lifting.** A normal `N ⊂ ⟨c⟩` is inside each coset's `⟨c⟩`, so `σ` maps the cosets of `N`
  onto cosets of `N`, and induces an extent of `G/N`.
- **The Fibonacci rule.** On one mode, `c = K⁻¹ M = [[1, -1], [-1, 2]]` has the powers
  `[[F₂ₖ₋₁, -F₂ₖ], [-F₂ₖ, F₂ₖ₊₁]]`, which are `±1` exactly when `p ∣ F₂ₖ`, that is when
  `α(p) ∣ 2k` (by `gcd(F_m, F_n) = F_gcd(m,n)`). If `4 ∤ α(p)`, the order of `c` in `PSL(2, p)` is
  odd; `K` has the odd order `p`, and `|PSL(2, p)|` is even, so parity excludes an extent. In
  `SL(2, p)`, either `c` has odd order too, or `c^k₀ = -1` and lifting carries an extent down
  to `PSL(2, p)`.
-/

namespace Artform.Scores.Bells

open Equiv Finset

section Sign

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation whose moved points all have the period `n`. -/
theorem sign_of_period (π : Perm α) (n : ℕ)
    (hper : ∀ x, π x ≠ x → ∀ j : ℕ, (π ^ j) x = x ↔ n ∣ j) :
    ∃ m : ℕ, m * n = #π.support ∧ Perm.sign π = ((-1 : ℤˣ) ^ (n + 1)) ^ m := by
  have hct : ∀ k ∈ π.cycleType, k = n := by
    intro k hk
    rw [Perm.cycleType_def, Multiset.mem_map] at hk
    obtain ⟨κ, hκ, rfl⟩ := hk
    have hκ' : κ ∈ π.cycleFactorsFinset := hκ
    obtain ⟨hcyc, hagree⟩ := Perm.mem_cycleFactorsFinset_iff.mp hκ'
    obtain ⟨a, ha⟩ := hcyc.nonempty_support
    have hκa : κ = π.cycleOf a := Perm.cycle_is_cycleOf ha hκ'
    have hκa' : κ a ≠ a := Perm.mem_support.mp ha
    have hπa : π a ≠ a := by rw [← hagree a ha]; exact hκa'
    have hpow : ∀ j : ℕ, (κ ^ j) a = (π ^ j) a := by
      intro j
      rw [hκa, Perm.cycleOf_pow_apply_self]
    have hord : orderOf κ = n := by
      apply Nat.dvd_antisymm
      · rw [orderOf_dvd_iff_pow_eq_one, hcyc.pow_eq_one_iff' hκa', hpow]
        exact (hper a hπa n).mpr dvd_rfl
      · rw [← hper a hπa, ← hpow, ← hcyc.pow_eq_one_iff' hκa']
        exact pow_orderOf_eq_one κ
    simp only [Function.comp_apply]
    rw [← hcyc.orderOf, hord]
  have hrep := Multiset.eq_replicate_of_mem hct
  refine ⟨Multiset.card π.cycleType, ?_, ?_⟩
  · rw [← Perm.sum_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  · rw [Perm.sign_of_cycleType, ← pow_mul]
    congr 1
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
    ring

end Sign

section Rankin

variable {G : Type*} [Group G]

/-- Rankin's links: the step chosen at `w` and at `c⁻¹ w` agree, `c = A⁻¹ B`. -/
theorem choice_link {A B : G} {σ : Perm G} (hstep : ∀ x, σ x = A * x ∨ σ x = B * x) (w : G) :
    σ ((A⁻¹ * B)⁻¹ * w) = A * ((A⁻¹ * B)⁻¹ * w) ↔ σ w = A * w := by
  have hB : ∀ y, B * ((A⁻¹ * B)⁻¹ * y) = A * y := fun y => by group
  constructor
  · intro h
    by_contra hw
    have hwB : σ w = B * w := (hstep w).resolve_left hw
    obtain ⟨v, hv⟩ := σ.surjective (A * w)
    rcases hstep v with hvA | hvB
    · rw [hvA] at hv
      have : v = w := mul_left_cancel hv
      subst this
      exact hw (hvA.trans hv)
    · rw [hvB] at hv
      have hv' : v = (A⁻¹ * B)⁻¹ * w := by
        rw [← hB w] at hv
        exact mul_left_cancel hv
      subst hv'
      rw [h] at hvB
      have hcw : (A⁻¹ * B)⁻¹ * w = w := by
        have := hvB.trans (hB w)
        exact mul_left_cancel this
      rw [hcw] at h
      exact hw h
  · intro h
    by_contra hc
    have hcB := (hstep ((A⁻¹ * B)⁻¹ * w)).resolve_left hc
    rw [hB w, ← h] at hcB
    have := σ.injective hcB
    rw [this] at hc
    exact hc h

/-- Rankin's parity: `σ = L_A τ`, where `τ` is `L_c` on the cosets taking `B`, `m` cycles of
length `ord c`. -/
theorem rankin_sign [Fintype G] [DecidableEq G] {A B : G} {σ : Perm G}
    (hstep : ∀ x, σ x = A * x ∨ σ x = B * x) :
    ∃ m : ℕ, m * orderOf (A⁻¹ * B) = #(univ.filter fun x => σ x ≠ A * x) ∧
      Perm.sign σ = Perm.sign (Equiv.mulLeft A) * ((-1) ^ (orderOf (A⁻¹ * B) + 1)) ^ m := by
  set c := A⁻¹ * B with hc
  set τ : Perm G := (Equiv.mulLeft A)⁻¹ * σ with hτ
  have hτx : ∀ x, τ x = A⁻¹ * σ x := fun x => by
    simp [hτ, Perm.mul_apply, Perm.inv_def, Equiv.mulLeft_symm]
  have hστ : σ = Equiv.mulLeft A * τ := by rw [hτ, mul_inv_cancel_left]
  have hmov : ∀ x, τ x ≠ x ↔ σ x ≠ A * x := fun x => by
    rw [hτx, Ne, Ne, inv_mul_eq_iff_eq_mul]
  have hmovc : ∀ x, τ x ≠ x → τ x = c * x := fun x hx => by
    have h := (hstep x).resolve_left ((hmov x).mp hx)
    rw [hτx, h, hc]
    group
  have hinv : ∀ x, τ x ≠ x → τ (c * x) ≠ c * x := fun x hx => by
    rw [hmov] at hx ⊢
    intro h
    apply hx
    have := (choice_link hstep (c * x)).mpr h
    rwa [← hc, inv_mul_cancel_left] at this
  have hpow : ∀ x, τ x ≠ x → ∀ j : ℕ, (τ ^ j) x = c ^ j * x ∧ τ ((τ ^ j) x) ≠ (τ ^ j) x := by
    intro x hx j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [pow_succ', Perm.mul_apply, ih.1, hmovc _ (ih.1 ▸ ih.2), ← mul_assoc, ← pow_succ']
      refine ⟨rfl, ?_⟩
      have := hinv _ (ih.1 ▸ ih.2)
      rwa [← mul_assoc, ← pow_succ'] at this
  have hper : ∀ x, τ x ≠ x → ∀ j : ℕ, (τ ^ j) x = x ↔ orderOf c ∣ j := by
    intro x hx j
    rw [(hpow x hx j).1, mul_eq_right, orderOf_dvd_iff_pow_eq_one]
  obtain ⟨m, hm, hsign⟩ := sign_of_period τ (orderOf c) hper
  refine ⟨m, ?_, ?_⟩
  · rw [hm]
    congr 1
    ext x
    simp only [Perm.mem_support, mem_filter, mem_univ, true_and, hmov]
  · rw [hστ, map_mul, hsign]

/-- An extent is one cycle through all of `G`, of sign `(-1)^(|G| + 1)`. -/
theorem extent_sign [Fintype G] [DecidableEq G] {A B : G} {σ : Perm G} (hσ : IsExtent A B σ) :
    Perm.sign σ = (-1) ^ (Fintype.card G + 1) := by
  rcases Nat.lt_or_ge (Fintype.card G) 2 with h | h
  · have hcard : Fintype.card G = 1 := by
      have := Fintype.card_pos (α := G)
      omega
    have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp hcard.le
    rw [Subsingleton.elim σ 1, map_one, hcard]
    rfl
  · have hmoved : ∀ x, σ x ≠ x := by
      intro x hx
      obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h x
      obtain ⟨k, hk⟩ := hσ.2 x y
      exact hy (hk ▸ Perm.pow_apply_eq_self_of_apply_eq_self hx k)
    have hx : Nonempty G := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨x⟩ := hx
    have hcyc : σ.IsCycle := by
      refine ⟨x, hmoved x, fun y _ => ?_⟩
      obtain ⟨k, hk⟩ := hσ.2 x y
      exact ⟨k, by rw [zpow_natCast]; exact hk⟩
    have hsupp : σ.support = univ := by
      ext y
      simp [Perm.mem_support, hmoved y]
    rw [hcyc.sign, hsupp, card_univ, pow_succ]
    simp

/-- Left multiplication by an element of odd order is even. -/
theorem sign_mulLeft_of_odd [Fintype G] [DecidableEq G] {g : G} (hg : Odd (orderOf g)) :
    Perm.sign (Equiv.mulLeft g) = 1 := by
  have hpow : ∀ (j : ℕ) (x : G), ((Equiv.mulLeft g) ^ j) x = g ^ j * x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', Perm.mul_apply, ih]
      change g * (g ^ j * x) = _
      rw [← mul_assoc, ← pow_succ']
  obtain ⟨m, -, hs⟩ := sign_of_period (Equiv.mulLeft g) (orderOf g) fun x _ j => by
    rw [hpow, mul_eq_right, orderOf_dvd_iff_pow_eq_one]
  obtain ⟨k, hk⟩ := hg
  rw [hs, hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
  simp

/-- The lifting lemma: when a normal subgroup `N` lies in `⟨c⟩`, an extent of `G` maps to an
extent of `G/N`. -/
theorem extent_lift [Finite G] {A B : G} {N : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.zpowers (A⁻¹ * B)) {σ : Perm G} (hσ : IsExtent A B σ) :
    ∃ σ' : Perm (G ⧸ N), IsExtent (A : G ⧸ N) (B : G ⧸ N) σ' ∧
      ∀ x : G, σ' (x : G ⧸ N) = (σ x : G ⧸ N) := by
  set c := A⁻¹ * B with hc
  have hlink := choice_link hσ.1
  have hconst : ∀ (k : ℤ) (w : G), σ (c ^ k * w) = A * (c ^ k * w) ↔ σ w = A * w := by
    intro k
    refine Int.induction_on k (fun w => by simp) (fun i ih w => ?_) (fun i ih w => ?_)
    · have := hlink (c ^ ((i : ℤ) + 1) * w)
      rw [← hc, show c⁻¹ * (c ^ ((i : ℤ) + 1) * w) = c ^ (i : ℤ) * w by group] at this
      rw [← this, ih]
    · have := hlink (c ^ (-(i : ℤ)) * w)
      rw [← hc, show c⁻¹ * (c ^ (-(i : ℤ)) * w) = c ^ (-(i : ℤ) - 1) * w by group] at this
      rw [this, ih]
  have hwd : ∀ n x : G, n ∈ N → ((σ (n * x) : G) : G ⧸ N) = ((σ x : G) : G ⧸ N) := by
    intro n x hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hN hn)
    have hn1 : ((c ^ k : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    by_cases hx : σ x = A * x
    · rw [(hconst k x).mpr hx, hx, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, hn1, one_mul]
    · have h1 : σ x = B * x := (hσ.1 x).resolve_left hx
      have h2 : σ (c ^ k * x) = B * (c ^ k * x) :=
        (hσ.1 _).resolve_left fun h => hx ((hconst k x).mp h)
      rw [h2, h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hn1, one_mul]
  let f : G ⧸ N → G ⧸ N := Quotient.lift (s := QuotientGroup.leftRel N)
    (fun x : G => ((σ x : G) : G ⧸ N)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
      have hn : a * (a⁻¹ * b) * a⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ hab' a
      have := hwd _ a hn
      rw [show a * (a⁻¹ * b) * a⁻¹ * a = b by group] at this
      exact this.symm)
  have hf : ∀ x : G, f (x : G ⧸ N) = (σ x : G ⧸ N) := fun x => rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := σ.surjective y
    exact ⟨x, hf x⟩
  let σ' : Perm (G ⧸ N) := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hσ' : ∀ x : G, σ' (x : G ⧸ N) = (σ x : G ⧸ N) := hf
  have hpow : ∀ (k : ℕ) (x : G), (σ' ^ k) (x : G ⧸ N) = ((σ ^ k) x : G ⧸ N) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ', Perm.mul_apply, ih, hσ', ← Perm.mul_apply, ← pow_succ']
  refine ⟨σ', ⟨fun y => ?_, fun y z => ?_⟩, hσ'⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rcases hσ.1 x with h | h
    · left
      rw [hσ', h, QuotientGroup.mk_mul]
    · right
      rw [hσ', h, QuotientGroup.mk_mul]
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := hσ.2 x w
    exact ⟨k, by rw [hpow, hk]⟩

/-- Rankin's parity at work: no extent when `A` and `c` have odd order and `|G|` is even. -/
theorem no_extent_of_odd [Fintype G] {A B : G} (hA : Odd (orderOf A))
    (hc : Odd (orderOf (A⁻¹ * B))) (hG : 2 ∣ Fintype.card G) (σ : Perm G) :
    ¬ IsExtent A B σ := by
  classical
  intro hσ
  obtain ⟨m, -, hs⟩ := rankin_sign hσ.1
  obtain ⟨t, ht⟩ := hc
  rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul, neg_one_sq, one_pow, one_pow,
    mul_one, sign_mulLeft_of_odd hA] at hs
  have he := extent_sign hσ
  rw [hs] at he
  obtain ⟨u, hu⟩ := hG
  rw [hu, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at he
  exact absurd he (by decide)

end Rankin

section Fibonacci

/-- The rank of apparition: `p ∣ F_n` exactly when `α(p) ∣ n`. -/
theorem dvd_fib_iff {p : ℕ} (hS : ∃ k, 0 < k ∧ p ∣ Nat.fib k) (n : ℕ) :
    p ∣ Nat.fib n ↔ fibRank p ∣ n := by
  obtain ⟨hpos, hdvd⟩ : 0 < fibRank p ∧ p ∣ Nat.fib (fibRank p) := Nat.sInf_mem hS
  constructor
  · intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact dvd_zero _
    · have hg : p ∣ Nat.fib (Nat.gcd n (fibRank p)) := by
        rw [Nat.fib_gcd]
        exact Nat.dvd_gcd hn hdvd
      have hle : fibRank p ≤ Nat.gcd n (fibRank p) :=
        Nat.sInf_le ⟨Nat.gcd_pos_of_pos_left _ hn0, hg⟩
      have heq : Nat.gcd n (fibRank p) = fibRank p :=
        le_antisymm (Nat.le_of_dvd hpos (Nat.gcd_dvd_right n _)) hle
      rw [← heq]
      exact Nat.gcd_dvd_left n _
  · intro h
    exact dvd_trans hdvd (Nat.fib_dvd _ _ h)

theorem dvd_two_mul_iff (a k : ℕ) :
    a ∣ 2 * k ↔ (if 2 ∣ a then a / 2 else a) ∣ k := by
  split_ifs with h
  · obtain ⟨b, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    exact Nat.mul_dvd_mul_iff_left (by norm_num)
  · have hc : Nat.Coprime a 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr h))
    exact hc.dvd_mul_left

theorem odd_of_not_four_dvd {a : ℕ} (h : ¬ 4 ∣ a) : Odd (if 2 ∣ a then a / 2 else a) := by
  split_ifs with h2
  · obtain ⟨b, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    rcases Nat.even_or_odd b with ⟨c, rfl⟩ | hb
    · exact absurd ⟨c, by ring⟩ h
    · exact hb
  · exact Nat.odd_iff.mpr (by omega)

end Fibonacci

section Leapfrog

open Matrix (SpecialLinearGroup)

variable {p : ℕ} [Fact p.Prime]

/-- The kick `K = K(1)` of the one-mode leapfrog on the dial `ZMod p`. -/
abbrev Kp (p : ℕ) : SpecialLinearGroup (Fin 2) (ZMod p) := (Step.kick (1 : ZMod p)).sl
/-- The move `M = M(-1)`. -/
abbrev Mp (p : ℕ) : SpecialLinearGroup (Fin 2) (ZMod p) := (Step.move (-1 : ZMod p)).sl

theorem stepC_mat : (((Kp p)⁻¹ * Mp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, -1; -1, 2] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  simp only [Kp, Mp, Step.coe_sl, Step.mat, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- `cᵏ = [[F₂ₖ₋₁, -F₂ₖ], [-F₂ₖ, F₂ₖ₊₁]]`. -/
theorem stepC_pow (k : ℕ) : ((((Kp p)⁻¹ * Mp p) ^ k : SpecialLinearGroup (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)) =
    !![(Nat.fib (2 * k + 1) : ZMod p) - Nat.fib (2 * k), -(Nat.fib (2 * k) : ZMod p);
      -(Nat.fib (2 * k) : ZMod p), Nat.fib (2 * k + 1)] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, stepC_mat, Matrix.mul_fin_two]
    have h2 : Nat.fib (2 * (k + 1)) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, Nat.fib_add_two]
    have h3 : Nat.fib (2 * (k + 1) + 1) = Nat.fib (2 * k + 1) + Nat.fib (2 * (k + 1)) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, Nat.fib_add_two,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    rw [h3, h2]
    push_cast
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem mem_center_iff_pm (g : SpecialLinearGroup (Fin 2) (ZMod p)) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) ↔
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hg⟩
    have h : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp h with h | h
    · left
      rw [← hg, show r = 1 by linear_combination h, map_one]
    · right
      rw [← hg, show r = -1 by linear_combination h, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, one_pow _, by rw [map_one, h]⟩
    · exact ⟨-1, by norm_num, by rw [map_neg, map_one, h]⟩

/-- `cᵏ` is `±1` exactly when `p ∣ F₂ₖ`. -/
theorem stepC_pow_mem_center_iff (k : ℕ) :
    ((Kp p)⁻¹ * Mp p) ^ k ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) ↔
      p ∣ Nat.fib (2 * k) := by
  rw [mem_center_iff_pm, stepC_pow]
  constructor
  · rintro (h | h)
    · have e := congrFun (congrFun h 0) 1
      simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, ne_eq, zero_ne_one, not_false_eq_true,
        Matrix.one_apply_ne, neg_eq_zero] at e
      exact (ZMod.natCast_eq_zero_iff _ _).mp e
    · have e := congrFun (congrFun h 0) 1
      simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.neg_apply, ne_eq, zero_ne_one,
        not_false_eq_true, Matrix.one_apply_ne, neg_zero, neg_eq_zero] at e
      exact (ZMod.natCast_eq_zero_iff _ _).mp e
  · intro h
    have h0 : (Nat.fib (2 * k) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    have hdet := Matrix.SpecialLinearGroup.det_coe (((Kp p)⁻¹ * Mp p) ^ k)
    rw [stepC_pow, Matrix.det_fin_two_of, h0] at hdet
    have hF : ((Nat.fib (2 * k + 1) : ZMod p) - 1) * ((Nat.fib (2 * k + 1) : ZMod p) + 1) = 0 := by
      linear_combination hdet
    rw [h0]
    rcases mul_eq_zero.mp hF with h1 | h1
    · left
      rw [show (Nat.fib (2 * k + 1) : ZMod p) = 1 by linear_combination h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · right
      rw [show (Nat.fib (2 * k + 1) : ZMod p) = -1 by linear_combination h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem Kp_pow (j : ℕ) : (((Kp p) ^ j : SpecialLinearGroup (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; (j : ZMod p), 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    simp only [Kp, Step.coe_sl, Step.mat, Matrix.mul_fin_two]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

theorem Kp_pow_mem_center_iff (hp2 : p ≠ 2) (j : ℕ) :
    Kp p ^ j ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) ↔ p ∣ j := by
  rw [mem_center_iff_pm, Kp_pow]
  constructor
  · rintro (h | h)
    · have e := congrFun (congrFun h 1) 0
      simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val_one, ne_eq, one_ne_zero, not_false_eq_true,
        Matrix.one_apply_ne] at e
      exact (ZMod.natCast_eq_zero_iff _ _).mp e
    · have e := congrFun (congrFun h 0) 0
      simp at e
      have := ZMod.neg_one_eq_one_iff.mp e.symm
      rcases this with h1 | h1
      · exact absurd h1 (Fact.out : p.Prime).one_lt.ne'
      · exact absurd h1 hp2
  · intro h
    left
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr h]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

theorem orderOf_Kp_PSL (hp2 : p ≠ 2) :
    orderOf ((Kp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = p := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Kp_pow_mem_center_iff hp2]
  · intro h
    rw [← pow_one (Kp p : SpecialLinearGroup (Fin 2) (ZMod p)), QuotientGroup.mk_pow, pow_one,
      QuotientGroup.eq_one_iff, ← pow_one (Kp p), Kp_pow_mem_center_iff hp2] at h
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one h)

theorem orderOf_Kp (hp2 : p ≠ 2) : orderOf (Kp p) = p := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_pow, Kp_pow,
      ZMod.natCast_self]
    ext i k
    fin_cases i <;> fin_cases k <;> simp
  · intro h
    have := (Kp_pow_mem_center_iff hp2 1).mp (by rw [pow_one, h]; exact Subgroup.one_mem _)
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one this)

theorem two_dvd_card_SL (hp2 : p ≠ 2) :
    2 ∣ Fintype.card (SpecialLinearGroup (Fin 2) (ZMod p)) := by
  let g : SpecialLinearGroup (Fin 2) (ZMod p) := ⟨-1, by simp [Matrix.det_neg]⟩
  have hg : orderOf g = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow]
      simp [g]
    · intro h
      have e := congrFun (congrFun (congrArg Subtype.val h) 0) 0
      simp only [Fin.isValue, Matrix.neg_apply, Matrix.one_apply_eq,
        Matrix.SpecialLinearGroup.coe_one, g] at e
      rcases ZMod.neg_one_eq_one_iff.mp e with h1 | h1
      · exact (Fact.out : p.Prime).one_lt.ne' h1
      · exact hp2 h1
  have := orderOf_dvd_card (x := g)
  rwa [hg] at this

theorem two_dvd_card_PSL [Fintype (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))] :
    2 ∣ Fintype.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  let S : SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hS2 : S ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [mem_center_iff_pm]
    right
    rw [Matrix.SpecialLinearGroup.coe_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hS1 : S ∉ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [mem_center_iff_pm]
    rintro (h | h) <;>
    · have e := congrFun (congrFun h 0) 0
      simp [S] at e
  have hg : orderOf (S : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hS2
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hS1
  have := orderOf_dvd_card (x := (S : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
  rwa [hg] at this

/-- The rank of apparition exists: `c` has finite order, and `c^(ord c) = 1`. -/
theorem exists_fib_dvd : ∃ k, 0 < k ∧ p ∣ Nat.fib k :=
  ⟨2 * orderOf ((Kp p)⁻¹ * Mp p), by have := orderOf_pos ((Kp p)⁻¹ * Mp p); omega,
    (stepC_pow_mem_center_iff _).mp (by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _)⟩

/-- The Fibonacci rule on `PSL(2, p)`. -/
theorem fibonacci_PSL (hp2 : p ≠ 2)
    (σ : Perm (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hσ : IsExtent ((Kp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      ((Mp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) σ) :
    4 ∣ fibRank p := by
  classical
  let _ : Fintype (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := Fintype.ofFinite _
  by_contra h4
  have hpow : ∀ j : ℕ, ((((Kp p)⁻¹ * Mp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) ^ j = 1 ↔
      (if 2 ∣ fibRank p then fibRank p / 2 else fibRank p) ∣ j := by
    intro j
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, stepC_pow_mem_center_iff,
      dvd_fib_iff exists_fib_dvd, dvd_two_mul_iff]
  have hord : orderOf ((((Kp p)⁻¹ * Mp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) =
      (if 2 ∣ fibRank p then fibRank p / 2 else fibRank p) :=
    Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((hpow _).mpr dvd_rfl))
      ((hpow _).mp (pow_orderOf_eq_one _))
  refine no_extent_of_odd (B := ((Mp p : SpecialLinearGroup (Fin 2) (ZMod p)) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) ?_ ?_ two_dvd_card_PSL σ hσ
  · rw [orderOf_Kp_PSL hp2]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hord]
    exact odd_of_not_four_dvd h4

/-- The Fibonacci rule on `SL(2, p)`. -/
theorem fibonacci_SL (hp2 : p ≠ 2) (σ : Perm (SpecialLinearGroup (Fin 2) (ZMod p)))
    (hσ : IsExtent (Kp p) (Mp p) σ) : 4 ∣ fibRank p := by
  classical
  by_contra h4
  have hk₀ : ((Kp p)⁻¹ * Mp p) ^ (if 2 ∣ fibRank p then fibRank p / 2 else fibRank p) ∈
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [stepC_pow_mem_center_iff, dvd_fib_iff exists_fib_dvd, dvd_two_mul_iff]
  rcases (mem_center_iff_pm _).mp hk₀ with h1 | h1
  · have hc1 : ((Kp p)⁻¹ * Mp p) ^ (if 2 ∣ fibRank p then fibRank p / 2 else fibRank p) = 1 :=
      Subtype.ext h1
    refine no_extent_of_odd ?_ ?_ (two_dvd_card_SL hp2) σ hσ
    · rw [orderOf_Kp hp2]
      exact (Fact.out : p.Prime).odd_of_ne_two hp2
    · exact (odd_of_not_four_dvd h4).of_dvd_nat (orderOf_dvd_of_pow_eq_one hc1)
  · have hN : Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) ≤
        Subgroup.zpowers ((Kp p)⁻¹ * Mp p) := by
      intro g hg
      rcases (mem_center_iff_pm g).mp hg with h | h
      · have : g = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _
      · have : g = ((Kp p)⁻¹ * Mp p) ^ (if 2 ∣ fibRank p then fibRank p / 2 else fibRank p) :=
          Subtype.ext (by rw [h, h1])
        rw [this]
        exact Subgroup.npow_mem_zpowers _ _
    obtain ⟨σ', hσ', -⟩ := extent_lift hN hσ
    exact h4 (fibonacci_PSL hp2 σ' hσ')

end Leapfrog

end Artform.Scores.Bells

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

/-- **T15** (Rankin's parity). -/
@[ledger "T15"]
theorem rankinParity : Statement.rankinParity := fun _ _ _ _ _ _ _ hstep =>
  ⟨Bells.choice_link hstep, Bells.rankin_sign hstep, Bells.extent_sign⟩

/-- **T15** (the lifting lemma). -/
@[ledger "T15"]
theorem extentLifting : Statement.extentLifting := fun _ _ _ _ _ _ _ hN _ hσ =>
  Bells.extent_lift hN hσ

/-- **T15** (the Fibonacci rule). -/
@[ledger "T15"]
theorem fibonacciRule : Statement.fibonacciRule := fun p hp hp2 => by
  have := Fact.mk hp
  exact ⟨fun σ hσ => Bells.fibonacci_SL hp2 σ hσ, fun σ hσ => Bells.fibonacci_PSL hp2 σ hσ⟩

/-! ## Non-vacuity

- The Klein four-group rings: `1 → a → ab → b → 1`. Its sign is that of a 4-cycle, and it lifts
  to an extent of the quotient by `⟨c⟩ = {1, ab}`.
- `α(5) = 5`, so neither `SL(2, 5)`, the binary icosahedral group, nor `PSL(2, 5)` has a forward
  extent under `K` and `M`. `α(7) = 8` passes the rule.
-/

/-- The Klein four-group, `Z/2 × Z/2` written multiplicatively. -/
abbrev Klein := Multiplicative (ZMod 2 × ZMod 2)

/-- The step `A = a`. -/
def kleinA : Klein := Multiplicative.ofAdd (1, 0)

/-- The step `B = b`. -/
def kleinB : Klein := Multiplicative.ofAdd (0, 1)

/-- The extent `1 → a → ab → b → 1`. -/
def kleinRun : Equiv.Perm Klein := List.formPerm [1, kleinA, kleinA * kleinB, kleinB]

theorem kleinRun_isExtent : Bells.IsExtent kleinA kleinB kleinRun := by
  refine ⟨by decide, fun x y => ?_⟩
  have h : ∀ x y : Klein, ∃ k ∈ Finset.range 4, (kleinRun ^ k) x = y := by decide
  obtain ⟨k, -, hk⟩ := h x y
  exact ⟨k, hk⟩

/-- Rankin's parity on the Klein extent: its sign is `-1`, that of a 4-cycle. -/
example : Equiv.Perm.sign kleinRun = -1 := by
  rw [(rankinParity Klein kleinA kleinB kleinRun kleinRun_isExtent.1).2.2 kleinRun_isExtent]
  decide

/-- `⟨c⟩ = {1, ab}` is normal, and the Klein extent lifts to an extent of the quotient. -/
example : ∃ σ' : Equiv.Perm (Klein ⧸ Subgroup.zpowers (kleinA⁻¹ * kleinB)),
    Bells.IsExtent (kleinA : Klein ⧸ Subgroup.zpowers (kleinA⁻¹ * kleinB))
      (kleinB : Klein ⧸ Subgroup.zpowers (kleinA⁻¹ * kleinB)) σ' := by
  have : (Subgroup.zpowers (kleinA⁻¹ * kleinB)).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨σ', h, -⟩ := extentLifting Klein kleinA kleinB _ le_rfl kleinRun kleinRun_isExtent
  exact ⟨σ', h⟩

theorem fibRank_five : Bells.fibRank 5 = 5 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by decide⟩
  · refine le_csInf ⟨5, by norm_num, by decide⟩ ?_
    rintro k ⟨hk, hd⟩
    by_contra h
    push Not at h
    interval_cases k <;> revert hd <;> decide

theorem fibRank_seven : Bells.fibRank 7 = 8 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by decide⟩
  · refine le_csInf ⟨8, by norm_num, by decide⟩ ?_
    rintro k ⟨hk, hd⟩
    by_contra h
    push Not at h
    interval_cases k <;> revert hd <;> decide

/-- `SL(2, 5)`, the binary icosahedral group, has no forward extent under `K` and `M`, nor has
`PSL(2, 5)`: `α(5) = 5`. For `SL(2, 5)` the proof passes through the lifting lemma, since
`c⁵ = -1` there. -/
example : (∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod 5)),
      ¬ Bells.IsExtent (Step.kick (1 : ZMod 5)).sl (Step.move (-1 : ZMod 5)).sl σ) ∧
    ∀ σ : Equiv.Perm (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)),
      ¬ Bells.IsExtent
        ((Step.kick (1 : ZMod 5)).sl : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))
        ((Step.move (-1 : ZMod 5)).sl : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))
        σ := by
  obtain ⟨h1, h2⟩ := fibonacciRule 5 (by norm_num) (by norm_num)
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have := h1 σ hσ
    rw [fibRank_five] at this
    omega
  · have := h2 σ hσ
    rw [fibRank_five] at this
    omega

/-- `α(7) = 8` passes the rule, and the ledger found forward extents of `SL(2, 7)`. -/
example : 4 ∣ Bells.fibRank 7 := by
  rw [fibRank_seven]
  norm_num

end Artform.Scores
