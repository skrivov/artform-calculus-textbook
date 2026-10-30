import ArtformScores.Statements

/-!
# The bells

T15 of the algebra of scores: change ringing as a calculus (the ledger's findings 042-043).
The artform has `N` positions, and its values are the rows, the arrangements of the bells.
- **Every method is light** (Theorem S5.2). A change is an involution, so the painted rows
  obey `u(t + 1) + u(t - 1) = (P_t + P_(t-1)) u(t)`. Every position is paired by each of two
  changes with a neighbour or with itself, so the sum cuts the row into mirror boxes and
  dodges.
- **Plain hunt is light in a mirror box** (Theorem S5.1). Every position below the last is
  paired with the next one by exactly one of `X` and `Y`, so `P_X + P_Y = S_mirror`. A bell's
  point on a circle of `2N` places advances one place per change, and the circle folded onto
  the box is the bell's path: a light ray between two mirrors.
- **The modes** of the mirror box are `v_k(i) = cos(πk(2i + 1)/(2N))`, with the eigenvalues
  `2 cos(πk/N)`, distinct for `0 ≤ k < N`, so an eigenbasis.
- **The presentation** (Moore 1897). Coxeter's rules present `S_(n+1)` on the swaps of
  neighbours. The swaps satisfy the rules, and generate. In the presented group the descending
  runs `s_m ⋯ s_k` are coset representatives of the subgroup on `s_0, …, s_(m-1)`, so it has
  at most `(n + 1)!` elements, and the realizer onto `S_(n+1)` is one to one.
-/

namespace Artform.Scores.Bells

open Equiv

section Proofs

variable {N : ℕ} {R : Type*}

theorem IsChange.symm_apply {π : Perm (Fin N)} (h : IsChange π) (i : Fin N) :
    π.symm i = π i :=
  (Equiv.symm_apply_eq π).mpr (h i).1.symm

theorem act_act {π : Perm (Fin N)} (h : IsChange π) (u : Fin N → R) : act π (act π u) = u := by
  funext i
  simp [act, (h i).1]

theorem paint_row_succ (π : ℕ → Perm (Fin N)) (t : ℕ) (hπ : IsChange (π t)) (f : Fin N → R) :
    paint f (row π (t + 1)) = act (π t) (paint f (row π t)) := by
  funext i
  simp [paint, act, row, Perm.mul_def, hπ.symm_apply]

theorem method_law [Add R] (π : ℕ → Perm (Fin N)) (hπ : ∀ t, IsChange (π t)) (f : Fin N → R)
    (t : ℕ) :
    paint f (row π (t + 2)) + paint f (row π t) =
      act (π (t + 1)) (paint f (row π (t + 1))) + act (π t) (paint f (row π (t + 1))) := by
  rw [paint_row_succ π (t + 1) (hπ _), paint_row_succ π t (hπ t), act_act (hπ t)]

theorem boxes_of_not_dodge [AddCommMagma R] {A B : Perm (Fin N)} (hA : IsChange A) (hB : IsChange B)
    (u : Fin N → R) (i : Fin N) (hd : ¬ IsDodge A B i) :
    act A u i + act B u i = boxSum A B u i ∧
      ((boxLeft A B i = i ∨ boxRight A B i = i) → A i = i ∨ B i = i) := by
  obtain ⟨-, hA1, hA2⟩ := hA i
  obtain ⟨-, hB1, hB2⟩ := hB i
  have hd' : (A i : ℕ) ≠ B i ∨ (A i : ℕ) = i := by
    by_contra h
    push Not at h
    exact hd ⟨Fin.ext h.1, fun h' => h.2 (congrArg Fin.val h')⟩
  have key : (A i = boxLeft A B i ∧ B i = boxRight A B i) ∨
      (A i = boxRight A B i ∧ B i = boxLeft A B i) := by
    unfold boxLeft boxRight
    split_ifs <;> first
      | (left; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
      | (right; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
  refine ⟨?_, ?_⟩
  · rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [act, boxSum, ← h1, ← h2]
    · simp only [act, boxSum, ← h1, ← h2]
      exact add_comm _ _
  · intro hw
    unfold boxLeft boxRight at hw
    by_contra hp
    push Not at hp
    have hp1 : (A i : ℕ) ≠ i := fun h => hp.1 (Fin.ext h)
    have hp2 : (B i : ℕ) ≠ i := fun h => hp.2 (Fin.ext h)
    rcases hw with hw | hw <;> split_ifs at hw <;>
      first
        | exact hp.1 hw
        | exact hp.2 hw
        | omega

theorem boxes_of_dodge [Add R] {A B : Perm (Fin N)} (hA : IsChange A) (hB : IsChange B)
    (u : Fin N → R) (i : Fin N) (hd : IsDodge A B i) :
    act A u i + act B u i = u (A i) + u (A i) ∧ A (A i) = i ∧ B (A i) = i := by
  refine ⟨by simp [act, hd.1], (hA i).1, ?_⟩
  rw [hd.1]
  exact (hB i).1

@[simp] theorem huntChange_val (e : ℕ) (i : Fin N) : (huntChange N e i : ℕ) = partner N e i :=
  rfl

theorem hunt_mirror [AddCommMonoid R] (u : Fin N → R) :
    act (huntX N) u + act (huntY N) u = mirror u := by
  funext i
  have hi := i.2
  simp only [Pi.add_apply, act, mirror, huntX, huntY]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [add_comm]
    congr 1 <;> congr 1 <;> apply Fin.ext <;> rw [huntChange_val] <;> (try dsimp only) <;>
      unfold partner <;> split_ifs <;> omega
  · congr 1 <;> congr 1 <;> apply Fin.ext <;> rw [huntChange_val] <;> (try dsimp only) <;>
      unfold partner <;> split_ifs <;> omega

theorem huntChange_isChange (e : ℕ) : IsChange (huntChange N e) := by
  intro i
  have hi := i.2
  refine ⟨Fin.ext ?_, ?_, ?_⟩ <;> simp only [huntChange_val] <;> unfold partner <;>
    split_ifs <;> omega

theorem huntChange_mod (e : ℕ) : huntChange N e = huntChange N (e % 2) :=
  Equiv.ext fun i => Fin.ext (by simp [partner])

/-- The painted rows of plain hunt obey the tick in the mirror box. -/
theorem hunt_law [AddCommMonoid R] (f : Fin N → R) (t : ℕ) :
    paint f (hunt N (t + 2)) + paint f (hunt N t) = mirror (paint f (hunt N (t + 1))) := by
  rw [hunt, method_law _ (fun t => huntChange_isChange t), ← hunt_mirror, huntX, huntY,
    huntChange_mod (t + 1), huntChange_mod t]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [h, show (t + 1) % 2 = 1 by omega, add_comm]
  · rw [h, show (t + 1) % 2 = 0 by omega]

theorem mod_add_small {m r j : ℕ} (hr : r < m) (hj : j ≤ m) :
    (r + j) % m = if r + j < m then r + j else r + j - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem add_mod_two_mul (hN : 0 < N) (k j : ℕ) (hj : j ≤ 2 * N) :
    (k + j) % (2 * N) = if k % (2 * N) + j < 2 * N then k % (2 * N) + j
      else k % (2 * N) + j - 2 * N := by
  rw [← Nat.mod_add_mod]
  exact mod_add_small (Nat.mod_lt k (by omega)) hj

theorem hunt_succ_apply (t : ℕ) (b : Fin N) :
    hunt N (t + 1) b = huntChange N t (hunt N t b) := by
  simp [hunt, row, Perm.mul_apply]

theorem start_lt {b : ℕ} (hb : b < N) : start N b < 2 * N := by
  unfold start; split_ifs <;> omega

theorem start_even (b : ℕ) : start N b % 2 = 0 := by
  unfold start; split_ifs <;> omega

theorem partner_fold (hN : 0 < N) (k : ℕ) : partner N k (fold N k) = fold N (k + 1) := by
  have hpar : k % (2 * N) % 2 = k % 2 := Nat.mod_mod_of_dvd k (Dvd.intro N rfl)
  have hr := Nat.mod_lt k (show 0 < 2 * N by omega)
  unfold fold partner
  rw [add_mod_two_mul hN k 1 (by omega), ← hpar]
  generalize k % (2 * N) = r at *
  split_ifs <;> omega

/-- The explicit positions: the bell `b` is at `fold N (start N b + t)` after `t` changes. -/
theorem hunt_apply (t : ℕ) (b : Fin N) : (hunt N t b : ℕ) = fold N (start N b + t) := by
  have hb := b.2
  have hN : 0 < N := by omega
  induction t with
  | zero =>
    have hs := start_lt (N := N) hb
    simp only [hunt, row, Perm.one_apply, add_zero]
    unfold fold
    rw [Nat.mod_eq_of_lt hs]
    unfold start at hs ⊢
    split_ifs <;> omega
  | succ t ih =>
    rw [hunt_succ_apply]
    change partner N t (hunt N t b) = _
    have hpar : (start N b + t) % 2 = t % 2 := by
      have := start_even (N := N) b
      omega
    have hp : partner N t (hunt N t b) = partner N (start N b + t) (hunt N t b) := by
      simp only [partner, hpar]
    rw [hp, ih, partner_fold hN, add_assoc]

theorem fold_mod (k : ℕ) : fold N (k % (2 * N)) = fold N k := by
  simp [fold]

/-- The plain course: for `N ≥ 3` the rows repeat after `2N` changes, and not before. -/
theorem hunt_eq_iff (hN : 3 ≤ N) (s t : ℕ) : hunt N s = hunt N t ↔ s % (2 * N) = t % (2 * N) := by
  have h2N : 0 < 2 * N := by omega
  constructor
  · intro h
    have h0 := congrArg (fun σ : Perm (Fin N) => (σ ⟨0, by omega⟩ : ℕ)) h
    have h1 := congrArg (fun σ : Perm (Fin N) => (σ ⟨1, by omega⟩ : ℕ)) h
    simp only [hunt_apply] at h0 h1
    have hs0 : start N 0 = 0 := by simp [start]
    have hs1 : start N 1 = 2 * N - 2 := by simp [start]; omega
    rw [hs0, zero_add, zero_add] at h0
    rw [hs1, add_comm, add_comm (2 * N - 2)] at h1
    unfold fold at h0 h1
    rw [add_mod_two_mul (by omega) s _ (by omega), add_mod_two_mul (by omega) t _ (by omega)] at h1
    have hs := Nat.mod_lt s h2N
    have ht := Nat.mod_lt t h2N
    generalize s % (2 * N) = a at *
    generalize t % (2 * N) = c at *
    split_ifs at h0 h1 <;> omega
  · intro h
    ext b
    rw [hunt_apply, hunt_apply, ← fold_mod, ← fold_mod (start N b + t), Nat.add_mod, h,
      ← Nat.add_mod]

/-- A bell moves one place per change, or lies at a wall. -/
theorem hunt_step (t : ℕ) (b : Fin N) :
    (hunt N (t + 1) b : ℕ) + 1 = hunt N t b ∨ (hunt N t b : ℕ) + 1 = hunt N (t + 1) b ∨
      (hunt N (t + 1) b = hunt N t b ∧ ((hunt N t b : ℕ) = 0 ∨ (hunt N t b : ℕ) + 1 = N)) := by
  have hN : 0 < N := by have := b.2; omega
  rw [Fin.ext_iff, hunt_apply, hunt_apply, ← add_assoc]
  have hr := Nat.mod_lt (start N b + t) (show 0 < 2 * N by omega)
  unfold fold
  rw [add_mod_two_mul hN _ 1 (by omega)]
  generalize (start N b + t) % (2 * N) = r at *
  split_ifs <;> omega

/-- A bell lies for one change only: for `N ≥ 2` it never makes a place twice running. -/
theorem hunt_lies_once (hN : 2 ≤ N) (t : ℕ) (b : Fin N) (h : hunt N (t + 1) b = hunt N t b) :
    hunt N (t + 2) b ≠ hunt N (t + 1) b := by
  rw [Fin.ext_iff, hunt_apply, hunt_apply, ← add_assoc] at h
  rw [Ne, Fin.ext_iff, hunt_apply, hunt_apply, ← add_assoc, ← add_assoc]
  have hr := Nat.mod_lt (start N b + t) (show 0 < 2 * N by omega)
  unfold fold at h ⊢
  rw [add_mod_two_mul (by omega) (start N b + t) 1 (by omega)] at h ⊢
  rw [add_mod_two_mul (by omega) (start N b + t) 2 (by omega)]
  generalize (start N b + t) % (2 * N) = r at *
  split_ifs at h ⊢ <;> omega

theorem mirror_smul (c : ℝ) (u : Fin N → ℝ) : mirror (c • u) = c • mirror u := by
  funext i
  simp [mirror, mul_add]

theorem mirror_add (u v : Fin N → ℝ) : mirror (u + v) = mirror u + mirror v := by
  funext i
  simp only [mirror, Pi.add_apply]
  abel

theorem cos_pi_mul_sub_eq_add (k : ℕ) (x : ℝ) :
    Real.cos (k * Real.pi - x) = Real.cos (k * Real.pi + x) := by
  rw [Real.cos_sub, Real.cos_add, Real.sin_nat_mul_pi]
  ring

/-- The modes of the mirror box: `S_mirror v_k = 2 cos(πk/N) v_k`. -/
theorem mirror_mode (k : ℕ) : mirror (mode N k) = (2 * Real.cos (Real.pi * k / N)) • mode N k := by
  funext i
  have hi := i.2
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [mirror, mode, Pi.smul_apply, smul_eq_mul]
  set x : ℝ := Real.pi * k * (2 * i + 1) / (2 * N) with hx
  set φ : ℝ := Real.pi * k / N with hφ
  have hdown : Real.cos (Real.pi * k * (2 * ((i - 1 : ℕ) : ℝ) + 1) / (2 * N)) =
      Real.cos (x - φ) := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0] at hx ⊢
      rw [hx, hφ, ← Real.cos_neg]
      congr 1
      field_simp
      push_cast
      ring
    · rw [Nat.cast_sub h0, hx, hφ]
      congr 1
      field_simp
      push_cast
      ring
  have hup : Real.cos (Real.pi * k * (2 * ((min (i + 1) (N - 1) : ℕ) : ℝ) + 1) / (2 * N)) =
      Real.cos (x + φ) := by
    by_cases h : (i : ℕ) + 1 < N
    · rw [min_eq_left (by omega), hx, hφ]
      congr 1
      field_simp
      push_cast
      ring
    · have hm : min ((i : ℕ) + 1) (N - 1) = i := by omega
      have hiN : ((i : ℕ) : ℝ) = N - 1 := by
        have h' : (i : ℕ) + 1 = N := by omega
        have : ((i : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast h'
        linarith
      rw [hm, hx, hφ, hiN]
      have e1 : Real.pi * k * (2 * ((N : ℝ) - 1) + 1) / (2 * N) =
          k * Real.pi - Real.pi * k / (2 * N) := by field_simp; ring
      have e2 : Real.pi * k * (2 * ((N : ℝ) - 1) + 1) / (2 * N) + Real.pi * k / N =
          k * Real.pi + Real.pi * k / (2 * N) := by field_simp; ring
      rw [e2, e1, cos_pi_mul_sub_eq_add]
  rw [hdown, hup, Real.cos_sub, Real.cos_add]
  ring

/-- The mirror box as a linear map. -/
noncomputable def mirrorEnd (N : ℕ) : Module.End ℝ (Fin N → ℝ) where
  toFun := mirror
  map_add' := mirror_add
  map_smul' := mirror_smul

theorem mode_ne_zero {k : ℕ} (hk : k < N) : mode N k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  simp only [mode, Pi.zero_apply] at h0
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (k : ℝ) < N := by exact_mod_cast hk
  refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne' h0
  · have : 0 ≤ Real.pi * k * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * N) := by positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [Real.pi_pos]

theorem eigenvalue_injective :
    Function.Injective fun k : Fin N => 2 * Real.cos (Real.pi * (k : ℕ) / N) := by
  intro a b h
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := a.2; omega)
  have ha : ((a : ℕ) : ℝ) ≤ N := by exact_mod_cast a.2.le
  have hb : ((b : ℕ) : ℝ) ≤ N := by exact_mod_cast b.2.le
  have hmem : ∀ c : ℝ, 0 ≤ c → c ≤ N → Real.pi * c / N ∈ Set.Icc 0 Real.pi := fun c h0 h1 =>
    ⟨by positivity, by rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos]⟩
  have hc : Real.cos (Real.pi * (a : ℕ) / N) = Real.cos (Real.pi * (b : ℕ) / N) := by
    simpa using h
  have := Real.injOn_cos (hmem _ (Nat.cast_nonneg _) ha) (hmem _ (Nat.cast_nonneg _) hb) hc
  have : ((a : ℕ) : ℝ) = (b : ℕ) := by
    field_simp at this
    nlinarith [Real.pi_pos]
  exact Fin.ext (by exact_mod_cast this)

/-- The `N` modes are independent: an eigenbasis of the mirror box. -/
theorem modes_independent : LinearIndependent ℝ fun k : Fin N => mode N k :=
  (mirrorEnd N).eigenvectors_linearIndependent' _ eigenvalue_injective _ fun k =>
    Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (mirror_mode k), mode_ne_zero k.2⟩

/-- The mirror box has no eigenvalue but the `2 cos(πk/N)`, `0 ≤ k < N`. -/
theorem mirror_spectrum {μ : ℝ} {v : Fin N → ℝ} (hv : v ≠ 0) (h : mirror v = μ • v) :
    ∃ k < N, μ = 2 * Real.cos (Real.pi * k / N) := by
  by_contra hne
  push Not at hne
  let μs : Option (Fin N) → ℝ := fun o => o.elim μ fun k => 2 * Real.cos (Real.pi * (k : ℕ) / N)
  let vs : Option (Fin N) → Fin N → ℝ := fun o => o.elim v fun k => mode N k
  have hinj : Function.Injective μs := by
    rintro (_ | a) (_ | b) hab <;> simp only [μs, Option.elim] at hab
    · rfl
    · exact absurd hab (hne b b.2)
    · exact absurd hab.symm (hne a a.2)
    · rw [eigenvalue_injective hab]
  have hli := (mirrorEnd N).eigenvectors_linearIndependent' μs hinj vs (by
    rintro (_ | k)
    · exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr h, hv⟩
    · exact Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (mirror_mode k), mode_ne_zero k.2⟩)
  have := hli.fintype_card_le_finrank
  simp at this

/-- The tick turns the mode `k` by `πk/N` per change, and `2N` changes are a period. -/
theorem turn_law (k : ℕ) (A B : ℝ) (t : ℕ) :
    turn N k A B (t + 2) + turn N k A B t = mirror (turn N k A B (t + 1)) ∧
      turn N k A B (t + 2 * N) = turn N k A B t := by
  set φ : ℝ := Real.pi * k / N with hφ
  constructor
  · rw [turn, turn, turn, mirror_smul, mirror_mode, smul_smul, ← add_smul]
    congr 1
    have e2 : φ * ((t + 2 : ℕ) : ℝ) = φ * ((t + 1 : ℕ) : ℝ) + φ := by push_cast; ring
    have e0 : φ * (t : ℝ) = φ * ((t + 1 : ℕ) : ℝ) - φ := by push_cast; ring
    rw [e2, e0, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub]
    ring
  · rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    have e : φ * ((t + 2 * N : ℕ) : ℝ) = φ * t + k * (2 * Real.pi) := by
      rw [hφ]; push_cast; field_simp
    rw [turn, turn, e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

end Proofs

section Coxeter

theorem swap_three {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : (swap a b * swap b c) ^ 3 = 1 ∧ (swap b c * swap a b) ^ 3 = 1 := by
  have h1 : swap a b * swap b c * swap a b = swap a c := by
    have := swap_apply_apply (swap a b) b c
    rw [swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_inv] at this
    exact this.symm
  have h2 : swap b c * swap a b * swap b c = swap a c := by
    have := swap_apply_apply (swap b c) a b
    rw [swap_apply_left, swap_apply_of_ne_of_ne hab hac, swap_inv] at this
    exact this.symm
  constructor
  · calc (swap a b * swap b c) ^ 3
        = (swap a b * swap b c * swap a b) * (swap b c * swap a b * swap b c) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [h1, h2, swap_mul_self]
  · calc (swap b c * swap a b) ^ 3
        = (swap b c * swap a b * swap b c) * (swap a b * swap b c * swap a b) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [h1, h2, swap_mul_self]

theorem swap_disjoint {α : Type*} [DecidableEq α] {a b c d : α} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : (swap a b * swap c d) ^ 2 = 1 := by
  have h : swap c d * swap a b * swap c d = swap a b := by
    have := swap_apply_apply (swap c d) a b
    rw [swap_apply_of_ne_of_ne hac had, swap_apply_of_ne_of_ne hbc hbd, swap_inv] at this
    exact this.symm
  calc (swap a b * swap c d) ^ 2 = swap a b * (swap c d * swap a b * swap c d) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h, swap_mul_self]

variable {n : ℕ}

theorem A_apply (i j : Fin n) : CoxeterMatrix.A n i j =
    if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 := rfl

/-- The rules hold: the swaps of neighbours satisfy Coxeter's relations of type `A`. -/
theorem law_relation (i j : Fin n) :
    (swap i.castSucc i.succ * swap j.castSucc j.succ) ^ (CoxeterMatrix.A n i j) = 1 := by
  rw [A_apply]
  split_ifs with h1 h2
  · subst h1; rw [pow_one, swap_mul_self]
  · have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    rcases h2 with h2 | h2
    · have hb : i.castSucc = j.succ := Fin.ext (by simp; omega)
      rw [hb]
      exact (swap_three (a := j.castSucc) (b := j.succ) (c := i.succ)
        (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega))).2
    · have hb : j.castSucc = i.succ := Fin.ext (by simp; omega)
      rw [hb]
      exact (swap_three (a := i.castSucc) (b := i.succ) (c := j.succ)
        (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega))).1
  · have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    exact swap_disjoint (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))

variable (n) in
/-- The simple reflection `s_j` of the Coxeter group of type `A`, or `1` past the last. -/
def sn (j : ℕ) : (CoxeterMatrix.A n).Group :=
  if h : j < n then (CoxeterMatrix.A n).toCoxeterSystem.simple ⟨j, h⟩ else 1

theorem sn_mul_self (j : ℕ) : sn n j * sn n j = 1 := by
  unfold sn
  split_ifs with h
  · exact (CoxeterMatrix.A n).toCoxeterSystem.simple_mul_simple_self _
  · exact mul_one 1

theorem sn_comm {i j : ℕ} (h : i + 2 ≤ j ∨ j + 2 ≤ i) : sn n i * sn n j = sn n j * sn n i := by
  unfold sn
  split_ifs with hi hj hj
  · set cs := (CoxeterMatrix.A n).toCoxeterSystem
    have hp := cs.simple_mul_simple_pow ⟨i, hi⟩ ⟨j, hj⟩
    rw [A_apply, ite_eq_right (by rw [Fin.mk.injEq]; omega),
      ite_eq_right (show ¬ (j + 1 = i ∨ i + 1 = j) by omega), pow_two] at hp
    rw [eq_inv_of_mul_eq_one_left hp, mul_inv_rev, cs.inv_simple, cs.inv_simple]
  all_goals simp

theorem sn_braid {j : ℕ} (h : j + 1 < n) :
    sn n j * sn n (j + 1) * sn n j = sn n (j + 1) * sn n j * sn n (j + 1) := by
  have hj : j < n := by omega
  unfold sn
  rw [dite_eq_left hj, dite_eq_left h]
  set cs := (CoxeterMatrix.A n).toCoxeterSystem
  have hp := cs.simple_mul_simple_pow ⟨j, hj⟩ ⟨j + 1, h⟩
  rw [A_apply, ite_eq_right (by rw [Fin.mk.injEq]; omega),
    ite_eq_left (show j + 1 + 1 = j ∨ j + 1 = j + 1 from Or.inr rfl)] at hp
  have h3 : (cs.simple ⟨j, hj⟩ * cs.simple ⟨j + 1, h⟩ * cs.simple ⟨j, hj⟩) *
      (cs.simple ⟨j + 1, h⟩ * cs.simple ⟨j, hj⟩ * cs.simple ⟨j + 1, h⟩) = 1 := by
    rw [← hp]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h3]
  simp only [mul_inv_rev, cs.inv_simple, mul_assoc]

variable (n) in
/-- The descending run `s_(a-1) ⋯ s_(k+1) s_k`, or `1` when `a ≤ k`. -/
def run : ℕ → ℕ → (CoxeterMatrix.A n).Group
  | 0, _ => 1
  | a + 1, k => if k ≤ a then sn n a * run a k else 1

theorem run_of_le {a k : ℕ} (h : a ≤ k) : run n a k = 1 := by
  cases a with
  | zero => rfl
  | succ a => simp only [run]; rw [ite_eq_right (by omega)]

theorem run_succ {a k : ℕ} (h : k ≤ a) : run n (a + 1) k = sn n a * run n a k := by
  simp only [run]; rw [ite_eq_left h]

theorem run_mul_sn {a k : ℕ} (h : k < a) : run n a (k + 1) * sn n k = run n a k := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [run_succ (by omega), run_succ (by omega), mul_assoc, ih h']
    · subst h'
      rw [run_of_le le_rfl, one_mul, run_succ le_rfl, run_of_le le_rfl, mul_one]

theorem run_comm {a k i : ℕ} (h : i + 2 ≤ k ∨ a + 1 ≤ i) :
    run n a k * sn n i = sn n i * run n a k := by
  induction a with
  | zero => simp [run]
  | succ a ih =>
    by_cases hk : k ≤ a
    · rw [run_succ hk, mul_assoc, ih (by omega), ← mul_assoc, sn_comm (by omega), mul_assoc]
    · rw [run_of_le (by omega), one_mul, mul_one]

theorem run_braid {a k i : ℕ} (hk : k < i) (hia : i < a) (ha : a ≤ n) :
    run n a k * sn n i = sn n (i - 1) * run n a k := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hia with h' | h'
    · rw [run_succ (by omega), mul_assoc, ih h' (by omega), ← mul_assoc, sn_comm (by omega),
        mul_assoc]
    · subst h'
      obtain ⟨a', rfl⟩ : ∃ a', i = a' + 1 := ⟨i - 1, by omega⟩
      rw [run_succ (by omega), run_succ (by omega), Nat.add_sub_cancel, mul_assoc, mul_assoc,
        run_comm (Or.inr le_rfl)]
      simp only [← mul_assoc]
      rw [sn_braid (by omega)]

/-- Every word in `s_0, …, s_m` is `h · run (m + 1) k`, with `h` a word in `s_0, …, s_(m-1)`:
the `m + 2` runs are coset representatives. -/
theorem coset_step {m : ℕ} (hm : m < n) (w : List ℕ) (hw : ∀ j ∈ w, j < m + 1) :
    ∃ v : List ℕ, (∀ j ∈ v, j < m) ∧ ∃ k ≤ m + 1,
      (w.map (sn n)).prod = (v.map (sn n)).prod * run n (m + 1) k := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], by simp, m + 1, le_rfl, by simp [run_of_le]⟩
  | append_singleton w i ih =>
    obtain ⟨v, hv, k, hk, he⟩ := ih (fun j hj => hw j (List.mem_append_left _ hj))
    have hi : i < m + 1 := hw i (by simp)
    rw [List.map_append, List.prod_append, he, List.map_singleton, List.prod_singleton, mul_assoc]
    rcases (show i + 2 ≤ k ∨ i + 1 = k ∨ i = k ∨ k < i by omega) with h | h | h | h
    · refine ⟨v ++ [i], ?_, k, hk, ?_⟩
      · intro j hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        exacts [hv j hj, by omega]
      · rw [run_comm (Or.inl h), List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, mul_assoc]
    · refine ⟨v, hv, i, by omega, ?_⟩
      rw [← h, run_mul_sn (by omega)]
    · refine ⟨v, hv, k + 1, by omega, ?_⟩
      rw [← h, ← run_mul_sn (a := m + 1) (k := i) (by omega), mul_assoc, sn_mul_self, mul_one]
    · refine ⟨v ++ [i - 1], ?_, k, hk, ?_⟩
      · intro j hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        exacts [hv j hj, by omega]
      · rw [run_braid h (by omega) (by omega), List.map_append, List.prod_append,
          List.map_singleton, List.prod_singleton, mul_assoc]

variable (n) in
/-- The normal forms `run 1 k₁ · run 2 k₂ ⋯ run m k_m`: `(m + 1)!` of them. -/
def nf : ℕ → List (CoxeterMatrix.A n).Group
  | 0 => [1]
  | m + 1 => (nf m).flatMap fun h => (List.range (m + 2)).map fun k => h * run n (m + 1) k

theorem nf_length (m : ℕ) : (nf n m).length = (m + 1).factorial := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nf, List.length_flatMap]
    simp [ih, Nat.factorial_succ]
    ring

theorem mem_nf {m : ℕ} (hm : m ≤ n) (w : List ℕ) (hw : ∀ j ∈ w, j < m) :
    (w.map (sn n)).prod ∈ nf n m := by
  induction m generalizing w with
  | zero =>
    cases w with
    | nil => simp [nf]
    | cons j w => exact absurd (hw j (by simp)) (by omega)
  | succ m ih =>
    obtain ⟨v, hv, k, hk, he⟩ := coset_step (n := n) (m := m) (by omega) w hw
    rw [he, nf, List.mem_flatMap]
    exact ⟨_, ih (by omega) v hv, List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩⟩

theorem mem_nf_self (g : (CoxeterMatrix.A n).Group) : g ∈ nf n n := by
  obtain ⟨ω, rfl⟩ := (CoxeterMatrix.A n).toCoxeterSystem.wordProd_surjective g
  have : (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω = ((ω.map Fin.val).map (sn n)).prod := by
    rw [CoxeterSystem.wordProd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [sn, j.2]
  rw [this]
  exact mem_nf le_rfl _ (by simp)

/-- The Coxeter group of type `A_n` has at most `(n + 1)!` elements. -/
theorem card_group_le : Finite (CoxeterMatrix.A n).Group ∧
    Nat.card (CoxeterMatrix.A n).Group ≤ (n + 1).factorial := by
  let f : Fin (nf n n).length → (CoxeterMatrix.A n).Group := fun j => (nf n n).get j
  have hf : Function.Surjective f := fun g => List.mem_iff_get.mp (mem_nf_self g)
  refine ⟨Finite.of_surjective f hf, ?_⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_fin, nf_length] at this

variable (n) in
/-- The realizer on the Coxeter group: `s_i` goes to the swap of the neighbours `i, i + 1`. -/
def realizer : (CoxeterMatrix.A n).Group →* Perm (Fin (n + 1)) :=
  PresentedGroup.toGroup (f := fun i : Fin n => swap i.castSucc i.succ) fun r hr => by
    obtain ⟨⟨i, j⟩, rfl⟩ := hr
    rw [Function.uncurry_apply_pair, CoxeterMatrix.relation, map_pow, map_mul,
      FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact law_relation i j

theorem realizer_mk (v : FreeGroup (Fin n)) :
    realizer n (PresentedGroup.mk (CoxeterMatrix.A n).relationsSet v) = law n v :=
  rfl

theorem realizer_surjective : Function.Surjective (realizer n) := by
  intro σ
  have hle : Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) ≤
      MonoidHom.mrange (realizer n) := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  obtain ⟨g, hg⟩ := hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
  exact ⟨g, hg⟩

theorem realizer_bijective : Function.Bijective (realizer n) := by
  obtain ⟨hfin, hcard⟩ := card_group_le (n := n)
  exact realizer_surjective.bijective_of_nat_card_le
    (by rw [Nat.card_perm, Nat.card_fin]; exact hcard)

theorem presentation :
    (∀ σ : Perm (Fin (n + 1)), ∃ v : FreeGroup (Fin n), law n v = σ) ∧
    ∀ v₁ v₂ : FreeGroup (Fin n), law n v₁ = law n v₂ ↔
      PresentedGroup.mk (CoxeterMatrix.A n).relationsSet v₁ =
        PresentedGroup.mk (CoxeterMatrix.A n).relationsSet v₂ := by
  refine ⟨fun σ => ?_, fun v₁ v₂ => ?_⟩
  · obtain ⟨g, rfl⟩ := realizer_surjective σ
    obtain ⟨v, rfl⟩ := PresentedGroup.mk_surjective (CoxeterMatrix.A n).relationsSet g
    exact ⟨v, (realizer_mk v).symm⟩
  · rw [← realizer_mk, ← realizer_mk]
    exact realizer_bijective.1.eq_iff

end Coxeter

end Artform.Scores.Bells

namespace Artform.Scores

/-- **T15** (every method is light in the boxes its score cuts). -/
@[ledger "T15"]
theorem methodsAreLight : Statement.methodsAreLight := fun _ _ _ =>
  ⟨fun π hπ f t => ⟨Bells.paint_row_succ π t (hπ t) f, Bells.method_law π hπ f t⟩,
    fun _ _ hA hB u i =>
      ⟨fun hd => ⟨(Bells.boxes_of_dodge hA hB u i hd).1, (Bells.boxes_of_dodge hA hB u i hd).2.2⟩,
        Bells.boxes_of_not_dodge hA hB u i⟩⟩

/-- **T15** (plain hunt is light in a mirror box). -/
@[ledger "T15"]
theorem plainHuntIsLight : Statement.plainHuntIsLight := fun _ =>
  ⟨fun _ _ u => Bells.hunt_mirror u, fun _ _ f t => Bells.hunt_law f t,
    fun t b => ⟨Bells.hunt_apply t b, Bells.hunt_step t b,
      fun hN h => Bells.hunt_lies_once hN t b h⟩,
    fun hN s t => Bells.hunt_eq_iff hN s t⟩

/-- **T15** (the modes of the mirror box). -/
@[ledger "T15"]
theorem mirrorModes : Statement.mirrorModes := fun _ =>
  ⟨Bells.mirror_mode, Bells.modes_independent, fun _ _ hv h => Bells.mirror_spectrum hv h,
    Bells.turn_law⟩

/-- **T15** (the presentation of the bells, Moore 1897). -/
@[ledger "T15"]
theorem bellsPresentation : Statement.bellsPresentation := fun _ => Bells.presentation

/-! ## Non-vacuity

- Plain Bob Minimus at its lead end: the cross `x` and then `12` cut the four bells into the
  box of the front pair and the dodge of the back pair.
- Plain hunt on five bells (Doubles): the treble's path, and the plain course of ten rows.
- On four bells the mode `k = 1` has the eigenvalue `√2`.
- On four bells the lead `X Y` of plain hunt has order 4 in the group that the rules present.
-/

/-- At Plain Bob Minimus's lead end, `x` then `12` (the ledger's numbering), the front pair is
a mirror box and the back pair a dodge. -/
example (u : Fin 4 → ℤ) :
    Bells.act (Bells.huntX 4) u 0 + Bells.act (Equiv.swap 2 3) u 0 = u 0 + u 1 ∧
      Bells.act (Bells.huntX 4) u 2 + Bells.act (Equiv.swap 2 3) u 2 = u 3 + u 3 := by
  have hX : Bells.IsChange (Bells.huntX 4) := by unfold Bells.IsChange; decide
  have hB : Bells.IsChange (Equiv.swap (2 : Fin 4) 3) := by unfold Bells.IsChange; decide
  obtain ⟨-, h0⟩ := (methodsAreLight ℤ 4).2 _ _ hX hB u 0
  obtain ⟨h2, -⟩ := (methodsAreLight ℤ 4).2 _ _ hX hB u 2
  have hd0 : ¬ Bells.IsDodge (Bells.huntX 4) (Equiv.swap 2 3) 0 := by
    unfold Bells.IsDodge; decide
  have hd2 : Bells.IsDodge (Bells.huntX 4) (Equiv.swap 2 3) 2 := by
    unfold Bells.IsDodge; decide
  have hl : Bells.boxLeft (Bells.huntX 4) (Equiv.swap 2 3) 0 = 0 := by decide
  have hr : Bells.boxRight (Bells.huntX 4) (Equiv.swap 2 3) 0 = 1 := by decide
  have hx : Bells.huntX 4 2 = 3 := by decide
  refine ⟨?_, ?_⟩
  · rw [(h0 hd0).1, Bells.boxSum, hl, hr]
  · rw [(h2 hd2).1, hx]

/-- Plain hunt on five bells: the treble rises one place per change, lies at the back, and
comes down; the plain course has ten rows. -/
example : ((List.range 11).map fun t => (Bells.hunt 5 t 0 : ℕ)) =
      [0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 0] ∧
    Bells.hunt 5 10 = 1 ∧ ∀ t, 0 < t → t < 10 → Bells.hunt 5 t ≠ 1 := by
  have h := (plainHuntIsLight 5).2.2.2 (by norm_num)
  refine ⟨by decide, (h 10 0).mpr rfl, fun t h0 h1 he => ?_⟩
  have := (h t 0).mp he
  omega

/-- On four bells the mode `k = 1` has the eigenvalue `2 cos(π/4) = √2`. -/
example : Bells.mirror (Bells.mode 4 1) = Real.sqrt 2 • Bells.mode 4 1 := by
  rw [(mirrorModes 4).1 1]
  congr 1
  rw [show Real.pi * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = Real.pi / 4 by push_cast; ring,
    Real.cos_pi_div_four]
  ring

/-- Plain hunt on four bells: the lead `X Y = s₀ s₂ s₁` has order 4 in the group that the
rules present, as its law has in `S₄`. -/
example : PresentedGroup.mk (CoxeterMatrix.A 3).relationsSet
    ((FreeGroup.of 0 * FreeGroup.of 2 * FreeGroup.of 1) ^ 4) = 1 := by
  rw [← map_one (PresentedGroup.mk (CoxeterMatrix.A 3).relationsSet)]
  exact ((bellsPresentation 3).2 _ _).mp (by decide)

end Artform.Scores
