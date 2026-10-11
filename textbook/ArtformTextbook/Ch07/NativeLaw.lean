import ArtformTextbook.Ch07.Statements.NativeLaw

/-!
# The selected native probability law (Section 7.6)

The proof of Theorem 7.4 in its formal part, following the book's algebra.

* `M_λ` has the identities for `λ ∈ [0, 1]`: each arithmetic reading `ρ` of `ℚ(√2, i)` in `ℂ`
  gives a weight `|ρ(x)|²` with them, and `M_λ` mixes the two readings (`isNativeContent_reading`).
* Conversely, splitting and the mixer give the parallelogram identity, and with it `M(0) = 0`
  and `M(−x) = M(x)`. The polar form `φ(x, y) = M(x + y) − M(x − y)` is then additive in each
  argument (`polar_add_left`), so `M` is a quadratic form over the dyadic coordinates
  (`map_coords`). The quarter turn and the grade symmetry `M(√2 x) = 2 M(x)` leave
  `M = a² + 2b² + c² + 2d² + 2k(ab + cd)` (`formula`). Nonnegativity at the dyadic points
  `−t + √2` forces `k² ≤ 2` (`sq_le_two`), by density of the dyadic rationals, and
  `k = (2λ − 1)√2` gives `M = M_λ`. The value at `1 + √2` fixes `λ` (`contentFamily_injective`).
* On the zero coefficient `a` of `H, T, H`, `p = |a|² = (2 + √2)/4` and
  `q = |σ(a)|² = (2 − √2)/4`, and `J_λ − r_λ² = λ(1 − λ)/2` (`duplication_defect`): duplication
  leaves `λ = 0` and `λ = 1`, and oriented retention, `r_λ > 1/2`, selects `λ = 1`.
-/

namespace Artform.NativeLaw

open Artform.Exact

/-! ### Arithmetic in `R₈` -/

@[simp] theorem coe_sqrtTwo : ((sqrtTwo : R8) : Q4) = ⟨0, 1, 0, 0⟩ := rfl
@[simp] theorem coe_invSqrtTwo : ((invSqrtTwo : R8) : Q4) = ⟨0, 1 / 2, 0, 0⟩ := rfl
@[simp] theorem coe_I : ((I : R8) : Q4) = ⟨0, 0, 1, 0⟩ := rfl
@[simp] theorem coe_half : ((half : R8) : Q4) = ⟨1 / 2, 0, 0, 0⟩ := rfl

theorem sqrtTwo_mul_invSqrtTwo : sqrtTwo * invSqrtTwo = 1 := by
  apply Subtype.ext; ext <;> simp

theorem I_mul_I : I * I = -1 := by
  apply Subtype.ext; ext <;> simp

theorem half_add_half : half + half = 1 := by
  apply Subtype.ext; ext <;> simp; norm_num

theorem sqrtTwo_mul_sqrtTwo : sqrtTwo * sqrtTwo = 1 + 1 := by
  apply Subtype.ext; ext <;> simp; norm_num

/-- The coordinates of `a = (1 + ζ)/2`: `a = 1/2 + √2/4 + i √2/4`. -/
theorem coe_hthZero : ((hthZero : R8) : Q4) = ⟨1 / 2, 1 / 4, 0, 1 / 4⟩ := by
  ext <;> simp [hthZero, zeta] <;> norm_num

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `|x|² = (a + b√2)² + (c + d√2)²`. -/
theorem normSq_toComplex (x : Q4) :
    Complex.normSq (Q4.toComplex x) =
      ((x.a : ℝ) + x.b * Real.sqrt 2) ^ 2 + ((x.c : ℝ) + x.d * Real.sqrt 2) ^ 2 := by
  rw [Complex.normSq_apply, Q4.toComplex_re, Q4.toComplex_im]
  ring

/-! ### The family `M_λ` has the identities -/

/-- The weight `|ρ(x)|²` of a ring map `ρ` from `ℚ(√2, i)` to `ℂ` has the identities of a native
content when `|ρ(1/√2)|² = 1/2` and `|ρ(i)|² = 1`. -/
theorem isNativeContent_reading (ρ : Q4 →+* ℂ)
    (hs : Complex.normSq (ρ (invSqrtTwo : Q4)) = 1 / 2)
    (hi : Complex.normSq (ρ (I : Q4)) = 1) :
    IsNativeContent (fun x : R8 => Complex.normSq (ρ x)) where
  splitting x := by
    simp only [MulMemClass.coe_mul, map_mul, hs]
    ring
  mixer x y := by
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, AddSubgroupClass.coe_sub, map_mul,
      map_add, map_sub, hs, Complex.normSq_add, Complex.normSq_sub]
    ring
  quarterTurn x := by
    simp only [MulMemClass.coe_mul, map_mul, hi, one_mul]
  calibration := by simp
  nonneg _ := Complex.normSq_nonneg _

/-- Every `M_λ` with `λ ∈ [0, 1]` has the identities of a native content. -/
theorem isNativeContent_contentFamily {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    IsNativeContent (contentFamily lam) := by
  have h1 := isNativeContent_reading Q4.toComplex
    (by rw [normSq_toComplex]; simp; nlinarith [sqrt_two_mul_self])
    (by rw [normSq_toComplex]; simp)
  have h2 := isNativeContent_reading (Q4.toComplex.comp sigma.toRingHom)
    (by simp only [RingHom.comp_apply]; rw [normSq_toComplex]; simp; nlinarith [sqrt_two_mul_self])
    (by simp only [RingHom.comp_apply]; rw [normSq_toComplex]; simp)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h2
  obtain ⟨hl0, hl1⟩ := hlam
  refine ⟨fun x => ?_, fun x y => ?_, fun x => ?_, ?_, fun x => ?_⟩
  · simp only [contentFamily]
    linear_combination lam * h1.splitting x + (1 - lam) * h2.splitting x
  · simp only [contentFamily]
    linear_combination lam * h1.mixer x y + (1 - lam) * h2.mixer x y
  · simp only [contentFamily]
    linear_combination lam * h1.quarterTurn x + (1 - lam) * h2.quarterTurn x
  · simp only [contentFamily]
    linear_combination lam * h1.calibration + (1 - lam) * h2.calibration
  · simp only [contentFamily]
    have := h1.nonneg x
    have := h2.nonneg x
    have : 0 ≤ 1 - lam := by linarith
    positivity

/-- `M_λ(1 + √2) = 3 − 2√2 + 4√2 λ`, so one content `M_λ` has one `λ`. -/
theorem contentFamily_injective {lam mu : ℝ} (heq : contentFamily lam = contentFamily mu) :
    lam = mu := by
  have h := congrFun heq (1 + sqrtTwo)
  simp only [contentFamily, normSq_toComplex, AddMemClass.coe_add, OneMemClass.coe_one,
    coe_sqrtTwo, sigma_a, sigma_b, sigma_c, sigma_d, Q4.add_a, Q4.add_b, Q4.add_c, Q4.add_d,
    Q4.one_a, Q4.one_b, Q4.one_c, Q4.one_d] at h
  push_cast at h
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have : (lam - mu) * (4 * Real.sqrt 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · linarith

/-! ### The identities leave the family `M_λ` -/

/-- The polar form `φ(x, y) = M(x + y) − M(x − y)` of a content. -/
def polar (M : R8 → ℝ) (x y : R8) : ℝ := M (x + y) - M (x - y)

/-- The coefficient with coordinates `(q, 0, 0, 0)`, for a dyadic rational `q`. -/
def ofDyadic (q : ℚ) (hq : IsDyadic q) : R8 :=
  ⟨⟨q, 0, 0, 0⟩, hq, isDyadic_zero, isDyadic_zero, isDyadic_zero⟩

/-- An additive map on `R₈` is `ℤ[1/2]`-linear: `g(q e) = q g(e)` for dyadic `q`. -/
theorem map_ofDyadic_mul (g : R8 →+ ℝ) {q : ℚ} (hq : IsDyadic q) (e : R8) :
    g (ofDyadic q hq * e) = q * g e := by
  obtain ⟨n, m, hnm⟩ := id hq
  have key : (2 ^ m : ℕ) • (ofDyadic q hq * e) = (n : ℤ) • e := by
    apply Subtype.ext
    change (2 ^ m : ℕ) • (((ofDyadic q hq : R8) : Q4) * (e : Q4)) = (n : ℤ) • (e : Q4)
    ext <;> simp only [Q4.nsmul_a, Q4.nsmul_b, Q4.nsmul_c, Q4.nsmul_d, Q4.zsmul_a, Q4.zsmul_b,
      Q4.zsmul_c, Q4.zsmul_d, Q4.mul_a, Q4.mul_b, Q4.mul_c, Q4.mul_d, ofDyadic, hnm] <;>
      push_cast <;> field_simp <;> ring
  have h := congrArg g key
  rw [map_nsmul, map_zsmul, nsmul_eq_mul, zsmul_eq_mul] at h
  have hq' : (q : ℝ) = (n : ℝ) / 2 ^ m := by rw [hnm]; push_cast; ring
  have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hq']
  push_cast at h
  field_simp
  linear_combination h

/-- An additive map on `R₈` is determined by its values at `1`, `√2`, `i` and `i√2`. -/
theorem map_coords (g : R8 →+ ℝ) {a b c d : ℚ} (ha : IsDyadic a) (hb : IsDyadic b)
    (hc : IsDyadic c) (hd : IsDyadic d) :
    g ⟨⟨a, b, c, d⟩, ha, hb, hc, hd⟩ =
      a * g 1 + b * g sqrtTwo + c * g I + d * g (I * sqrtTwo) := by
  have hx : (⟨⟨a, b, c, d⟩, ha, hb, hc, hd⟩ : R8) =
      ofDyadic a ha * 1 + ofDyadic b hb * sqrtTwo + ofDyadic c hc * I +
        ofDyadic d hd * (I * sqrtTwo) := by
    apply Subtype.ext
    ext <;> simp [ofDyadic]
  rw [hx, map_add, map_add, map_add, map_ofDyadic_mul, map_ofDyadic_mul, map_ofDyadic_mul,
    map_ofDyadic_mul]

namespace IsNativeContent

variable {M : R8 → ℝ} (h : IsNativeContent M)
include h

/-- `M(0) = 0`, from splitting at `0`. -/
theorem map_zero : M 0 = 0 := by
  have := h.splitting 0
  rw [zero_mul] at this
  linarith

theorem map_mul_invSqrtTwo (x : R8) : M (x * invSqrtTwo) = M x / 2 := by
  have := h.splitting x
  linarith

/-- The grade symmetry `M(√2 x) = 2 M(x)`. -/
theorem map_sqrtTwo_mul (x : R8) : M (sqrtTwo * x) = 2 * M x := by
  have := h.splitting (sqrtTwo * x)
  rw [show sqrtTwo * x * invSqrtTwo = x by linear_combination x * sqrtTwo_mul_invSqrtTwo] at this
  linarith

/-- The parallelogram identity, from the mixer and splitting. -/
theorem parallelogram (x y : R8) : M (x + y) + M (x - y) = 2 * M x + 2 * M y := by
  have := h.mixer x y
  rw [h.map_mul_invSqrtTwo, h.map_mul_invSqrtTwo] at this
  linarith

/-- Symmetry `M(−x) = M(x)`, from the parallelogram identity. -/
theorem map_neg (x : R8) : M (-x) = M x := by
  have := h.parallelogram 0 x
  rw [zero_add, zero_sub, h.map_zero] at this
  linarith

theorem polar_comm (x y : R8) : polar M x y = polar M y x := by
  unfold polar
  rw [add_comm y x, show y - x = -(x - y) by abel, h.map_neg]

theorem polar_zero_left (y : R8) : polar M 0 y = 0 := by
  unfold polar
  rw [zero_add, zero_sub, h.map_neg, sub_self]

theorem polar_self (x : R8) : polar M x x = 4 * M x := by
  unfold polar
  have := h.parallelogram x x
  rw [sub_self, h.map_zero] at this ⊢
  linarith

theorem polar_mid (x x' y : R8) :
    polar M (x + x') y + polar M (x - x') y = 2 * polar M x y := by
  unfold polar
  have h1 := h.parallelogram (x + y) x'
  have h2 := h.parallelogram (x - y) x'
  rw [show x + y + x' = x + x' + y by abel, show x + y - x' = x - x' + y by abel] at h1
  rw [show x - y + x' = x + x' - y by abel, show x - y - x' = x - x' - y by abel] at h2
  linarith

/-- The polar form is additive in its first argument: halve `u + v` and `u − v`. -/
theorem polar_add_left (u v y : R8) : polar M (u + v) y = polar M u y + polar M v y := by
  have k1 := h.polar_mid ((u + v) * half) ((u - v) * half) y
  have k2 := h.polar_mid ((u + v) * half) ((u + v) * half) y
  rw [show (u + v) * half + (u - v) * half = u by linear_combination u * half_add_half,
    show (u + v) * half - (u - v) * half = v by linear_combination v * half_add_half] at k1
  rw [show (u + v) * half + (u + v) * half = u + v by
      linear_combination (u + v) * half_add_half, sub_self, h.polar_zero_left] at k2
  linarith

/-- The polar form in its first argument, as an additive map. -/
def polarHom (y : R8) : R8 →+ ℝ :=
  AddMonoidHom.mk' (fun x => polar M x y) (fun u v => h.polar_add_left u v y)

/-- `M(1 − i) = M(1 + i)`, by the quarter turn: `i(1 − i) = 1 + i`. -/
theorem map_one_sub_I : M (1 - I) = M (1 + I) := by
  rw [← h.quarterTurn (1 - I)]
  congr 1
  linear_combination (-1 : R8) * I_mul_I

/-- `M` is the quadratic form `a² + 2b² + c² + 2d² + 2k(ab + cd)` in the coordinates
`a + b√2 + i(c + d√2)`, with `4k = φ(1, √2)`. -/
theorem formula {a b c d : ℚ} (ha : IsDyadic a) (hb : IsDyadic b) (hc : IsDyadic c)
    (hd : IsDyadic d) :
    M ⟨⟨a, b, c, d⟩, ha, hb, hc, hd⟩ =
      (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + 2 * (d : ℝ) ^ 2 +
        2 * (polar M 1 sqrtTwo / 4) * (a * b + c * d) := by
  set x : R8 := ⟨⟨a, b, c, d⟩, ha, hb, hc, hd⟩
  have e (y : R8) : polar M x y = a * polar M 1 y + b * polar M sqrtTwo y +
      c * polar M I y + d * polar M (I * sqrtTwo) y :=
    map_coords (h.polarHom y) ha hb hc hd
  -- The values of `M` at `1`, `√2`, `i` and `i√2`.
  have m2 : M sqrtTwo = 2 := by
    have := h.map_sqrtTwo_mul 1
    rw [mul_one, h.calibration] at this
    linarith
  have m3 : M I = 1 := by
    have := h.quarterTurn 1
    rwa [mul_one, h.calibration] at this
  have m4 : M (I * sqrtTwo) = 2 := by rw [h.quarterTurn, m2]
  -- The polar form at `1`, `√2`, `i` and `i√2`.
  have p11 : polar M 1 1 = 4 := by rw [h.polar_self, h.calibration]; norm_num
  have p22 : polar M sqrtTwo sqrtTwo = 8 := by rw [h.polar_self, m2]; norm_num
  have p33 : polar M I I = 4 := by rw [h.polar_self, m3]; norm_num
  have p44 : polar M (I * sqrtTwo) (I * sqrtTwo) = 8 := by rw [h.polar_self, m4]; norm_num
  have p34 : polar M I (I * sqrtTwo) = polar M 1 sqrtTwo := by
    unfold polar
    rw [show I + I * sqrtTwo = I * (1 + sqrtTwo) by ring,
      show I - I * sqrtTwo = I * (1 - sqrtTwo) by ring, h.quarterTurn, h.quarterTurn]
  have p13 : polar M 1 I = 0 := by
    unfold polar
    rw [h.map_one_sub_I, sub_self]
  have p24 : polar M sqrtTwo (I * sqrtTwo) = 0 := by
    unfold polar
    rw [show sqrtTwo + I * sqrtTwo = sqrtTwo * (1 + I) by ring,
      show sqrtTwo - I * sqrtTwo = sqrtTwo * (1 - I) by ring, h.map_sqrtTwo_mul,
      h.map_sqrtTwo_mul, h.map_one_sub_I, sub_self]
  -- The quarter turn gives `φ(1, i√2) = −φ(√2, i)`, the grade symmetry `φ(1, i√2) = φ(√2, i)`.
  have q1 : polar M 1 (I * sqrtTwo) = -polar M sqrtTwo I := by
    unfold polar
    have u : M (1 + I * sqrtTwo) = M (sqrtTwo - I) := by
      rw [← h.quarterTurn (1 + I * sqrtTwo), ← h.map_neg (sqrtTwo - I)]
      congr 1
      linear_combination sqrtTwo * I_mul_I
    have v : M (1 - I * sqrtTwo) = M (sqrtTwo + I) := by
      rw [← h.quarterTurn (1 - I * sqrtTwo)]
      congr 1
      linear_combination (-sqrtTwo) * I_mul_I
    rw [u, v]
    ring
  have q2 : polar M 1 (I * sqrtTwo) = polar M sqrtTwo I := by
    have g1 : polar M sqrtTwo (I + I) = 2 * polar M 1 (I * sqrtTwo) := by
      unfold polar
      rw [show sqrtTwo + (I + I) = sqrtTwo * (1 + I * sqrtTwo) by
          linear_combination (-I) * sqrtTwo_mul_sqrtTwo,
        show sqrtTwo - (I + I) = sqrtTwo * (1 - I * sqrtTwo) by
          linear_combination I * sqrtTwo_mul_sqrtTwo,
        h.map_sqrtTwo_mul, h.map_sqrtTwo_mul]
      ring
    have g2 : polar M sqrtTwo (I + I) = 2 * polar M sqrtTwo I := by
      rw [h.polar_comm, h.polar_add_left, h.polar_comm I]
      ring
    linarith
  have p14 : polar M 1 (I * sqrtTwo) = 0 := by linarith
  have p23 : polar M sqrtTwo I = 0 := by linarith
  -- Expand `φ(x, x) = 4 M(x)` in both arguments.
  have hx := h.polar_self x
  rw [e x, h.polar_comm 1 x, h.polar_comm sqrtTwo x, h.polar_comm I x,
    h.polar_comm (I * sqrtTwo) x, e 1, e sqrtTwo, e I, e (I * sqrtTwo),
    h.polar_comm sqrtTwo 1, h.polar_comm I 1, h.polar_comm (I * sqrtTwo) 1,
    h.polar_comm I sqrtTwo, h.polar_comm (I * sqrtTwo) sqrtTwo,
    h.polar_comm (I * sqrtTwo) I, p11, p22, p33, p44, p34, p13, p24, p14, p23] at hx
  linear_combination -hx / 4

/-- Nonnegativity forces `k² ≤ 2`: `M(−t + √2) = (t − k)² + 2 − k² ≥ 0` at every dyadic `t`, and
the dyadic rationals are dense. -/
theorem sq_le_two : (polar M 1 sqrtTwo / 4) ^ 2 ≤ 2 := by
  set k := polar M 1 sqrtTwo / 4 with hk
  have key (t : ℚ) (ht : IsDyadic t) : k ^ 2 - 2 ≤ ((t : ℝ) - k) ^ 2 := by
    have := h.nonneg ⟨⟨-t, 1, 0, 0⟩, ht.neg, isDyadic_one, isDyadic_zero, isDyadic_zero⟩
    rw [h.formula ht.neg isDyadic_one isDyadic_zero isDyadic_zero, ← hk] at this
    push_cast at this
    nlinarith [this]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < k ^ 2 - 2 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have ht : IsDyadic ((⌊k * 2 ^ m⌋ : ℚ) / 2 ^ m) := ⟨⌊k * 2 ^ m⌋, m, rfl⟩
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hfl := Int.floor_le (k * 2 ^ m)
  have hfl' := Int.lt_floor_add_one (k * 2 ^ m)
  have hkey := key _ ht
  push_cast at hkey
  set f : ℝ := (⌊k * 2 ^ m⌋ : ℝ)
  have hpow : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [one_div_pow]
  have hle : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
  -- `0 ≤ k − t < 2^{−m}`.
  have d1 : f / 2 ^ m ≤ k := by rw [div_le_iff₀ h2m]; linarith
  have d2 : k - f / 2 ^ m < (1 / 2) ^ m := by
    rw [hpow, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2m]; linarith
  nlinarith

/-- The identities, calibration and nonnegativity leave the family `M_λ`. -/
theorem exists_eq_contentFamily : ∃ lam ∈ Set.Icc (0 : ℝ) 1, M = contentFamily lam := by
  set k := polar M 1 sqrtTwo / 4 with hk
  have habs : |k| ≤ Real.sqrt 2 := Real.abs_le_sqrt h.sq_le_two
  have hs0 := Real.sqrt_nonneg 2
  refine ⟨1 / 2 + k * Real.sqrt 2 / 4, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [neg_abs_le k, sqrt_two_mul_self]
  · nlinarith [le_abs_self k, sqrt_two_mul_self]
  · funext x
    obtain ⟨⟨a, b, c, d⟩, ha, hb, hc, hd⟩ := x
    rw [h.formula ha hb hc hd, ← hk]
    simp only [contentFamily, normSq_toComplex, sigma_a, sigma_b, sigma_c, sigma_d]
    push_cast
    linear_combination (-((b : ℝ) ^ 2 + (d : ℝ) ^ 2 + k * (a * b + c * d))) * sqrt_two_mul_self

end IsNativeContent

/-! ### Duplication and oriented retention on `H, T, H` -/

/-- `p = |a|² = (2 + √2)/4` for the zero coefficient `a = (1 + ζ)/2` of `H, T, H`. -/
theorem normSq_hthZero :
    Complex.normSq (Q4.toComplex (hthZero : Q4)) = (2 + Real.sqrt 2) / 4 := by
  rw [coe_hthZero, normSq_toComplex]
  push_cast
  linear_combination (1 / 8 : ℝ) * sqrt_two_mul_self

/-- `q = |σ(a)|² = (2 − √2)/4`. -/
theorem normSq_sigma_hthZero :
    Complex.normSq (Q4.toComplex (sigma (hthZero : Q4))) = (2 - Real.sqrt 2) / 4 := by
  rw [coe_hthZero, normSq_toComplex]
  simp only [sigma_a, sigma_b, sigma_c, sigma_d]
  push_cast
  linear_combination (1 / 8 : ℝ) * sqrt_two_mul_self

/-- The single-copy probability `r_λ = λp + (1 − λ)q`. -/
theorem contentFamily_hthZero (lam : ℝ) :
    contentFamily lam hthZero =
      lam * ((2 + Real.sqrt 2) / 4) + (1 - lam) * ((2 - Real.sqrt 2) / 4) := by
  rw [contentFamily, normSq_hthZero, normSq_sigma_hthZero]

/-- The zero-zero weight of two independent copies, `J_λ = λp² + (1 − λ)q²`. -/
theorem contentFamily_hthZero_mul (lam : ℝ) :
    contentFamily lam (hthZero * hthZero) =
      lam * ((2 + Real.sqrt 2) / 4) ^ 2 + (1 - lam) * ((2 - Real.sqrt 2) / 4) ^ 2 := by
  rw [contentFamily, MulMemClass.coe_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    normSq_hthZero, normSq_sigma_hthZero]
  ring

/-- `J_λ − r_λ² = λ(1 − λ)(p − q)² = λ(1 − λ)/2`. -/
theorem duplication_defect (lam : ℝ) :
    contentFamily lam (hthZero * hthZero) - contentFamily lam hthZero * contentFamily lam hthZero =
      lam * (1 - lam) / 2 := by
  rw [contentFamily_hthZero_mul, contentFamily_hthZero]
  linear_combination lam * (1 - lam) / 4 * sqrt_two_mul_self

end Artform.NativeLaw

namespace Artform

open Artform.Exact Artform.NativeLaw

/-- **Theorem 7.4** (the selected native probability law), in its formal part: the identities
leave the family `M_λ` with one `λ ∈ [0, 1]`; duplication on the zero coefficient of `H, T, H`
leaves `λ = 0` and `λ = 1`; oriented retention selects `M(z) = |z|²`, which multiplies. -/
@[book "qr:selected-law"]
theorem selectedLaw : Statement.selectedLaw := by
  have classify (M : R8 → ℝ) : IsNativeContent M ↔
      ∃! lam : ℝ, lam ∈ Set.Icc (0 : ℝ) 1 ∧ M = contentFamily lam := by
    constructor
    · intro h
      obtain ⟨lam, hlam, hM⟩ := h.exists_eq_contentFamily
      exact ⟨lam, ⟨hlam, hM⟩, fun mu hmu => contentFamily_injective (hmu.2.symm.trans hM)⟩
    · rintro ⟨lam, ⟨hlam, rfl⟩, -⟩
      exact isNativeContent_contentFamily hlam
  have dup (M : R8 → ℝ) (h : IsNativeContent M) :
      M (hthZero * hthZero) = M hthZero * M hthZero ↔
        M = contentFamily 0 ∨ M = contentFamily 1 := by
    obtain ⟨lam, -, rfl⟩ := h.exists_eq_contentFamily
    constructor
    · intro hdup
      have hd := duplication_defect lam
      have : lam * (1 - lam) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h1
      · left
        rw [h0]
      · right
        rw [show lam = 1 by linarith]
    · rintro (h0 | h1)
      · have := duplication_defect 0
        rw [h0]
        linarith
      · have := duplication_defect 1
        rw [h1]
        linarith
  have select (M : R8 → ℝ) :
      (IsNativeContent M ∧ M (hthZero * hthZero) = M hthZero * M hthZero ∧
          1 / 2 < M hthZero) ↔
        ∀ z : R8, M z = Complex.normSq (Q4.toComplex z) := by
    constructor
    · rintro ⟨h, hdup, hret⟩
      rcases (dup M h).mp hdup with h0 | h1
      · rw [h0, contentFamily_hthZero] at hret
        nlinarith [Real.sqrt_nonneg 2]
      · intro z
        rw [h1, contentFamily]
        ring
    · intro hM
      have hM1 : M = contentFamily 1 := by
        funext z
        rw [hM z, contentFamily]
        ring
      subst hM1
      refine ⟨isNativeContent_contentFamily ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
      · have := duplication_defect 1
        linarith
      · rw [contentFamily_hthZero]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  have product (M : R8 → ℝ) (h : IsNativeContent M)
      (hdup : M (hthZero * hthZero) = M hthZero * M hthZero) (hret : 1 / 2 < M hthZero)
      (x y : R8) : M (x * y) = M x * M y := by
    have hM := (select M).mp ⟨h, hdup, hret⟩
    rw [hM, hM, hM, MulMemClass.coe_mul, map_mul, map_mul]
  exact ⟨classify, dup, select, product⟩

/-! ## Non-vacuity -/

/-- The squared law `M₁(z) = |z|²` meets every hypothesis on the running example `H, T, H`: the
identities, duplication on its zero coefficient, and oriented retention,
`M₁(a) = (2 + √2)/4 > 1/2`. -/
example : IsNativeContent (contentFamily 1) ∧
    contentFamily 1 (hthZero * hthZero) = contentFamily 1 hthZero * contentFamily 1 hthZero ∧
    1 / 2 < contentFamily 1 hthZero := by
  refine ⟨isNativeContent_contentFamily ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
  · have := duplication_defect 1
    linarith
  · rw [contentFamily_hthZero]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]

/-- The even mixture `M_{1/2}` meets the identities but fails duplication
(Figure `fig:qr-duplication`): one copy of `H, T, H` reports zero with probability `1/2`, and
two copies report zero-zero with `3/8 ≠ (1/2)²`. -/
example : IsNativeContent (contentFamily (1 / 2)) ∧ contentFamily (1 / 2) hthZero = 1 / 2 ∧
    contentFamily (1 / 2) (hthZero * hthZero) = 3 / 8 ∧
    contentFamily (1 / 2) (hthZero * hthZero) ≠
      contentFamily (1 / 2) hthZero * contentFamily (1 / 2) hthZero := by
  have h1 : contentFamily (1 / 2) hthZero = 1 / 2 := by
    rw [contentFamily_hthZero]
    ring
  have h2 : contentFamily (1 / 2) (hthZero * hthZero) = 3 / 8 := by
    rw [contentFamily_hthZero_mul]
    linear_combination (1 / 16 : ℝ) * NativeLaw.sqrt_two_mul_self
  refine ⟨isNativeContent_contentFamily ⟨by norm_num, by norm_num⟩, h1, h2, ?_⟩
  rw [h1, h2]
  norm_num

/-- The other arithmetic reading `M_0(z) = |σ(z)|²` meets the identities and duplication, but
not oriented retention: `M_0(a) = (2 − √2)/4 < 1/2`. -/
example : IsNativeContent (contentFamily 0) ∧
    contentFamily 0 (hthZero * hthZero) = contentFamily 0 hthZero * contentFamily 0 hthZero ∧
    contentFamily 0 hthZero < 1 / 2 := by
  refine ⟨isNativeContent_contentFamily ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
  · have := duplication_defect 0
    linarith
  · rw [contentFamily_hthZero]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]

end Artform
