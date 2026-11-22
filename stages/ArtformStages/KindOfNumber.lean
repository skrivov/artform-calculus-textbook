import ArtformStages.FillingWaves

/-!
# The kind of number

The charter of the research ledger on a layered universe leaves open the kind of number of the
waves (D16). Here the waves of one line on the dial of `n`, the line of `FillingWaves.lean` read
alone, take their numbers in a field `K`. Their reading is given by a *turn*
`χ : AddChar (ZMod n) K`, a map from `ℤ/n` to `K` that turns sums into products: the write moves a
wave by one, and the reading by `χ` multiplies the value at `k` by `χ k`. A turn is *faithful* when
`χ k = 1` only for `k = 0`. The dial forces the kind of number (finding 473 of the ledger):

* `lineWrite`, `lineRead`, `span_write_read_of_faithful` (KN1): where `n` is not `0` in `K`, with a
  faithful turn every `K`-linear map of the waves is a sum of products of the write and the reading;
* `not_span_write_read_of_not_faithful` (KN2): if `χ k = 1` for some `k ≠ 0`, the write made `k`
  times passes the write and the reading and is no multiple of `1`, so the products of the write and
  the reading do not make every table;
* `exists_faithful_iff` (KN3): a faithful turn into `K` exists exactly when `K` has a primitive
  `n`-th root of unity;
* `real_turn_not_faithful` (KN4): for `n ≥ 3` every real turn takes only the values `1` and `-1`,
  and none is faithful;
* `stdAddChar_faithful`, `stdAddChar_norm`, `lineRead_stdAddChar_norm` (KN5): the dial's standard
  turn is faithful, its values have size `1`, and its reading keeps the sum of the squares of the
  sizes.

KN1 is proved as `Stage.span_write_read` is, with `χ` for the standard turn: a faithful turn is
primitive (`AddChar.zmod_char_primitive_of_eq_one_only_at_zero`), so its sums over the dial are
`n` at `0` and `0` elsewhere. KN2 shows that the write made `k` times passes every product of the
write and the reading, but not the table that keeps the value at `0` and puts `0` elsewhere.
-/

noncomputable section

namespace Artform.Stages

variable (K : Type*) [Field K] (n : ℕ)

/-- **KN1.** The write of the waves of one line: it moves every wave by one; its value at `k` is
the old value at `k - 1`. -/
def lineWrite : Module.End K (ZMod n → K) := LinearMap.funLeft K K fun k => k - 1

variable {K n}

/-- **KN1.** The reading by the turn `χ`: it multiplies the value at `k` by `χ k`. -/
def lineRead (χ : AddChar (ZMod n) K) : Module.End K (ZMod n → K) where
  toFun ψ k := χ k * ψ k
  map_add' ψ φ := funext fun k => mul_add _ _ _
  map_smul' a ψ := funext fun k => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The write, read at `k`. -/
theorem lineWrite_apply (ψ : ZMod n → K) (k : ZMod n) : lineWrite K n ψ k = ψ (k - 1) := rfl

/-- The reading, read at `k`. -/
theorem lineRead_apply (χ : AddChar (ZMod n) K) (ψ : ZMod n → K) (k : ZMod n) :
    lineRead χ ψ k = χ k * ψ k := rfl

/-- The write made `j` times moves every wave by `j`. -/
theorem lineWrite_pow (j : ℕ) :
    lineWrite K n ^ j = LinearMap.funLeft K K fun k : ZMod n => k - j := by
  induction j with
  | zero =>
    refine LinearMap.ext fun ψ => funext fun k => ?_
    simp only [pow_zero, Module.End.one_apply, LinearMap.funLeft_apply, Nat.cast_zero, sub_zero]
  | succ j ih =>
    refine LinearMap.ext fun ψ => funext fun k => ?_
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.funLeft_apply, LinearMap.funLeft_apply,
      lineWrite_apply, Nat.cast_succ, sub_sub]

/-- The reading by `χ` is the multiplication by `χ`. -/
theorem lineRead_eq_lmul (χ : AddChar (ZMod n) K) :
    lineRead χ = Algebra.lmul K (ZMod n → K) fun k => χ k := by
  refine LinearMap.ext fun ψ => funext fun k => ?_
  rfl

/-- **KN1.** A faithful turn makes every table: where `n` is not `0` in `K`, every `K`-linear map
of the waves of one line to themselves is a sum, with coefficients in `K`, of products of the write
and the reading by `χ`. -/
theorem span_write_read_of_faithful (hn : (n : K) ≠ 0) (χ : AddChar (ZMod n) K)
    (hχ : ∀ k, χ k = 1 → k = 0) :
    Submodule.span K (Submonoid.closure {lineWrite K n, lineRead χ} :
      Set (Module.End K (ZMod n → K))) = ⊤ := by
  have : NeZero n := ⟨fun h => hn (by rw [h, Nat.cast_zero])⟩
  rw [← Algebra.adjoin_eq_span, eq_top_iff]
  intro f _
  rw [Subalgebra.mem_toSubmodule]
  set A := Algebra.adjoin K ({lineWrite K n, lineRead χ} : Set (Module.End K (ZMod n → K)))
  have hW : lineWrite K n ∈ A := Algebra.subset_adjoin (Set.mem_insert _ _)
  -- every shift is a power of the write
  have hshift : ∀ v : ZMod n, (LinearMap.funLeft K K fun k : ZMod n => k - v) ∈ A := by
    intro v
    have h := A.pow_mem hW v.val
    rwa [lineWrite_pow, ZMod.natCast_zmod_val] at h
  -- every multiplication by a function made of `χ` is in `A`
  have hmul : ∀ g ∈ Algebra.adjoin K ({fun k => χ k} : Set (ZMod n → K)),
      Algebra.lmul K (ZMod n → K) g ∈ A := by
    intro g hg
    have hle : (Algebra.adjoin K ({fun k => χ k} : Set (ZMod n → K))).map
        (Algebra.lmul K (ZMod n → K)) ≤ A := by
      rw [AlgHom.map_adjoin, Set.image_singleton, ← lineRead_eq_lmul]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
    exact hle (Subalgebra.mem_map.mpr ⟨g, hg, rfl⟩)
  -- the indicator of every count is made of `χ`, by the orthogonality of a primitive turn
  have hprim := AddChar.zmod_char_primitive_of_eq_one_only_at_zero n χ hχ
  have hind : ∀ a : ZMod n, (fun k : ZMod n => if k = a then (1 : K) else 0) ∈
      Algebra.adjoin K ({fun k => χ k} : Set (ZMod n → K)) := by
    intro a
    have key : (fun k : ZMod n => if k = a then (1 : K) else 0) =
        (n : K)⁻¹ • ∑ j : ZMod n, χ (-(j * a)) • (fun k : ZMod n => χ k) ^ j.val := by
      funext k
      simp only [Pi.smul_apply, Finset.sum_apply, Pi.pow_apply, smul_eq_mul]
      have h1 : ∀ j : ZMod n, χ (-(j * a)) * χ k ^ j.val = χ (j * (k - a)) := by
        intro j
        rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val,
          ← AddChar.map_add_eq_mul]
        congr 1
        ring
      simp only [h1]
      rw [AddChar.sum_mulShift _ hprim, ZMod.card]
      by_cases h : k = a
      · simp [h, hn]
      · simp [h, sub_eq_zero]
    rw [key]
    exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _) _) _
  -- every table is a sum of indicators after shifts
  have hf : f = ∑ c : ZMod n, ∑ d : ZMod n,
      f (fun x => if x = d then (1 : K) else 0) c •
        (Algebra.lmul K (ZMod n → K) (fun x => if x = c then (1 : K) else 0) *
          LinearMap.funLeft K K fun k : ZMod n => k - (c - d)) := by
    refine LinearMap.ext fun ψ => funext fun x => ?_
    have hψ : ψ = ∑ d, ψ d • fun y => if y = d then (1 : K) else 0 := by
      funext y
      simp [Finset.sum_apply]
    conv_lhs => rw [hψ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, Module.End.mul_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', Pi.mul_apply, LinearMap.funLeft_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_sub_cancel]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [hf]
  exact Subalgebra.sum_mem _ fun c _ => Subalgebra.sum_mem _ fun d _ =>
    Subalgebra.smul_mem _ (A.mul_mem (hmul _ (hind c)) (hshift _)) _

/-- **KN2.** An unfaithful turn does not make every table. If `χ k = 1` for some `k ≠ 0` of `ℤ/n`
(so that `n ≥ 2`), the write made `k` times passes the write and the reading, and it is no multiple
of `1`; so the products of the write and the reading do not make every table. -/
theorem not_span_write_read_of_not_faithful [NeZero n] (χ : AddChar (ZMod n) K) (k : ZMod n)
    (hk : k ≠ 0) (hχ : χ k = 1) :
    lineWrite K n ^ k.val * lineWrite K n = lineWrite K n * lineWrite K n ^ k.val ∧
      lineWrite K n ^ k.val * lineRead χ = lineRead χ * lineWrite K n ^ k.val ∧
      (∀ c : K, lineWrite K n ^ k.val ≠ c • 1) ∧
      Submodule.span K (Submonoid.closure {lineWrite K n, lineRead χ} :
        Set (Module.End K (ZMod n → K))) ≠ ⊤ := by
  have hTW : lineWrite K n ^ k.val * lineWrite K n = lineWrite K n * lineWrite K n ^ k.val :=
    pow_mul_comm' _ _
  have hTR : lineWrite K n ^ k.val * lineRead χ = lineRead χ * lineWrite K n ^ k.val := by
    refine LinearMap.ext fun ψ => funext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, lineWrite_pow, LinearMap.funLeft_apply,
      lineRead_apply, lineRead_apply, LinearMap.funLeft_apply, ZMod.natCast_zmod_val,
      AddChar.map_sub_eq_div, hχ, div_one]
  -- the wave that is `1` at `0` and `0` elsewhere, moved by `k`
  have hδ : (lineWrite K n ^ k.val) (fun y => if y = 0 then (1 : K) else 0) =
      fun y => if y = k then 1 else 0 := by
    funext y
    rw [lineWrite_pow, LinearMap.funLeft_apply, ZMod.natCast_zmod_val]
    simp only [sub_eq_zero]
  have hT1 : ∀ c : K, lineWrite K n ^ k.val ≠ c • 1 := by
    intro c h
    have := congrFun (hδ.symm.trans (LinearMap.congr_fun h _)) k
    simp [hk] at this
  refine ⟨hTW, hTR, hT1, fun htop => ?_⟩
  -- the tables that pass the write made `k` times
  let C : Submodule K (Module.End K (ZMod n → K)) :=
    { carrier := {X | lineWrite K n ^ k.val * X = X * lineWrite K n ^ k.val}
      add_mem' := fun {X Y} hX hY => by
        change lineWrite K n ^ k.val * X = X * lineWrite K n ^ k.val at hX
        change lineWrite K n ^ k.val * Y = Y * lineWrite K n ^ k.val at hY
        change lineWrite K n ^ k.val * (X + Y) = (X + Y) * lineWrite K n ^ k.val
        rw [mul_add, add_mul, hX, hY]
      zero_mem' := by
        change lineWrite K n ^ k.val * 0 = 0 * lineWrite K n ^ k.val
        rw [mul_zero, zero_mul]
      smul_mem' := fun c X hX => by
        change lineWrite K n ^ k.val * X = X * lineWrite K n ^ k.val at hX
        change lineWrite K n ^ k.val * (c • X) = (c • X) * lineWrite K n ^ k.val
        rw [mul_smul_comm, smul_mul_assoc, hX] }
  have hle : Submodule.span K (Submonoid.closure {lineWrite K n, lineRead χ} :
      Set (Module.End K (ZMod n → K))) ≤ C := by
    rw [Submodule.span_le]
    intro X hX
    induction hX using Submonoid.closure_induction with
    | mem X hX =>
      rcases hX with rfl | rfl
      · exact hTW
      · exact hTR
    | one =>
      change lineWrite K n ^ k.val * 1 = 1 * lineWrite K n ^ k.val
      rw [mul_one, one_mul]
    | mul X Y _ _ hX hY =>
      change lineWrite K n ^ k.val * (X * Y) = X * Y * lineWrite K n ^ k.val
      change lineWrite K n ^ k.val * X = X * lineWrite K n ^ k.val at hX
      change lineWrite K n ^ k.val * Y = Y * lineWrite K n ^ k.val at hY
      rw [← mul_assoc, hX, mul_assoc, hY, mul_assoc]
  rw [htop] at hle
  -- the table that keeps the value at `0` and puts `0` elsewhere does not pass it
  let E : Module.End K (ZMod n → K) :=
    (LinearMap.proj 0 : (ZMod n → K) →ₗ[K] K).smulRight fun y => if y = 0 then (1 : K) else 0
  have hE : lineWrite K n ^ k.val * E = E * lineWrite K n ^ k.val := hle Submodule.mem_top
  have h1 := congrFun (LinearMap.congr_fun hE fun y => if y = 0 then (1 : K) else 0) k
  have h0k : (0 : ZMod n) ≠ k := Ne.symm hk
  simp only [Module.End.mul_apply, E, LinearMap.smulRight_apply, LinearMap.proj_apply, hδ,
    ite_true, one_smul] at h1
  simp [h0k] at h1

/-- **KN3.** A faithful turn into `K` exists exactly when `K` has a primitive `n`-th root of
unity. -/
theorem exists_faithful_iff [NeZero n] :
    (∃ χ : AddChar (ZMod n) K, ∀ k, χ k = 1 → k = 0) ↔ ∃ ζ : K, IsPrimitiveRoot ζ n := by
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨χ 1, ⟨?_, fun l hl => ?_⟩⟩
    · rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self,
        AddChar.map_zero_eq_one]
    · rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one] at hl
      exact (ZMod.natCast_eq_zero_iff l n).mp (hχ _ hl)
  · rintro ⟨ζ, hζ⟩
    let χ : AddChar (ZMod n) K :=
      { toFun := fun k => ζ ^ k.val
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by
          rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add] }
    refine ⟨χ, fun k hk => ?_⟩
    have h1 : n ∣ k.val := hζ.dvd_of_pow_eq_one _ hk
    exact (ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt k))

/-- **KN4.** No real turn for a dial of 3 or more: for `n ≥ 3` every real turn of `ℤ/n` takes only
the values `1` and `-1`, and none is faithful. -/
theorem real_turn_not_faithful (hn : 3 ≤ n) (χ : AddChar (ZMod n) ℝ) :
    (∀ k, χ k = 1 ∨ χ k = -1) ∧ ¬ ∀ k, χ k = 1 → k = 0 := by
  have : NeZero n := ⟨by omega⟩
  have hvals : ∀ k, χ k = 1 ∨ χ k = -1 := by
    intro k
    have h : χ k ^ n = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        AddChar.map_zero_eq_one]
    have h' : |χ k| ^ n = 1 := by rw [pow_abs, h, abs_one]
    have h'' : |χ k| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by omega)).mp h'
    exact (abs_eq zero_le_one).mp h''
  refine ⟨hvals, fun hf => ?_⟩
  have h2 : χ 2 = 1 := by
    rw [← one_add_one_eq_two, AddChar.map_add_eq_mul]
    rcases hvals 1 with h | h <;> rw [h] <;> norm_num
  have h20 : (2 : ZMod n) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 n).mp h')
    omega
  exact h20 (hf 2 h2)

/-- **KN5.** The dial's standard turn is faithful. -/
theorem stdAddChar_faithful [NeZero n] : ∀ k : ZMod n, (ZMod.stdAddChar k : ℂ) = 1 → k = 0 :=
  fun _ h => ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)

/-- **KN5.** The values of the dial's standard turn have size `1`. -/
theorem stdAddChar_norm [NeZero n] : ∀ k : ZMod n, ‖(ZMod.stdAddChar k : ℂ)‖ = 1 := fun k => by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- **KN5.** So the reading by the dial's standard turn keeps the sum of the squares of the sizes
of a wave's numbers. -/
theorem lineRead_stdAddChar_norm [NeZero n] (ψ : ZMod n → ℂ) :
    ∑ k, ‖lineRead ZMod.stdAddChar ψ k‖ ^ 2 = ∑ k, ‖ψ k‖ ^ 2 := by
  simp only [lineRead_apply, norm_mul, stdAddChar_norm, one_mul]

end Artform.Stages
