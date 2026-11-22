import ArtformStages.FillingWaves
import ArtformStages.KindOfNumber

/-!
# The kind of number on a stage

Finding 481 of the research ledger on a layered universe: the kind of number of finding 473, on
the waves of the fillings of a stage (`FillingWaves.lean`). For a stage with finitely many acts
and laws and at least one act, on the dial of `n ≥ 1`, the *reading by a turn*
`χ : AddChar (ZMod n) ℂ` of a line `ℓ` multiplies the value at a filling `c` by `χ` of `c`'s count
on `ℓ`.

* `Stage.waveReadBy`, `Stage.waveReadBy_std` (KN8): the reading by the dial's standard turn is the
  reading `Stage.waveRead` of finding 472;
* `Stage.span_write_readBy_iff` (KN8): the writes of the lines and the readings by `χ` make every
  table of the waves exactly when `χ` is faithful, `χ k = 1` only for `k = 0`.

With a faithful `χ`, `χ 1` is a primitive `n`-th root of unity, so the standard turn is `χ` made
some `b` times, and the reading of finding 472 is the reading by `χ` made `b` times;
`Stage.span_write_read` then makes every table. If `χ k = 1` for some `k ≠ 0`, the write of one
line made `k` times passes every write and every reading by `χ`, but not the table that keeps the
value at the empty filling and puts `0` elsewhere.
-/

noncomputable section

namespace Artform.Stages

namespace Stage

variable {α : Type*} (S : Stage α) (n : ℕ)

/-- **KN8.** The reading of the line `ℓ` by the turn `χ`: it multiplies the value at `c` by
`χ (c ℓ)`. -/
def waveReadBy (χ : AddChar (ZMod n) ℂ) (ℓ : α × S.World) : Module.End ℂ (S.Wave n) where
  toFun ψ c := χ (c ℓ) * ψ c
  map_add' ψ φ := funext fun c => mul_add _ _ _
  map_smul' a ψ := funext fun c => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The reading by `χ`, read at `c`. -/
theorem waveReadBy_apply (χ : AddChar (ZMod n) ℂ) (ℓ : α × S.World) (ψ : S.Wave n)
    (c : α × S.World → ZMod n) : S.waveReadBy n χ ℓ ψ c = χ (c ℓ) * ψ c := rfl

/-- **KN8.** The reading by the dial's standard turn is the reading of finding 472. -/
theorem waveReadBy_std [NeZero n] : S.waveReadBy n ZMod.stdAddChar = S.waveRead n := by
  funext ℓ
  exact LinearMap.ext fun ψ => funext fun c => rfl

/-- The reading by `χ` is the multiplication by the turn of the count. -/
theorem waveReadBy_eq_lmul (χ : AddChar (ZMod n) ℂ) (ℓ : α × S.World) :
    S.waveReadBy n χ ℓ = Algebra.lmul ℂ (S.Wave n) fun c => χ (c ℓ) := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  rfl

/-- A faithful turn sends `1` to a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_of_faithful [NeZero n] (χ : AddChar (ZMod n) ℂ)
    (hχ : ∀ k, χ k = 1 → k = 0) : IsPrimitiveRoot (χ 1) n := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self,
      AddChar.map_zero_eq_one]
  · rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one] at hl
    exact (ZMod.natCast_eq_zero_iff l n).mp (hχ _ hl)

/-- With a faithful turn `χ`, the standard turn is `χ` made some `b` times. -/
theorem exists_std_eq_pow [NeZero n] (χ : AddChar (ZMod n) ℂ) (hχ : ∀ k, χ k = 1 → k = 0) :
    ∃ b : ℕ, ∀ k : ZMod n, ZMod.stdAddChar k = χ k ^ b := by
  have hprim := isPrimitiveRoot_of_faithful n χ hχ
  have h1 : (ZMod.stdAddChar (1 : ZMod n)) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self,
      AddChar.map_zero_eq_one]
  obtain ⟨b, -, hb⟩ := hprim.eq_pow_of_pow_eq_one h1
  refine ⟨b, fun k => ?_⟩
  have hk : k = k.val • (1 : ZMod n) := by rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [hk, AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow, ← hb, ← pow_mul, ← pow_mul,
    mul_comm]

/-- **KN8.** The writes of the lines and the readings by `χ` make every table of the waves on the
fillings exactly when `χ` is faithful. -/
theorem span_write_readBy_iff [Finite α] [DecidableEq α] [Finite S.World] [DecidableEq S.World]
    [Nonempty α] [NeZero n] (χ : AddChar (ZMod n) ℂ) :
    Submodule.span ℂ (Submonoid.closure (Set.range (S.waveWrite n) ∪ Set.range (S.waveReadBy n χ)) :
        Set (Module.End ℂ (S.Wave n))) = ⊤ ↔ ∀ k, χ k = 1 → k = 0 := by
  classical
  constructor
  · intro htop k hk
    by_contra hk0
    obtain ⟨a₀⟩ := ‹Nonempty α›
    let ℓ₀ : α × S.World := (a₀, 1)
    let v : α × S.World → ZMod n := Pi.single ℓ₀ k
    have hv : v ≠ 0 := fun h => hk0 (by simpa [v] using congrFun h ℓ₀)
    have hχv : ∀ ℓ, χ (v ℓ) = 1 := fun ℓ => by
      by_cases h : ℓ = ℓ₀
      · rw [h]
        simpa [v] using hk
      · simp [v, h]
    let T := S.waveShift n v
    have hTW : ∀ ℓ, T * S.waveWrite n ℓ = S.waveWrite n ℓ * T := fun ℓ => by
      rw [waveWrite, waveShift_mul, waveShift_mul, add_comm]
    have hTR : ∀ ℓ, T * S.waveReadBy n χ ℓ = S.waveReadBy n χ ℓ * T := fun ℓ => by
      refine LinearMap.ext fun ψ => funext fun c => ?_
      simp only [T, Module.End.mul_apply, waveShift_apply, waveReadBy_apply, Pi.sub_apply,
        AddChar.map_sub_eq_div, hχv, div_one]
    -- the tables that pass `T`
    let C : Submodule ℂ (Module.End ℂ (S.Wave n)) :=
      { carrier := {X | T * X = X * T}
        add_mem' := fun {X Y} hX hY => by
          change T * X = X * T at hX
          change T * Y = Y * T at hY
          change T * (X + Y) = (X + Y) * T
          rw [mul_add, add_mul, hX, hY]
        zero_mem' := by
          change T * 0 = 0 * T
          rw [mul_zero, zero_mul]
        smul_mem' := fun c X hX => by
          change T * X = X * T at hX
          change T * (c • X) = (c • X) * T
          rw [mul_smul_comm, smul_mul_assoc, hX] }
    have hle : Submodule.span ℂ (Submonoid.closure
        (Set.range (S.waveWrite n) ∪ Set.range (S.waveReadBy n χ)) :
          Set (Module.End ℂ (S.Wave n))) ≤ C := by
      rw [Submodule.span_le]
      intro X hX
      induction hX using Submonoid.closure_induction with
      | mem X hX =>
        rcases hX with ⟨ℓ, rfl⟩ | ⟨ℓ, rfl⟩
        · exact hTW ℓ
        · exact hTR ℓ
      | one =>
        change T * 1 = 1 * T
        rw [mul_one, one_mul]
      | mul X Y _ _ hX hY =>
        change T * (X * Y) = X * Y * T
        change T * X = X * T at hX
        change T * Y = Y * T at hY
        rw [← mul_assoc, hX, mul_assoc, hY, mul_assoc]
    rw [htop] at hle
    -- the table that keeps the value at the empty filling and puts `0` elsewhere
    let δ₀ : S.Wave n := fun c => if c = 0 then 1 else 0
    let E : Module.End ℂ (S.Wave n) :=
      (LinearMap.proj 0 : S.Wave n →ₗ[ℂ] ℂ).smulRight δ₀
    have hE : T * E = E * T := hle Submodule.mem_top
    have h1 := congrFun (LinearMap.congr_fun hE δ₀) v
    have hv' : (0 : α × S.World → ZMod n) - v ≠ 0 := by
      rw [zero_sub, neg_ne_zero]
      exact hv
    simp only [Module.End.mul_apply, E, T, δ₀, LinearMap.smulRight_apply, LinearMap.proj_apply,
      waveShift_apply, sub_self, hv', hv, ↓reduceIte, one_smul, zero_smul, Pi.smul_apply] at h1
    exact one_ne_zero h1
  · intro hχ
    obtain ⟨b, hb⟩ := exists_std_eq_pow n χ hχ
    have hread : ∀ ℓ, S.waveRead n ℓ = S.waveReadBy n χ ℓ ^ b := fun ℓ => by
      rw [waveRead_eq_lmul, waveReadBy_eq_lmul, ← map_pow]
      congr 1
      funext c
      rw [Pi.pow_apply, hb]
    have hstd := S.span_write_read n
    rw [← Algebra.adjoin_eq_span, eq_top_iff] at hstd ⊢
    refine hstd.trans (Subalgebra.toSubmodule.monotone (Algebra.adjoin_le ?_))
    refine Set.union_subset (fun X hX => Algebra.subset_adjoin (Or.inl hX)) ?_
    rintro _ ⟨ℓ, rfl⟩
    have hmem : S.waveReadBy n χ ℓ ∈
        Algebra.adjoin ℂ (Set.range (S.waveWrite n) ∪ Set.range (S.waveReadBy n χ)) :=
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self ℓ))
    rw [SetLike.mem_coe, hread]
    exact Subalgebra.pow_mem _ hmem b

end Stage

end Artform.Stages
