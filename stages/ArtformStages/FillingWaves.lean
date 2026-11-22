import ArtformStages.KeepField

/-!
# Waves on the fillings

Layer 6 of the research ledger on a layered universe puts numbers on the laws (charter D16). Here
a *wave* is a complex number on every filling of a stage's lines on the dial of `n`, for a stage
with finitely many acts and laws: the fillings and their ends are those of `KeepField.lean`
(finding 472 of the ledger). Three kinds of table act on the waves:

* the *write* of a line `ℓ` moves every wave to the filling with one more on `ℓ`: its value at `c`
  is the old value at `c` less one on `ℓ`;
* the *reading* of `ℓ` multiplies the value at `c` by the turn of `c`'s count on `ℓ`, the dial's
  standard character `ZMod.stdAddChar`, `k ↦ e^{2πik/n}`;
* the *kept law* of a closed filling `z`, one whose ends are `0`, moves every wave by `z`.

The statements:

* `Stage.waveWrite`, `Stage.waveRead`, `Stage.waveKept`, `Stage.read_write`, `Stage.read_kept`,
  `Stage.write_comm`, `Stage.write_kept_comm`, `Stage.read_comm` (WV1): Weyl's relation;
* `Stage.waveSector`, `Stage.waveKept_sector`, `Stage.waveRead_sector`, `Stage.waveWrite_sector`
  (WV2): a kept law and a reading keep every charge sector, and the write of `ℓ` takes the sector
  of `ρ` to that of `ρ` with one more at the head of `ℓ` and one less at its tail;
* `Stage.waveWrite_norm`, `Stage.waveRead_norm`, `Stage.waveKept_norm` (WV3): the three kinds of
  table keep the sum of the squares of the sizes of a wave's numbers;
* `Stage.span_write_read` (WV4): every linear map of the waves is a sum of products of writes and
  readings;
* `Stage.kept_comm`, `Stage.wavePart`, `Stage.write_part`, `Stage.kept_part`, `Stage.read_part`
  (WV5): kept laws pass each other; writes and kept laws keep every part, and a reading moves a
  part, each kept law's number multiplied by the turn of that law's count on the line, to the
  power `-1`.

The proof of WV4 writes each table as the sum of its entries times the units of the fillings. The
unit at `(c, d)` is the shift by `c - d`, a product of writes, followed by the multiplication by the
indicator of `c`, which the readings make by the orthogonality of the turns,
`∑ j, e^{2πij(x - a)/n} = n [x = a]`.
-/

noncomputable section

namespace Artform.Stages

namespace Stage

variable {α : Type*} (S : Stage α) (n : ℕ)

/-- A wave: a complex number on every filling of the lines on the dial of `n`. -/
abbrev Wave : Type _ := (α × S.World → ZMod n) → ℂ

/-- The shift by a filling `v`: the value at `c` is the old value at `c - v`. -/
def waveShift (v : α × S.World → ZMod n) : Module.End ℂ (S.Wave n) :=
  LinearMap.funLeft ℂ ℂ fun c => c - v

/-- **WV1.** The write of the line `ℓ`: it moves every wave to the filling with one more on `ℓ`;
its value at `c` is the old value at `c` less one on `ℓ`. -/
def waveWrite [DecidableEq α] [DecidableEq S.World] (ℓ : α × S.World) :
    Module.End ℂ (S.Wave n) := S.waveShift n (Pi.single ℓ 1)

/-- **WV1.** The reading of the line `ℓ`: it multiplies the value at `c` by the turn of `c`'s count
on `ℓ`. -/
def waveRead [NeZero n] (ℓ : α × S.World) : Module.End ℂ (S.Wave n) where
  toFun ψ c := ZMod.stdAddChar (c ℓ) * ψ c
  map_add' ψ φ := funext fun c => mul_add _ _ _
  map_smul' a ψ := funext fun c => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **WV1.** The kept law of a closed filling `z`, one whose ends are `0`: it moves every wave by
`z`. -/
def waveKept [Fintype α] [Fintype S.World] [DecidableEq S.World] (z : (S.endsDial n).ker) :
    Module.End ℂ (S.Wave n) :=
  S.waveShift n z

/-- The shift by `v`, read at `c`. -/
theorem waveShift_apply (v : α × S.World → ZMod n) (ψ : S.Wave n) (c : α × S.World → ZMod n) :
    S.waveShift n v ψ c = ψ (c - v) := rfl

/-- The write of `ℓ`, read at `c`. -/
theorem waveWrite_apply [DecidableEq α] [DecidableEq S.World] (ℓ : α × S.World) (ψ : S.Wave n)
    (c : α × S.World → ZMod n) :
    S.waveWrite n ℓ ψ c = ψ (c - Pi.single ℓ 1) := rfl

/-- The reading of `ℓ`, read at `c`. -/
theorem waveRead_apply [NeZero n] (ℓ : α × S.World) (ψ : S.Wave n) (c : α × S.World → ZMod n) :
    S.waveRead n ℓ ψ c = ZMod.stdAddChar (c ℓ) * ψ c := rfl

/-- The kept law of `z`, read at `c`. -/
theorem waveKept_apply [Fintype α] [Fintype S.World] [DecidableEq S.World]
    (z : (S.endsDial n).ker) (ψ : S.Wave n) (c : α × S.World → ZMod n) :
    S.waveKept n z ψ c = ψ (c - z) := rfl

/-- Shifts add: the shift by `v` after the shift by `w` is the shift by `v + w`. -/
theorem waveShift_mul (v w : α × S.World → ZMod n) :
    S.waveShift n v * S.waveShift n w = S.waveShift n (v + w) := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  simp only [Module.End.mul_apply, waveShift_apply, sub_sub]

/-- The shift by `0` is the identity. -/
theorem waveShift_zero : S.waveShift n 0 = 1 := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  simp only [waveShift_apply, sub_zero, Module.End.one_apply]

/-! ### Weyl's relation -/

/-- **WV1.** Weyl's relation: the reading of `ℓ` after the write of `ℓ'` is the turn of `1` if
`ℓ = ℓ'`, of `0` otherwise, times the write of `ℓ'` after the reading of `ℓ`. -/
theorem read_write [DecidableEq α] [DecidableEq S.World] [NeZero n] (ℓ ℓ' : α × S.World) :
    S.waveRead n ℓ * S.waveWrite n ℓ' =
      ZMod.stdAddChar (if ℓ = ℓ' then 1 else 0 : ZMod n) • (S.waveWrite n ℓ' * S.waveRead n ℓ) := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    waveRead_apply, waveWrite_apply, Pi.sub_apply, Pi.single_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_sub_cancel]

/-- **WV1.** The reading of `ℓ` after the kept law of `z` is the turn of `z`'s count on `ℓ` times
the kept law of `z` after the reading of `ℓ`. -/
theorem read_kept [Fintype α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
    (ℓ : α × S.World) (z : (S.endsDial n).ker) :
    S.waveRead n ℓ * S.waveKept n z =
      ZMod.stdAddChar ((z : α × S.World → ZMod n) ℓ) • (S.waveKept n z * S.waveRead n ℓ) := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    waveRead_apply, waveKept_apply, Pi.sub_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_sub_cancel]

/-- **WV1.** Writes pass each other. -/
theorem write_comm [DecidableEq α] [DecidableEq S.World] (ℓ ℓ' : α × S.World) :
    S.waveWrite n ℓ * S.waveWrite n ℓ' = S.waveWrite n ℓ' * S.waveWrite n ℓ := by
  rw [waveWrite, waveWrite, waveShift_mul, waveShift_mul, add_comm]

/-- **WV1.** Writes and kept laws pass each other. -/
theorem write_kept_comm [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World]
    (ℓ : α × S.World) (z : (S.endsDial n).ker) :
    S.waveWrite n ℓ * S.waveKept n z = S.waveKept n z * S.waveWrite n ℓ := by
  rw [waveWrite, waveKept, waveShift_mul, waveShift_mul, add_comm]

/-- **WV1.** Readings pass each other. -/
theorem read_comm [NeZero n] (ℓ ℓ' : α × S.World) :
    S.waveRead n ℓ * S.waveRead n ℓ' = S.waveRead n ℓ' * S.waveRead n ℓ := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  simp only [Module.End.mul_apply, waveRead_apply]
  ring

/-! ### Gauss's law on the waves -/

/-- **WV2.** The charge sector of an assignment `ρ` of ends: the waves that are `0` off the fillings
whose ends are `ρ`. -/
def waveSector [Fintype α] [Fintype S.World] [DecidableEq S.World] (ρ : S.World → ZMod n) :
    Submodule ℂ (S.Wave n) where
  carrier := {ψ | ∀ c, S.endsDial n c ≠ ρ → ψ c = 0}
  add_mem' {ψ φ} hψ hφ c hc := by
    simp only [Pi.add_apply, hψ c hc, hφ c hc, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' a ψ hψ c hc := by
    simp only [Pi.smul_apply, hψ c hc, smul_zero]

/-- The ends of one on the line `ℓ` on the dial: one at its head less one at its tail. -/
theorem endsDial_single [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World]
    (ℓ : α × S.World) :
    S.endsDial n (Pi.single ℓ 1) = Pi.single (S.head ℓ) 1 - Pi.single ℓ.2 1 := by
  simp only [endsDial, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro p _ hp
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ ℓ) h

/-- **WV2.** A kept law takes every charge sector to itself. -/
theorem waveKept_sector [Fintype α] [Fintype S.World] [DecidableEq S.World]
    (z : (S.endsDial n).ker) (ρ : S.World → ZMod n) {ψ : S.Wave n}
    (hψ : ψ ∈ S.waveSector n ρ) : S.waveKept n z ψ ∈ S.waveSector n ρ := by
  intro c hc
  rw [waveKept_apply]
  apply hψ
  rw [map_sub, AddMonoidHom.mem_ker.mp z.2, sub_zero]
  exact hc

/-- **WV2.** A reading takes every charge sector to itself. -/
theorem waveRead_sector [Fintype α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
    (ℓ : α × S.World) (ρ : S.World → ZMod n) {ψ : S.Wave n}
    (hψ : ψ ∈ S.waveSector n ρ) : S.waveRead n ℓ ψ ∈ S.waveSector n ρ := by
  intro c hc
  rw [waveRead_apply, hψ c hc, mul_zero]

/-- **WV2.** The write of `ℓ` takes the sector of `ρ` to the sector of `ρ` with one more at the
head of `ℓ` and one less at its tail. -/
theorem waveWrite_sector [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World]
    (ℓ : α × S.World) (ρ : S.World → ZMod n) {ψ : S.Wave n}
    (hψ : ψ ∈ S.waveSector n ρ) :
    S.waveWrite n ℓ ψ ∈ S.waveSector n (ρ + Pi.single (S.head ℓ) 1 - Pi.single ℓ.2 1) := by
  intro c hc
  rw [waveWrite_apply]
  apply hψ
  rw [map_sub, endsDial_single]
  intro h
  apply hc
  rw [← h]
  abel

/-! ### The readings make the indicators -/

/-- The reading of `ℓ` is the multiplication by the turn of the count on `ℓ`. -/
theorem waveRead_eq_lmul [NeZero n] (ℓ : α × S.World) :
    S.waveRead n ℓ = Algebra.lmul ℂ (S.Wave n) fun c => ZMod.stdAddChar (c ℓ) := by
  refine LinearMap.ext fun ψ => funext fun c => ?_
  rfl

/-- The indicator of the count `a` on the line `ℓ` is made of the turns of that count, by the
orthogonality of the turns. -/
theorem indicator_line_mem [NeZero n] (ℓ : α × S.World) (a : ZMod n) :
    (fun c : α × S.World → ZMod n => if c ℓ = a then (1 : ℂ) else 0) ∈
      Algebra.adjoin ℂ (Set.range fun ℓ : α × S.World =>
        fun c : α × S.World → ZMod n => ZMod.stdAddChar (c ℓ)) := by
  have key : (fun c : α × S.World → ZMod n => if c ℓ = a then (1 : ℂ) else 0) =
      (n : ℂ)⁻¹ • ∑ j : ZMod n, ZMod.stdAddChar (-(j * a)) •
        (fun c : α × S.World → ZMod n => ZMod.stdAddChar (c ℓ)) ^ j.val := by
    funext c
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.pow_apply, smul_eq_mul]
    have h1 : ∀ j : ZMod n, ZMod.stdAddChar (-(j * a)) * ZMod.stdAddChar (c ℓ) ^ j.val =
        ZMod.stdAddChar (j * (c ℓ - a)) := by
      intro j
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp only [h1]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    by_cases h : c ℓ = a
    · simp [h, hn]
    · simp [h, sub_eq_zero]
  rw [key]
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self ℓ)) _) _) _

/-- The indicator of a filling is made of the turns of the counts on the lines. -/
theorem indicator_mem [Fintype α] [Fintype S.World] [NeZero n] (c₀ : α × S.World → ZMod n) :
    (fun c : α × S.World → ZMod n => if c = c₀ then (1 : ℂ) else 0) ∈
      Algebra.adjoin ℂ (Set.range fun ℓ : α × S.World =>
        fun c : α × S.World → ZMod n => ZMod.stdAddChar (c ℓ)) := by
  have key : (fun c : α × S.World → ZMod n => if c = c₀ then (1 : ℂ) else 0) =
      ∏ ℓ, fun c : α × S.World → ZMod n => if c ℓ = c₀ ℓ then (1 : ℂ) else 0 := by
    funext c
    rw [Finset.prod_apply, Fintype.prod_boole]
    simp only [funext_iff]
  rw [key]
  exact Subalgebra.prod_mem _ fun ℓ _ => S.indicator_line_mem n ℓ (c₀ ℓ)

/-! ### The sum of squares -/

section Finite

variable [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World] [NeZero n]

/-- A shift keeps the sum of the squares of the sizes of a wave's numbers. -/
theorem waveShift_norm (v : α × S.World → ZMod n) (ψ : S.Wave n) :
    ∑ c, ‖S.waveShift n v ψ c‖ ^ 2 = ∑ c, ‖ψ c‖ ^ 2 :=
  Fintype.sum_equiv (Equiv.subRight v) _ _ fun _ => rfl

/-- **WV3.** The write keeps the sum of the squares of the sizes of a wave's numbers. -/
theorem waveWrite_norm (ℓ : α × S.World) (ψ : S.Wave n) :
    ∑ c, ‖S.waveWrite n ℓ ψ c‖ ^ 2 = ∑ c, ‖ψ c‖ ^ 2 :=
  S.waveShift_norm n _ ψ

/-- **WV3.** The reading keeps the sum of the squares of the sizes of a wave's numbers. -/
theorem waveRead_norm (ℓ : α × S.World) (ψ : S.Wave n) :
    ∑ c, ‖S.waveRead n ℓ ψ c‖ ^ 2 = ∑ c, ‖ψ c‖ ^ 2 := by
  simp only [waveRead_apply, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

/-- **WV3.** A kept law keeps the sum of the squares of the sizes of a wave's numbers. -/
theorem waveKept_norm (z : (S.endsDial n).ker) (ψ : S.Wave n) :
    ∑ c, ‖S.waveKept n z ψ c‖ ^ 2 = ∑ c, ‖ψ c‖ ^ 2 :=
  S.waveShift_norm n _ ψ

end Finite

/-! ### Writes and readings make every table -/

/-- **WV4.** Writes and readings make every table: every linear map of the waves to themselves is
a sum, with complex coefficients, of products of writes and readings. -/
theorem span_write_read [Finite α] [DecidableEq α] [Finite S.World] [DecidableEq S.World]
    [NeZero n] :
    Submodule.span ℂ (Submonoid.closure (Set.range (S.waveWrite n) ∪ Set.range (S.waveRead n)) :
      Set (Module.End ℂ (S.Wave n))) = ⊤ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite S.World
  rw [← Algebra.adjoin_eq_span, eq_top_iff]
  intro f _
  rw [Subalgebra.mem_toSubmodule]
  set A := Algebra.adjoin ℂ (Set.range (S.waveWrite n) ∪ Set.range (S.waveRead n))
  -- every shift is a product of writes
  have hshift : ∀ v, S.waveShift n v ∈ A := by
    intro v
    let M : AddSubmonoid (α × S.World → ZMod n) :=
      { carrier := {v | S.waveShift n v ∈ A}
        zero_mem' := by
          change S.waveShift n 0 ∈ A
          rw [waveShift_zero]
          exact A.one_mem
        add_mem' := fun {v w} hv hw => by
          change S.waveShift n (v + w) ∈ A
          rw [← waveShift_mul]
          exact A.mul_mem hv hw }
    rw [← Finset.univ_sum_single v]
    refine AddSubmonoid.sum_mem M fun ℓ _ => ?_
    have h1 : (Pi.single ℓ (v ℓ) : α × S.World → ZMod n) = (v ℓ).val • Pi.single ℓ 1 := by
      rw [← Pi.single_smul', nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [h1]
    exact AddSubmonoid.nsmul_mem M (Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)) _
  -- every multiplication by a function made of the turns is in `A`
  have hmul : ∀ g ∈ Algebra.adjoin ℂ (Set.range fun ℓ : α × S.World =>
      fun c : α × S.World → ZMod n => ZMod.stdAddChar (c ℓ)),
      Algebra.lmul ℂ (S.Wave n) g ∈ A := by
    intro g hg
    have hle : (Algebra.adjoin ℂ (Set.range fun ℓ : α × S.World =>
        fun c : α × S.World → ZMod n => ZMod.stdAddChar (c ℓ))).map
          (Algebra.lmul ℂ (S.Wave n)) ≤ A := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ ⟨_, ⟨ℓ, rfl⟩, rfl⟩
      exact Or.inr ⟨ℓ, S.waveRead_eq_lmul n ℓ⟩
    exact hle (Subalgebra.mem_map.mpr ⟨g, hg, rfl⟩)
  -- every table is a sum of indicators after shifts
  have hf : f = ∑ c : α × S.World → ZMod n, ∑ d : α × S.World → ZMod n,
      f (fun x => if x = d then (1 : ℂ) else 0) c •
        (Algebra.lmul ℂ (S.Wave n) (fun x => if x = c then (1 : ℂ) else 0) *
          S.waveShift n (c - d)) := by
    refine LinearMap.ext fun ψ => funext fun x => ?_
    have hψ : ψ = ∑ d, ψ d • fun y => if y = d then (1 : ℂ) else 0 := by
      funext y
      simp [Finset.sum_apply]
    conv_lhs => rw [hψ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, Module.End.mul_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', Pi.mul_apply, waveShift_apply, ite_mul, one_mul, zero_mul, mul_ite,
      mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_sub_cancel]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [hf]
  exact Subalgebra.sum_mem _ fun c _ => Subalgebra.sum_mem _ fun d _ =>
    Subalgebra.smul_mem _ (A.mul_mem (hmul _ (S.indicator_mem n c)) (hshift _)) _

/-! ### The parts -/

/-- **WV5.** Kept laws pass each other. -/
theorem kept_comm [Fintype α] [Fintype S.World] [DecidableEq S.World] (z z' : (S.endsDial n).ker) :
    S.waveKept n z * S.waveKept n z' = S.waveKept n z' * S.waveKept n z := by
  rw [waveKept, waveKept, waveShift_mul, waveShift_mul, add_comm]

/-- **WV5.** The part of `χ`: the waves on which every kept law `z` acts as the one number
`χ z`. -/
def wavePart [Fintype α] [Fintype S.World] [DecidableEq S.World] (χ : (S.endsDial n).ker → ℂ) :
    Submodule ℂ (S.Wave n) where
  carrier := {ψ | ∀ z, S.waveKept n z ψ = χ z • ψ}
  add_mem' {ψ φ} hψ hφ z := by rw [map_add, hψ z, hφ z, smul_add]
  zero_mem' z := by rw [map_zero, smul_zero]
  smul_mem' a ψ hψ z := by rw [map_smul, hψ z, smul_comm]

/-- **WV5.** A write keeps every part, with the same numbers. -/
theorem write_part [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World]
    (ℓ : α × S.World) (χ : (S.endsDial n).ker → ℂ) {ψ : S.Wave n}
    (hψ : ψ ∈ S.wavePart n χ) : S.waveWrite n ℓ ψ ∈ S.wavePart n χ := by
  intro z
  rw [← Module.End.mul_apply, ← write_kept_comm, Module.End.mul_apply, hψ z, map_smul]

/-- **WV5.** A kept law keeps every part, with the same numbers. -/
theorem kept_part [Fintype α] [Fintype S.World] [DecidableEq S.World] (z' : (S.endsDial n).ker)
    (χ : (S.endsDial n).ker → ℂ) {ψ : S.Wave n}
    (hψ : ψ ∈ S.wavePart n χ) : S.waveKept n z' ψ ∈ S.wavePart n χ := by
  intro z
  rw [← Module.End.mul_apply, kept_comm, Module.End.mul_apply, hψ z, map_smul]

/-- **WV5.** The reading of `ℓ` takes the part of `χ` to the part in which each kept law's number
is multiplied by the turn of that law's count on `ℓ`, to the power `-1`. -/
theorem read_part [Fintype α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
    (ℓ : α × S.World) (χ : (S.endsDial n).ker → ℂ) {ψ : S.Wave n}
    (hψ : ψ ∈ S.wavePart n χ) :
    S.waveRead n ℓ ψ ∈
      S.wavePart n fun z => χ z * (ZMod.stdAddChar ((z : α × S.World → ZMod n) ℓ))⁻¹ := by
  intro z
  funext c
  have h := congrFun (hψ z) c
  rw [waveKept_apply] at h
  simp only [waveKept_apply, waveRead_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, h,
    AddChar.map_sub_eq_div, div_eq_mul_inv]
  ring

end Stage

end Artform.Stages
