import ArtformStages.Trail

/-!
# Keep, by the trail

THEORY.md defines `keep(S; M)` by the trail: a closed walk of `S` is rest exactly when its
trail is in `M`, where `M` is a set of closed trails that holds sums and differences and
looks the same from every dot. Its Theorems A and B are proved here in that form.

* **Theorem A.** `C` is a carry over `S` exactly when it is over `S` and keeps of a walk
  nothing but its dot in `S` and its trail (`isCarry_iff_trail`).
* **Theorem B.** `keep(S; M)` is a carry over `S`, a closed walk is rest in it exactly when
  its trail is in `M` (`keepTrail_isCarry`, `mem_rest_keepTrail`), and every carry over `S`
  is `keep(S; M)` for the `M` of its own trails (`rest_eq_keepTrail_of_isCarry`).
-/

noncomputable section

namespace Artform.Stages

open Subgroup

variable {α : Type*}

namespace Stage

variable (S : Stage α) {C : Stage α}

/-- **Theorem A** (1 and 2). `C` is a carry over `S` exactly when it is over `S`, and two
walks that end at one dot of `S` and leave one trail there are one law of `C`. -/
theorem isCarry_iff_trail :
    C.IsCarry S ↔ C.IsOver S ∧
      ∀ u v, S.law u = S.law v → S.trail u = S.trail v → C.law u = C.law v := by
  constructor
  · intro h
    refine ⟨h.1, fun u v hlaw htrail => ?_⟩
    have hk : S.keep.law u = S.keep.law v := S.keep_law_eq_iff.mpr ⟨hlaw, htrail⟩
    rw [C.law_eq_law_iff]
    exact keep_isOver_of_isCarry h (S.keep.law_eq_law_iff.mp hk)
  · rintro ⟨hover, h⟩
    refine isCarry_iff.mpr ⟨fun w hw => ?_, hover⟩
    have hw1 : S.law w = S.law 1 := by
      rw [map_one, S.law_eq_one_iff]
      exact commutator_le_left _ _ hw
    have hw2 : S.trail w = S.trail 1 := by
      rw [trail_one, S.trail_eq_zero_of_mem_commutator hw]
    have := h w 1 hw1 hw2
    rwa [map_one, C.law_eq_one_iff] at this

/-- **T2(b).** What a closed walk does in a carry is fixed by its trail: two closed walks
of `S` that leave one trail are one law of the carry. -/
theorem law_eq_of_trail_eq (h : C.IsCarry S) {n m : FreeGroup α} (hn : n ∈ S.rest)
    (hm : m ∈ S.rest) (ht : S.trail n = S.trail m) : C.law n = C.law m := by
  refine ((S.isCarry_iff_trail).mp h).2 n m ?_ ht
  rw [S.law_eq_one_iff.mpr hn, S.law_eq_one_iff.mpr hm]

/-- **T2(a).** In a carry every face has one kept law, its carry: the closed walk `r` of
`S`, made at the end of a walk and with that walk undone after it, does the same in the
carry for any two walks to one dot. -/
theorem law_conj_eq_of_law_eq (h : C.IsCarry S) {r : FreeGroup α} (hr : r ∈ S.rest)
    {w w' : FreeGroup α} (hw : S.law w = S.law w') :
    C.law (w * r * w⁻¹) = C.law (w' * r * w'⁻¹) := by
  have hn := (inferInstance : S.rest.Normal).conj_mem r hr
  refine law_eq_of_trail_eq S h (hn w) (hn w') ?_
  rw [S.trail_conj w hr, S.trail_conj w' hr, hw]

/-- Condition (ii) of THEORY.md §3.4: a set of trails that looks the same from every dot. -/
def ShiftInvariant (M : AddSubgroup S.Chain) : Prop := ∀ g, ∀ c ∈ M, S.shift g c ∈ M

/-- The closed walks of `S` whose trail lies in `M`. -/
def closedWith (M : AddSubgroup S.Chain) : Subgroup (FreeGroup α) where
  carrier := {n | n ∈ S.rest ∧ S.trail n ∈ M}
  mul_mem' := by
    rintro a b ⟨ha, hta⟩ ⟨hb, htb⟩
    refine ⟨S.rest.mul_mem ha hb, ?_⟩
    rw [S.trail_mul_of_mem_rest ha]
    exact M.add_mem hta htb
  one_mem' := ⟨S.rest.one_mem, by
    rw [trail_one]
    exact M.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, hta⟩
    refine ⟨S.rest.inv_mem ha, ?_⟩
    rw [S.trail_inv_of_mem_rest ha]
    exact M.neg_mem hta

variable {S}

theorem mem_closedWith {M : AddSubgroup S.Chain} {n : FreeGroup α} :
    n ∈ S.closedWith M ↔ n ∈ S.rest ∧ S.trail n ∈ M := Iff.rfl

theorem closedWith_normal {M : AddSubgroup S.Chain} (hM : S.ShiftInvariant M) :
    (S.closedWith M).Normal where
  conj_mem n hn w := by
    obtain ⟨hn1, hn2⟩ := hn
    refine ⟨(inferInstance : S.rest.Normal).conj_mem n hn1 w, ?_⟩
    rw [S.trail_conj w hn1]
    exact hM _ _ hn2

variable (S) in
/-- `keep(S; M)`: a closed walk of `S` is rest exactly when its trail is in `M`. -/
def keepTrail (M : AddSubgroup S.Chain) : Stage α := ofRest (S.closedWith M)

/-- **Theorem B.** In `keep(S; M)` a walk is rest exactly when it is a closed walk of `S`
whose trail is in `M`. -/
theorem mem_rest_keepTrail {M : AddSubgroup S.Chain} (hM : S.ShiftInvariant M)
    {n : FreeGroup α} : n ∈ (S.keepTrail M).rest ↔ n ∈ S.rest ∧ S.trail n ∈ M := by
  have := closedWith_normal hM
  rw [keepTrail, rest_ofRest]
  exact mem_closedWith

/-- **Theorem B.** `keep(S; M)` is a carry over `S`. -/
theorem keepTrail_isCarry {M : AddSubgroup S.Chain} (hM : S.ShiftInvariant M) :
    (S.keepTrail M).IsCarry S := by
  refine isCarry_iff.mpr ⟨fun w hw => (mem_rest_keepTrail hM).mpr ⟨?_, ?_⟩,
    fun w hw => ((mem_rest_keepTrail hM).mp hw).1⟩
  · exact commutator_le_left _ _ hw
  · rw [S.trail_eq_zero_of_mem_commutator hw]
    exact M.zero_mem

theorem shiftInvariant_bot : S.ShiftInvariant ⊥ := by
  intro g c hc
  rw [AddSubgroup.mem_bot] at hc ⊢
  rw [hc, map_zero]

/-- With `M` nothing but the trail 0, the whole trail is kept: `keep(S; 0)` is the richest
carry. -/
theorem rest_keepTrail_bot : (S.keepTrail ⊥).rest = S.keep.rest := by
  ext n
  rw [mem_rest_keepTrail shiftInvariant_bot, rest_keep, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨hn, h0⟩
    exact (S.trail_eq_zero_iff hn).mp h0
  · intro h
    have hn : n ∈ S.rest := commutator_le_left _ _ h
    exact ⟨hn, (S.trail_eq_zero_iff hn).mpr h⟩

variable (S) in
/-- The trails that the walks of a subgroup of closed walks leave. -/
def trails (K : Subgroup (FreeGroup α)) (hK : K ≤ S.rest) : AddSubgroup S.Chain where
  carrier := {c | ∃ n ∈ K, S.trail n = c}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, K.mul_mem ha hb, S.trail_mul_of_mem_rest (hK ha) b⟩
  zero_mem' := ⟨1, K.one_mem, trail_one S⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, K.inv_mem ha, S.trail_inv_of_mem_rest (hK ha)⟩

theorem shiftInvariant_trails (h : C.IsOver S) : S.ShiftInvariant (S.trails C.rest h) := by
  rintro g _ ⟨n, hn, rfl⟩
  obtain ⟨w, rfl⟩ := S.law_surjective g
  exact ⟨w * n * w⁻¹, (inferInstance : C.rest.Normal).conj_mem n hn w, S.trail_conj w (h hn)⟩

/-- **Theorems A and B.** Every carry over `S` is `keep(S; M)`, with `M` the trails of the
walks that are rest in it: the same walks are rest in both. -/
theorem rest_eq_keepTrail_of_isCarry (h : C.IsCarry S) :
    C.rest = (S.keepTrail (S.trails C.rest h.1)).rest := by
  ext n
  rw [mem_rest_keepTrail (shiftInvariant_trails h.1)]
  constructor
  · intro hn
    exact ⟨h.1 hn, n, hn, rfl⟩
  · rintro ⟨hn, c, hc, hcn⟩
    have hrest : n * c⁻¹ ∈ S.rest := S.rest.mul_mem hn (S.rest.inv_mem (h.1 hc))
    have h0 : S.trail (n * c⁻¹) = 0 := by
      rw [S.trail_mul_of_mem_rest hn, S.trail_inv_of_mem_rest (h.1 hc), hcn, add_neg_cancel]
    have hcomm : n * c⁻¹ ∈ C.rest := (isCarry_iff.mp h).1 ((S.trail_eq_zero_iff hrest).mp h0)
    simpa using C.rest.mul_mem hcomm hc

end Stage

end Artform.Stages

end
