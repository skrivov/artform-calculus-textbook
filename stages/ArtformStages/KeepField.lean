import ArtformStages.Trail
import ArtformStages.TorusHarmonic
import ArtformStages.Maxwell

/-!
# Keep to the field

Keep of the whole trail keeps of a walk its dot and its trail (T4(a), `Stage.keep_law_eq_iff`).
Here the trail is read as a field. The *ends* of a chain are, at each dot, what its lines bring in
less what they take out, and they obey Gauss's law on every stage, with any number of charges and
with nothing asked (finding 471 of the research ledger on a layered universe):

* `Stage.ends`, `Stage.ends_trail` (KP1): the ends of the trail of a walk are one at its dot less
  one at rest, Lemma 1.1 of THEORY.md and T7 of THEORY-3.md;
* `Stage.ends_sum` (KP2): the values of the ends of every chain add up to `0`;
* `Stage.exists_ends` (KP3): every assignment on the dots whose values add up to `0` is the ends
  of some chain;
* `Stage.ends_single`, `Stage.ends_write` (KP4): `k` written on one line adds `k` at its head and
  takes `k` from its tail, so one act is a hop, the making of a pair or an unmaking;
* `Stage.endsDial`, `Stage.endsDial_mem_range_iff`, `Stage.card_endsDial_fiber`,
  `Stage.cast_fiber_exponent`, `Stage.charges_alone_iff` (KP5): on a stage with finitely many acts
  and laws, on the dial of `n ≥ 1`, the ends of fillings form a map of additive groups; an
  assignment is the ends of some filling exactly when its values add up to `0` in `ℤ/n`; then it
  is the ends of exactly `n ^ r` fillings, `r = |acts| |laws| - |laws| + 1`; so `k` charges of one
  click stand alone exactly when `n` divides `k`;
* `twoRows`, `twoRowsWorld`, `twoRowsWorld_law_a`, `twoRowsWorld_law_b` (KP6): for `n, m ≥ 2` the
  world of the stage of two rows that pass is `ℤ/n × ℤ/m`, the law of `a` going to `(1, 0)` and
  that of `b` to `(0, 1)`;
* `twoRowsField`, `twoRows_ends_eq_neg_divergence` (KP7): read through that isomorphism, the ends
  of every chain at every corner are minus the divergence of the field that the chain gives the
  lines of the torus.

The proof of KP1 is an induction on the walk, by Fox's rule `trail_mul`: the ends of a chain
looked at from a dot are its ends moved by that dot. KP3 writes `f` as the sum of the trails of
walks to its dots, each one of them taken `f g` times. KP5 counts the kernel of the map and its
image, the assignments whose values add up to `0`.
-/

noncomputable section

namespace Artform.Stages

variable {α : Type*}

namespace Stage

variable (S : Stage α)

/-- The head of the line `(a, g)`: the dot `g * law a`, where it ends. Its tail is `g`. -/
def head (p : α × S.World) : S.World := p.2 * S.law (FreeGroup.of p.1)

/-- The line `(a, h)` ends at the dot `g` exactly when `h = g * (law a)⁻¹`: the lines into `g` are
the lines `(a, g * (law a)⁻¹)`, one for each act. -/
theorem eq_head_iff {a : α} {g h : S.World} :
    g = S.head (a, h) ↔ h = g * (S.law (FreeGroup.of a))⁻¹ := by
  rw [head, eq_mul_inv_iff_mul_eq, eq_comm]

/-- The ends of a chain: the sum over the lines of the chain's count times one at the head less
one at the tail. At each dot it is what the lines into it carry less what the lines out of it
carry (`ends_apply`). -/
def ends : S.Chain →+ (S.World →₀ ℤ) where
  toFun c := c.sum fun p k => k • (Finsupp.single (S.head p) 1 - Finsupp.single p.2 1)
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => zero_smul ℤ _) fun _ _ _ => add_smul _ _ _

/-- **KP4.** A write books its line: the chain with the count `k` on the line `(a, g)` and nothing
elsewhere has the ends `k` at the head `g * law a` less `k` at the tail `g`. -/
theorem ends_single (a : α) (g : S.World) (k : ℤ) :
    S.ends (Finsupp.single (a, g) k) =
      Finsupp.single (g * S.law (FreeGroup.of a)) k - Finsupp.single g k := by
  simp only [ends, AddMonoidHom.coe_mk, ZeroHom.coe_mk, head]
  rw [Finsupp.sum_single_index (by simp)]
  simp only [smul_sub, Finsupp.smul_single_one]

/-- **KP4.** So one act, one click written on the line `(a, g)`, is a hop where a charge stands at
the tail, the making of a pair where nothing stands at either end, and an unmaking where a charge
stands at the tail and its opposite at the head; `f` is what stands elsewhere. -/
theorem ends_write (c : S.Chain) (a : α) (g : S.World) (f : S.World →₀ ℤ) :
    (S.ends c = f + Finsupp.single g 1 →
      S.ends (c + Finsupp.single (a, g) 1) =
        f + Finsupp.single (g * S.law (FreeGroup.of a)) 1) ∧
    (S.ends c = f →
      S.ends (c + Finsupp.single (a, g) 1) =
        f + (Finsupp.single (g * S.law (FreeGroup.of a)) 1 - Finsupp.single g 1)) ∧
    (S.ends c = f + (Finsupp.single g 1 - Finsupp.single (g * S.law (FreeGroup.of a)) 1) →
      S.ends (c + Finsupp.single (a, g) 1) = f) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [map_add, h, ends_single]
    abel
  · rw [map_add, h, ends_single]
  · rw [map_add, h, ends_single]
    abel

/-- The ends of a chain looked at from the dot `g` are its ends moved by `g`. -/
theorem ends_shift (g : S.World) (c : S.Chain) :
    S.ends (S.shift g c) = Finsupp.mapDomain (g * ·) (S.ends c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Finsupp.mapDomain_add]
  | single p k =>
    obtain ⟨a, h⟩ := p
    rw [shift_single, ends_single, ends_single]
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, mul_assoc]

/-- **KP1** (THEORY.md's Lemma 1.1). The ends of the trail of a walk are one at its dot less one
at rest. -/
theorem ends_trail (w : FreeGroup α) :
    S.ends (S.trail w) = Finsupp.single (S.law w) 1 - Finsupp.single 1 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of a => rw [trail_of, ends_single, one_mul]
  | inv_of a ih =>
    rw [trail_inv, map_neg, ends_shift, ih]
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, inv_mul_cancel, mul_one, map_inv,
      neg_sub]
  | mul u v hu hv =>
    rw [trail_mul, map_add, ends_shift, hu, hv]
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, mul_one, map_mul]
    abel

/-- **KP2.** No lone charge: the values of the ends of every chain add up to `0`. -/
theorem ends_sum (c : S.Chain) : (S.ends c).sum (fun _ k => k) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl, hc, hd, add_zero]
  | single p k =>
    rw [ends_single, Finsupp.sum_sub_index fun _ _ _ => rfl, Finsupp.sum_single_index rfl,
      Finsupp.sum_single_index rfl, sub_self]

/-- **KP3.** Every charge that adds up to `0` is made: some chain has it as its ends. -/
theorem exists_ends (f : S.World →₀ ℤ) (hf : f.sum (fun _ k => k) = 0) :
    ∃ c : S.Chain, S.ends c = f := by
  obtain ⟨t⟩ := S.nonempty_walks
  refine ⟨f.sum fun g k => k • S.trail (t.walk g), ?_⟩
  have h1 := map_finsuppSum (Finsupp.singleAddHom (1 : S.World)) f fun _ k => k
  rw [hf, map_zero] at h1
  simp only [Finsupp.singleAddHom_apply] at h1
  rw [map_finsuppSum]
  simp only [map_zsmul, ends_trail, t.law_walk, smul_sub, Finsupp.smul_single_one]
  rw [Finsupp.sum_sub, Finsupp.sum_single, ← h1, sub_zero]

section Dial

variable [Fintype α]

/-- The ends of a chain at the dot `g`: what the lines `(a, g * (law a)⁻¹)` into it carry less what
the lines `(a, g)` out of it carry. -/
theorem ends_apply (c : S.Chain) (g : S.World) :
    S.ends c g = ∑ a, c (a, g * (S.law (FreeGroup.of a))⁻¹) - ∑ a, c (a, g) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    abel
  | single p k =>
    obtain ⟨b, h⟩ := p
    rw [ends_single]
    simp only [Finsupp.sub_apply, Finsupp.single_apply, Prod.mk.injEq, ite_and,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_mul_inv_iff_mul_eq]

variable [Fintype S.World]

/-- A finite stage has at most one law more than its acts times its laws. -/
theorem card_world_le : Fintype.card S.World ≤ Fintype.card α * Fintype.card S.World + 1 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have h : ∀ w : FreeGroup α, w = 1 := fun w => by
      induction w using FreeGroup.induction_on with
      | one => rfl
      | of a => exact isEmptyElim a
      | inv_of a _ => exact isEmptyElim a
      | mul u v hu hv => rw [hu, hv, mul_one]
    have hs : Subsingleton S.World := ⟨fun x y => by
      obtain ⟨u, rfl⟩ := S.law_surjective x
      obtain ⟨v, rfl⟩ := S.law_surjective y
      rw [h u, h v]⟩
    have := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  · have := Fintype.card_pos (α := α)
    nlinarith

/-- The exponent `|acts| |laws| + 1 - |laws|` of `card_endsDial_fiber`, a whole number, is
`r = |acts| |laws| - |laws| + 1` read in the integers. -/
theorem cast_fiber_exponent :
    ((Fintype.card α * Fintype.card S.World + 1 - Fintype.card S.World : ℕ) : ℤ) =
      Fintype.card α * Fintype.card S.World - Fintype.card S.World + 1 := by
  rw [Nat.cast_sub S.card_world_le]
  push_cast
  ring

variable [DecidableEq S.World] (n : ℕ)

/-- **KP5.** The ends of a filling on the dial of `n`, a number of `ℤ/n` on every line, read as
for a chain: the sum over the lines of its count times one at the head less one at the tail. They
form a map of additive groups. -/
def endsDial : (α × S.World → ZMod n) →+ (S.World → ZMod n) where
  toFun F := ∑ p, F p • (Pi.single (S.head p) 1 - Pi.single p.2 1)
  map_zero' := by simp
  map_add' F G := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The ends of a filling at the dot `g`: what the lines into it carry less what the lines out of
it carry. -/
theorem endsDial_apply (F : α × S.World → ZMod n) (g : S.World) :
    S.endsDial n F g = ∑ a, F (a, g * (S.law (FreeGroup.of a))⁻¹) - ∑ a, F (a, g) := by
  simp only [endsDial, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Fintype.sum_prod_type, eq_head_iff,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The ends of the reading of a chain on the dial are the reading of its ends. -/
theorem endsDial_intCast (c : S.Chain) :
    S.endsDial n (fun p => (c p : ZMod n)) = fun g => (S.ends c g : ZMod n) := by
  funext g
  rw [endsDial_apply, ends_apply]
  push_cast
  rfl

/-- The values of the ends of every filling add up to `0`. -/
theorem endsDial_sum (F : α × S.World → ZMod n) : ∑ g, S.endsDial n F g = 0 := by
  have h1 : ∑ g : S.World, ∑ a, F (a, g * (S.law (FreeGroup.of a))⁻¹) =
      ∑ g : S.World, ∑ a, F (a, g) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ =>
      Fintype.sum_equiv (Equiv.mulRight (S.law (FreeGroup.of a))⁻¹) _ _ fun _ => rfl
  simp only [endsDial_apply, Finset.sum_sub_distrib, h1, sub_self]

/-- **KP5.** An assignment on the dots is the ends of some filling on the dial exactly when its
values add up to `0` in `ℤ/n`. -/
theorem endsDial_mem_range_iff (f : S.World → ZMod n) :
    f ∈ (S.endsDial n).range ↔ ∑ g, f g = 0 := by
  refine ⟨fun ⟨F, hF⟩ => hF ▸ S.endsDial_sum n F, fun hf => ?_⟩
  obtain ⟨t⟩ := S.nonempty_walks
  refine ⟨∑ h, f h • fun p => ((S.trail (t.walk h) p : ℤ) : ZMod n), ?_⟩
  rw [map_sum]
  simp only [ZMod.map_smul, endsDial_intCast, ends_trail, t.law_walk]
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finsupp.sub_apply, Finsupp.single_apply,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h1 : (1 : S.World) = g <;> simp [h1, hf]

/-- **KP5.** On the dial of `n ≥ 1` every assignment whose values add up to `0` is the ends of
exactly `n ^ r` fillings, `r = |acts| |laws| - |laws| + 1`. It is written `|acts| |laws| + 1 -
|laws|`, so that the subtraction of whole numbers does not cut it off at `0`: the two are the same
number on every stage, `0` where there are no acts. -/
theorem card_endsDial_fiber [NeZero n] (f : S.World → ZMod n) (hf : ∑ g, f g = 0) :
    Nat.card {F : α × S.World → ZMod n // S.endsDial n F = f} =
      n ^ (Fintype.card α * Fintype.card S.World + 1 - Fintype.card S.World) := by
  obtain ⟨F₀, hF₀⟩ := (S.endsDial_mem_range_iff n f).mpr hf
  have e1 : Nat.card {F : α × S.World → ZMod n // S.endsDial n F = f} =
      Nat.card (S.endsDial n).ker := Nat.card_congr
    { toFun := fun F => ⟨F.1 - F₀, by rw [AddMonoidHom.mem_ker, map_sub, F.2, hF₀, sub_self]⟩
      invFun := fun K => ⟨K.1 + F₀, by rw [map_add, AddMonoidHom.mem_ker.mp K.2, hF₀, zero_add]⟩
      left_inv := fun F => Subtype.ext (sub_add_cancel F.1 F₀)
      right_inv := fun K => Subtype.ext (add_sub_cancel_right K.1 F₀) }
  have e2 : Nat.card (S.endsDial n).ker * Nat.card (S.endsDial n).range =
      n ^ (Fintype.card α * Fintype.card S.World) := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, Nat.card_fun, Nat.card_zmod,
      Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let σ : (S.World → ZMod n) →+ ZMod n :=
    { toFun := fun f => ∑ g, f g
      map_zero' := by simp
      map_add' := fun _ _ => Finset.sum_add_distrib }
  have hσ : (S.endsDial n).range = σ.ker := by
    ext f
    rw [endsDial_mem_range_iff, AddMonoidHom.mem_ker]
    rfl
  have hsurj : σ.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr fun x => ⟨Pi.single 1 x, by simp [σ]⟩
  have e3 : Nat.card (S.endsDial n).range * n = n ^ Fintype.card S.World := by
    have h := AddSubgroup.card_mul_index σ.ker
    rw [AddSubgroup.index_ker, hsurj, AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := S.World)] at h
    rw [hσ]
    exact h
  have hn : 0 < n ^ Fintype.card S.World := pow_pos (NeZero.pos n) _
  have key : Nat.card (S.endsDial n).ker * n ^ Fintype.card S.World =
      n ^ (Fintype.card α * Fintype.card S.World + 1 - Fintype.card S.World) *
        n ^ Fintype.card S.World := by
    calc Nat.card (S.endsDial n).ker * n ^ Fintype.card S.World
        = Nat.card (S.endsDial n).ker * Nat.card (S.endsDial n).range * n := by
          rw [← e3, mul_assoc]
      _ = n ^ (Fintype.card α * Fintype.card S.World + 1) := by rw [e2, pow_succ]
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel S.card_world_le]
  rw [e1]
  exact Nat.eq_of_mul_eq_mul_right hn key

/-- **KP5.** So `k` charges of one click, at the dots `x 0`, ..., `x (k - 1)` and nothing else,
stand alone on the dial of `n` exactly when `n` divides `k`. -/
theorem charges_alone_iff (k : ℕ) (x : Fin k → S.World) :
    (∑ i, Pi.single (x i) (1 : ZMod n)) ∈ (S.endsDial n).range ↔ n ∣ k := by
  rw [endsDial_mem_range_iff, ← ZMod.natCast_eq_zero_iff]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

end Dial

end Stage

/-! ### Two rows that pass -/

/-- The stage of two rows that pass, of periods `n` and `m`: the acts `a = 0` and `b = 1` of
`Fin 2`, with the rules `a^n`, `b^m` and `a b a⁻¹ b⁻¹`. -/
def twoRows (n m : ℕ) : Stage (Fin 2) :=
  ⟨{FreeGroup.of 0 ^ n, FreeGroup.of 1 ^ m,
    FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹}⟩

variable (n m : ℕ)

/-- In two rows, `a` made `n` times is rest. -/
theorem twoRows_pow_a : (twoRows n m).law (FreeGroup.of 0) ^ n = 1 := by
  rw [← map_pow, Stage.law_eq_one_iff]
  exact (twoRows n m).rules_subset_rest (by simp [twoRows])

/-- In two rows, `b` made `m` times is rest. -/
theorem twoRows_pow_b : (twoRows n m).law (FreeGroup.of 1) ^ m = 1 := by
  rw [← map_pow, Stage.law_eq_one_iff]
  exact (twoRows n m).rules_subset_rest (by simp [twoRows])

/-- In two rows, `a` and `b` pass each other. -/
theorem twoRows_commute :
    Commute ((twoRows n m).law (FreeGroup.of 0)) ((twoRows n m).law (FreeGroup.of 1)) := by
  have h : (twoRows n m).law
      (FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) = 1 :=
    (twoRows n m).law_eq_one_iff.mpr ((twoRows n m).rules_subset_rest (by simp [twoRows]))
  simp only [map_mul, map_inv] at h
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

/-- The point of the torus of a law of two rows: `a` is one step across, `b` one step up. -/
def twoRowsToTorus : (twoRows n m).World →* Multiplicative (ZMod n × ZMod m) :=
  PresentedGroup.toGroup (f := ![Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (0, 1)]) <| by
    rintro r (rfl | rfl | rfl)
    · simp [← ofAdd_nsmul]
    · simp [← ofAdd_nsmul]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]

/-- The law of `a` is one step across. -/
theorem twoRowsToTorus_a :
    twoRowsToTorus n m ((twoRows n m).law (FreeGroup.of 0)) = Multiplicative.ofAdd (1, 0) :=
  PresentedGroup.toGroup.of _

/-- The law of `b` is one step up. -/
theorem twoRowsToTorus_b :
    twoRowsToTorus n m ((twoRows n m).law (FreeGroup.of 1)) = Multiplicative.ofAdd (0, 1) :=
  PresentedGroup.toGroup.of _

/-- The law of two rows at the point `(i, j)` of the torus: `a` made `i` times, then `b` made `j`
times. -/
def torusToTwoRows [NeZero n] [NeZero m] :
    Multiplicative (ZMod n × ZMod m) →* (twoRows n m).World where
  toFun x := (twoRows n m).law (FreeGroup.of 0) ^ (Multiplicative.toAdd x).1.val *
    (twoRows n m).law (FreeGroup.of 1) ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (twoRows_pow_a n m), ← pow_eq_pow_mod _ (twoRows_pow_b n m),
      pow_add, pow_add]
    exact ((twoRows_commute n m).pow_pow _ _).mul_mul_mul_comm _ _

variable [Fact (1 < n)] [Fact (1 < m)]

/-- **KP6.** For `n, m ≥ 2` the world of the stage of two rows that pass is the group
`ℤ/n × ℤ/m`; the isomorphism sends the law of `a` to `(1, 0)` and that of `b` to `(0, 1)`
(`twoRowsWorld_law_a`, `twoRowsWorld_law_b`). -/
def twoRowsWorld : (twoRows n m).World ≃* Multiplicative (ZMod n × ZMod m) :=
  (twoRowsToTorus n m).toMulEquiv (torusToTwoRows n m)
    (PresentedGroup.ext (Fin.forall_fin_two.mpr
      ⟨by
        change torusToTwoRows n m (twoRowsToTorus n m ((twoRows n m).law (FreeGroup.of 0))) =
          (twoRows n m).law (FreeGroup.of 0)
        rw [twoRowsToTorus_a]
        simp [torusToTwoRows, ZMod.val_one],
      by
        change torusToTwoRows n m (twoRowsToTorus n m ((twoRows n m).law (FreeGroup.of 1))) =
          (twoRows n m).law (FreeGroup.of 1)
        rw [twoRowsToTorus_b]
        simp [torusToTwoRows, ZMod.val_one]⟩))
    (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, torusToTwoRows, MonoidHom.coe_mk,
        OneHom.coe_mk, map_mul, map_pow, twoRowsToTorus_a, twoRowsToTorus_b, ← ofAdd_nsmul,
        ← ofAdd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk, add_zero,
        zero_add, ZMod.natCast_zmod_val, Prod.mk.eta, ofAdd_toAdd])

/-- **KP6.** The isomorphism sends the law of `a` to `(1, 0)`. -/
@[simp]
theorem twoRowsWorld_law_a :
    twoRowsWorld n m ((twoRows n m).law (FreeGroup.of 0)) = Multiplicative.ofAdd (1, 0) :=
  twoRowsToTorus_a n m

/-- **KP6.** The isomorphism sends the law of `b` to `(0, 1)`. -/
@[simp]
theorem twoRowsWorld_law_b :
    twoRowsWorld n m ((twoRows n m).law (FreeGroup.of 1)) = Multiplicative.ofAdd (0, 1) :=
  twoRowsToTorus_b n m

/-- The field that a chain of two rows gives the lines of the torus: on the line across at the
corner `w` the count of the line `(a, g)`, on the line up the count of the line `(b, g)`, where `g`
is the law at `w`. -/
def twoRowsField (c : (twoRows n m).Chain) : (ZMod n × ZMod m) × Fin 2 → ℝ :=
  fun ℓ => (c (ℓ.2, (twoRowsWorld n m).symm (Multiplicative.ofAdd ℓ.1)) : ℝ)

/-- **KP7.** Read through `twoRowsWorld`, the ends of every chain of two rows at every corner are
minus the divergence, with the gauge of the torus, of the field that the chain gives the lines of
the torus. -/
theorem twoRows_ends_eq_neg_divergence (c : (twoRows n m).Chain) (w : ZMod n × ZMod m) :
    ((twoRows n m).ends c ((twoRowsWorld n m).symm (Multiplicative.ofAdd w)) : ℝ) =
      -divergence (torus n m).gauge (twoRowsField n m c) w := by
  have h0 : (twoRowsWorld n m).symm (Multiplicative.ofAdd (w - (1, 0))) =
      (twoRowsWorld n m).symm (Multiplicative.ofAdd w) *
        ((twoRows n m).law (FreeGroup.of 0))⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_mul, map_inv, twoRowsWorld_law_a, MulEquiv.apply_symm_apply,
      ofAdd_sub, div_eq_mul_inv]
  have h1 : (twoRowsWorld n m).symm (Multiplicative.ofAdd (w - (0, 1))) =
      (twoRowsWorld n m).symm (Multiplicative.ofAdd w) *
        ((twoRows n m).law (FreeGroup.of 1))⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_mul, map_inv, twoRowsWorld_law_b, MulEquiv.apply_symm_apply,
      ofAdd_sub, div_eq_mul_inv]
  rw [divergence, Pi.neg_apply, neg_neg, torus_gaugeT_mulVec, Stage.ends_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp only [twoRowsField, h0, h1]
  push_cast
  ring

end Artform.Stages
