import ArtformScores.Coset
import ArtformScores.Lifting

/-!
# Completeness on one mode, from a certificate

The proof of T4 at one prime `p`, from a certificate of the coset table of
`H = ⟨X⟩` in the group presented by the one-mode rules (`Coset.lean`).
- **Soundness.** Every relator of R1 and R3 has the law `1`, so the realizer
  `X ↦ M(1)`, `Y ↦ K(1)` is a homomorphism on the presented group.
- **Onto.** Over a field every law is a score (`isScore_of_field`), and every step
  is the law of a word.
- **One to one.** The certificate's cosets `H r_j` cover the presented group
  (`Coset.cover_of_check`), so a word with the law `1` lies in some `H r_j`. Then
  the law of `r_j` lies in `⟨M(1)⟩`, whose bottom row is `(0, 1)`. The certificate's
  bottom rows show that only `r_0` qualifies, so the word lies in `H`, and `X^p = 1`
  makes it `1`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

section Powers

variable {S : Type*} [CommRing S]

theorem move_sl_zpow (k : ℤ) : (Step.move (1 : S)).sl ^ k = (Step.move (k : S)).sl := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [Step.mat]
  | succ k ih =>
    rw [zpow_add_one, ih]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  | pred k ih =>
    rw [zpow_sub_one, ih, ← Step.sl_neg]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Step.mat, Step.neg, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, sub_eq_add_neg]
    ring

theorem kick_sl_zpow (k : ℤ) : (Step.kick (1 : S)).sl ^ k = (Step.kick (k : S)).sl := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [Step.mat]
  | succ k ih =>
    rw [zpow_add_one, ih]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  | pred k ih =>
    rw [zpow_sub_one, ih, ← Step.sl_neg]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Step.mat, Step.neg, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, sub_eq_add_neg]

/-- Over a field, every law of determinant 1 with constant stencils is a score. -/
theorem isScore_of_field {F : Type*} [Field F] (A : SpecialLinearGroup (Fin 2) F) : IsScore A := by
  by_cases h : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two, h, zero_mul, zero_sub] at hdet
    have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      intro h'
      rw [h', mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    refine IsScore.of_mul_left (IsScore.step (Step.move 1)) (isScore_of_isUnit _ ?_)
    simpa [Step.mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h]
      using h10
  · exact isScore_of_isUnit A (isUnit_iff_ne_zero.mpr h)

end Powers

namespace OneMode

variable {p : ℕ}

theorem law_X : law p (FreeGroup.of .X) = (Step.move 1).sl := by simp [law]

theorem law_Y : law p (FreeGroup.of .Y) = (Step.kick 1).sl := by simp [law]

theorem law_move [NeZero p] (f : ZMod p) : law p (move p f) = (Step.move f).sl := by
  rw [move, map_pow, law_X, ← zpow_natCast, move_sl_zpow, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem law_kick [NeZero p] (f : ZMod p) : law p (kick p f) = (Step.kick f).sl := by
  rw [kick, map_pow, law_Y, ← zpow_natCast, kick_sl_zpow, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Soundness: every relator has the law `1`. -/
theorem law_relators [NeZero p] : ∀ r ∈ relators p, law p r = 1 := by
  have hw : ∀ u : (ZMod p)ˣ, law p (whiteheadWord p u) = realize (whitehead u) := fun u => by
    simp [whiteheadWord, whitehead, law_move, law_kick, mul_assoc]
  rintro r (⟨f, g, rfl | rfl⟩ | ⟨u, f, rfl | rfl⟩) <;>
    simp only [map_mul, map_inv, hw, law_move, law_kick, mul_inv_eq_one]
  · simpa [add_comm] using (merging (ZMod p) g f).2
  · simpa [add_comm] using (merging (ZMod p) g f).1
  · exact (whiteheadRule (ZMod p) u f).2.1
  · exact (whiteheadRule (ZMod p) u f).2.2

end OneMode

end Artform.Scores

namespace Artform.Scores.OneMode

open Matrix (SpecialLinearGroup)

variable {p : ℕ}

/-- The presented group of the one-mode rules. -/
abbrev Pres (p : ℕ) := PresentedGroup (relators p)

/-- The generators in the presented group. -/
def gen (p : ℕ) (a : Gen) : Pres p := PresentedGroup.of a

theorem mk_of (a : Gen) : PresentedGroup.mk (relators p) (FreeGroup.of a) = gen p a := rfl

theorem lift_gen : FreeGroup.lift (gen p) = PresentedGroup.mk (relators p) :=
  FreeGroup.ext_hom _ _ fun a => by simp [mk_of]

/-- `X^p = 1` and `Y^p = 1` in the presented group, by merging. -/
theorem gen_pow (h : (1 : ZMod p).val + (-1 : ZMod p).val = p) (a : Gen) : gen p a ^ p = 1 := by
  cases a
  · have hr := PresentedGroup.one_of_mem (rels := relators p) (Or.inl ⟨1, -1, Or.inl rfl⟩)
    simp only [move, map_pow, add_neg_cancel, ZMod.val_zero, pow_zero, inv_one, mul_one, ← pow_add,
      h, mk_of] at hr
    exact hr
  · have hr := PresentedGroup.one_of_mem (rels := relators p) (Or.inl ⟨1, -1, Or.inr rfl⟩)
    simp only [kick, map_pow, add_neg_cancel, ZMod.val_zero, pow_zero, inv_one, mul_one, ← pow_add,
      h, mk_of] at hr
    exact hr

theorem zpow_eq_of_cast {G : Type*} [Group G] {x : G} (hx : x ^ p = 1) {m k : ℤ}
    (h : (m : ZMod p) = (k : ZMod p)) : x ^ m = x ^ k := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub m k p).mp h
  rw [show k = m + p * c by omega, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

theorem pow_val_eq [NeZero p] {G : Type*} [Group G] {x : G} (hx : x ^ p = 1) {f : ZMod p} {k : ℤ}
    (hk : (k : ZMod p) = f) : x ^ f.val = x ^ k := by
  rw [← zpow_natCast]
  exact zpow_eq_of_cast hx (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, hk])

/-- The letter of a code in a certificate's words: `0 = X`, `1 = X⁻¹`, `2 = Y` and
`3 = Y⁻¹`. -/
def letterOf : ℕ → Gen × Bool
  | 0 => (.X, true)
  | 1 => (.X, false)
  | 2 => (.Y, true)
  | _ => (.Y, false)

/-- A relator of a certificate, by its parameters. -/
inductive Desc (p : ℕ)
  /-- `X^p`, from merging -/
  | powX
  /-- `Y^p`, from merging -/
  | powY
  /-- Whitehead's rule `w(u) M(1) w(u)⁻¹ = K(-u⁻²)` at the unit `a` with inverse `b`,
  with exponents `α ≡ a`, `β ≡ -b` and `γ ≡ -b²` -/
  | rm (a b : ZMod p) (α β γ : ℤ)
  /-- Whitehead's rule `w(u) K(1) w(u)⁻¹ = M(-u²)`, with `δ ≡ -a²` -/
  | rk (a b : ZMod p) (α β δ : ℤ)

/-- The power `g^k` as a word. -/
def pw (g : Gen) (k : ℤ) : List (Gen × Bool) :=
  if 0 ≤ k then List.replicate k.toNat (g, true) else List.replicate (-k).toNat (g, false)

/-- The word of a relator, freely reduced. -/
def Desc.word : Desc p → List (Gen × Bool)
  | .powX => List.replicate p (.X, true)
  | .powY => List.replicate p (.Y, true)
  | .rm _ _ α β γ => Coset.reduceWord (pw .X α ++ pw .Y β ++ pw .X α ++ pw .X 1 ++ pw .X (-α) ++
      pw .Y (-β) ++ pw .X (-α) ++ pw .Y (-γ))
  | .rk _ _ α β δ => Coset.reduceWord (pw .X α ++ pw .Y β ++ pw .X α ++ pw .Y 1 ++ pw .X (-α) ++
      pw .Y (-β) ++ pw .X (-α) ++ pw .X (-δ))

/-- The parameters of a relator fit its rule. -/
def Desc.valid : Desc p → Bool
  | .powX | .powY => decide ((1 : ZMod p).val + (-1 : ZMod p).val = p)
  | .rm a b α β γ => decide (a * b = 1) && decide ((α : ZMod p) = a) &&
      decide ((β : ZMod p) = -b) && decide ((γ : ZMod p) = -(b * b * 1))
  | .rk a b α β δ => decide (a * b = 1) && decide ((α : ZMod p) = a) &&
      decide ((β : ZMod p) = -b) && decide ((δ : ZMod p) = -(a * a * 1))

theorem evalWord_pw {G : Type*} [Group G] (f : Gen → G) (g : Gen) (k : ℤ) :
    Coset.evalWord f (pw g k) = f g ^ k := by
  unfold pw
  split
  · rename_i hk
    simp only [Coset.evalWord, List.map_replicate, Coset.letter, List.prod_replicate]
    rw [← zpow_natCast, Int.toNat_of_nonneg hk]
  · rename_i hk
    simp only [Coset.evalWord, List.map_replicate, Coset.letter, List.prod_replicate]
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

/-- Every valid relator is `1` in the presented group. -/
theorem Desc.eval [NeZero p] (hpow : ∀ a, gen p a ^ p = 1) (d : Desc p) (hd : d.valid = true) :
    Coset.evalWord (gen p) d.word = 1 := by
  cases d with
  | powX => simpa [Desc.word, Coset.evalWord, Coset.letter, List.prod_replicate] using hpow .X
  | powY => simpa [Desc.word, Coset.evalWord, Coset.letter, List.prod_replicate] using hpow .Y
  | rm a b α β γ =>
    simp only [Desc.valid, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨hab, hα⟩, hβ⟩, hγ⟩ := hd
    have hr := PresentedGroup.one_of_mem (rels := relators p)
      (Or.inr ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, 1, Or.inl rfl⟩)
    simp only [map_mul, map_inv, whiteheadWord, move, kick, map_pow, Units.val_mk, Units.inv_mk,
      mk_of] at hr
    rw [pow_val_eq (hpow .X) hα, pow_val_eq (hpow .Y) hβ,
      pow_val_eq (hpow .X) (k := 1) (by simp), pow_val_eq (hpow .Y) hγ] at hr
    simp only [Desc.word, Coset.evalWord_reduceWord, Coset.evalWord_append, evalWord_pw]
    rw [← hr]
    group
  | rk a b α β δ =>
    simp only [Desc.valid, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨hab, hα⟩, hβ⟩, hδ⟩ := hd
    have hr := PresentedGroup.one_of_mem (rels := relators p)
      (Or.inr ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, 1, Or.inr rfl⟩)
    simp only [map_mul, map_inv, whiteheadWord, move, kick, map_pow, Units.val_mk, Units.inv_mk,
      mk_of] at hr
    rw [pow_val_eq (hpow .X) hα, pow_val_eq (hpow .Y) hβ,
      pow_val_eq (hpow .Y) (k := 1) (by simp), pow_val_eq (hpow .X) hδ] at hr
    simp only [Desc.word, Coset.evalWord_reduceWord, Coset.evalWord_append, evalWord_pw]
    rw [← hr]
    group

end Artform.Scores.OneMode

namespace Artform.Scores.OneMode

open Matrix (SpecialLinearGroup)

variable {p : ℕ}

theorem lift_law : FreeGroup.lift (fun a => law p (FreeGroup.of a)) = law p :=
  FreeGroup.ext_hom _ _ fun a => by simp

/-- The realizer of the presented group. -/
noncomputable def realizer (p : ℕ) [NeZero p] : Pres p →* SpecialLinearGroup (Fin 2) (ZMod p) :=
  PresentedGroup.toGroup (f := fun a => law p (FreeGroup.of a)) fun r hr => by
    rw [lift_law]
    exact law_relators r hr

theorem realizer_gen [NeZero p] (a : Gen) : realizer p (gen p a) = law p (FreeGroup.of a) :=
  PresentedGroup.toGroup.of _

theorem realizer_mk [NeZero p] (v : FreeGroup Gen) :
    realizer p (PresentedGroup.mk (relators p) v) = law p v := by
  rw [← lift_gen, ← MonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun a => by simp [realizer_gen]) v

/-- The bottom row `(c, d)` of a law, read letter by letter. -/
def bottomStep : ZMod p × ZMod p → Gen × Bool → ZMod p × ZMod p
  | (c, d), (.X, true) => (c, c + d)
  | (c, d), (.X, false) => (c, d - c)
  | (c, d), (.Y, true) => (c + d, d)
  | (c, d), (.Y, false) => (c - d, d)

/-- The bottom row of the law of a word. -/
def bottom (w : List (Gen × Bool)) : ZMod p × ZMod p := w.foldl bottomStep (0, 1)

theorem foldl_bottomStep (w : List (Gen × Bool)) (v : ZMod p × ZMod p) :
    w.foldl bottomStep v =
      (v.1 * ((Coset.evalWord (fun a => law p (FreeGroup.of a)) w : SpecialLinearGroup (Fin 2)
          (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 +
        v.2 * ((Coset.evalWord (fun a => law p (FreeGroup.of a)) w : SpecialLinearGroup (Fin 2)
          (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0,
      v.1 * ((Coset.evalWord (fun a => law p (FreeGroup.of a)) w : SpecialLinearGroup (Fin 2)
          (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 +
        v.2 * ((Coset.evalWord (fun a => law p (FreeGroup.of a)) w : SpecialLinearGroup (Fin 2)
          (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1) := by
  induction w generalizing v with
  | nil => simp
  | cons x w ih =>
    rw [List.foldl_cons, ih, Coset.evalWord_cons, Matrix.SpecialLinearGroup.coe_mul]
    obtain ⟨c, d⟩ := v
    obtain ⟨_ | _, _ | _⟩ := x
    all_goals
      refine Prod.ext ?_ ?_ <;>
        simp [bottomStep, Coset.letter, law_X, law_Y, Step.mat, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bottom_eq [NeZero p] (w : List (Gen × Bool)) :
    bottom w = (((realizer p (Coset.evalWord (gen p) w) : SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0,
      ((realizer p (Coset.evalWord (gen p) w) : SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1) := by
  have h : (realizer p) ∘ (gen p) = fun a => law p (FreeGroup.of a) := funext realizer_gen
  rw [Coset.map_evalWord, h, bottom, foldl_bottomStep]
  simp

theorem exists_word_of_isScore [NeZero p] {A : SpecialLinearGroup (Fin 2) (ZMod p)}
    (h : IsScore A) : ∃ v, law p v = A := by
  obtain ⟨w, rfl⟩ := h
  induction w with
  | nil => exact ⟨1, by simp⟩
  | cons s w ih =>
    obtain ⟨v, hv⟩ := ih
    cases s with
    | kick f => exact ⟨v * kick p f, by rw [map_mul, hv, law_kick, realize_cons]⟩
    | move f => exact ⟨v * move p f, by rw [map_mul, hv, law_move, realize_cons]⟩

/-- T4 from a checked certificate: on one mode over `F_p`, every law is the law of a word,
and two words have the same law exactly when they are equal in the presented group. -/
theorem complete_of_cert (p : ℕ) (C : Coset.Cert Gen) (descs : List (Desc p))
    (hrels : C.rels = descs.map Desc.word) (hcheck : Coset.check C [.X, .Y] [.X] = true)
    (hvalid : descs.all Desc.valid = true) (hpow : (1 : ZMod p).val + (-1 : ZMod p).val = p)
    (hbottom : (List.range C.n).all
      (fun j => j == 0 || decide (bottom (p := p) (C.word j) ≠ (0, 1))) = true)
    [Fact p.Prime] :
    (∀ A : SpecialLinearGroup (Fin 2) (ZMod p), ∃ v, law p v = A) ∧
      ∀ v₁ v₂ : FreeGroup Gen, law p v₁ = law p v₂ ↔
        PresentedGroup.mk (relators p) v₁ = PresentedGroup.mk (relators p) v₂ := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨fun A => exists_word_of_isScore (isScore_of_field A),
    fun v₁ v₂ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hpow' : ∀ a, gen p a ^ p = 1 := gen_pow hpow
    have hrelsC : ∀ w ∈ C.rels, Coset.evalWord (gen p) w = 1 := by
      rw [hrels]
      intro w hw
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
      exact Desc.eval hpow' d (List.all_eq_true.mp hvalid d hd)
    obtain ⟨j, hj, hmem⟩ := Coset.cover_of_check (H := Subgroup.zpowers (gen p .X))
      (fun a => by cases a <;> simp)
      (fun a ha => by simp only [List.mem_singleton] at ha; subst ha; exact Subgroup.mem_zpowers _)
      hrelsC hcheck (v₁ * v₂⁻¹) 0 (Coset.check_n_pos hcheck)
    have h0 : Coset.rep (gen p) C 0 = 1 := by simp [Coset.rep, Coset.check_word_zero hcheck]
    rw [h0, one_mul, lift_gen] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hρ : realizer p (PresentedGroup.mk (relators p) (v₁ * v₂⁻¹)) = 1 := by
      rw [realizer_mk, map_mul, map_inv, h, mul_inv_cancel]
    have hρk : realizer p (gen p .X ^ k) = (Step.move ((k : ℤ) : ZMod p)).sl := by
      rw [map_zpow, realizer_gen, law_X, move_sl_zpow]
    have hρj : realizer p (Coset.rep (gen p) C j) = ((Step.move ((k : ℤ) : ZMod p)).sl)⁻¹ := by
      have e := congrArg (realizer p) hk
      rw [map_mul, map_inv, hρ, one_mul, hρk] at e
      rw [e, inv_inv]
    have hj0 : j = 0 := by
      by_contra hne
      have hb := List.all_eq_true.mp hbottom j (List.mem_range.mpr hj)
      have hbot : bottom (p := p) (C.word j) = (0, 1) := by
        rw [bottom_eq, ← Coset.rep, hρj]
        simp [Step.mat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of]
      simp [hne, hbot] at hb
    subst hj0
    rw [h0, inv_one, mul_one] at hk
    have hk0 : ((k : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p) := by
      have e := congrArg (realizer p) hk
      rw [hρk, hρ] at e
      simpa [Step.mat] using congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod p) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) e
    rw [zpow_eq_of_cast (hpow' .X) hk0, zpow_zero, map_mul, map_inv] at hk
    exact (mul_inv_eq_one.mp hk.symm)
  · simpa [realizer_mk] using congrArg (realizer p) h

end Artform.Scores.OneMode
