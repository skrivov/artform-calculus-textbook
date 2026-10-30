import ArtformScores.StepGroups

/-!
# The presentations of the step groups

The ledger's T13, finding 037, Theorem Q, part 3. The kick and the tick `T = M K` act on the lines
of `ℤ²`, where `-I` acts trivially. On the line coordinate `r = y / x`:
- at `μ = 3`, `K` shifts `r` by `1`, and `T` rotates the three arcs between `-1`, `-1/2` and `0`, so
  the arc `(-1, 0)` and its outside play ping-pong, and `Σ₃ ≅ Z ∗ Z₃`;
- at `μ = 2`, `T` is the involution that swaps the two sets, and `Σ₂` is the central extension by
  `⟨-I⟩` of `Z ∗ Z₂`;
- at `μ = 1`, `J = K M K` and `T` swap `r > 0` and `r < 0`, and `SL(2, Z)` is the central extension
  of `Z₂ ∗ Z₃`.
So a word in `K` and `M` is the identity law exactly when the table's relations imply it.
-/

namespace Artform.Scores.StepGroup

open Matrix (SpecialLinearGroup)
open scoped Pointwise Function Cardinal

local notation "SL2Z" => SpecialLinearGroup (Fin 2) ℤ

/-! ### The ping-pong of two factors -/

section Pair

/-- Two groups as a family over `Bool`. -/
def Fam (A B : Type) : Bool → Type
  | false => A
  | true => B

instance famGroup (A B : Type) [Group A] [Group B] : ∀ i, Group (Fam A B i)
  | false => inferInstanceAs (Group A)
  | true => inferInstanceAs (Group B)

variable {A B : Type} [Group A] [Group B] {G : Type*} [Group G]

/-- Two homomorphisms as a family over `Bool`. -/
def famHom (f : A →* G) (g : B →* G) : ∀ i, Fam A B i →* G
  | false => f
  | true => g

/-- The ping-pong lemma for two factors. -/
theorem pair_injective {α : Type*} [MulAction G α] (f : A →* G) (g : B →* G)
    (hcard : 3 ≤ #A ∨ 3 ≤ #B) (X Y : Set α) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hd : Disjoint X Y) (h1 : ∀ h : A, h ≠ 1 → f h • Y ⊆ X) (h2 : ∀ h : B, h ≠ 1 → g h • X ⊆ Y) :
    Function.Injective (Monoid.CoprodI.lift (famHom f g)) := by
  refine Monoid.CoprodI.lift_injective_of_ping_pong (famHom f g) ?_
    (fun i => Bool.rec X Y i) ?_ ?_ ?_
  · rcases hcard with h | h
    · exact Or.inr ⟨false, h⟩
    · exact Or.inr ⟨true, h⟩
  · rintro (_ | _)
    · exact hX
    · exact hY
  · rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · exact hd
    · exact hd.symm
    · exact absurd rfl hij
  · rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · exact h1
    · exact h2
    · exact absurd rfl hij

/-- A homomorphism whose kernel lies in `Z` when the quotient by `Z` is a free product that plays
ping-pong. -/
theorem ker_le_of_ping_pong {P : Type*} [Group P] {α : Type*} [MulAction G α] (ψ : P →* G)
    (Z : Subgroup P) [Z.Normal] (hZ : Z ≤ ψ.ker) (a : A →* P ⧸ Z) (b : B →* P ⧸ Z)
    (hgen : (Monoid.CoprodI.lift (famHom a b)).range = ⊤)
    (hcard : 3 ≤ #A ∨ 3 ≤ #B) (X Y : Set α) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hd : Disjoint X Y)
    (h1 : ∀ h : A, h ≠ 1 → QuotientGroup.lift Z ψ hZ (a h) • Y ⊆ X)
    (h2 : ∀ h : B, h ≠ 1 → QuotientGroup.lift Z ψ hZ (b h) • X ⊆ Y) :
    ψ.ker ≤ Z := by
  intro g hg
  have hcomp : (QuotientGroup.lift Z ψ hZ).comp (Monoid.CoprodI.lift (famHom a b)) =
      Monoid.CoprodI.lift (famHom ((QuotientGroup.lift Z ψ hZ).comp a)
        ((QuotientGroup.lift Z ψ hZ).comp b)) := by
    refine Monoid.CoprodI.ext_hom _ _ ?_
    rintro (_ | _)
    · refine MonoidHom.ext fun h => ?_
      simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of]
      rfl
    · refine MonoidHom.ext fun h => ?_
      simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of]
      rfl
  have hinj : Function.Injective
      ((QuotientGroup.lift Z ψ hZ).comp (Monoid.CoprodI.lift (famHom a b))) := by
    rw [hcomp]
    exact pair_injective _ _ hcard X Y hX hY hd h1 h2
  obtain ⟨c, hc⟩ : (g : P ⧸ Z) ∈ (Monoid.CoprodI.lift (famHom a b)).range := by
    rw [hgen]
    exact Subgroup.mem_top _
  have h3 : (QuotientGroup.lift Z ψ hZ).comp (Monoid.CoprodI.lift (famHom a b)) c = 1 := by
    rw [MonoidHom.comp_apply, hc, QuotientGroup.lift_mk]
    exact hg
  have hc1 : c = 1 := (injective_iff_map_eq_one _).mp hinj c h3
  rw [hc1, map_one] at hc
  exact (QuotientGroup.eq_one_iff g).mp hc.symm

end Pair

/-! ### Homomorphisms from the cyclic factors -/

/-- The homomorphism from `Z_k` taking `1` to an element `g` with `gᵏ = 1`. -/
noncomputable def zmodHom {G : Type*} [Group G] (k : ℕ) (g : G) (hg : g ^ k = 1) :
    Multiplicative (ZMod k) →* G :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift k
    ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      simp only [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩)

theorem zmodHom_natCast {G : Type*} [Group G] (k : ℕ) (g : G) (hg : g ^ k = 1) (n : ℕ) :
    zmodHom k g hg (Multiplicative.ofAdd (n : ZMod k)) = g ^ n := by
  have h : ((n : ZMod k)) = ((n : ℤ) : ZMod k) := by simp
  simp only [zmodHom, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd]
  rw [h, ZMod.lift_coe]
  simp

/-! ### The lines of the plane -/

/-- Two vectors on one line through a sign. -/
def signS : Setoid (ℤ × ℤ) where
  r v w := w = v ∨ w = -v
  iseqv := by
    refine ⟨fun v => Or.inl rfl, ?_, ?_⟩
    · rintro v w (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (by simp)
    · rintro u v w (rfl | rfl) (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (by simp)

/-- The lines, as vectors up to sign. -/
abbrev Line := Quotient signS

/-- The line of `(x, y)`. -/
def mkL (x y : ℤ) : Line := Quotient.mk _ (x, y)

theorem mkL_neg (x y : ℤ) : mkL (-x) (-y) = mkL x y := Quotient.sound (Or.inr (by simp))

theorem mkL_eq {x y x' y' : ℤ} (h : mkL x y = mkL x' y') :
    (x' = x ∧ y' = y) ∨ (x' = -x ∧ y' = -y) := by
  rcases Quotient.exact h with h1 | h1
  · left
    simpa using h1
  · right
    simpa using h1

/-- A law on a vector. -/
def actL (A : SL2Z) (v : ℤ × ℤ) : ℤ × ℤ :=
  (A.1 0 0 * v.1 + A.1 0 1 * v.2, A.1 1 0 * v.1 + A.1 1 1 * v.2)

instance : MulAction SL2Z Line where
  smul A := Quotient.map (actL A) (by
    rintro v w (rfl | rfl)
    · exact Or.inl rfl
    · refine Or.inr ?_
      ext <;> simp [actL] <;> ring)
  one_smul c := by
    induction c using Quotient.inductionOn with
    | h v =>
      change Quotient.mk _ (actL 1 v) = Quotient.mk _ v
      congr 1
      ext <;> simp [actL]
  mul_smul A B c := by
    induction c using Quotient.inductionOn with
    | h v =>
      change Quotient.mk _ (actL (A * B) v) = Quotient.mk _ (actL A (actL B v))
      congr 1
      ext <;> simp [actL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem smul_mkL (A : SL2Z) (x y : ℤ) :
    A • mkL x y = mkL (A.1 0 0 * x + A.1 0 1 * y) (A.1 1 0 * x + A.1 1 1 * y) := rfl

/-- `-I` acts trivially on the lines. -/
theorem neg_one_smul_line (A : SL2Z) (hA : A.1 = !![-1, 0; 0, -1]) (c : Line) : A • c = c := by
  induction c using Quotient.inductionOn with
  | h v =>
    obtain ⟨x, y⟩ := v
    change A • mkL x y = mkL x y
    rw [smul_mkL, hA]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one, neg_mul, one_mul, zero_mul, add_zero, zero_add]
    exact mkL_neg x y

/-- The action on the lines, as permutations. -/
noncomputable abbrev chi : SL2Z →* Equiv.Perm Line := MulAction.toPermHom SL2Z Line

theorem chi_smul (A : SL2Z) (c : Line) : chi A • c = A • c := rfl

theorem chi_smul_subset {A : SL2Z} {X Y : Set Line} (h : ∀ c ∈ Y, A • c ∈ X) : chi A • Y ⊆ X := by
  rintro _ ⟨c, hc, rfl⟩
  exact h c hc

/-! ### The sets of the ping-pong -/

/-- The lines with `r > 0`. -/
def posL : Set Line := {c | ∃ x y : ℤ, c = mkL x y ∧ 0 < x ∧ 0 < y}

/-- The lines with `r < 0`. -/
def negL : Set Line := {c | ∃ x y : ℤ, c = mkL x y ∧ 0 < x ∧ y < 0}

/-- The lines with `-1 < r < 0`. -/
def arcL : Set Line := {c | ∃ x y : ℤ, c = mkL x y ∧ 0 < x ∧ -x < y ∧ y < 0}

/-- The lines outside the closed arc `[-1, 0]`. -/
def outL : Set Line :=
  {c | ∃ x y : ℤ, c = mkL x y ∧ ((0 < x ∧ 0 < y) ∨ (0 < x ∧ y < -x) ∨ (x = 0 ∧ 0 < y))}

theorem disjoint_pos_neg : Disjoint posL negL := by
  refine Set.disjoint_left.mpr ?_
  rintro c ⟨x, y, rfl, h1, h2⟩ ⟨x', y', he, h3, h4⟩
  rcases mkL_eq he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem disjoint_out_arc : Disjoint outL arcL := by
  refine Set.disjoint_left.mpr ?_
  rintro c ⟨x, y, rfl, h1⟩ ⟨x', y', he, h3, h4, h5⟩
  rcases mkL_eq he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem posL_nonempty : posL.Nonempty := ⟨_, 1, 1, rfl, by norm_num, by norm_num⟩
theorem negL_nonempty : negL.Nonempty := ⟨_, 1, -1, rfl, by norm_num, by norm_num⟩
theorem arcL_nonempty : arcL.Nonempty := ⟨_, 2, -1, rfl, by norm_num, by norm_num, by norm_num⟩
theorem outL_nonempty : outL.Nonempty := ⟨_, 1, 1, rfl, Or.inl ⟨by norm_num, by norm_num⟩⟩

/-- A power of the kick takes the arc outside. -/
theorem kick_arc {n : ℤ} (hn : n ≠ 0) : ∀ c ∈ arcL, Kz ^ n • c ∈ outL := by
  rintro _ ⟨x, y, rfl, h1, h2, h3⟩
  rw [smul_mkL, Kz_zpow]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
  refine ⟨x, n * x + y, rfl, ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · refine Or.inr (Or.inl ⟨h1, ?_⟩)
    nlinarith
  · refine Or.inl ⟨h1, ?_⟩
    nlinarith

/-- A law whose matrix is given, on a line. -/
theorem smul_of_coe {A : SL2Z} {a b c d : ℤ} (hA : A.1 = !![a, b; c, d]) (x y : ℤ) :
    A • mkL x y = mkL (a * x + b * y) (c * x + d * y) := by
  rw [smul_mkL, hA]
  rfl

/-- A law taking the outside to the arc, given in the three cases of the outside. -/
theorem out_arc {A : SL2Z} {a b c d : ℤ} (hA : A.1 = !![a, b; c, d])
    (h : ∀ x y : ℤ, ((0 < x ∧ 0 < y) ∨ (0 < x ∧ y < -x) ∨ (x = 0 ∧ 0 < y)) →
      ∃ x' y' : ℤ, mkL (a * x + b * y) (c * x + d * y) = mkL x' y' ∧
        0 < x' ∧ -x' < y' ∧ y' < 0) :
    ∀ c ∈ outL, A • c ∈ arcL := by
  rintro _ ⟨x, y, rfl, hxy⟩
  rw [smul_of_coe hA]
  obtain ⟨x', y', he, h1⟩ := h x y hxy
  exact ⟨x', y', he, h1⟩

/-- The tick at the pull `μ`. -/
theorem tick_coe (μ : ℤ) : (Mz μ * Kz).1 = !![1 - μ, -μ; 1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Mz_coe, Kz_coe, Matrix.mul_fin_two]
  refine congrArg₂ (fun a b => !![a, b; 1, 1]) ?_ ?_ <;> ring

/-! ### Words and relations -/

/-- The law of a word in `K` and `M` at the pull `μ`. -/
noncomputable abbrev wordLaw (μ : ℤ) : FreeGroup (Fin 2) →* SL2Z := FreeGroup.lift ![Kz, Mz μ]

theorem wordLaw_K (μ : ℤ) : wordLaw μ wK = Kz := by simp [wordLaw, wK]

theorem wordLaw_M (μ : ℤ) : wordLaw μ wM = Mz μ := by simp [wordLaw, wM]

/-- The group presented by a set of relations. -/
abbrev Pres (rels : Set (FreeGroup (Fin 2))) := FreeGroup (Fin 2) ⧸ Subgroup.normalClosure rels

/-- The class of a word in the presented group. -/
abbrev mkP (rels : Set (FreeGroup (Fin 2))) : FreeGroup (Fin 2) →* Pres rels := QuotientGroup.mk' _

section Presented

variable {μ : ℤ} {rels : Set (FreeGroup (Fin 2))}

/-- The law of an element of the presented group. -/
noncomputable def presLaw (hr : ∀ r ∈ rels, wordLaw μ r = 1) : Pres rels →* SL2Z :=
  QuotientGroup.lift _ (wordLaw μ) (Subgroup.normalClosure_le_normal hr)

theorem presLaw_mk (hr : ∀ r ∈ rels, wordLaw μ r = 1) (w : FreeGroup (Fin 2)) :
    presLaw hr (mkP rels w) = wordLaw μ w := rfl

theorem mkP_rel {r : FreeGroup (Fin 2)} (h : r ∈ rels) : mkP rels r = 1 :=
  (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure h)

/-- A subgroup containing the images of the generators is everything. -/
theorem gens_top {Q : Type*} [Group Q] (π : FreeGroup (Fin 2) →* Q) (hπ : Function.Surjective π)
    (R : Subgroup Q) (h0 : π wK ∈ R) (h1 : π wM ∈ R) : R = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro q -
  obtain ⟨w, rfl⟩ := hπ q
  induction w using FreeGroup.induction_on with
  | one => rw [map_one]; exact one_mem _
  | of x =>
    fin_cases x
    · exact h0
    · exact h1
  | inv_of x hx =>
    rw [map_inv]
    exact inv_mem hx
  | mul x y hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- From the kernel on the lines to the relations. -/
theorem word_iff_of_ker (hr : ∀ r ∈ rels, wordLaw μ r = 1) (Z : Subgroup (Pres rels))
    (hker : (chi.comp (presLaw hr)).ker ≤ Z) (hZ1 : ∀ g ∈ Z, presLaw hr g = 1 → g = 1)
    (w : FreeGroup (Fin 2)) : wordLaw μ w = 1 ↔ w ∈ Subgroup.normalClosure rels := by
  constructor
  · intro h
    have h1 : mkP rels w ∈ (chi.comp (presLaw hr)).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, presLaw_mk, h, map_one]
    have h2 := hZ1 _ (hker h1) (by rw [presLaw_mk]; exact h)
    exact (QuotientGroup.eq_one_iff w).mp h2
  · intro h
    exact (Subgroup.normalClosure_le_normal (N := (wordLaw μ).ker) hr) h

end Presented

section Range

variable {A B Q : Type*} [Group Q]

theorem mem_range_left {A B : Type} [Group A] [Group B] {Q : Type*} [Group Q] (a : A →* Q)
    (b : B →* Q) (h : A) : a h ∈ (Monoid.CoprodI.lift (famHom a b)).range :=
  ⟨Monoid.CoprodI.of (i := false) h, Monoid.CoprodI.lift_of _ _⟩

theorem mem_range_right {A B : Type} [Group A] [Group B] {Q : Type*} [Group Q] (a : A →* Q)
    (b : B →* Q) (h : B) : b h ∈ (Monoid.CoprodI.lift (famHom a b)).range :=
  ⟨Monoid.CoprodI.of (i := true) h, Monoid.CoprodI.lift_of _ _⟩

end Range

theorem z3_cases (h : Multiplicative (ZMod 3)) (hh : h ≠ 1) :
    h = Multiplicative.ofAdd ((1 : ℕ) : ZMod 3) ∨ h = Multiplicative.ofAdd ((2 : ℕ) : ZMod 3) := by
  revert h
  decide

theorem z2_cases (h : Multiplicative (ZMod 2)) (hh : h ≠ 1) :
    h = Multiplicative.ofAdd ((1 : ℕ) : ZMod 2) := by
  revert h
  decide

theorem toAdd_ne_zero {h : Multiplicative ℤ} (hh : h ≠ 1) : Multiplicative.toAdd h ≠ 0 := by
  intro h0
  apply hh
  rw [← ofAdd_toAdd h, h0]
  rfl

theorem card_mint : 3 ≤ #(Multiplicative ℤ) :=
  le_trans (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3)).le)
    (Cardinal.aleph0_le_mk _)

theorem card_z3 : 3 ≤ #(Multiplicative (ZMod 3)) := by
  rw [Cardinal.mk_fintype]
  norm_cast

/-! ### `μ = 3` -/

theorem tick3_coe : (Mz 3 * Kz).1 = !![-2, -3; 1, 1] := by
  rw [tick_coe]
  norm_num

theorem tick3_sq_coe : ((Mz 3 * Kz) ^ 2).1 = !![1, 3; -1, -2] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, tick3_coe, Matrix.mul_fin_two]
  norm_num

theorem tick3_cube : (Mz 3 * Kz) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, tick3_sq_coe, tick3_coe, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  norm_num

theorem tick3_out : ∀ c ∈ outL, (Mz 3 * Kz) • c ∈ arcL := by
  refine out_arc tick3_coe ?_
  rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨2 * x + 3 * y, -x - y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega, by omega⟩
  · exact ⟨-2 * x + -3 * y, 1 * x + 1 * y, rfl, by omega, by omega, by omega⟩
  · exact ⟨2 * x + 3 * y, -x - y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega, by omega⟩

theorem tick3_sq_out : ∀ c ∈ outL, (Mz 3 * Kz) ^ 2 • c ∈ arcL := by
  refine out_arc tick3_sq_coe ?_
  rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨1 * x + 3 * y, -1 * x + -2 * y, rfl, by omega, by omega, by omega⟩
  · exact ⟨-x - 3 * y, x + 2 * y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega, by omega⟩
  · exact ⟨1 * x + 3 * y, -1 * x + -2 * y, rfl, by omega, by omega, by omega⟩

theorem hr3 : ∀ r ∈ relsQ3, wordLaw 3 r = 1 := by
  rintro _ rfl
  rw [map_pow, map_mul, wordLaw_M, wordLaw_K]
  exact tick3_cube

/-- The relation of the table presents `Σ₃`. -/
theorem word_iff_three (w : FreeGroup (Fin 2)) :
    wordLaw 3 w = 1 ↔ w ∈ Subgroup.normalClosure relsQ3 := by
  refine word_iff_of_ker hr3 ⊥ ?_ (fun g hg _ => hg) w
  have ht3 : (mkP relsQ3 wM * mkP relsQ3 wK) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow]
    exact mkP_rel rfl
  refine ker_le_of_ping_pong (α := Line) (chi.comp (presLaw hr3)) ⊥ bot_le
    ((QuotientGroup.mk' ⊥).comp (zpowersHom _ (mkP relsQ3 wK)))
    ((QuotientGroup.mk' ⊥).comp (zmodHom 3 _ ht3)) ?_ (Or.inl card_mint) outL arcL
    outL_nonempty arcL_nonempty disjoint_out_arc ?_ ?_
  · refine gens_top ((QuotientGroup.mk' ⊥).comp (mkP relsQ3))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) _ ?_ ?_
    · have h := mem_range_left ((QuotientGroup.mk' ⊥).comp (zpowersHom _ (mkP relsQ3 wK)))
        ((QuotientGroup.mk' ⊥).comp (zmodHom 3 _ ht3)) (Multiplicative.ofAdd (1 : ℤ))
      simpa using h
    · have hk := mem_range_left ((QuotientGroup.mk' ⊥).comp (zpowersHom _ (mkP relsQ3 wK)))
        ((QuotientGroup.mk' ⊥).comp (zmodHom 3 _ ht3)) (Multiplicative.ofAdd (1 : ℤ))
      have ht := mem_range_right ((QuotientGroup.mk' ⊥).comp (zpowersHom _ (mkP relsQ3 wK)))
        ((QuotientGroup.mk' ⊥).comp (zmodHom 3 _ ht3)) (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3))
      have h := mul_mem ht (inv_mem hk)
      simp only [MonoidHom.comp_apply, zmodHom_natCast, pow_one, zpowersHom_apply, toAdd_ofAdd,
        zpow_one, ← map_inv, ← map_mul, mul_inv_cancel_right] at h
      exact h
  · intro h hh
    have e : QuotientGroup.lift ⊥ (chi.comp (presLaw hr3)) bot_le
        ((QuotientGroup.mk' ⊥).comp (zpowersHom _ (mkP relsQ3 wK)) h) =
        chi (Kz ^ Multiplicative.toAdd h) := by
      change chi (presLaw hr3 (zpowersHom _ (mkP relsQ3 wK) h)) = _
      rw [zpowersHom_apply, map_zpow, presLaw_mk, wordLaw_K]
    rw [e]
    exact chi_smul_subset (kick_arc (toAdd_ne_zero hh))
  · intro h hh
    have e : ∀ n : ℕ, QuotientGroup.lift ⊥ (chi.comp (presLaw hr3)) bot_le
        ((QuotientGroup.mk' ⊥).comp (zmodHom 3 _ ht3) (Multiplicative.ofAdd (n : ZMod 3))) =
        chi ((Mz 3 * Kz) ^ n) := by
      intro n
      change chi (presLaw hr3 (zmodHom 3 _ ht3 (Multiplicative.ofAdd (n : ZMod 3)))) = _
      rw [zmodHom_natCast, map_pow, map_mul, presLaw_mk, presLaw_mk, wordLaw_M, wordLaw_K]
    rcases z3_cases h hh with rfl | rfl
    · rw [e, pow_one]
      exact chi_smul_subset tick3_out
    · rw [e]
      exact chi_smul_subset tick3_sq_out

/-! ### A central element of order two -/

section Central

variable {P : Type*} [Group P]

theorem normal_zpowers (z : P) (hc : ∀ g, g * z = z * g) : (Subgroup.zpowers z).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ g
  have h : Commute g (z ^ k) := Commute.zpow_right (hc g) k
  refine ⟨k, ?_⟩
  change z ^ k = g * z ^ k * g⁻¹
  rw [h.eq, mul_inv_cancel_right]

theorem zpow_two_cases {z : P} (hz : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hz, one_zpow, one_mul, zpow_one]

end Central

/-- A matrix equal to `-I` is the identity on the lines. -/
theorem chi_neg (A : SL2Z) (hA : A.1 = !![-1, 0; 0, -1]) : chi A = 1 :=
  Equiv.ext fun c => neg_one_smul_line A hA c

/-- `-I` is not the identity. -/
theorem neg_ne_one_law {A : SL2Z} (hA : A.1 = !![-1, 0; 0, -1]) : A ≠ 1 := by
  intro h
  rw [h] at hA
  have h1 := congrFun (congrFun hA 0) 0
  simp at h1

/-! ### `μ = 2` -/

theorem tick2_coe : (Mz 2 * Kz).1 = !![-1, -2; 1, 1] := by
  rw [tick_coe]
  norm_num

theorem tick2_sq_coe : ((Mz 2 * Kz) ^ 2).1 = !![-1, 0; 0, -1] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, tick2_coe, Matrix.mul_fin_two]
  norm_num

theorem tick2_four : (Mz 2 * Kz) ^ 4 = 1 := by
  refine Subtype.ext ?_
  have h : (Mz 2 * Kz) ^ 4 = (Mz 2 * Kz) ^ 2 * (Mz 2 * Kz) ^ 2 := by rw [← pow_add]
  rw [h, Matrix.SpecialLinearGroup.coe_mul, tick2_sq_coe, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  norm_num

theorem tick2_comm : (Mz 2 * Kz) ^ 2 * Kz = Kz * (Mz 2 * Kz) ^ 2 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, tick2_sq_coe, Kz_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem tick2_out : ∀ c ∈ outL, (Mz 2 * Kz) • c ∈ arcL := by
  refine out_arc tick2_coe ?_
  rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨x + 2 * y, -x - y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega, by omega⟩
  · exact ⟨-1 * x + -2 * y, 1 * x + 1 * y, rfl, by omega, by omega, by omega⟩
  · exact ⟨x + 2 * y, -x - y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega, by omega⟩

theorem hr2 : ∀ r ∈ relsQ2, wordLaw 2 r = 1 := by
  rintro _ (rfl | rfl)
  · rw [map_pow, map_mul, wordLaw_M, wordLaw_K]
    exact tick2_four
  · rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_mul, wordLaw_M, wordLaw_K,
      mul_inv_eq_one]
    exact tick2_comm

/-- The relations of the table present `Σ₂`. -/
theorem word_iff_two (w : FreeGroup (Fin 2)) :
    wordLaw 2 w = 1 ↔ w ∈ Subgroup.normalClosure relsQ2 := by
  set kk := mkP relsQ2 wK with hkk
  set mm := mkP relsQ2 wM with hmm
  set tt := mm * kk with htt
  have h4 : tt ^ 4 = 1 := by
    rw [htt, hmm, hkk, ← map_mul, ← map_pow]
    exact mkP_rel (Or.inl rfl)
  have hcomm : tt ^ 2 * kk = kk * tt ^ 2 := by
    have h := mkP_rel (rels := relsQ2) (r := (wM * wK) ^ 2 * wK * (wK * (wM * wK) ^ 2)⁻¹)
      (Or.inr rfl)
    rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_mul, mul_inv_eq_one] at h
    exact h
  have hz2 : (tt ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  have hcentral : ∀ g, g * tt ^ 2 = tt ^ 2 * g := by
    have htop := gens_top (mkP relsQ2) (QuotientGroup.mk'_surjective _)
      (Subgroup.centralizer {tt ^ 2}) ?_ ?_
    · intro g
      have hg : g ∈ Subgroup.centralizer {tt ^ 2} := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg _ rfl).symm
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact hcomm
    · have hkc : kk ∈ Subgroup.centralizer {tt ^ 2} := by
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro _ rfl
        exact hcomm
      have htc : tt ∈ Subgroup.centralizer {tt ^ 2} := by
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro _ rfl
        rw [← pow_succ, ← pow_succ']
      have h := mul_mem htc (inv_mem hkc)
      rw [htt, mul_inv_cancel_right] at h
      exact h
  have hnorm := normal_zpowers (tt ^ 2) hcentral
  have hlaw : presLaw hr2 (tt ^ 2) = (Mz 2 * Kz) ^ 2 := by
    rw [map_pow, htt, map_mul, hmm, hkk, presLaw_mk, presLaw_mk, wordLaw_M, wordLaw_K]
  have hZ : Subgroup.zpowers (tt ^ 2) ≤ (chi.comp (presLaw hr2)).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, MonoidHom.comp_apply, hlaw]
    exact chi_neg _ tick2_sq_coe
  refine word_iff_of_ker hr2 (Subgroup.zpowers (tt ^ 2)) ?_ ?_ w
  · have ht2 : (QuotientGroup.mk' (Subgroup.zpowers (tt ^ 2)) tt) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    refine ker_le_of_ping_pong (α := Line) (chi.comp (presLaw hr2)) (Subgroup.zpowers (tt ^ 2)) hZ
      ((QuotientGroup.mk' _).comp (zpowersHom _ kk)) (zmodHom 2 _ ht2) ?_ (Or.inl card_mint)
      outL arcL outL_nonempty arcL_nonempty disjoint_out_arc ?_ ?_
    · refine gens_top ((QuotientGroup.mk' _).comp (mkP relsQ2))
        ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) _ ?_ ?_
      · have h := mem_range_left ((QuotientGroup.mk' (Subgroup.zpowers (tt ^ 2))).comp
          (zpowersHom _ kk)) (zmodHom 2 _ ht2) (Multiplicative.ofAdd (1 : ℤ))
        simp only [MonoidHom.comp_apply, zpowersHom_apply, toAdd_ofAdd, zpow_one] at h
        exact h
      · have h0 := mem_range_left ((QuotientGroup.mk' (Subgroup.zpowers (tt ^ 2))).comp
          (zpowersHom _ kk)) (zmodHom 2 _ ht2) (Multiplicative.ofAdd (1 : ℤ))
        have ht := mem_range_right ((QuotientGroup.mk' (Subgroup.zpowers (tt ^ 2))).comp
          (zpowersHom _ kk)) (zmodHom 2 _ ht2) (Multiplicative.ofAdd ((1 : ℕ) : ZMod 2))
        have h := mul_mem ht (inv_mem h0)
        simp only [MonoidHom.comp_apply, zmodHom_natCast, pow_one, zpowersHom_apply, toAdd_ofAdd,
          zpow_one, ← map_inv, ← map_mul] at h
        have e : tt * kk⁻¹ = mm := by rw [htt, mul_inv_cancel_right]
        rw [e] at h
        exact h
    · intro h hh
      have e : QuotientGroup.lift _ (chi.comp (presLaw hr2)) hZ
          ((QuotientGroup.mk' _).comp (zpowersHom _ kk) h) =
          chi (Kz ^ Multiplicative.toAdd h) := by
        change chi (presLaw hr2 (zpowersHom _ kk h)) = _
        rw [zpowersHom_apply, map_zpow, hkk, presLaw_mk, wordLaw_K]
      rw [e]
      exact chi_smul_subset (kick_arc (toAdd_ne_zero hh))
    · intro h hh
      obtain rfl := z2_cases h hh
      rw [zmodHom_natCast, pow_one]
      change chi (presLaw hr2 tt) • outL ⊆ arcL
      have e : presLaw hr2 tt = Mz 2 * Kz := by
        rw [htt, map_mul, hmm, hkk, presLaw_mk, presLaw_mk, wordLaw_M, wordLaw_K]
      rw [e]
      exact chi_smul_subset tick2_out
  · rintro _ ⟨k, rfl⟩ h
    rcases zpow_two_cases hz2 k with h1 | h1
    · exact h1
    · change (tt ^ 2) ^ k = 1
      change presLaw hr2 ((tt ^ 2) ^ k) = 1 at h
      rw [h1, hlaw] at h
      exact absurd h (neg_ne_one_law tick2_sq_coe)

/-! ### `μ = 1` -/

theorem tick1_coe : (Mz 1 * Kz).1 = !![0, -1; 1, 1] := by
  rw [tick_coe]
  norm_num

theorem tick1_sq_coe : ((Mz 1 * Kz) ^ 2).1 = !![-1, -1; 1, 0] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, tick1_coe, Matrix.mul_fin_two]
  norm_num

theorem J_coe : (Kz * Mz 1 * Kz).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Kz_coe, Mz_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem J_coe' : (Mz 1 * Kz * Mz 1).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, tick1_coe, Mz_coe, Matrix.mul_fin_two]
  norm_num

theorem J_sq_coe : ((Kz * Mz 1 * Kz) ^ 2).1 = !![-1, 0; 0, -1] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, J_coe, Matrix.mul_fin_two]
  norm_num

theorem J_four : (Kz * Mz 1 * Kz) ^ 4 = 1 := by
  refine Subtype.ext ?_
  have h : (Kz * Mz 1 * Kz) ^ 4 = (Kz * Mz 1 * Kz) ^ 2 * (Kz * Mz 1 * Kz) ^ 2 := by
    rw [← pow_add]
  rw [h, Matrix.SpecialLinearGroup.coe_mul, J_sq_coe, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  norm_num

theorem J_neg_pos : ∀ c ∈ negL, (Kz * Mz 1 * Kz) • c ∈ posL := by
  rintro _ ⟨x, y, rfl, h1, h2⟩
  rw [smul_of_coe J_coe]
  exact ⟨0 * x + -1 * y, 1 * x + 0 * y, rfl, by omega, by omega⟩

theorem tick1_pos_neg : ∀ c ∈ posL, (Mz 1 * Kz) • c ∈ negL := by
  rintro _ ⟨x, y, rfl, h1, h2⟩
  rw [smul_of_coe tick1_coe]
  exact ⟨y, -x - y, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega⟩

theorem tick1_sq_pos_neg : ∀ c ∈ posL, (Mz 1 * Kz) ^ 2 • c ∈ negL := by
  rintro _ ⟨x, y, rfl, h1, h2⟩
  rw [smul_of_coe tick1_sq_coe]
  exact ⟨x + y, -x, by rw [← mkL_neg]; congr 1 <;> ring, by omega, by omega⟩

theorem hr1 : ∀ r ∈ relsQ1, wordLaw 1 r = 1 := by
  rintro _ (rfl | rfl)
  · rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_mul, wordLaw_M, wordLaw_K,
      mul_inv_eq_one]
    exact Subtype.ext (J_coe.trans J_coe'.symm)
  · rw [map_pow, map_mul, map_mul, wordLaw_M, wordLaw_K]
    exact J_four

/-- The relations of the table present `Σ₁ = SL(2, Z)`. -/
theorem word_iff_one (w : FreeGroup (Fin 2)) :
    wordLaw 1 w = 1 ↔ w ∈ Subgroup.normalClosure relsQ1 := by
  set kk := mkP relsQ1 wK with hkk
  set mm := mkP relsQ1 wM with hmm
  set jj := kk * mm * kk with hjj
  set tt := mm * kk with htt
  have hbr : kk * mm * kk = mm * kk * mm := by
    have h := mkP_rel (rels := relsQ1) (r := wK * wM * wK * (wM * wK * wM)⁻¹) (Or.inl rfl)
    rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_mul, mul_inv_eq_one] at h
    exact h
  have h4 : jj ^ 4 = 1 := by
    rw [hjj, hkk, hmm, ← map_mul, ← map_mul, ← map_pow]
    exact mkP_rel (Or.inr rfl)
  have hz2 : (jj ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  -- `J` swaps `K` and `M`
  have hkj : kk * jj = jj * mm := by
    rw [hjj]
    calc kk * (kk * mm * kk) = kk * (mm * kk * mm) := by rw [hbr]
      _ = kk * mm * kk * mm := by group
  have hmj : mm * jj = jj * kk := by
    rw [hjj]
    calc mm * (kk * mm * kk) = mm * kk * mm * kk := by group
      _ = kk * mm * kk * kk := by rw [hbr]
  have hkz : jj ^ 2 * kk = kk * jj ^ 2 := by
    rw [pow_two]
    calc jj * jj * kk = jj * (jj * kk) := mul_assoc _ _ _
      _ = jj * (mm * jj) := by rw [hmj]
      _ = jj * mm * jj := (mul_assoc _ _ _).symm
      _ = kk * jj * jj := by rw [hkj]
      _ = kk * (jj * jj) := mul_assoc _ _ _
  have hmz : jj ^ 2 * mm = mm * jj ^ 2 := by
    rw [pow_two]
    calc jj * jj * mm = jj * (jj * mm) := mul_assoc _ _ _
      _ = jj * (kk * jj) := by rw [hkj]
      _ = jj * kk * jj := (mul_assoc _ _ _).symm
      _ = mm * jj * jj := by rw [hmj]
      _ = mm * (jj * jj) := mul_assoc _ _ _
  have ht3 : tt ^ 3 = jj ^ 2 := by
    rw [pow_succ, pow_two, pow_two]
    calc tt * tt * tt = (mm * kk * mm) * (kk * mm * kk) := by rw [htt]; group
      _ = jj * jj := by rw [← hbr]
  have hcentral : ∀ g, g * jj ^ 2 = jj ^ 2 * g := by
    have htop := gens_top (mkP relsQ1) (QuotientGroup.mk'_surjective _)
      (Subgroup.centralizer {jj ^ 2}) ?_ ?_
    · intro g
      have hg : g ∈ Subgroup.centralizer {jj ^ 2} := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg _ rfl).symm
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact hkz
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact hmz
  have hnorm := normal_zpowers (jj ^ 2) hcentral
  have hJlaw : presLaw hr1 jj = Kz * Mz 1 * Kz := by
    rw [hjj, map_mul, map_mul, hkk, hmm, presLaw_mk, presLaw_mk, wordLaw_M, wordLaw_K]
  have hTlaw : presLaw hr1 tt = Mz 1 * Kz := by
    rw [htt, map_mul, hkk, hmm, presLaw_mk, presLaw_mk, wordLaw_M, wordLaw_K]
  have hlaw : presLaw hr1 (jj ^ 2) = (Kz * Mz 1 * Kz) ^ 2 := by
    rw [map_pow, hJlaw]
  have hZ : Subgroup.zpowers (jj ^ 2) ≤ (chi.comp (presLaw hr1)).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, MonoidHom.comp_apply, hlaw]
    exact chi_neg _ J_sq_coe
  refine word_iff_of_ker hr1 (Subgroup.zpowers (jj ^ 2)) ?_ ?_ w
  · have hj2 : (QuotientGroup.mk' (Subgroup.zpowers (jj ^ 2)) jj) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    have ht3' : (QuotientGroup.mk' (Subgroup.zpowers (jj ^ 2)) tt) ^ 3 = 1 := by
      rw [← map_pow, ht3]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    refine ker_le_of_ping_pong (α := Line) (chi.comp (presLaw hr1)) (Subgroup.zpowers (jj ^ 2)) hZ
      (zmodHom 2 _ hj2) (zmodHom 3 _ ht3') ?_ (Or.inr card_z3) posL negL posL_nonempty
      negL_nonempty disjoint_pos_neg ?_ ?_
    · have hJr := mem_range_left (zmodHom 2 _ hj2) (zmodHom 3 _ ht3')
        (Multiplicative.ofAdd ((1 : ℕ) : ZMod 2))
      have hTr := mem_range_right (zmodHom 2 _ hj2) (zmodHom 3 _ ht3')
        (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3))
      rw [zmodHom_natCast, pow_one] at hJr hTr
      have hKr := mul_mem hJr (inv_mem hTr)
      have eK : jj * tt⁻¹ = kk := by
        rw [hjj, htt]
        group
      rw [← map_inv, ← map_mul, eK] at hKr
      refine gens_top ((QuotientGroup.mk' _).comp (mkP relsQ1))
        ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) _ hKr ?_
      have hMr := mul_mem hTr (inv_mem hKr)
      have eM : tt * kk⁻¹ = mm := by
        rw [htt, mul_inv_cancel_right]
      rw [← map_inv, ← map_mul, eM] at hMr
      exact hMr
    · intro h hh
      obtain rfl := z2_cases h hh
      rw [zmodHom_natCast, pow_one]
      change chi (presLaw hr1 jj) • negL ⊆ posL
      rw [hJlaw]
      exact chi_smul_subset J_neg_pos
    · intro h hh
      rcases z3_cases h hh with rfl | rfl
      · rw [zmodHom_natCast, pow_one]
        change chi (presLaw hr1 tt) • posL ⊆ negL
        rw [hTlaw]
        exact chi_smul_subset tick1_pos_neg
      · rw [zmodHom_natCast, map_pow]
        change chi (presLaw hr1 tt) ^ 2 • posL ⊆ negL
        rw [← map_pow, hTlaw]
        exact chi_smul_subset tick1_sq_pos_neg
  · rintro _ ⟨k, rfl⟩ h
    rcases zpow_two_cases hz2 k with h1 | h1
    · exact h1
    · change (jj ^ 2) ^ k = 1
      change presLaw hr1 ((jj ^ 2) ^ k) = 1 at h
      rw [h1, hlaw] at h
      exact absurd h (neg_ne_one_law J_sq_coe)

/-! ### The free products -/

section FreeProducts

/-- The two forms of a free product of two groups. -/
noncomputable def coprodEquiv (A B : Type) [Group A] [Group B] :
    Monoid.Coprod A B ≃* Monoid.CoprodI (Fam A B) :=
  MonoidHom.toMulEquiv
    (Monoid.Coprod.lift (Monoid.CoprodI.of (M := Fam A B) (i := false))
      (Monoid.CoprodI.of (M := Fam A B) (i := true)))
    (Monoid.CoprodI.lift (famHom Monoid.Coprod.inl Monoid.Coprod.inr))
    (by
      refine Monoid.Coprod.hom_ext ?_ ?_
      · refine MonoidHom.ext fun a => ?_
        rfl
      · refine MonoidHom.ext fun b => ?_
        rfl)
    (by
      refine Monoid.CoprodI.ext_hom _ _ ?_
      rintro (_ | _)
      · refine MonoidHom.ext fun a => ?_
        simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of, MonoidHom.id_apply]
        exact Monoid.Coprod.lift_apply_inl _ _ _
      · refine MonoidHom.ext fun b => ?_
        simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of, MonoidHom.id_apply]
        exact Monoid.Coprod.lift_apply_inr _ _ _)

/-- The map from `Z ∗ Z₃` to the laws at `μ = 3`. -/
noncomputable def z3Map :
    Monoid.CoprodI (Fam (Multiplicative ℤ) (Multiplicative (ZMod 3))) →* SL2Z :=
  Monoid.CoprodI.lift (famHom (zpowersHom SL2Z Kz) (zmodHom 3 (Mz 3 * Kz) tick3_cube))

theorem z3Map_injective : Function.Injective z3Map := by
  refine pair_injective (α := Line) _ _ (Or.inl card_mint) outL arcL outL_nonempty arcL_nonempty
    disjoint_out_arc ?_ ?_
  · intro h hh
    rintro _ ⟨c, hc, rfl⟩
    rw [zpowersHom_apply]
    exact kick_arc (toAdd_ne_zero hh) c hc
  · intro h hh
    rintro _ ⟨c, hc, rfl⟩
    rcases z3_cases h hh with rfl | rfl
    · change (zmodHom 3 (Mz 3 * Kz) tick3_cube (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3))) • c ∈ arcL
      rw [zmodHom_natCast, pow_one]
      exact tick3_out c hc
    · change (zmodHom 3 (Mz 3 * Kz) tick3_cube (Multiplicative.ofAdd ((2 : ℕ) : ZMod 3))) • c ∈ arcL
      rw [zmodHom_natCast]
      exact tick3_sq_out c hc

theorem z3Map_range : z3Map.range = stepGroup 3 := by
  have hK : Kz ∈ stepGroup 3 := Subgroup.subset_closure (Or.inl rfl)
  have hM : Mz 3 ∈ stepGroup 3 := Subgroup.subset_closure (Or.inr rfl)
  apply le_antisymm
  · refine Monoid.CoprodI.lift_range_le _
      (famHom (zpowersHom SL2Z Kz) (zmodHom 3 (Mz 3 * Kz) tick3_cube)) ?_
    rintro (_ | _)
    · rintro _ ⟨h, rfl⟩
      exact zpow_mem hK _
    · rintro _ ⟨h, rfl⟩
      have hn : (show Multiplicative (ZMod 3) from h) =
          Multiplicative.ofAdd (((Multiplicative.toAdd (show Multiplicative (ZMod 3) from h)).val :
            ℕ) : ZMod 3) := by
        rw [ZMod.natCast_zmod_val]
        rfl
      change zmodHom 3 (Mz 3 * Kz) tick3_cube (show Multiplicative (ZMod 3) from h) ∈ _
      rw [hn, zmodHom_natCast]
      exact pow_mem (mul_mem hM hK) _
  · have hk : Kz ∈ z3Map.range := by
      have h := mem_range_left (zpowersHom SL2Z Kz) (zmodHom 3 (Mz 3 * Kz) tick3_cube)
        (Multiplicative.ofAdd (1 : ℤ))
      simp only [zpowersHom_apply, toAdd_ofAdd, zpow_one] at h
      exact h
    have ht : Mz 3 * Kz ∈ z3Map.range := by
      have h := mem_range_right (zpowersHom SL2Z Kz) (zmodHom 3 (Mz 3 * Kz) tick3_cube)
        (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3))
      rwa [zmodHom_natCast, pow_one] at h
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl)
    · exact hk
    · have h := mul_mem ht (inv_mem hk)
      rwa [mul_inv_cancel_right] at h

end FreeProducts

/-- **T13** (Theorem Q, part 3: the presentations). -/
@[ledger "T13"]
theorem stepPresentations : Statement.stepPresentations := by
  refine ⟨word_iff_one, word_iff_two, word_iff_three, ?_, ?_⟩
  · have h3 : stepGroup 3 = gammaUpper 3 := by
      have := ((stepGroups.1 3 (by norm_num)).2).mpr (by norm_num)
      simpa using this
    exact ⟨(coprodEquiv _ _).trans ((MonoidHom.ofInjective z3Map_injective).trans
      (MulEquiv.subgroupCongr (z3Map_range.trans h3)))⟩
  · have h4 : stepGroup 4 = gammaUpper 4 := by
      have := ((stepGroups.1 4 (by norm_num)).2).mpr (by norm_num)
      simpa using this
    have hinj : Function.Injective (FreeGroup.lift ![Kz, Mz 4]) := by
      simpa using (stepGroupsFree.2 4 (by norm_num)).mpr (by norm_num)
    have hr : (FreeGroup.lift ![Kz, Mz 4]).range = gammaUpper 4 := by
      have hK : Kz ∈ stepGroup 4 := Subgroup.subset_closure (Or.inl rfl)
      have hM : Mz 4 ∈ stepGroup 4 := Subgroup.subset_closure (Or.inr rfl)
      rw [← h4]
      apply le_antisymm
      · refine FreeGroup.range_lift_le ?_
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hK
        · exact hM
      · refine (Subgroup.closure_le _).mpr ?_
        rintro _ (rfl | rfl)
        · exact ⟨FreeGroup.of 0, by simp⟩
        · exact ⟨FreeGroup.of 1, by simp⟩
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)⟩

/-! ## Non-vacuity -/

/-- At `μ = 3` the word `(K M)³`, a conjugate of the relator, is implied by the relation. -/
example : (wK * wM) ^ 3 ∈ Subgroup.normalClosure relsQ3 := by
  refine (word_iff_three _).mp ?_
  rw [map_pow, map_mul, wordLaw_K, wordLaw_M]
  have h : Kz * Mz 3 = Kz * (Mz 3 * Kz) * Kz⁻¹ := by group
  rw [h, conj_pow, tick3_cube, mul_one, mul_inv_cancel]

/-- At `μ = 3` the kick is not implied by the relation. -/
example : wK ∉ Subgroup.normalClosure relsQ3 := by
  intro h
  have h1 := (word_iff_three _).mpr h
  rw [wordLaw_K] at h1
  have h2 := congrArg (fun A : SL2Z => A.1 1 0) h1
  simp [Step.mat] at h2

/-- At `μ = 2` the word `(M K)²` is not implied by the relations: it is `-I`. -/
example : (wM * wK) ^ 2 ∉ Subgroup.normalClosure relsQ2 := by
  intro h
  have h1 := (word_iff_two _).mpr h
  rw [map_pow, map_mul, wordLaw_M, wordLaw_K] at h1
  exact neg_ne_one_law tick2_sq_coe h1

/-- At `μ = 1`, `(K M K)²` is not implied by the relations, and its square is. -/
example : (wK * wM * wK) ^ 2 ∉ Subgroup.normalClosure relsQ1 ∧
    (wK * wM * wK) ^ 4 ∈ Subgroup.normalClosure relsQ1 := by
  refine ⟨fun h => ?_, Subgroup.subset_normalClosure (Or.inr rfl)⟩
  have h1 := (word_iff_one _).mpr h
  rw [map_pow, map_mul, map_mul, wordLaw_M, wordLaw_K] at h1
  exact neg_ne_one_law J_sq_coe h1

end Artform.Scores.StepGroup
