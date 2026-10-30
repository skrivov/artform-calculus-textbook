import ArtformScores.ExtentTable

/-!
# The two squares are the projective line over `F₅`

The ledger's finding 038, Theorem Y. Label the corners `v₀, …, v₅` by `∞, 0, 1, 2, 3, 4`. Then `L`
is `x ↦ 1 / (2 x + 1)` and `R` is `x ↦ 2 x + 3`, and the group they generate is `PGL(2, 5)`, the
image of `GL(2, 5)` in the permutations of the projective line: it has at most `480 / 4 = 120`
elements, since the scalars act trivially, and the two squares' run has `120`. Moore's presentation
of `S₅` gives the isomorphism `PGL(2, 5) ≅ S₅`, on the ten fixed-point-free involutions. A check
over all of `S₆` shows that `L` and `R` are Möbius maps for exactly the labellings in one orbit.
-/

namespace Artform.Scores.Bells

open Equiv

/-- A Möbius map, on `F₅` with `none` for the point at infinity. -/
def mobOpt (a b c d : K5) : Option K5 → Option K5
  | none => if c = 0 then none else some (a / c)
  | some k => if c * k + d = 0 then none else some ((a * k + b) / (c * k + d))

theorem corner_apply (i : Fin 6) : corner i = pointOf i := rfl

theorem smul_eq_mobOpt (g : Matrix.GeneralLinearGroup (Fin 2) K5) (x : OnePoint K5) :
    g • x = mobOpt (g 0 0) (g 0 1) (g 1 0) (g 1 1) x := by
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    simp only [mobOpt]
    rfl
  | coe k =>
    rw [OnePoint.smul_some_eq_ite]
    simp only [mobOpt]
    rfl

theorem mob_L : ∀ i : Fin 6, pointOf (squareL i) = mobOpt 0 1 2 1 (pointOf i) := by
  decide +kernel

theorem mob_R : ∀ i : Fin 6, pointOf (squareR i) = mobOpt 2 3 0 1 (pointOf i) := by
  decide +kernel

/-- The turns are Möbius maps. -/
theorem permCongr_squareL : corner.permCongr squareL = rho matL := by
  ext x
  obtain ⟨i, rfl⟩ := corner.surjective x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, rho, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rw [smul_eq_mobOpt, corner_apply, corner_apply]
  exact mob_L i

theorem permCongr_squareR : corner.permCongr squareR = rho matR := by
  ext x
  obtain ⟨i, rfl⟩ := corner.surjective x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, rho, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rw [smul_eq_mobOpt, corner_apply, corner_apply]
  exact mob_R i

theorem map_le_range : twoSquares.map toLine.toMonoidHom ≤ rho.range := by
  rw [twoSquares, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · exact ⟨matL, permCongr_squareL.symm⟩
  · exact ⟨matR, permCongr_squareR.symm⟩

/-- A scalar acts trivially. -/
theorem scalar_mem_ker (u : K5ˣ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (!![(u : K5), 0; 0, (u : K5)])
      (by rw [Matrix.det_fin_two_of]; simp) ∈ rho.ker := by
  rw [MonoidHom.mem_ker]
  ext x
  simp only [rho, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  rw [smul_eq_mobOpt]
  change mobOpt (u : K5) 0 0 (u : K5) x = x
  have hu : (u : K5) ≠ 0 := u.ne_zero
  induction x using OnePoint.rec with
  | infty => simp [mobOpt, OnePoint.infty]
  | coe k =>
    change mobOpt (u : K5) 0 0 (u : K5) (some k) = some k
    simp only [mobOpt, zero_mul, zero_add, hu]
    simp only [ite_false, add_zero]
    congr 1
    field_simp

theorem card_range_le : Nat.card rho.range ≤ 120 := by
  have h1 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) K5) = 480 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup rho.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv, h1] at h2
  have h3 : 4 ≤ Nat.card rho.ker := by
    have h4 : Nat.card K5ˣ = 4 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      rfl
    rw [← h4]
    refine Nat.card_le_card_of_injective (fun u => ⟨_, scalar_mem_ker u⟩) ?_
    intro u v e
    have := congrArg (fun g : rho.ker => (g.1 : Matrix (Fin 2) (Fin 2) K5) 0 0) e
    simpa [Units.ext_iff] using this
  nlinarith

/-- The two squares generate `PGL(2, 5)`, acting on the projective line. -/
theorem map_eq_range : twoSquares.map toLine.toMonoidHom = rho.range := by
  apply Subgroup.eq_of_le_of_card_ge map_le_range
  rw [Subgroup.card_map_of_injective toLine.injective, card_squares]
  exact card_range_le

section Iso

/-- The transpositions of `S₅` in the group of the two squares. -/
def t0 : Perm (Fin 6) := ⟨![2, 4, 0, 5, 1, 3], ![2, 4, 0, 5, 1, 3], by decide, by decide⟩
def t1 : Perm (Fin 6) := ⟨![5, 3, 4, 1, 2, 0], ![5, 3, 4, 1, 2, 0], by decide, by decide⟩
def t2 : Perm (Fin 6) := ⟨![3, 4, 5, 0, 1, 2], ![3, 4, 5, 0, 1, 2], by decide, by decide⟩
def t3 : Perm (Fin 6) := ⟨![1, 0, 4, 5, 2, 3], ![1, 0, 4, 5, 2, 3], by decide, by decide⟩

theorem squareL_mem : squareL ∈ twoSquares := Subgroup.subset_closure (by simp)
theorem squareR_mem : squareR ∈ twoSquares := Subgroup.subset_closure (by simp)

theorem t0_mem : t0 ∈ twoSquares := by
  have : t0 = squareR * squareR * squareL * squareR * squareL := by decide
  rw [this]
  exact mul_mem (mul_mem (mul_mem (mul_mem squareR_mem squareR_mem) squareL_mem) squareR_mem)
    squareL_mem

theorem t1_mem : t1 ∈ twoSquares := by
  have : t1 = squareR * squareL * squareL * squareR * squareL := by decide
  rw [this]
  exact mul_mem (mul_mem (mul_mem (mul_mem squareR_mem squareL_mem) squareL_mem) squareR_mem)
    squareL_mem

theorem t2_mem : t2 ∈ twoSquares := by
  have : t2 = squareL * squareR⁻¹ * squareL⁻¹ * squareR⁻¹ * squareL := by decide
  rw [this]
  exact mul_mem (mul_mem (mul_mem (mul_mem squareL_mem (inv_mem squareR_mem)) (inv_mem squareL_mem))
    (inv_mem squareR_mem)) squareL_mem

theorem t3_mem : t3 ∈ twoSquares := by
  have : t3 = squareR * squareL * squareR * squareL * squareL := by decide
  rw [this]
  exact mul_mem (mul_mem (mul_mem (mul_mem squareR_mem squareL_mem) squareR_mem) squareL_mem)
    squareL_mem

/-- The generators of `S₅` in the group of the two squares. -/
def tGen : Fin 4 → twoSquares := ![⟨t0, t0_mem⟩, ⟨t1, t1_mem⟩, ⟨t2, t2_mem⟩, ⟨t3, t3_mem⟩]

/-- The map from words. -/
def tWord : FreeGroup (Fin 4) →* twoSquares := FreeGroup.lift tGen

theorem tGen_relations (i j : Fin 4) : (tGen i * tGen j) ^ (CoxeterMatrix.A 4 i j) = 1 := by
  apply Subtype.ext
  revert i j
  decide +kernel

theorem tWord_ker {v : FreeGroup (Fin 4)} (hv : Bells.law 4 v = 1) : tWord v = 1 := by
  have hb := (bellsPresentation 4).2 v 1
  rw [map_one] at hb
  have hmk := hb.mp hv
  let θ : PresentedGroup (CoxeterMatrix.A 4).relationsSet →* twoSquares :=
    PresentedGroup.toGroup (f := tGen) (by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      simp only [Function.uncurry, CoxeterMatrix.relation, map_pow, map_mul,
        FreeGroup.lift_apply_of]
      exact tGen_relations i j)
  have h2 : θ (PresentedGroup.mk _ v) = tWord v := rfl
  rw [← h2, hmk, map_one, map_one]

/-- The isomorphism with `S₅`. -/
theorem iso_S5 : Nonempty (twoSquares ≃* Perm (Fin 5)) := by
  have hsurj : Function.Surjective (Bells.law 4) := (bellsPresentation 4).1
  let ψ : Perm (Fin 5) →* twoSquares :=
    MonoidHom.liftOfSurjective (Bells.law 4) hsurj ⟨tWord, fun v hv => tWord_ker hv⟩
  have hψ : ∀ v, ψ (Bells.law 4 v) = tWord v := fun v =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ v
  have hrange : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_turns, Subgroup.closure_le]
    have hL : turnL = tWord (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 3 *
        FreeGroup.of 2) := by
      apply Subtype.ext
      simp only [tWord, map_mul, FreeGroup.lift_apply_of]
      decide
    have hR : turnR = tWord (FreeGroup.of 3 * FreeGroup.of 1 * FreeGroup.of 2) := by
      apply Subtype.ext
      simp only [tWord, map_mul, FreeGroup.lift_apply_of]
      decide
    rintro x (rfl | rfl)
    · exact ⟨_, (hψ _).trans hL.symm⟩
    · exact ⟨_, (hψ _).trans hR.symm⟩
  have hcard : Nat.card (Perm (Fin 5)) ≤ Nat.card twoSquares := by
    rw [card_squares, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  exact ⟨(MulEquiv.ofBijective ψ (hrange.bijective_of_nat_card_le hcard)).symm⟩

end Iso

section Labelling

/-- The mask of the codes of the group's elements. -/
def maskSquares : ℕ :=
  match pass1 nextSix codeSix (digits 120 Cert.wordSquares) oneSix 0 with
  | some (_, mask) => mask
  | none => 0

/-- The code of a permutation of the corners. -/
def codeOf (σ : Perm (Fin 6)) : ℕ :=
  codeSix ((σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val, (σ 5).val)

theorem codeOf_coe (g : twoSquares) : codeOf g.1 = codeSix (encSix g) := rfl

theorem codeOf_inj {σ τ : Perm (Fin 6)} (e : codeOf σ = codeOf τ) : σ = τ := by
  simp only [codeOf, codeSix] at e
  have hd : ∀ (g : Perm (Fin 6)) (i : Fin 6), (g i).val < 6 := fun g i => (g i).isLt
  obtain ⟨e1, e6⟩ := digit_eq (hd σ 5) (hd τ 5) e
  obtain ⟨e2, e5⟩ := digit_eq (hd σ 4) (hd τ 4) e1
  obtain ⟨e3, e4⟩ := digit_eq (hd σ 3) (hd τ 3) e2
  obtain ⟨e7, e8⟩ := digit_eq (hd σ 2) (hd τ 2) e3
  obtain ⟨e9, e10⟩ := digit_eq (hd σ 1) (hd τ 1) e7
  have e11 : (σ 0).val = (τ 0).val := by omega
  ext i
  fin_cases i
  · exact e11
  · exact e10
  · exact e8
  · exact e4
  · exact e5
  · exact e6

/-- Membership in the group, by the mask. -/
theorem mem_iff_mask (σ : Perm (Fin 6)) :
    σ ∈ twoSquares ↔ maskSquares.testBit (codeOf σ) = true := by
  have hc : checkRun nextSix codeSix (digits 120 Cert.wordSquares) oneSix = true := by
    decide +kernel
  have hc2 : checkRun modelSquares.next modelSquares.code (digits 120 Cert.wordSquares)
      (modelSquares.enc 1) = true := hc
  obtain ⟨-, -, hall⟩ := walk_of_check modelSquares.next modelSquares.code modelSquares.hnext
    modelSquares.hcode (π := MonoidHom.id _) closure_turns (digits_ne_nil (by norm_num) _) hc2
  rw [checkRun] at hc
  cases hp : pass1 nextSix codeSix (digits 120 Cert.wordSquares) oneSix 0 with
  | none => rw [hp] at hc; simp at hc
  | some out =>
    have hmask : maskSquares = out.2 := by
      simp only [maskSquares, hp]
    have hp2 : pass1 modelSquares.next modelSquares.code (digits 120 Cert.wordSquares)
        (modelSquares.enc 1) 0 = some out := hp
    obtain ⟨-, h2, -, -⟩ := pass1_spec modelSquares.next modelSquares.code modelSquares.hnext _ 1 0
      out hp2
    rw [hmask]
    constructor
    · intro hσ
      apply (h2 _).mpr
      right
      exact ⟨⟨σ, hσ⟩, hall _, rfl⟩
    · intro hb
      rcases (h2 _).mp hb with h | ⟨y, -, hy⟩
      · simp at h
      · have : σ = y.1 := codeOf_inj hy
        rw [this]
        exact y.2

/-- The normalizer: a labelling that makes both turns Möbius maps is the standard one, up to the
group. -/
theorem normalizer_check : ∀ h : Perm (Fin 6),
    maskSquares.testBit (codeOf (h * squareL * h⁻¹)) = true →
    maskSquares.testBit (codeOf (h * squareR * h⁻¹)) = true →
    maskSquares.testBit (codeOf h) = true := by
  decide +kernel

/-- A group element that fixes the corners `v₀, v₁, v₂` is `1`: the action is sharply
three-transitive. -/
theorem sharply_check : ∀ h : Perm (Fin 6), maskSquares.testBit (codeOf h) = true →
    h 0 = 0 → h 1 = 1 → h 2 = 2 → h = 1 := by
  decide +kernel

theorem toLine_mem_range_iff (y : Perm (Fin 6)) : toLine y ∈ rho.range ↔ y ∈ twoSquares := by
  rw [← map_eq_range]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have : x = y := toLine.injective hxy
    rwa [← this]
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The labelling `c` relative to the book's. -/
noncomputable def relLabel (c : Fin 6 ≃ OnePoint K5) : Perm (Fin 6) := c.trans corner.symm

theorem permCongr_eq (c : Fin 6 ≃ OnePoint K5) (x : Perm (Fin 6)) :
    c.permCongr x = toLine (relLabel c * x * (relLabel c)⁻¹) := by
  ext p
  obtain ⟨i, rfl⟩ := c.surjective p
  simp [toLine, relLabel, Equiv.permCongrHom, Equiv.Perm.mul_apply, Equiv.permCongr_apply,
    Equiv.Perm.inv_def]

/-- The labellings that make `L` and `R` Möbius maps are one orbit of `PGL(2, 5)`. -/
theorem labelling_iff (c : Fin 6 ≃ OnePoint K5) :
    IsMobiusLabelling c ↔ ∃ g, ∀ i, c i = rho g (corner i) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [permCongr_eq, toLine_mem_range_iff, mem_iff_mask] at h1 h2
    have hm := (mem_iff_mask _).mpr (normalizer_check _ h1 h2)
    obtain ⟨g, hg⟩ := (toLine_mem_range_iff _).mpr hm
    refine ⟨g, fun i => ?_⟩
    rw [hg]
    simp [toLine, relLabel, Equiv.permCongrHom, Equiv.permCongr_apply]
  · rintro ⟨g, hg⟩
    have hc : c = corner.trans (rho g) := Equiv.ext hg
    subst hc
    have key : ∀ x : Perm (Fin 6), corner.permCongr x ∈ rho.range →
        (corner.trans (rho g)).permCongr x ∈ rho.range := by
      rintro x ⟨a, ha⟩
      refine ⟨g * a * g⁻¹, ?_⟩
      ext p
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      simp [Equiv.permCongr_apply, Equiv.Perm.inv_def, ha]
    exact ⟨key _ ⟨matL, permCongr_squareL.symm⟩, key _ ⟨matR, permCongr_squareR.symm⟩⟩

/-- The labelling is forced: `v₀, v₁, v₂` at `∞, 0, 1` leave only the book's. -/
theorem labelling_forced {c : Fin 6 ≃ OnePoint K5} (hc : IsMobiusLabelling c)
    (h0 : c 0 = corner 0) (h1 : c 1 = corner 1) (h2 : c 2 = corner 2) : c = corner := by
  obtain ⟨hL, hR⟩ := hc
  rw [permCongr_eq, toLine_mem_range_iff, mem_iff_mask] at hL hR
  have hm := normalizer_check _ hL hR
  have hrel : relLabel c = 1 := by
    apply sharply_check _ hm
    · simp [relLabel, h0]
    · simp [relLabel, h1]
    · simp [relLabel, h2]
  ext i
  have := congrArg (fun σ : Perm (Fin 6) => corner (σ i)) hrel
  simpa [relLabel] using this

/-- There are `120` such labellings. -/
theorem card_labellings : {c | IsMobiusLabelling c}.ncard = 120 := by
  have hset : {c | IsMobiusLabelling c} =
      (fun y : twoSquares => (y.1 : Fin 6 ≃ Fin 6).trans corner) '' Set.univ := by
    ext c
    constructor
    · intro hc
      obtain ⟨hL, hR⟩ := hc
      rw [permCongr_eq, toLine_mem_range_iff, mem_iff_mask] at hL hR
      have hm := (mem_iff_mask _).mpr (normalizer_check _ hL hR)
      refine ⟨⟨_, hm⟩, trivial, ?_⟩
      ext i
      simp [relLabel]
    · rintro ⟨y, -, rfl⟩
      rw [Set.mem_ofPred_eq, labelling_iff]
      obtain ⟨g, hg⟩ := (toLine_mem_range_iff y.1).mpr y.2
      refine ⟨g, fun i => ?_⟩
      rw [hg]
      simp [toLine, Equiv.permCongrHom, Equiv.permCongr_apply]
  rw [hset, Set.ncard_image_of_injective, Set.ncard_univ, card_squares]
  intro x y e
  apply Subtype.ext
  ext i
  have := congrArg (fun c : Fin 6 ≃ OnePoint K5 => c i) e
  simp only [Equiv.trans_apply] at this
  exact congrArg Fin.val (corner.injective this)

end Labelling

section Tick

/-- The tick is the one-mode kick of strength `2`, `x ↦ x / (2 x + 1)`. -/
theorem tick_is_kick : corner.permCongr (squareR * squareL) = rho matK2 := by
  have hmob : ∀ i : Fin 6, pointOf ((squareR * squareL) i) = mobOpt 1 0 2 1 (pointOf i) := by
    decide +kernel
  ext x
  obtain ⟨i, rfl⟩ := corner.surjective x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, rho, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rw [smul_eq_mobOpt, corner_apply, corner_apply]
  exact hmob i

/-- The ring of the tick: `v₀ → v₄ → v₅ → v₂ → v₃ → v₀`, and `v₁` keeps its letter. -/
theorem tick_ring : (squareR * squareL) 0 = 4 ∧ (squareR * squareL) 4 = 5 ∧
    (squareR * squareL) 5 = 2 ∧ (squareR * squareL) 2 = 3 ∧ (squareR * squareL) 3 = 0 ∧
    (squareR * squareL) 1 = 1 := by decide

theorem tick_order : orderOf (squareR * squareL) = 5 :=
  orderOf_eq_prime (by decide) (by decide)

/-- `L` and `R` do not have square determinants. -/
theorem turns_not_square : matL.det = (3 : K5) ∧ ¬ IsSquare (3 : K5) ∧ matR.det = (2 : K5) ∧
    ¬ IsSquare (2 : K5) := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · change Matrix.det !![(0 : K5), 1; 2, 1] = 3
    rw [Matrix.det_fin_two_of]
    decide
  · change Matrix.det !![(2 : K5), 3; 0, 1] = 2
    rw [Matrix.det_fin_two_of]
    decide

/-- Each turn carries the edges of the icosahedron (`det = ±1`) onto those of the great icosahedron
(`det = ±2`), and back. -/
theorem turns_swap_edges : ∀ u v : K5 × K5,
    ((detK5 u v = 1 ∨ detK5 u v = -1) → (detK5 (stateL u) (stateL v) = 2 ∨
      detK5 (stateL u) (stateL v) = -2) ∧ (detK5 (stateR u) (stateR v) = 2 ∨
      detK5 (stateR u) (stateR v) = -2)) ∧
    ((detK5 u v = 2 ∨ detK5 u v = -2) → (detK5 (stateL u) (stateL v) = 1 ∨
      detK5 (stateL u) (stateL v) = -1) ∧ (detK5 (stateR u) (stateR v) = 1 ∨
      detK5 (stateR u) (stateR v) = -1)) := by
  decide +kernel

theorem mobOpt_scale : ∀ t a b c d : K5, t ≠ 0 → ∀ x,
    mobOpt (t * a) (t * b) (t * c) (t * d) x = mobOpt a b c d x := by
  decide +kernel

/-- A law with square determinant is a rotation: it acts as an element of `SL(2, 5)`. -/
theorem rotation_of_square (g : Matrix.GeneralLinearGroup (Fin 2) K5)
    (h : IsSquare (g.1.det)) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) K5,
      rho g = rho (s : Matrix.GeneralLinearGroup (Fin 2) K5) := by
  obtain ⟨t, ht⟩ := h
  have hdet : g.1.det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) K5 →* K5)
    exact this.ne_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [ht] at hdet
  let s : Matrix.SpecialLinearGroup (Fin 2) K5 := ⟨t⁻¹ • g.1, by
    rw [Matrix.det_smul, ht]
    simp
    field_simp⟩
  refine ⟨s, ?_⟩
  ext x
  simp only [rho, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  rw [smul_eq_mobOpt, smul_eq_mobOpt]
  exact (mobOpt_scale t⁻¹ _ _ _ _ (inv_ne_zero ht0) x).symm

/-- Each product of two turns has a square determinant, so it is a rotation. -/
theorem double_turns_square : IsSquare (matL * matL).1.det ∧ IsSquare (matL * matR).1.det ∧
    IsSquare (matR * matL).1.det ∧ IsSquare (matR * matR).1.det := by
  have hL : matL.1.det = 3 := turns_not_square.1
  have hR : matR.1.det = 2 := turns_not_square.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Units.val_mul, Matrix.det_mul]
  · rw [hL]; decide
  · rw [hL, hR]; decide
  · rw [hR, hL]; decide
  · rw [hR]; decide

end Tick

end Artform.Scores.Bells

namespace Artform.Scores

open Bells

/-- **T13** (Theorem Y: the two squares are the projective line over `F₅`). -/
@[ledger "T13"]
theorem twoSquaresProjective : Statement.twoSquaresProjective := by
  refine ⟨fun i => ?_, fun i => ?_, map_eq_range, card_squares, iso_S5, labelling_iff,
    card_labellings, fun c hc h0 h1 h2 => labelling_forced hc h0 h1 h2, tick_is_kick, tick_ring,
    tick_order, turns_not_square, turns_swap_edges, rotation_of_square, double_turns_square⟩
  · have := congrArg (fun σ : Equiv.Perm (OnePoint K5) => σ (corner i)) permCongr_squareL
    simpa [rho, Equiv.permCongr_apply] using this
  · have := congrArg (fun σ : Equiv.Perm (OnePoint K5) => σ (corner i)) permCongr_squareR
    simpa [rho, Equiv.permCongr_apply] using this

/-! ## Non-vacuity

The book's run of the two squares: the tick moves the corner `v₀` to `v₄`, and after five ticks
every corner is home.
-/

example : ((squareR * squareL) ^ 5) 0 = 0 ∧ (squareR * squareL) 0 = 4 := by decide

end Artform.Scores
