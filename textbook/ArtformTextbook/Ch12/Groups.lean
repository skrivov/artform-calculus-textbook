import Mathlib.Analysis.Real.Pi.Irrational
import ArtformTextbook.Ch12.GroupsCube
import ArtformTextbook.Ch12.GroupsValentiner

/-!
# The colour groups of Chapter 12 and their characters

The proofs of Proposition 12.9 (`prop:mm-a5-tensor`), Proposition 12.13
(`prop:mm-s1080-orders`), Proposition 12.14 (`prop:mm-s1080-tensor`) and Theorem 12.16
(`thm:mm-loop`).

The groups are enumerated in `GroupsIco`, `GroupsCube` and `GroupsValentiner`, from the
certificate `scripts/certificates/colour_groups.py` that the kernel checks in
`ColourGroupsCheck`. The general facts about `SU(3)` are in `GroupsSU3`.
-/

namespace Artform

open ColourGroups Exact Matrix

/-! ### Proposition 12.9 -/

/-- **Proposition 12.9** (the tensor square of the icosahedral triplet). For the icosahedral
group `3 ⊗ 3 = 1 ⊕ 3 ⊕ 5`, `Λ²3 = 3`, `Sym²3 = 1 ⊕ 5` and `⟨χ⁴⟩ = 3`; for the cube group
`Sym²3_r = 1 ⊕ 2 ⊕ 3_s` and `⟨χ⁴⟩ = 4`. -/
@[book "prop:mm-a5-tensor"]
theorem a5Tensor : Statement.a5Tensor :=
  ⟨a5_sq, a5_alt, a5_sym, fun ρ hρ σ hσ => a5_pairing ρ σ hρ hσ, a5_avg_fourth,
    cube_sym_char, fun ρ hρ σ hσ => cube_pairing ρ σ hρ hσ, cube_avg_fourth⟩

/-! ### Proposition 12.13 -/

namespace ColourGroups

/-- Every trace of the table is a cube root of unity times a real number. -/
theorem table_traces (i : Fin 17) :
    ∃ (j : ℕ) (t : ℝ), (s1080ClassTable i).trace = Exact.omega ^ j * t := by
  fin_cases i
  · exact ⟨0, 3, by simp [s1080ClassTable]⟩
  · exact ⟨0, -1, by simp [s1080ClassTable]⟩
  · exact ⟨1, 3, by simp [s1080ClassTable]; ring⟩
  · exact ⟨2, 3, by simp [s1080ClassTable]; ring⟩
  · exact ⟨0, 0, by simp [s1080ClassTable]⟩
  · exact ⟨0, 0, by simp [s1080ClassTable]⟩
  · exact ⟨0, 1, by simp [s1080ClassTable]⟩
  · exact ⟨0, Real.goldenRatio, by simp [s1080ClassTable]⟩
  · exact ⟨0, 1 - Real.goldenRatio, by simp [s1080ClassTable]⟩
  · exact ⟨2, -1, by simp [s1080ClassTable]⟩
  · exact ⟨1, -1, by simp [s1080ClassTable]⟩
  · exact ⟨2, 1, by simp [s1080ClassTable]⟩
  · exact ⟨1, 1, by simp [s1080ClassTable]⟩
  · exact ⟨1, 1 - Real.goldenRatio, by simp [s1080ClassTable]; ring⟩
  · exact ⟨2, Real.goldenRatio, by simp [s1080ClassTable]; ring⟩
  · exact ⟨1, Real.goldenRatio, by simp [s1080ClassTable]; ring⟩
  · exact ⟨2, 1 - Real.goldenRatio, by simp [s1080ClassTable]; ring⟩

end ColourGroups

/-- **Proposition 12.13** (orders from traces). The eigenvalues of a matrix of `SU(3)` from its
trace; the class table of `S(1080)`, its traces, sizes and orders; the exponent `60`. -/
@[book "prop:mm-s1080-orders"]
theorem s1080Orders : Statement.s1080Orders :=
  ⟨fun _ hM t ht => SU3.roots_charpoly_of_real_trace hM t ht,
    fun _ hM j t ht => SU3.roots_charpoly_of_trace hM j t ht, table_traces, class_table,
    order_of_trace, order_count, exponent_valentiner⟩

/-! ### Proposition 12.14 -/

namespace ColourGroups

theorem colourChar_one_valentiner : colourChar valentiner 1 = 3 := by
  simp [colourChar, Matrix.trace_one]

theorem avg_normSq :
    groupAvg valentiner (fun g =>
      colourChar valentiner g * (starRingEnd ℂ) (colourChar valentiner g)) = 1 := by
  rw [avg_exact (fun z => z * (starRingEnd ℂ) z) (fun t => t * ZOP.conj t)
    (fun t => by rw [ZOP.toComplex_mul, ZOP.toComplex_conj]) 1080 classSum_1]
  norm_num

end ColourGroups

/-- **Proposition 12.14** (the tensor squares of the Valentiner triplet). `⟨χχ̄⟩ = 1`,
`⟨χ²χ̄²⟩ = 2`, so `3 ⊗ 3̄ = 1 ⊕ 8` and `3 ⊗ 3 = 3̄ ⊕ 6` with the eight and the six irreducible;
for `C₃ × A₅` the second average is `3` and the eight splits as `3 ⊕ 5`. -/
@[book "prop:mm-s1080-tensor"]
theorem s1080Tensor : Statement.s1080Tensor := by
  refine ⟨avg_normSq, ?_, ?_, ?_, ?_, fun g => ?_, SU3.altSqChar_colourChar valentiner, ?_, ?_,
    ?_, C3A5_fourth, C3A5_eight, fun ρ hρ σ hσ => C3A5_pairing ρ σ
      (by simp only [List.mem_cons, List.not_mem_nil] at hρ ⊢; tauto)
      (by simp only [List.mem_cons, List.not_mem_nil] at hσ ⊢; tauto)⟩
  · rw [avg_exact (fun z => z ^ 2 * (starRingEnd ℂ) z ^ 2)
      (fun t => (t * ZOP.conj t) * (t * ZOP.conj t))
      (fun t => by rw [ZOP.toComplex_mul, ZOP.toComplex_mul, ZOP.toComplex_conj]; ring)
      2160 classSum_2]
    norm_num
  · rw [classPairing]
    simp only [map_one, mul_one]
    exact avg_normSq
  · rw [colourChar_one_valentiner, Complex.conj_ofNat]
    norm_num
  · rw [classPairing]
    rw [avg_exact
      (fun z => (z * (starRingEnd ℂ) z - 1) * (starRingEnd ℂ) (z * (starRingEnd ℂ) z - 1))
      (fun t => (t * ZOP.conj t - 1) * ZOP.conj (t * ZOP.conj t - 1))
      (fun t => by
        rw [ZOP.toComplex_mul, ZOP.toComplex_conj, ZOP.toComplex_sub, ZOP.toComplex_mul,
          ZOP.toComplex_conj, ZOP.toComplex_one]) 1080 classSum_3]
    norm_num
  · rw [SU3.symSqChar_colourChar]
    ring
  · rw [classPairing]
    rw [avg_exact (fun z => (starRingEnd ℂ) z * (starRingEnd ℂ) ((starRingEnd ℂ) z))
      (fun t => ZOP.conj t * ZOP.conj (ZOP.conj t))
      (fun t => by simp only [ZOP.toComplex_mul, ZOP.toComplex_conj]) 1080 classSum_4]
    norm_num
  · rw [SU3.symSqChar_colourChar, colourChar_one_valentiner, Complex.conj_ofNat]
    norm_num
  · rw [classPairing]
    have e : (fun g => symSqChar (colourChar valentiner) g *
        (starRingEnd ℂ) (symSqChar (colourChar valentiner) g)) =
        fun g => (fun z => (z * z - (starRingEnd ℂ) z) *
          (starRingEnd ℂ) (z * z - (starRingEnd ℂ) z)) (colourChar valentiner g) := by
      funext g
      rw [SU3.symSqChar_colourChar, sq]
    rw [e, avg_exact
      (fun z => (z * z - (starRingEnd ℂ) z) * (starRingEnd ℂ) (z * z - (starRingEnd ℂ) z))
      (fun t => (t * t - ZOP.conj t) * ZOP.conj (t * t - ZOP.conj t))
      (fun t => by
        rw [ZOP.toComplex_mul, ZOP.toComplex_conj, ZOP.toComplex_sub, ZOP.toComplex_mul,
          ZOP.toComplex_conj]) 1080 classSum_5]
    norm_num

/-! ### Theorem 12.16 -/

namespace ColourGroups

/-- The holonomy of the `n`-fold loop is the `n`-th power of the holonomy. -/
theorem hol_loopPow {X : Skeleton} {G : Type*} [Group G] (U : X.LinkTable G) {v : X.V}
    (γ : X.Path v v) (n : ℕ) : Skeleton.hol U (γ.loopPow n) = Skeleton.hol U γ ^ n := by
  induction n with
  | zero => simp [Skeleton.Path.loopPow]
  | succ n ih => rw [Skeleton.Path.loopPow, Skeleton.hol_comp, ih, pow_succ']

/-- The canvas of one square: four vertices, four edges `i → i + 1` and one face. -/
abbrev squareCanvas : Canvas where
  V := Fin 4
  E := Fin 4
  F := Unit
  src i := i
  tgt i := i + 1
  boundary _ := [(0, true), (1, true), (2, true), (3, true)]
  closed _ := by
    refine ⟨by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.take, List.isChain_cons_cons, stepStart,
      stepEnd, List.IsChain.singleton, and_true]
    decide

/-- The transport skeleton of the square. -/
abbrev squareSkel : Skeleton := Skeleton.ofGraph squareCanvas.src squareCanvas.tgt

/-- The loop round the square, `e₃ e₂ e₁ e₀` from the vertex `0`. -/
def squareLoop : squareSkel.Path (0 : Fin 4) (0 : Fin 4) :=
  let p1 : squareSkel.Path (0 : Fin 4) (1 : Fin 4) :=
    @Skeleton.Path.cons squareSkel (0 : Fin 4) ((0 : Fin 4), true)
      (@Skeleton.Path.nil squareSkel (0 : Fin 4))
  let p2 : squareSkel.Path (0 : Fin 4) (2 : Fin 4) :=
    @Skeleton.Path.cons squareSkel (0 : Fin 4) ((1 : Fin 4), true) p1
  let p3 : squareSkel.Path (0 : Fin 4) (3 : Fin 4) :=
    @Skeleton.Path.cons squareSkel (0 : Fin 4) ((2 : Fin 4), true) p2
  @Skeleton.Path.cons squareSkel (0 : Fin 4) ((3 : Fin 4), true) p3

/-- The link table with the value `g` on the edge `e₀` and `1` on the others. -/
def squareTable {G : Type*} [Group G] (g : G) : squareSkel.LinkTable G :=
  Skeleton.LinkTable.ofGraph fun e : Fin 4 => if e = 0 then g else 1

theorem hol_squareLoop {G : Type*} [Group G] (g : G) :
    Skeleton.hol (squareTable g) squareLoop = g := by
  simp [squareLoop, squareTable, Skeleton.hol, Skeleton.LinkTable.ofGraph]

/-- The element `diag(e^{i}, e^{-i}, 1)` of `SU(3)`, of infinite order. -/
noncomputable def spinElt : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal ![Complex.exp Complex.I, Complex.exp (-Complex.I), 1], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal, det_diagonal, Fin.prod_univ_three]
    refine ⟨?_, ?_⟩
    · rw [← diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp [← Complex.exp_conj, ← Complex.exp_add]
    · simp [← Complex.exp_add]⟩

theorem spinElt_pow_ne_one (e : ℕ) (he : 0 < e) : spinElt ^ e ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp only [spinElt, SubmonoidClass.coe_pow, diagonal_pow, diagonal_apply_eq,
    OneMemClass.coe_one, one_apply_eq, Pi.pow_apply, Matrix.cons_val_zero] at h00
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h00
  obtain ⟨n, hn⟩ := h00
  have hre : (e : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : (e : ℝ) = 0 := by simpa using hre
    exact absurd (by exact_mod_cast this : e = 0) (by omega)
  apply irrational_pi
  refine ⟨e / (2 * n), ?_⟩
  have h2n : (2 * (n : ℝ)) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    positivity
  push_cast
  field_simp
  linarith

/-- `diag(e^{i}, e^{-i}, 1)` has infinite order. -/
theorem orderOf_spinElt : orderOf spinElt = 0 :=
  orderOf_eq_zero_iff'.mpr spinElt_pow_ne_one

/-- The triplet of a colour group `G ≤ SU(3)`: each element acts on `ℂ³` by its matrix. -/
noncomputable def tripletRep (G : Subgroup (specialUnitaryGroup (Fin 3) ℂ)) :
    Representation ℂ G (Fin 3 → ℂ) where
  toFun g := Matrix.toLin' ((g : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

end ColourGroups

/-- **Theorem 12.16** (every loop closes). For a finite colour group of exponent `e`,
`Hol_U(γ)^e = 1` for every connection on every canvas and every loop; the exponents of the four
models are `12`, `30`, `30` and `60`; no `e` does this for `SU(3)`. -/
@[book "thm:mm-loop"]
theorem mmLoop : Statement.mmLoop := by
  refine ⟨fun G _ _ ρ K U v γ => ?_, exponent_cubeGroup, exponent_icoGroup, exponent_C3A5,
    exponent_valentiner, fun e he => ⟨squareCanvas, squareTable spinElt, (0 : Fin 4), squareLoop,
      ?_⟩⟩
  · have h1 : Skeleton.hol U γ ^ Monoid.exponent G = 1 := Monoid.pow_exponent_eq_one _
    have h2 : Skeleton.hol U (γ.loopPow (Monoid.exponent G)) = 1 := by rw [hol_loopPow, h1]
    refine ⟨h1, fun c => ?_, ?_⟩
    · rw [h2, map_one, Module.End.one_apply]
    · rw [h2, Representation.char_one, Module.finrank_fin_fun]
      norm_num
  · rw [hol_squareLoop]
    exact spinElt_pow_ne_one e he

/-! ### The claims made in Definition 12.11 -/

namespace ColourGroups

/-- Definition 12.11: `C₃ × A₅` has `180` elements. -/
theorem C3A5_card : Nat.card C3A5 = 180 := card_C3A5

/-- Definition 12.11: the image of the triplet contains `I`, `ω I` and `ω² I`, the centre of
`SU(3)` (Proposition 10.2). -/
theorem C3A5_centre (j : ℕ) :
    ∃ x : C3A5, ((C3A5.triplet x : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      Exact.omega ^ j • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  refine ⟨(Multiplicative.ofAdd (j : ZMod 3), 1), ?_⟩
  simp [C3A5.triplet, ZMod.val_natCast, Exact.omega_pow_mod]

/-- Definition 12.11: the character of `C₃ × A₅` is `χ(ω^j, g) = ω^j χ₃(g)`, with values in
`ℤ[ω, φ]`. -/
theorem C3A5_char_values (x : C3A5) :
    C3A5.char x = Exact.omega ^ (Multiplicative.toAdd x.1).val * colourChar icoGroup x.2 ∧
      ∃ z : ZOP, C3A5.char x = ZOP.toComplex z := by
  refine ⟨char_C3A5 x, ?_⟩
  obtain ⟨k, hk⟩ := icoElt_surjective x.2
  refine ⟨ZOP.omegaPow ⟨(Multiplicative.toAdd x.1).val, ZMod.val_lt _⟩ *
    a5TabZ .three (a5ClassZ (trA5 k)), ?_⟩
  rw [char_C3A5, a5_three, ← hk, a5Char_icoElt, ZOP.toComplex_mul, ZOP.toComplex_omegaPow]

end ColourGroups

/-! ## Non-vacuity -/

/-- The hypotheses of Proposition 12.13 are met by matrices of the book's groups: the identity,
with real trace `3`, and `ω I`, the generator of the centre, with trace `ω · 3`. -/
example : (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ ∧
    (1 : Matrix (Fin 3) (Fin 3) ℂ).trace = ((3 : ℝ) : ℂ) ∧
    Exact.omega ^ 1 • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ ∧
    (Exact.omega ^ 1 • (1 : Matrix (Fin 3) (Fin 3) ℂ)).trace = Exact.omega ^ 1 * ((3 : ℝ) : ℂ) :=
  ⟨Submonoid.one_mem _, by simp [Matrix.trace_one], omega_pow_smul_mem 1 (Submonoid.one_mem _),
    by simp [Matrix.trace_smul, Matrix.trace_one]⟩

/-- Proposition 12.14 is about the intended group: Valentiner's group contains `F` and has
`1080` elements, and the character of its symmetric square at the identity is `6`. -/
example : valentinerF ∈ valentiner ∧ Nat.card valentiner = 1080 ∧
    symSqChar (colourChar valentiner) 1 = 6 :=
  ⟨Subgroup.subset_closure (Or.inr rfl), card_valentiner, s1080Tensor.2.2.2.2.2.2.2.2.1⟩

/-- Proposition 12.9 read at the identity of the icosahedral group: `9 = 1 + 3 + 5`. -/
example : colourChar icoGroup 1 ^ 2 = a5Char .one 1 + a5Char .three 1 + a5Char .five 1 :=
  a5Tensor.1 1

/-- Theorem 12.16 on the book's running example: the cube group, Model I, with its triplet, on
the canvas of one square with a quarter-turn on one edge; the hypotheses are met, and the
holonomy of the loop round the square, to the twelfth power, is `1`. -/
example : Skeleton.hol (squareTable (cubeElt 4)) squareLoop ^ 12 = 1 := by
  have h := (mmLoop.1 cubeGroup (tripletRep cubeGroup) squareCanvas (squareTable (cubeElt 4))
    (0 : Fin 4) squareLoop).1
  rwa [exponent_cubeGroup] at h

end Artform
