import ArtformScores.LeapfrogUnits

/-!
# The classes of the leapfrog phase

The ledger's T8, finding 057, Theorem S3.4. A law `L` of the leapfrog phase has a primitive left
eigenvector `u` on the normalization, unique up to a unit, with `u L = λ u`. The stencil lattice
`S u₀ + S u₁` contains `δ` times the normalization, so it is the preimage of its image `V` in the
fibre `E` over the node, and it determines the law up to processing. `V` is the whole of `E`
(unglued) or a line `F z` with `z` a unit (glued), and the units of the normalization act on the
lines through `⟨-1, ρ⟩`.
-/

namespace Artform.Scores.Leapfrog

open Polynomial
open LaurentPolynomial (T T_add T_zero)
open Matrix (SpecialLinearGroup)
open scoped QuadraticAlgebra

variable {F : Type*} [Field F] {q : F} (hq0 : q ≠ 0) (hq1 : q ≠ 1)

/-- Two `2 × 2` matrices with equal entries are equal. -/
theorem mat2_ext {R : Type*} {a b c d a' b' c' d' : R} (h0 : a = a') (h1 : b = b') (h2 : c = c')
    (h3 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  subst_vars
  rfl

/-! ### Eigenvectors on the normalization -/

/-- `u` is a left eigenvector of `M` on the normalization: `u M = λ u`. -/
def IsEigen (M : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) (u : Fin 2 → Norm q) : Prop :=
  Matrix.vecMul u (M.map (psi hq0)) = lamN hq0 • u

/-- `u` is primitive: its entries generate the normalization. -/
def Prim (u : Fin 2 → Norm q) : Prop := IsCoprime (u 0) (u 1)

variable {M M' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)} {u u' : Fin 2 → Norm q}

theorem isEigen_iff : IsEigen hq0 M u ↔
    u 0 * psi hq0 (M 0 0) + u 1 * psi hq0 (M 1 0) = lamN hq0 * u 0 ∧
    u 0 * psi hq0 (M 0 1) + u 1 * psi hq0 (M 1 1) = lamN hq0 * u 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    funext j
    fin_cases j
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h1

include hq1 in
theorem lam_sub_ne (a : LaurentPolynomial F) : lamN hq0 - psi hq0 a ≠ 0 := by
  intro h
  have h1 : psi hq0 (1 - a) + psi hq0 (T 1 - 1) * sN q = 0 := by
    simp only [map_sub, map_one, psi_T_one]
    simp only [lamN, deltaN] at h
    linear_combination h
  exact T_one_ne_one (sub_eq_zero.mp (form_eq_zero hq0 hq1 h1).2)

/-- The entries of a law of the leapfrog phase. -/
theorem law_rels (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) (ht : phase L = phaseT q) :
    psi hq0 (L.1 0 0) * psi hq0 (L.1 1 1) - psi hq0 (L.1 0 1) * psi hq0 (L.1 1 0) = 1 ∧
    psi hq0 (L.1 0 0) + psi hq0 (L.1 1 1) = psi hq0 (phaseT q) := by
  have hd := L.2
  rw [Matrix.det_fin_two] at hd
  have htr : L.1 0 0 + L.1 1 1 = phaseT q := by
    rw [← ht, phase, Matrix.trace_fin_two]
  have h1 := congrArg (psi hq0) hd
  have h2 := congrArg (psi hq0) htr
  simp only [map_sub, map_mul, map_one, map_add] at h1 h2
  exact ⟨h1, h2⟩

include hq1 in
/-- Every law of the phase has a primitive eigenvector. -/
theorem exists_eigen (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F))
    (ht : phase L = phaseT q) : ∃ u : Fin 2 → Norm q, IsEigen hq0 L.1 u ∧ Prim u := by
  obtain ⟨hd, htr⟩ := law_rels hq0 L ht
  have hroot := lam_root hq0
  rw [← htr] at hroot
  have hne := lam_sub_ne hq0 hq1 (L.1 0 0)
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span {psi hq0 (L.1 1 0), lamN hq0 - psi hq0 (L.1 0 0)})).principal
  have hg' : Ideal.span {psi hq0 (L.1 1 0), lamN hq0 - psi hq0 (L.1 0 0)} = Ideal.span {g} := hg
  have hc' : psi hq0 (L.1 1 0) ∈ Ideal.span {g} := hg' ▸ Ideal.subset_span (by simp)
  have hl' : lamN hq0 - psi hq0 (L.1 0 0) ∈ Ideal.span {g} := hg' ▸ Ideal.subset_span (by simp)
  have hgm : g ∈ Ideal.span {psi hq0 (L.1 1 0), lamN hq0 - psi hq0 (L.1 0 0)} :=
    hg'.symm ▸ Ideal.mem_span_singleton_self g
  obtain ⟨u0, hu0⟩ := Ideal.mem_span_singleton'.mp hc'
  obtain ⟨u1, hu1⟩ := Ideal.mem_span_singleton'.mp hl'
  obtain ⟨x0, x1, hx⟩ := Ideal.mem_span_pair.mp hgm
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hu1
    exact hne hu1.symm
  refine ⟨![u0, u1], ?_, ⟨x0, x1, ?_⟩⟩
  · rw [isEigen_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · apply mul_left_cancel₀ hg0
      linear_combination (psi hq0 (L.1 0 0) - lamN hq0) * hu0 + psi hq0 (L.1 1 0) * hu1
    · apply mul_left_cancel₀ hg0
      linear_combination psi hq0 (L.1 0 1) * hu0 + (psi hq0 (L.1 1 1) - lamN hq0) * hu1 - hd - hroot
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply mul_left_cancel₀ hg0
    linear_combination x0 * hu0 + x1 * hu1 + hx

include hq1 in
/-- Two primitive eigenvectors of one law differ by a unit of the normalization. -/
theorem eigen_unique (he : IsEigen hq0 M u) (hp : Prim u) (he' : IsEigen hq0 M u') (hp' : Prim u') :
    ∃ v : (Norm q)ˣ, ∀ i, u' i = v * u i := by
  obtain ⟨h0, -⟩ := (isEigen_iff hq0).mp he
  obtain ⟨h0', -⟩ := (isEigen_iff hq0).mp he'
  have hne := lam_sub_ne hq0 hq1 (M 0 0)
  have hD : u 0 * u' 1 = u' 0 * u 1 := by
    have : (lamN hq0 - psi hq0 (M 0 0)) * (u 0 * u' 1 - u' 0 * u 1) = 0 := by
      linear_combination (-(u' 1)) * h0 + u 1 * h0'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  obtain ⟨a0, a1, ha⟩ := hp
  obtain ⟨b0, b1, hb⟩ := hp'
  have hv0 : (a0 * u' 0 + a1 * u' 1) * u 0 = u' 0 := by
    linear_combination u' 0 * ha + a1 * hD
  have hv1 : (a0 * u' 0 + a1 * u' 1) * u 1 = u' 1 := by
    linear_combination u' 1 * ha - a0 * hD
  have hw0 : (b0 * u 0 + b1 * u 1) * u' 0 = u 0 := by
    linear_combination u 0 * hb - b1 * hD
  have hw1 : (b0 * u 0 + b1 * u 1) * u' 1 = u 1 := by
    linear_combination u 1 * hb + b0 * hD
  have hvw : (a0 * u' 0 + a1 * u' 1) * (b0 * u 0 + b1 * u 1) = 1 := by
    linear_combination (1 - (a0 * u' 0 + a1 * u' 1) * (b0 * u 0 + b1 * u 1)) * ha +
      a0 * (b0 * u 0 + b1 * u 1) * hv0 + a1 * (b0 * u 0 + b1 * u 1) * hv1 + a0 * hw0 + a1 * hw1
  refine ⟨⟨_, _, hvw, by rw [mul_comm]; exact hvw⟩, fun i => ?_⟩
  fin_cases i
  · exact hv0.symm
  · exact hv1.symm

theorem IsEigen.unit_mul (he : IsEigen hq0 M u) (v : (Norm q)ˣ) :
    IsEigen hq0 M (fun i => (v : Norm q) * u i) := by
  obtain ⟨h0, h1⟩ := (isEigen_iff hq0).mp he
  refine (isEigen_iff hq0).mpr ⟨?_, ?_⟩
  · linear_combination (v : Norm q) * h0
  · linear_combination (v : Norm q) * h1

theorem Prim.unit_mul (hp : Prim u) (v : (Norm q)ˣ) : Prim (fun i => (v : Norm q) * u i) := by
  obtain ⟨a0, a1, ha⟩ := hp
  refine ⟨((v⁻¹ : (Norm q)ˣ) : Norm q) * a0, ((v⁻¹ : (Norm q)ˣ) : Norm q) * a1, ?_⟩
  have hv := Units.inv_mul v
  simp only at *
  linear_combination ((v⁻¹ : (Norm q)ˣ) : Norm q) * (v : Norm q) * ha + hv

/-! ### The stencil lattice of an eigenvector -/

/-- `y` lies in the stencil lattice `S u₀ + S u₁`. -/
def Lat (u : Fin 2 → Norm q) (y : Norm q) : Prop :=
  ∃ f₀ f₁ : LaurentPolynomial F, y = psi hq0 f₀ * u 0 + psi hq0 f₁ * u 1

theorem Lat.add {y y' : Norm q} (h : Lat hq0 u y) (h' : Lat hq0 u y') : Lat hq0 u (y + y') := by
  obtain ⟨f₀, f₁, rfl⟩ := h
  obtain ⟨g₀, g₁, rfl⟩ := h'
  exact ⟨f₀ + g₀, f₁ + g₁, by simp only [map_add]; ring⟩

theorem psi_delta : psi hq0 (T 1 - 1) = deltaN hq0 := by
  rw [map_sub, psi_T_one, map_one, deltaN]

theorem psi_delta' : psi hq0 deltaS = deltaN hq0 := psi_delta hq0

/-- The lattice is closed under `δ` times the normalization, the first generator. -/
theorem lat_delta_form0 (he : IsEigen hq0 M u) (f g : LaurentPolynomial F) :
    Lat hq0 u (deltaN hq0 * (psi hq0 f + psi hq0 g * sN q) * u 0) := by
  obtain ⟨h0, -⟩ := (isEigen_iff hq0).mp he
  refine ⟨f * (T 1 - 1) + g * (M 0 0 - 1), g * M 1 0, ?_⟩
  simp only [map_add, map_mul, psi_delta]
  simp only [map_sub, map_one]
  simp only [lamN] at h0
  linear_combination (-psi hq0 g) * h0

/-- The lattice is closed under `δ` times the normalization, the second generator. -/
theorem lat_delta_form1 (he : IsEigen hq0 M u) (f g : LaurentPolynomial F) :
    Lat hq0 u (deltaN hq0 * (psi hq0 f + psi hq0 g * sN q) * u 1) := by
  obtain ⟨-, h1⟩ := (isEigen_iff hq0).mp he
  refine ⟨g * M 0 1, f * (T 1 - 1) + g * (M 1 1 - 1), ?_⟩
  simp only [map_add, map_mul, psi_delta]
  simp only [map_sub, map_one]
  simp only [lamN] at h1
  linear_combination (-psi hq0 g) * h1

include hq1 in
/-- The lattice contains `δ` times the normalization. -/
theorem lat_delta (he : IsEigen hq0 M u) (hp : Prim u) (y : Norm q) :
    Lat hq0 u (deltaN hq0 * y) := by
  obtain ⟨a0, a1, ha⟩ := hp
  obtain ⟨f, g, hfg⟩ := exists_form hq0 hq1 (y * a0)
  obtain ⟨f', g', hfg'⟩ := exists_form hq0 hq1 (y * a1)
  have h := (lat_delta_form0 hq0 he f g).add hq0 (lat_delta_form1 hq0 he f' g')
  rw [← hfg, ← hfg'] at h
  have e : deltaN hq0 * (y * a0) * u 0 + deltaN hq0 * (y * a1) * u 1 = deltaN hq0 * y := by
    linear_combination (deltaN hq0 * y) * ha
  rwa [e] at h

include hq1 in
/-- An element whose value on the fibre lies in the image of the lattice lies in the lattice. -/
theorem lat_of_eps (he : IsEigen hq0 M u) (hp : Prim u) {y : Norm q} (a b : F)
    (h : eps hq0 hq1 y = a • eps hq0 hq1 (u 0) + b • eps hq0 hq1 (u 1)) : Lat hq0 u y := by
  have h0 : eps hq0 hq1 (y - (psi hq0 (LaurentPolynomial.C a) * u 0 +
      psi hq0 (LaurentPolynomial.C b) * u 1)) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, eps_psi, eps_psi, atZero_C, atZero_C, h,
      Algebra.smul_def, Algebra.smul_def, sub_self]
  obtain ⟨y', hy'⟩ := exists_delta_mul hq0 hq1 h0
  have hl := (lat_delta hq0 hq1 he hp y').add hq0
    (show Lat hq0 u (psi hq0 (LaurentPolynomial.C a) * u 0 + psi hq0 (LaurentPolynomial.C b) * u 1)
      from ⟨_, _, rfl⟩)
  rw [← hy', sub_add_cancel] at hl
  exact hl

include hq1 in
/-- The entries of a primitive eigenvector are independent over the stencils. -/
theorem lat_indep (he : IsEigen hq0 M u) (hp : Prim u) {α β : LaurentPolynomial F}
    (h : psi hq0 α * u 0 + psi hq0 β * u 1 = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨f0, f1, hf⟩ := lat_delta hq0 hq1 he hp 1
  obtain ⟨g0, g1, hg⟩ := lat_delta hq0 hq1 he hp (sN q)
  rw [mul_one] at hf
  have ha1 : psi hq0 α * deltaN hq0 = psi hq0 (α * f1 - β * f0) * u 1 := by
    simp only [map_sub, map_mul]
    linear_combination psi hq0 α * hf + psi hq0 f0 * h
  have ha2 : psi hq0 α * (deltaN hq0 * sN q) = psi hq0 (α * g1 - β * g0) * u 1 := by
    simp only [map_sub, map_mul]
    linear_combination psi hq0 α * hg + psi hq0 g0 * h
  have hb1 : psi hq0 β * deltaN hq0 = -(psi hq0 (α * f1 - β * f0) * u 0) := by
    simp only [map_sub, map_mul]
    linear_combination psi hq0 β * hf + psi hq0 f1 * h
  have hb2 : psi hq0 β * (deltaN hq0 * sN q) = -(psi hq0 (α * g1 - β * g0) * u 0) := by
    simp only [map_sub, map_mul]
    linear_combination psi hq0 β * hg + psi hq0 g1 * h
  have hd := deltaN_ne_zero hq0
  have hc1 : psi hq0 α * deltaN hq0 *
      (psi hq0 (α * g1 - β * g0) + psi hq0 (-(α * f1 - β * f0)) * sN q) = 0 := by
    simp only [map_neg]
    linear_combination psi hq0 (α * g1 - β * g0) * ha1 - psi hq0 (α * f1 - β * f0) * ha2
  have hc2 : psi hq0 β * deltaN hq0 *
      (psi hq0 (α * g1 - β * g0) + psi hq0 (-(α * f1 - β * f0)) * sN q) = 0 := by
    simp only [map_neg]
    linear_combination psi hq0 (α * g1 - β * g0) * hb1 - psi hq0 (α * f1 - β * f0) * hb2
  have inj := (injective_iff_map_eq_zero _).mp (psi_injective hq0)
  by_cases hz : psi hq0 (α * g1 - β * g0) + psi hq0 (-(α * f1 - β * f0)) * sN q = 0
  · have hA := (form_eq_zero hq0 hq1 hz).2
    have hA' : psi hq0 (α * f1 - β * f0) = 0 := by
      rw [neg_eq_zero] at hA
      rw [hA, map_zero]
    rw [hA', zero_mul] at ha1
    rw [hA', zero_mul, neg_zero] at hb1
    exact ⟨inj _ ((mul_eq_zero.mp ha1).resolve_right hd),
      inj _ ((mul_eq_zero.mp hb1).resolve_right hd)⟩
  · exact ⟨inj _ ((mul_eq_zero.mp ((mul_eq_zero.mp hc1).resolve_right hz)).resolve_right hd),
      inj _ ((mul_eq_zero.mp ((mul_eq_zero.mp hc2).resolve_right hz)).resolve_right hd)⟩

include hq1 in
/-- A matrix over the stencils is determined by its action on a primitive eigenvector. -/
theorem matrix_inj (he : IsEigen hq0 M u) (hp : Prim u)
    {N N' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)}
    (h : Matrix.vecMul u (N.map (psi hq0)) = Matrix.vecMul u (N'.map (psi hq0))) : N = N' := by
  have key : ∀ j, N 0 j = N' 0 j ∧ N 1 j = N' 1 j := by
    intro j
    have hj := congrFun h j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at hj
    have h0 : psi hq0 (N 0 j - N' 0 j) * u 0 + psi hq0 (N 1 j - N' 1 j) * u 1 = 0 := by
      simp only [map_sub]
      linear_combination hj
    obtain ⟨h1, h2⟩ := lat_indep hq0 hq1 he hp h0
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  refine Matrix.ext fun i j => ?_
  fin_cases i
  · exact (key j).1
  · exact (key j).2

include hq1 in
/-- Two laws with eigenvectors spanning one lattice are related by processing. -/
theorem conj_of_lat (L L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial F))
    (he : IsEigen hq0 L.1 u) (hp : Prim u) (he' : IsEigen hq0 L'.1 u')
    (h₁ : Lat hq0 u (u' 0)) (h₂ : Lat hq0 u (u' 1)) (h₃ : Lat hq0 u' (u 0))
    (h₄ : Lat hq0 u' (u 1)) :
    ∃ P : GL (Fin 2) (LaurentPolynomial F), (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * L *
        ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
          Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) := by
  obtain ⟨p00, p10, e0⟩ := h₁
  obtain ⟨p01, p11, e1⟩ := h₂
  obtain ⟨r00, r10, e2⟩ := h₃
  obtain ⟨r01, r11, e3⟩ := h₄
  let P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F) := !![p00, p01; p10, p11]
  let Q : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F) := !![r00, r01; r10, r11]
  have hu' : u' = Matrix.vecMul u (P.map (psi hq0)) := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
    fin_cases j
    · change u' 0 = u 0 * psi hq0 p00 + u 1 * psi hq0 p10
      rw [e0]; ring
    · change u' 1 = u 0 * psi hq0 p01 + u 1 * psi hq0 p11
      rw [e1]; ring
  have hu : u = Matrix.vecMul u' (Q.map (psi hq0)) := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
    fin_cases j
    · change u 0 = u' 0 * psi hq0 r00 + u' 1 * psi hq0 r10
      linear_combination e2
    · change u 1 = u' 0 * psi hq0 r01 + u' 1 * psi hq0 r11
      linear_combination e3
  have hPQ : P * Q = 1 := by
    apply matrix_inj hq0 hq1 he hp
    rw [Matrix.map_mul, ← Matrix.vecMul_vecMul, ← hu', ← hu]
    have h1 : (1 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map (psi hq0) = 1 :=
      map_one (psi hq0).mapMatrix
    rw [h1, Matrix.vecMul_one]
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  have hint : P * L'.1 = L.1 * P := by
    apply matrix_inj hq0 hq1 he hp
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hu',
      he, he', Matrix.smul_vecMul, ← hu']
  refine ⟨⟨Q, P, hQP, hPQ⟩, ?_⟩
  change L'.1 = Q * L.1 * P
  calc L'.1 = (Q * P) * L'.1 := by rw [hQP, Matrix.one_mul]
    _ = Q * (P * L'.1) := Matrix.mul_assoc _ _ _
    _ = Q * L.1 * P := by rw [hint, Matrix.mul_assoc]

/-! ### The image of the lattice on the fibre -/

/-- The image of the lattice is the whole fibre: the unglued class. -/
def Spans (u : Fin 2 → Norm q) : Prop :=
  ∀ z : Fib q, ∃ a b : F, z = a • eps hq0 hq1 (u 0) + b • eps hq0 hq1 (u 1)

/-- The image of the lattice lies on the line through the unit `z`: a glued class. -/
def GluedBy (u : Fin 2 → Norm q) (z : (Fib q)ˣ) : Prop :=
  ∃ a b : F, eps hq0 hq1 (u 0) = a • (z : Fib q) ∧ eps hq0 hq1 (u 1) = b • (z : Fib q)

/-- Two elements of the fibre generating it span it over `F`, or lie on a line through a unit. -/
theorem fibre_dichotomy (w0 w1 a b : Fib q) (hab : a * w0 + b * w1 = 1) :
    (∀ z : Fib q, ∃ α β : F, z = α • w0 + β • w1) ∨
      ∃ z : (Fib q)ˣ, ∃ α β : F, w0 = α • (z : Fib q) ∧ w1 = β • (z : Fib q) := by
  by_cases hD : w0.re * w1.im - w0.im * w1.re = 0
  · right
    by_cases h0 : w0 = 0
    · rw [h0, mul_zero, zero_add] at hab
      have hu : IsUnit w1 := IsUnit.of_mul_eq_one b (by rw [mul_comm]; exact hab)
      exact ⟨hu.unit, 0, 1, by simp [h0], by simp⟩
    · -- `w1` is a multiple of `w0`
      have hf : ∃ f : F, w1 = f • w0 := by
        by_cases hr : w0.re = 0
        · have hi : w0.im ≠ 0 := by
            intro hi
            exact h0 (by ext <;> simp [hr, hi])
          refine ⟨w1.im / w0.im, ?_⟩
          have h1 : w1.re = 0 := by
            have : w0.im * w1.re = 0 := by rw [hr] at hD; linear_combination -hD
            exact (mul_eq_zero.mp this).resolve_left hi
          ext
          · simp [hr, h1]
          · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
            field_simp
        · refine ⟨w1.re / w0.re, ?_⟩
          ext
          · simp only [QuadraticAlgebra.re_smul, smul_eq_mul]
            field_simp
          · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
            field_simp
            linear_combination hD
      obtain ⟨f, hf⟩ := hf
      have hu : IsUnit w0 := by
        refine IsUnit.of_mul_eq_one (a + b * algebraMap F (Fib q) f) ?_
        rw [hf, Algebra.smul_def] at hab
        linear_combination hab
      exact ⟨hu.unit, 1, f, by simp, by simpa using hf⟩
  · left
    intro z
    refine ⟨(z.re * w1.im - z.im * w1.re) / (w0.re * w1.im - w0.im * w1.re),
      (w0.re * z.im - w0.im * z.re) / (w0.re * w1.im - w0.im * w1.re), ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
      ring

/-- The image of a primitive eigenvector is the whole fibre or a line through a unit. -/
theorem spans_or_glued (hp : Prim u) : Spans hq0 hq1 u ∨ ∃ z, GluedBy hq0 hq1 u z := by
  obtain ⟨a, b, hab⟩ := hp.map (eps hq0 hq1)
  rcases fibre_dichotomy _ _ a b hab with h | ⟨z, α, β, h0, h1⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, α, β, h0, h1⟩

/-- Over a spanning pair the coefficients are unique. -/
theorem Spans.indep (hs : Spans hq0 hq1 u) {α β : F}
    (h : α • eps hq0 hq1 (u 0) + β • eps hq0 hq1 (u 1) = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨b0, b1, h1⟩ := hs 1
  obtain ⟨c0, c1, h2⟩ := hs rE
  set w0 := eps hq0 hq1 (u 0)
  set w1 := eps hq0 hq1 (u 1)
  have e1 : b0 * w0.re + b1 * w1.re = 1 := by simpa using (congrArg QuadraticAlgebra.re h1).symm
  have e2 : b0 * w0.im + b1 * w1.im = 0 := by simpa using (congrArg QuadraticAlgebra.im h1).symm
  have e3 : c0 * w0.re + c1 * w1.re = 0 := by
    simpa [rE] using (congrArg QuadraticAlgebra.re h2).symm
  have e4 : c0 * w0.im + c1 * w1.im = 1 := by
    simpa [rE] using (congrArg QuadraticAlgebra.im h2).symm
  have e5 : α * w0.re + β * w1.re = 0 := by simpa using congrArg QuadraticAlgebra.re h
  have e6 : α * w0.im + β * w1.im = 0 := by simpa using congrArg QuadraticAlgebra.im h
  have hdet : (b0 * c1 - b1 * c0) * (w0.re * w1.im - w0.im * w1.re) = 1 := by
    linear_combination (c0 * w0.im + c1 * w1.im) * e1 + e4 - (c0 * w0.re + c1 * w1.re) * e2
  have ha : α * (w0.re * w1.im - w0.im * w1.re) = 0 := by
    linear_combination w1.im * e5 - w1.re * e6
  have hb : β * (w0.re * w1.im - w0.im * w1.re) = 0 := by
    linear_combination w0.re * e6 - w0.im * e5
  have hD : w0.re * w1.im - w0.im * w1.re ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  exact ⟨(mul_eq_zero.mp ha).resolve_right hD, (mul_eq_zero.mp hb).resolve_right hD⟩

/-- The image of a lattice is not both the whole fibre and a line. -/
theorem Spans.not_glued (hs : Spans hq0 hq1 u) (z : (Fib q)ˣ) : ¬ GluedBy hq0 hq1 u z := by
  rintro ⟨a0, a1, h0, h1⟩
  obtain ⟨b0, b1, h2⟩ := hs 1
  obtain ⟨c0, c1, h3⟩ := hs rE
  rw [h0, h1] at h2 h3
  have e1 := congrArg QuadraticAlgebra.re h2
  have e2 := congrArg QuadraticAlgebra.im h2
  have e3 := congrArg QuadraticAlgebra.re h3
  have e4 := congrArg QuadraticAlgebra.im h3
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, rE] at e1 e2 e3 e4
  have : (1 : F) = 0 := by
    linear_combination ((c0 * a0 + c1 * a1) * (z : Fib q).im) * e1 -
      (c0 * a0 + c1 * a1) * (z : Fib q).re * e2 + e4
  exact one_ne_zero this

theorem GluedBy.unit_mul {z : (Fib q)ˣ} (h : GluedBy hq0 hq1 u z) (v : (Norm q)ˣ) :
    GluedBy hq0 hq1 (fun i => (v : Norm q) * u i) (epsU hq0 hq1 v * z) := by
  obtain ⟨a, b, h0, h1⟩ := h
  refine ⟨a, b, ?_, ?_⟩
  · simp only [map_mul, h0, Units.val_mul]
    rw [mul_smul_comm]
    rfl
  · simp only [map_mul, h1, Units.val_mul]
    rw [mul_smul_comm]
    rfl

theorem Spans.unit_mul (h : Spans hq0 hq1 u) (v : (Norm q)ˣ) :
    Spans hq0 hq1 (fun i => (v : Norm q) * u i) := by
  intro z
  obtain ⟨a, b, hab⟩ := h (eps hq0 hq1 ((v⁻¹ : (Norm q)ˣ) : Norm q) * z)
  refine ⟨a, b, ?_⟩
  simp only [map_mul]
  rw [← mul_smul_comm, ← mul_smul_comm, ← mul_add, ← hab, ← mul_assoc, ← map_mul, Units.mul_inv,
    map_one, one_mul]

/-- A primitive eigenvector has a nonzero coefficient on its line. -/
theorem coef_ne (hp : Prim u) {z : (Fib q)ˣ} {a b : F}
    (h0 : eps hq0 hq1 (u 0) = a • (z : Fib q)) (h1 : eps hq0 hq1 (u 1) = b • (z : Fib q)) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra hab
  simp only [not_or, ne_eq, not_not] at hab
  obtain ⟨x, y, hxy⟩ := hp.map (eps hq0 hq1)
  rw [h0, h1, hab.1, hab.2] at hxy
  simp at hxy

/-- The line of a primitive eigenvector determines the class of its unit. -/
theorem glued_unique (h2 : (2 : F) ≠ 0) (hp : Prim u) {z z' : (Fib q)ˣ} (h : GluedBy hq0 hq1 u z)
    (h' : GluedBy hq0 hq1 u z') : theta z = theta z' := by
  obtain ⟨a, b, h0, h1⟩ := h
  obtain ⟨a', b', h0', h1'⟩ := h'
  have key : ∀ c c' : F, c ≠ 0 → c • (z : Fib q) = c' • (z' : Fib q) → theta z = theta z' := by
    intro c c' hc he
    have hc' : c' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at he
      have := (smul_eq_zero.mp he).resolve_left hc
      exact z.ne_zero this
    refine (theta_eq_iff h2).mpr ⟨c / c', div_ne_zero hc hc', ?_⟩
    rw [← Algebra.smul_def, div_eq_inv_mul, mul_smul, he, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rcases coef_ne hq0 hq1 hp h0 h1 with hc | hc
  · exact key a a' hc (h0.symm.trans h0')
  · exact key b b' hc (h1.symm.trans h1')

/-! ### The class of a law -/

/-- The data of the class `w` on an eigenvector. -/
def Data (u : Fin 2 → Norm q) : Option (U q ⧸ gluing q) → Prop
  | none => Spans hq0 hq1 u
  | some c => ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c

/-- The law `L` has the class `w`. -/
def ClassOf (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F))
    (w : Option (U q ⧸ gluing q)) : Prop :=
  ∃ u, IsEigen hq0 L.1 u ∧ Prim u ∧ Data hq0 hq1 u w

variable {L L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)}
  {w w' : Option (U q ⧸ gluing q)}

/-- Every law of the phase has a class. -/
theorem exists_classOf (ht : phase L = phaseT q) : ∃ w, ClassOf hq0 hq1 L w := by
  obtain ⟨u, he, hp⟩ := exists_eigen hq0 hq1 L ht
  rcases spans_or_glued hq0 hq1 hp with h | ⟨z, h⟩
  · exact ⟨none, u, he, hp, h⟩
  · exact ⟨some (theta z : U q), u, he, hp, z, h, rfl⟩

/-- A law has one class. -/
theorem classOf_unique (h2 : (2 : F) ≠ 0) (h : ClassOf hq0 hq1 L w) (h' : ClassOf hq0 hq1 L w') :
    w = w' := by
  obtain ⟨u, he, hp, hd⟩ := h
  obtain ⟨u', he', hp', hd'⟩ := h'
  obtain ⟨v, hv⟩ := eigen_unique hq0 hq1 he hp he' hp'
  obtain rfl : u' = fun i => (v : Norm q) * u i := funext hv
  cases w with
  | none =>
    have hd1 : Spans hq0 hq1 u := hd
    cases w' with
    | none => rfl
    | some c =>
      have hd2 : ∃ z, GluedBy hq0 hq1 (fun i => (v : Norm q) * u i) z ∧
          ((theta z : U q) : U q ⧸ gluing q) = c := hd'
      obtain ⟨z, hz, -⟩ := hd2
      exact absurd hz ((Spans.unit_mul hq0 hq1 hd1 v).not_glued hq0 hq1 z)
  | some c =>
    have hd1 : ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd
    obtain ⟨z, hz, hzc⟩ := hd1
    cases w' with
    | none =>
      have hd2 : Spans hq0 hq1 (fun i => (v : Norm q) * u i) := hd'
      exact absurd (hz.unit_mul hq0 hq1 v) (hd2.not_glued hq0 hq1 _)
    | some c' =>
      have hd2 : ∃ z, GluedBy hq0 hq1 (fun i => (v : Norm q) * u i) z ∧
          ((theta z : U q) : U q ⧸ gluing q) = c' := hd'
      obtain ⟨z', hz', hzc'⟩ := hd2
      have h1 := glued_unique hq0 hq1 h2 hp' hz' (hz.unit_mul hq0 hq1 v)
      have h3 : ((theta (epsU hq0 hq1 v) : U q) : U q ⧸ gluing q) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (theta_eps_mem hq0 hq1 v)
      have h4 : ((theta z' : U q) : U q ⧸ gluing q) = (theta z : U q) := by
        rw [h1, map_mul, QuotientGroup.mk_mul, h3]
        exact one_mul ((theta z : U q) : U q ⧸ gluing q)
      exact congrArg some (hzc.symm.trans (h4.symm.trans hzc'))

/-- The value on the fibre of an element of the lattice. -/
theorem eps_lat (f₀ f₁ : LaurentPolynomial F) :
    eps hq0 hq1 (psi hq0 f₀ * u 0 + psi hq0 f₁ * u 1) =
      atZero F f₀ • eps hq0 hq1 (u 0) + atZero F f₁ • eps hq0 hq1 (u 1) := by
  rw [map_add, map_mul, map_mul, eps_psi, eps_psi, Algebra.smul_def, Algebra.smul_def]

/-- Processing keeps the class. -/
theorem ClassOf.conj_aux (h : ClassOf hq0 hq1 L w)
    (Pm Qm : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) (hQP : Qm * Pm = 1)
    (hL : L'.1 = Pm * L.1 * Qm) : ClassOf hq0 hq1 L' w := by
  obtain ⟨u, he, hp, hd⟩ := h
  have hmap1 : (1 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map (psi hq0) = 1 :=
    map_one (psi hq0).mapMatrix
  let u' : Fin 2 → Norm q := Matrix.vecMul u (Qm.map (psi hq0))
  have hback : u = Matrix.vecMul u' (Pm.map (psi hq0)) := by
    simp only [u']
    rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, hQP, hmap1, Matrix.vecMul_one]
  have hu'j : ∀ j, u' j = psi hq0 (Qm 0 j) * u 0 + psi hq0 (Qm 1 j) * u 1 := by
    intro j
    simp only [u', Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
    ring
  have hu_j : ∀ j, u j = psi hq0 (Pm 0 j) * u' 0 + psi hq0 (Pm 1 j) * u' 1 := by
    intro j
    conv_lhs => rw [hback]
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
    ring
  refine ⟨u', ?_, ?_, ?_⟩
  · -- the eigenvector equation
    change Matrix.vecMul u' (L'.1.map (psi hq0)) = lamN hq0 • u'
    rw [hL]
    simp only [u']
    rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul, Matrix.map_mul, ← Matrix.vecMul_vecMul]
    have he' : Matrix.vecMul u (L.1.map (psi hq0)) = lamN hq0 • u := he
    rw [he', Matrix.smul_vecMul]
  · -- primitive
    obtain ⟨a0, a1, ha⟩ := hp
    refine ⟨a0 * psi hq0 (Pm 0 0) + a1 * psi hq0 (Pm 0 1),
      a0 * psi hq0 (Pm 1 0) + a1 * psi hq0 (Pm 1 1), ?_⟩
    rw [← ha, hu_j 0, hu_j 1]
    ring
  · -- the data
    cases w with
    | none =>
      have hd1 : Spans hq0 hq1 u := hd
      intro z
      obtain ⟨a, b, hab⟩ := hd1 z
      refine ⟨a * atZero F (Pm 0 0) + b * atZero F (Pm 0 1),
        a * atZero F (Pm 1 0) + b * atZero F (Pm 1 1), ?_⟩
      rw [hab, hu_j 0, hu_j 1, eps_lat, eps_lat]
      simp only [smul_add, smul_smul, add_smul]
      abel
    | some c =>
      have hd1 : ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd
      obtain ⟨z, ⟨a, b, h0, h1⟩, hc⟩ := hd1
      refine ⟨z, ⟨atZero F (Qm 0 0) * a + atZero F (Qm 1 0) * b,
        atZero F (Qm 0 1) * a + atZero F (Qm 1 1) * b, ?_, ?_⟩, hc⟩
      · rw [hu'j 0, eps_lat, h0, h1, smul_smul, smul_smul, add_smul]
      · rw [hu'j 1, eps_lat, h0, h1, smul_smul, smul_smul, add_smul]

/-- Processing keeps the class. -/
theorem ClassOf.conj (h : ClassOf hq0 hq1 L w) (P : GL (Fin 2) (LaurentPolynomial F))
    (hL : (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * L *
        ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))) :
    ClassOf hq0 hq1 L' w :=
  h.conj_aux hq0 hq1 _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hL

include hq1 in
/-- An element whose value lies on the line of an eigenvector lies in its lattice. -/
theorem glued_lat (he : IsEigen hq0 M u) (hp : Prim u) {z : (Fib q)ˣ} (h : GluedBy hq0 hq1 u z)
    {y : Norm q} {c : F} (hy : eps hq0 hq1 y = c • (z : Fib q)) : Lat hq0 u y := by
  obtain ⟨a, b, h0, h1⟩ := h
  rcases coef_ne hq0 hq1 hp h0 h1 with hc | hc
  · refine lat_of_eps hq0 hq1 he hp (c / a) 0 ?_
    rw [h0, hy, zero_smul, add_zero, smul_smul, div_mul_cancel₀ _ hc]
  · refine lat_of_eps hq0 hq1 he hp 0 (c / b) ?_
    rw [h1, hy, zero_smul, zero_add, smul_smul, div_mul_cancel₀ _ hc]

/-- Two laws with the same class are related by processing. -/
theorem conj_of_classOf (h2 : (2 : F) ≠ 0) (h : ClassOf hq0 hq1 L w) (h' : ClassOf hq0 hq1 L' w) :
    ∃ P : GL (Fin 2) (LaurentPolynomial F), (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * L *
        ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
          Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) := by
  obtain ⟨u, he, hp, hd⟩ := h
  obtain ⟨u', he', hp', hd'⟩ := h'
  cases w with
  | none =>
    have hd1 : Spans hq0 hq1 u := hd
    have hd2 : Spans hq0 hq1 u' := hd'
    have hl : ∀ i, Lat hq0 u (u' i) := fun i => by
      obtain ⟨a, b, hab⟩ := hd1 (eps hq0 hq1 (u' i))
      exact lat_of_eps hq0 hq1 he hp a b hab
    have hl' : ∀ i, Lat hq0 u' (u i) := fun i => by
      obtain ⟨a, b, hab⟩ := hd2 (eps hq0 hq1 (u i))
      exact lat_of_eps hq0 hq1 he' hp' a b hab
    exact conj_of_lat hq0 hq1 L L' he hp he' (hl 0) (hl 1) (hl' 0) (hl' 1)
  | some c =>
    have hd1 : ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd
    have hd2 : ∃ z, GluedBy hq0 hq1 u' z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd'
    obtain ⟨z, hz, hzc⟩ := hd1
    obtain ⟨z', hz', hc⟩ := hd2
    have hm : (theta z')⁻¹ * theta z ∈ gluing q := QuotientGroup.eq.mp (hc.trans hzc.symm)
    obtain ⟨v, hv⟩ := exists_unit_of_mem hq0 hq1 hm
    -- `(ε v) z′ = a z`
    have hth : theta z = theta (epsU hq0 hq1 v * z') := by
      rw [map_mul, hv, mul_comm, mul_inv_cancel_left]
    obtain ⟨a, ha, hy⟩ := (theta_eq_iff h2).mp hth
    have hw := hz'.unit_mul hq0 hq1 v
    have hew := he'.unit_mul hq0 v
    have hpw := hp'.unit_mul v
    have hl : ∀ i, Lat hq0 u ((v : Norm q) * u' i) := by
      intro i
      obtain ⟨α, β, h0, h1⟩ := hw
      have hi : ∃ c : F, eps hq0 hq1 ((v : Norm q) * u' i) = c • (z : Fib q) := by
        fin_cases i
        · exact ⟨α * a, by
            refine h0.trans ?_
            rw [hy, ← Algebra.smul_def, smul_smul]⟩
        · exact ⟨β * a, by
            refine h1.trans ?_
            rw [hy, ← Algebra.smul_def, smul_smul]⟩
      obtain ⟨c, hc⟩ := hi
      exact glued_lat hq0 hq1 he hp hz hc
    have hl' : ∀ i, Lat hq0 (fun i => (v : Norm q) * u' i) (u i) := by
      intro i
      obtain ⟨α, β, h0, h1⟩ := hz
      have hz0 : (z : Fib q) = a⁻¹ • ((epsU hq0 hq1 v * z' : (Fib q)ˣ) : Fib q) := by
        rw [hy, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ ha, one_smul]
      have hi : ∃ c : F, eps hq0 hq1 (u i) = c • ((epsU hq0 hq1 v * z' : (Fib q)ˣ) : Fib q) := by
        fin_cases i
        · exact ⟨α * a⁻¹, by
            refine h0.trans ?_
            rw [hz0, smul_smul]⟩
        · exact ⟨β * a⁻¹, by
            refine h1.trans ?_
            rw [hz0, smul_smul]⟩
      obtain ⟨c, hc⟩ := hi
      exact glued_lat hq0 hq1 hew hpw hw hc
    exact conj_of_lat hq0 hq1 L L' he hp hew (hl 0) (hl 1) (hl' 0) (hl' 1)

/-! ### The zero mode -/

/-- A law whose image is the whole fibre is the identity at the zero mode. -/
theorem atZero_eq_one_of_spans (he : IsEigen hq0 L.1 u) (hs : Spans hq0 hq1 u) :
    Matrix.SpecialLinearGroup.map (atZero F) L = 1 := by
  obtain ⟨h0, h1⟩ := (isEigen_iff hq0).mp he
  have h0' := congrArg (eps hq0 hq1) h0
  have h1' := congrArg (eps hq0 hq1) h1
  simp only [map_add, map_mul, eps_psi, eps_lam, one_mul] at h0' h1'
  have e0 : (atZero F (L.1 0 0) - 1) • eps hq0 hq1 (u 0) +
      atZero F (L.1 1 0) • eps hq0 hq1 (u 1) = 0 := by
    rw [sub_smul, one_smul, Algebra.smul_def, Algebra.smul_def]
    linear_combination h0'
  have e1 : atZero F (L.1 0 1) • eps hq0 hq1 (u 0) +
      (atZero F (L.1 1 1) - 1) • eps hq0 hq1 (u 1) = 0 := by
    rw [sub_smul, one_smul, Algebra.smul_def, Algebra.smul_def]
    linear_combination h1'
  obtain ⟨ha, hc⟩ := hs.indep hq0 hq1 e0
  obtain ⟨hb, hd⟩ := hs.indep hq0 hq1 e1
  ext i j
  fin_cases i <;> fin_cases j
  · exact sub_eq_zero.mp ha
  · exact hb
  · exact hc
  · exact sub_eq_zero.mp hd

include hq1 in
/-- A law that is the identity at the zero mode has the whole fibre as its image. -/
theorem spans_of_atZero_eq_one (he : IsEigen hq0 L.1 u) (hp : Prim u)
    (hL : Matrix.SpecialLinearGroup.map (atZero F) L = 1) : Spans hq0 hq1 u := by
  obtain ⟨h0, h1⟩ := (isEigen_iff hq0).mp he
  have entry : ∀ i j, atZero F (L.1 i j) = (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.1 i j) hL
    simpa using this
  obtain ⟨a', ha'⟩ := dvd_of_atZero (f := L.1 0 0 - 1) (by simp [entry])
  obtain ⟨b', hb'⟩ := dvd_of_atZero (f := L.1 0 1) (by simp [entry])
  obtain ⟨c', hc'⟩ := dvd_of_atZero (f := L.1 1 0) (by simp [entry])
  obtain ⟨d', hd'⟩ := dvd_of_atZero (f := L.1 1 1 - 1) (by simp [entry])
  have hδ := deltaN_ne_zero hq0
  have pa : psi hq0 (L.1 0 0) = 1 + deltaN hq0 * psi hq0 a' := by
    have := congrArg (psi hq0) ha'
    rw [map_sub, map_one, map_mul, psi_delta] at this
    linear_combination this
  have pb : psi hq0 (L.1 0 1) = deltaN hq0 * psi hq0 b' := by
    rw [hb', map_mul, psi_delta]
  have pc : psi hq0 (L.1 1 0) = deltaN hq0 * psi hq0 c' := by
    rw [hc', map_mul, psi_delta]
  have pd : psi hq0 (L.1 1 1) = 1 + deltaN hq0 * psi hq0 d' := by
    have := congrArg (psi hq0) hd'
    rw [map_sub, map_one, map_mul, psi_delta] at this
    linear_combination this
  rw [pa, pc] at h0
  rw [pb, pd] at h1
  simp only [lamN] at h0 h1
  -- `s u₀` and `s u₁` lie in the lattice
  have hs0 : sN q * u 0 = psi hq0 a' * u 0 + psi hq0 c' * u 1 := by
    apply mul_left_cancel₀ hδ
    linear_combination -h0
  have hs1 : sN q * u 1 = psi hq0 b' * u 0 + psi hq0 d' * u 1 := by
    apply mul_left_cancel₀ hδ
    linear_combination -h1
  have hlat0 : ∀ y, Lat hq0 u (y * u 0) := by
    intro y
    obtain ⟨f, g, rfl⟩ := exists_form hq0 hq1 y
    refine ⟨f + g * a', g * c', ?_⟩
    simp only [map_add, map_mul]
    linear_combination psi hq0 g * hs0
  have hlat1 : ∀ y, Lat hq0 u (y * u 1) := by
    intro y
    obtain ⟨f, g, rfl⟩ := exists_form hq0 hq1 y
    refine ⟨g * b', f + g * d', ?_⟩
    simp only [map_add, map_mul]
    linear_combination psi hq0 g * hs1
  obtain ⟨x0, x1, hx⟩ := hp
  intro z
  obtain ⟨y, rfl⟩ := eps_surjective hq0 hq1 z
  have hy : y = y * x0 * u 0 + y * x1 * u 1 := by linear_combination (-y) * hx
  obtain ⟨f₀, f₁, hf⟩ := (hlat0 (y * x0)).add hq0 (hlat1 (y * x1))
  rw [← hy] at hf
  exact ⟨atZero F f₀, atZero F f₁, by rw [hf]; exact eps_lat hq0 hq1 f₀ f₁⟩

/-- A law has the unglued class exactly when it is the identity at the zero mode. -/
theorem classOf_none_iff (h : ClassOf hq0 hq1 L w) :
    w = none ↔ Matrix.SpecialLinearGroup.map (atZero F) L = 1 := by
  obtain ⟨u, he, hp, hd⟩ := h
  constructor
  · rintro rfl
    exact atZero_eq_one_of_spans hq0 hq1 he hd
  · intro hL
    have hs := spans_of_atZero_eq_one hq0 hq1 he hp hL
    cases w with
    | none => rfl
    | some c =>
      have hd1 : ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd
      obtain ⟨z, hz, -⟩ := hd1
      exact absurd hz (hs.not_glued hq0 hq1 z)

/-! ### Time reversal -/

theorem star_smul_fib (a : F) (w : Fib q) : star (a • w) = a • star w := by
  ext <;> simp

theorem theta_star (z : (Fib q)ˣ) : theta (star z) = (theta z)⁻¹ := by
  refine Subtype.ext ?_
  change star z * (star (star z))⁻¹ = (z * (star z)⁻¹)⁻¹
  rw [star_star, mul_inv_rev, inv_inv, mul_comm]

/-- Time reversal inverts the class. -/
theorem ClassOf.inv (h : ClassOf hq0 hq1 L w) :
    ClassOf hq0 hq1 L⁻¹ (w.map (·⁻¹)) := by
  obtain ⟨u, he, hp, hd⟩ := h
  obtain ⟨h0, h1⟩ := (isEigen_iff hq0).mp he
  let u' : Fin 2 → Norm q := fun i => sigma hq1 (u i)
  have h0' := congrArg (sigma hq1) h0
  have h1' := congrArg (sigma hq1) h1
  simp only [map_add, map_mul, sigma_psi] at h0' h1'
  have hl := sigma_lam hq0 hq1
  -- entries of the inverse
  have hdet := L.2
  rw [Matrix.det_fin_two] at hdet
  have hdet' := congrArg (psi hq0) hdet
  simp only [map_sub, map_mul, map_one] at hdet'
  have hinv : (L⁻¹ : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)).1 =
      !![L.1 1 1, -L.1 0 1; -L.1 1 0, L.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨u', ?_, hp.map (sigma hq1), ?_⟩
  · rw [isEigen_iff, hinv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_neg, u']
    constructor
    · linear_combination (-(psi hq0 (L.1 1 1) * sigma hq1 (u 0) -
          psi hq0 (L.1 1 0) * sigma hq1 (u 1))) * hl +
        lamN hq0 * (-psi hq0 (L.1 1 1) * h0' + psi hq0 (L.1 1 0) * h1' +
          sigma hq1 (u 0) * hdet')
    · linear_combination (-(psi hq0 (L.1 0 0) * sigma hq1 (u 1) -
          psi hq0 (L.1 0 1) * sigma hq1 (u 0))) * hl +
        lamN hq0 * (sigma hq1 (u 1) * hdet' - psi hq0 (L.1 0 0) * h1' +
          psi hq0 (L.1 0 1) * h0')
  · cases w with
    | none =>
      have hd1 : Spans hq0 hq1 u := hd
      change Spans hq0 hq1 u'
      intro z
      obtain ⟨a, b, hab⟩ := hd1 (star z)
      refine ⟨a, b, ?_⟩
      simp only [u', eps_sigma]
      rw [← star_smul_fib, ← star_smul_fib, ← star_add, ← hab, star_star]
    | some c =>
      have hd1 : ∃ z, GluedBy hq0 hq1 u z ∧ ((theta z : U q) : U q ⧸ gluing q) = c := hd
      obtain ⟨z, ⟨a, b, h0z, h1z⟩, hc⟩ := hd1
      change ∃ z', GluedBy hq0 hq1 u' z' ∧ ((theta z' : U q) : U q ⧸ gluing q) = c⁻¹
      refine ⟨star z, ⟨a, b, ?_, ?_⟩, ?_⟩
      · simp only [u', eps_sigma, h0z, Units.coe_star, star_smul_fib]
      · simp only [u', eps_sigma, h1z, Units.coe_star, star_smul_fib]
      · rw [theta_star, QuotientGroup.mk_inv, hc]

/-! ### The normal forms -/

theorem phase_companionLaw : phase (companionLaw q) = phaseT q := by
  simp [phase, companionLaw, companion, Matrix.trace_fin_two]

theorem phase_ungluedLaw : phase (ungluedLaw q) = phaseT q := by
  simp only [phase, ungluedLaw, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one, kap1, deltaS, phaseT, stencilG]
  linear_combination (-LaurentPolynomial.C q) * T_mul_T_neg (F := F)

theorem phase_gluedLaw (y : F) : phase (gluedLaw q y) = phaseT q := by
  simp only [phase, gluedLaw, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one, kap1, deltaS, phaseT, stencilG]
  linear_combination (-LaurentPolynomial.C q) * T_mul_T_neg (F := F)

/-- The companion tick has the trivial class. -/
theorem classOf_companionLaw : ClassOf hq0 hq1 (companionLaw q) (some 1) := by
  refine ⟨![1, lamN hq0], ?_, ⟨1, 0, by simp⟩, ?_⟩
  · refine (isEigen_iff hq0).mpr ?_
    simp only [companionLaw, companion, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.cons_val_fin_one, map_zero, map_one, map_neg]
    constructor
    · ring
    · linear_combination -lam_root hq0
  · refine ⟨1, ⟨1, 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp [eps_lam]
    · rw [map_one]
      rfl

/-- The law `ungluedLaw` has the unglued class. -/
theorem classOf_ungluedLaw : ClassOf hq0 hq1 (ungluedLaw q) none := by
  refine ⟨![1, sN q], ?_, ⟨1, 0, by simp⟩, ?_⟩
  · refine (isEigen_iff hq0).mpr ?_
    simp only [ungluedLaw, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.cons_val_fin_one, map_one, map_add, map_mul, psi_delta']
    have hs := s_sq hq0
    constructor
    · simp only [lamN]; ring
    · simp only [lamN]; linear_combination (-deltaN hq0) * hs
  · change Spans hq0 hq1 _
    intro z
    refine ⟨z.re, z.im, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, eps_s]
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    exact elt_eq z

/-- `y + r` is a unit when `y² ≠ q`. -/
theorem isUnit_y_add_rE {y : F} (hy : y * y ≠ q) : IsUnit (algebraMap F (Fib q) y + rE) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_def]
  refine IsUnit.mk0 _ ?_
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_omega,
    QuadraticAlgebra.im_omega, rE, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  intro h0
  exact hy (by linear_combination h0)

/-- The law `gluedLaw q y` has the class of `y + r`. -/
theorem classOf_gluedLaw {y : F} (hy : y * y ≠ q) :
    ClassOf hq0 hq1 (gluedLaw q y) (some (theta (isUnit_y_add_rE hy).unit : U q)) := by
  have hC : psi hq0 (LaurentPolynomial.C y) = algebraMap F (Norm q) y := psi_C hq0 y
  have hx : psi hq0 (T 1) = deltaN hq0 + 1 := by rw [psi_T_one, deltaN]; ring
  refine ⟨![deltaN hq0, algebraMap F (Norm q) y + sN q], ?_, ?_, ?_⟩
  · refine (isEigen_iff hq0).mpr ?_
    simp only [gluedLaw, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.cons_val_fin_one, map_one, map_add, map_sub, map_mul, hx, hC]
    have hs := s_sq hq0
    constructor
    · simp only [lamN]; ring
    · simp only [lamN]; linear_combination (-deltaN hq0) * hs
  · have hne : y * y - q ≠ 0 := sub_ne_zero.mpr hy
    have hc : algebraMap F (Norm q) (y * y - q)⁻¹ *
        (algebraMap F (Norm q) y * algebraMap F (Norm q) y - qN q) = 1 := by
      rw [← map_mul, ← map_sub, ← map_mul, inv_mul_cancel₀ hne, map_one]
    refine ⟨-(algebraMap F (Norm q) (y * y - q)⁻¹ * (sN q * (sN q - qN q))),
      algebraMap F (Norm q) (y * y - q)⁻¹ * (algebraMap F (Norm q) y - sN q), ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-algebraMap F (Norm q) (y * y - q)⁻¹) * delta_rel hq0 + hc
  · refine ⟨(isUnit_y_add_rE hy).unit, ⟨0, 1, ?_, ?_⟩, rfl⟩
    · simp [eps_delta]
    · simp [eps_const, eps_s]

/-- Every class is a law's. -/
theorem exists_law (h2 : (2 : F) ≠ 0) (w : Option (U q ⧸ gluing q)) :
    ∃ L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F),
      phase L = phaseT q ∧ ClassOf hq0 hq1 L w := by
  cases w with
  | none => exact ⟨_, phase_ungluedLaw, classOf_ungluedLaw hq0 hq1⟩
  | some c =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨z, rfl⟩ := theta_surjective hq0 h2 u
    by_cases hz : (z : Fib q).im = 0
    · have h1 : theta z = 1 := theta_const (by ext <;> simp [hz])
      refine ⟨_, phase_companionLaw, ?_⟩
      rw [h1]
      exact classOf_companionLaw hq0 hq1
    · have hn : QuadraticAlgebra.norm (z : Fib q) ≠ 0 :=
        (z.isUnit.map (QuadraticAlgebra.norm : Fib q →* F)).ne_zero
      have hy : ((z : Fib q).re / (z : Fib q).im) * ((z : Fib q).re / (z : Fib q).im) ≠ q := by
        intro h0
        apply hn
        rw [QuadraticAlgebra.norm_def]
        field_simp at h0
        simp only [zero_mul, add_zero]
        rw [← pow_two]
        linear_combination h0
      refine ⟨gluedLaw q ((z : Fib q).re / (z : Fib q).im), phase_gluedLaw _, ?_⟩
      have ht : theta z = theta (isUnit_y_add_rE hy).unit := by
        refine (theta_eq_iff h2).mpr ⟨(z : Fib q).im⁻¹, inv_ne_zero hz, ?_⟩
        rw [IsUnit.unit_spec]
        ext
        · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.algebraMap_re,
            QuadraticAlgebra.re_omega, rE, add_zero]
          simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
            QuadraticAlgebra.algebraMap_im]
          field_simp
          ring
        · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.algebraMap_im,
            QuadraticAlgebra.im_omega, rE, zero_add]
          simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
            QuadraticAlgebra.algebraMap_im]
          field_simp
          ring
      rw [ht]
      exact classOf_gluedLaw hq0 hq1 hy

/-! ### The discriminant is not a square -/

include hq0 hq1 in
/-- `t² - 4` is not a square in the fraction field: `σ` swaps its two square roots `±(λ - 1/λ)`. -/
theorem nonSquareDisc_phase (h2 : (2 : F) ≠ 0) : NonSquareDisc (phaseT q) := by
  intro y z h
  have h20 : (2 : Norm q) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap F (Norm q)).injective
    rw [map_zero, map_ofNat]
    exact h0
  have hl := sigma_lam hq0 hq1
  have hroot := lam_root hq0
  set l := lamN hq0 with hll
  set m := sigma hq1 l with hm
  have hlne : l ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hl
    exact zero_ne_one hl
  have ht : psi hq0 (phaseT q) = l + m := by
    apply mul_left_cancel₀ hlne
    linear_combination -hroot - hl
  have hsm : sigma hq1 m = l := by
    have h1 := congrArg (sigma hq1) hl
    rw [map_mul, map_one, ← hm] at h1
    -- `σ(m) m = 1 = l m`
    have hmne : m ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hl
      exact zero_ne_one hl
    apply mul_right_cancel₀ hmne
    linear_combination h1 - hl
  have hne : l - m ≠ 0 := by
    intro h0
    have h3 : l - psi hq0 (LaurentPolynomial.C 2⁻¹ * phaseT q) = 0 := by
      have hc : algebraMap F (Norm q) 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap F (Norm q)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
      rw [map_mul, psi_C, ht]
      linear_combination algebraMap F (Norm q) 2⁻¹ * h0 - l * hc
    exact lam_sub_ne hq0 hq1 _ h3
  have h1 := congrArg (psi hq0) h
  simp only [map_mul, map_sub, map_ofNat, ht] at h1
  have hfac : (psi hq0 y - (l - m) * psi hq0 z) * (psi hq0 y + (l - m) * psi hq0 z) = 0 := by
    linear_combination h1 + ((4 : Norm q) * psi hq0 z * psi hq0 z) * hl
  have hz : (2 * (l - m)) * psi hq0 z = 0 := by
    rcases mul_eq_zero.mp hfac with h3 | h3
    · have h4 := congrArg (sigma hq1) h3
      simp only [map_sub, map_mul, map_zero, sigma_psi, hsm, ← hm] at h4
      linear_combination h4 - h3
    · have h4 := congrArg (sigma hq1) h3
      simp only [map_add, map_sub, map_mul, map_zero, sigma_psi, hsm, ← hm] at h4
      linear_combination h3 - h4
  have hz0 : psi hq0 z = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h20 hne)
  exact (injective_iff_map_eq_zero _).mp (psi_injective hq0) z hz0

/-! ### The trivial class -/

/-- A law with a cyclic vector is conjugate to the companion tick. -/
theorem classOf_of_cyclic (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT q)
    {v : Fin 2 → LaurentPolynomial F}
    (hv : IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det) :
    ClassOf hq0 hq1 L (some 1) := by
  set Pm := cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v with hPm
  have hrel := (trivialClass_of_cyclic (phaseT q) (nonSquareDisc_phase hq0 hq1 h2) L v ht hv).1
  have hu : IsUnit Pm := (Matrix.isUnit_iff_isUnit_det _).mpr hv
  obtain ⟨Pu, hPu⟩ := hu
  have hQP : ((Pu⁻¹ : (Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))ˣ) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * Pm = 1 := by
    rw [← hPu, Units.inv_mul]
  have hPQ : Pm * ((Pu⁻¹ : (Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))ˣ) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) = 1 := by
    rw [← hPu, Units.mul_inv]
  refine (classOf_companionLaw hq0 hq1).conj_aux hq0 hq1 Pm _ hQP ?_
  change L.1 = Pm * companion (phaseT q) * _
  rw [← hrel, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-- A law conjugate to the companion tick has a cyclic vector. -/
theorem cyclic_of_conj (P : GL (Fin 2) (LaurentPolynomial F))
    (hL : (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * companionLaw q *
        ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))) :
    ∃ v : Fin 2 → LaurentPolynomial F,
      IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det := by
  have hQP : ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) *
        (P : GL (Fin 2) (LaurentPolynomial F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hLP : (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) *
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * companion (phaseT q) := by
    rw [hL, Matrix.mul_assoc, hQP, Matrix.mul_one]
    rfl
  refine ⟨fun i => (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) i 0, ?_⟩
  have hc : cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))
      (fun i => (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) i 0) =
      (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) := by
    have hcol : ∀ i, Matrix.mulVec (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F))
        (fun i => (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) i 0) i =
        (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) i 1 := by
      intro i
      have := congrFun (congrFun hLP i) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, companion, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
        mul_zero, mul_one, zero_add] at this
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · rfl
    · exact hcol 0
    · rfl
    · exact hcol 1
  rw [hc, ← Matrix.isUnit_iff_isUnit_det]
  exact P.isUnit

/-! ### The classes -/

/-- The class map. -/
noncomputable def classMap (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) :
    Option (U q ⧸ gluing q) :=
  Classical.epsilon (ClassOf hq0 hq1 L)

theorem classMap_spec (ht : phase L = phaseT q) : ClassOf hq0 hq1 L (classMap hq0 hq1 L) :=
  Classical.epsilon_spec (exists_classOf hq0 hq1 ht)

theorem classMap_eq (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT q) (h : ClassOf hq0 hq1 L w) :
    classMap hq0 hq1 L = w :=
  classOf_unique hq0 hq1 h2 (classMap_spec hq0 hq1 ht) h

theorem phase_inv (L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)) : phase L⁻¹ = phase L := by
  simp only [phase, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  ring

/-- Same class, same law up to processing. -/
theorem classMap_eq_iff (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT q) (ht' : phase L' = phaseT q) :
    classMap hq0 hq1 L = classMap hq0 hq1 L' ↔
      ∃ P : GL (Fin 2) (LaurentPolynomial F), (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
        (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) * L *
          ((P⁻¹ : GL (Fin 2) (LaurentPolynomial F)) :
            Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) := by
  constructor
  · intro h
    have h1 := classMap_spec hq0 hq1 ht
    have h3 := classMap_spec hq0 hq1 ht'
    rw [h] at h1
    exact conj_of_classOf hq0 hq1 h2 h1 h3
  · rintro ⟨P, hP⟩
    exact (classMap_eq hq0 hq1 h2 ht' ((classMap_spec hq0 hq1 ht).conj hq0 hq1 P hP)).symm

theorem classMap_eq_some_one_iff (h2 : (2 : F) ≠ 0) (ht : phase L = phaseT q) :
    classMap hq0 hq1 L = some 1 ↔ ∃ v : Fin 2 → LaurentPolynomial F,
      IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det := by
  constructor
  · intro h
    have h1 := classMap_spec hq0 hq1 ht
    rw [h] at h1
    obtain ⟨P, hP⟩ := conj_of_classOf hq0 hq1 h2 (classOf_companionLaw hq0 hq1) h1
    exact cyclic_of_conj P hP
  · rintro ⟨v, hv⟩
    exact classMap_eq hq0 hq1 h2 ht (classOf_of_cyclic hq0 hq1 h2 ht hv)

/-! ### The split node -/

/-- Evaluation of the fibre at a square root `h` of `q`. -/
def evalAt (h : F) (hh : h * h = q) : Fib q →* F where
  toFun z := z.re + z.im * h
  map_one' := by simp
  map_mul' a b := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero, ← hh]
    ring

theorem evalAt_apply (h : F) (hh : h * h = q) (z : Fib q) : evalAt h hh z = z.re + z.im * h := rfl

theorem evalAt_conj (h : F) (hh : h * h = q) (z : Fib q) :
    evalAt h hh z * (z.re - z.im * h) = QuadraticAlgebra.norm z := by
  rw [evalAt_apply, QuadraticAlgebra.norm_def]
  linear_combination -(z.im * z.im) * hh

/-- The split node: evaluation at `h` as a map from `U` to the units of `F`. -/
noncomputable def splitHom (h : F) (hh : h * h = q) : U q →* Fˣ :=
  (Units.map (evalAt h hh)).comp (U q).subtype

theorem val_splitHom (h : F) (hh : h * h = q) (u : U q) :
    (splitHom h hh u : F) = ((u : (Fib q)ˣ) : Fib q).re + ((u : (Fib q)ˣ) : Fib q).im * h := rfl

include hq0 in
/-- At a split node `U` is the group of units of `F`. -/
theorem splitHom_bijective (h2 : (2 : F) ≠ 0) (h : F) (hh : h * h = q) :
    Function.Bijective (splitHom h hh) := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [← hh, mul_zero])
  constructor
  · refine (injective_iff_map_eq_one _).mpr fun u hu => ?_
    have hn := mem_U.mp u.2
    have hv : ((u : (Fib q)ˣ) : Fib q).re + ((u : (Fib q)ˣ) : Fib q).im * h = 1 := by
      rw [← val_splitHom h hh u, hu, Units.val_one]
    have hc := evalAt_conj h hh ((u : (Fib q)ˣ) : Fib q)
    rw [evalAt_apply, hv, one_mul, hn] at hc
    have hre : ((u : (Fib q)ˣ) : Fib q).re = 1 := by
      have : 2 * ((u : (Fib q)ˣ) : Fib q).re = 2 := by linear_combination hv + hc
      exact mul_left_cancel₀ h2 (by rw [this, mul_one])
    have him : ((u : (Fib q)ˣ) : Fib q).im = 0 := by
      have h3 : 2 * h * ((u : (Fib q)ˣ) : Fib q).im = 0 := by linear_combination hv - hc
      exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hh0)
    refine Subtype.ext (Units.ext ?_)
    ext
    · simpa using hre
    · simpa using him
  · intro a
    have ha := a.ne_zero
    have hai : (a : F) * (a : F)⁻¹ = 1 := mul_inv_cancel₀ ha
    let z : Fib q := ⟨((a : F) + (a : F)⁻¹) / 2, ((a : F) - (a : F)⁻¹) / (2 * h)⟩
    have hre : z.re + z.im * h = a := by
      simp only [z]
      field_simp
      ring
    have hn : QuadraticAlgebra.norm z = 1 := by
      rw [QuadraticAlgebra.norm_def]
      simp only [z, zero_mul, add_zero, ← hh]
      field_simp
      ring
    have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hn]; exact isUnit_one)
    refine ⟨⟨hu.unit, mem_U.mpr hn⟩, Units.ext ?_⟩
    rw [val_splitHom]
    exact hre

include hq0 hq1 in
/-- At a split node, `ρ` is `(1 - h)/(1 + h)`. -/
theorem splitHom_gluing (h : F) (hh : h * h = q) :
    (gluing q).map (splitHom h hh) =
      Subgroup.closure {x : Fˣ | (x : F) = -1 ∨ (x : F) * (1 + h) = 1 - h} := by
  rw [gluing, MonoidHom.map_closure]
  congr 1
  have hρ := theta_eps_s1 hq0 hq1
  have hneg := theta_eps_s hq0 hq1
  have heval : ∀ w w' : Fib q, evalAt h hh (w * w') = evalAt h hh w * evalAt h hh w' :=
    fun w w' => map_mul _ w w'
  have hR : evalAt h hh (rE : Fib q) = h := by simp [evalAt_apply, rE]
  have hadd : ∀ w w' : Fib q, evalAt h hh (w + w') = evalAt h hh w + evalAt h hh w' := by
    intro w w'
    simp only [evalAt_apply, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    ring
  have hone : evalAt h hh (1 : Fib q) = 1 := map_one _
  have hnegv : ∀ w : Fib q, evalAt h hh (-w) = -evalAt h hh w := by
    intro w
    simp only [evalAt_apply, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]
    ring
  have hneg1 : evalAt h hh (-1 : Fib q) = -1 := by rw [hnegv, hone]
  have hρ1 : evalAt h hh (1 + rE) = 1 + h := by rw [hadd, hone, hR]
  have hρ2 : evalAt h hh (1 - rE) = 1 - h := by
    rw [sub_eq_add_neg, hadd, hnegv, hone, hR, ← sub_eq_add_neg]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases hu with hu | hu
    · left
      rw [val_splitHom, ← evalAt_apply h hh, hu, hneg1]
    · right
      rw [val_splitHom, ← evalAt_apply h hh, ← hρ1, ← heval, hu, hρ2]
  · rintro (hx | hx)
    · refine ⟨theta (epsU hq0 hq1 (uS q)), Or.inl hneg, Units.ext ?_⟩
      rw [val_splitHom, ← evalAt_apply h hh, hx]
      change evalAt h hh (thetaV _) = -1
      rw [hneg, hneg1]
    · have hu1 : (1 : F) + h ≠ 0 := by
        intro h0
        have h3 : h = -1 := by linear_combination h0
        apply hq1
        rw [← hh, h3]
        ring
      refine ⟨theta (epsU hq0 hq1 (uS1 q)), Or.inr hρ, Units.ext ?_⟩
      apply mul_right_cancel₀ hu1
      have hv : ((splitHom h hh (theta (epsU hq0 hq1 (uS1 q))) : Fˣ) : F) =
          evalAt h hh (thetaV (epsU hq0 hq1 (uS1 q))) := rfl
      rw [hv, hx, ← hρ1, ← heval, hρ, hρ2]

/-! ### The counts over a finite field -/

/-- The kernel of `theta` is the group of nonzero constants. -/
theorem card_ker_theta (h2 : (2 : F) ≠ 0) :
    Nat.card (theta : (Fib q)ˣ →* U q).ker = Nat.card Fˣ := by
  let f : Fˣ →* (Fib q)ˣ := Units.map (algebraMap F (Fib q) : F →* Fib q)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := congrArg (fun z : (Fib q)ˣ => (z : Fib q).re) hab
    exact Units.ext h1
  have hr : f.range = (theta : (Fib q)ˣ →* U q).ker := by
    ext z
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨a, rfl⟩
      refine theta_const ?_
      change algebraMap F (Fib q) (a : F) = algebraMap F (Fib q) (algebraMap F (Fib q) (a : F)).re
      simp
    · intro hz
      have h1 : theta z = theta (1 : (Fib q)ˣ) := by rw [hz, map_one]
      obtain ⟨a, ha, hza⟩ := (theta_eq_iff h2).mp h1
      refine ⟨(Units.mk0 a ha)⁻¹, Units.ext ?_⟩
      have hv : ((f (Units.mk0 a ha)⁻¹ : (Fib q)ˣ) : Fib q) = algebraMap F (Fib q) a⁻¹ := rfl
      have h3 : algebraMap F (Fib q) a⁻¹ * algebraMap F (Fib q) a = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ha, map_one]
      rw [hv]
      rw [Units.val_one] at hza
      linear_combination algebraMap F (Fib q) a⁻¹ * hza + (z : Fib q) * h3
  rw [← hr]
  exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

variable (q) in
instance finite_fib [Finite F] : Finite (Fib q) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd q 0).symm

theorem card_fib [Finite F] : Nat.card (Fib q) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd q 0), Nat.card_prod]

include hq0 in
/-- `|E^×| = |F^×| |U|`. -/
theorem card_units_fib [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (Fib q)ˣ = Nat.card Fˣ * Nat.card (U q) := by
  have h1 := Subgroup.card_mul_index (theta : (Fib q)ˣ →* U q).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (theta_surjective hq0 h2),
    Subgroup.card_top, card_ker_theta h2] at h1
  exact h1.symm

include hq0 in
/-- At a split node, `|U| = |F| - 1`. -/
theorem card_U_of_square [Finite F] (h2 : (2 : F) ≠ 0) (hs : IsSquare q) :
    Nat.card (U q) = Nat.card F - 1 := by
  obtain ⟨h, rfl⟩ := hs
  rw [← Nat.card_units F]
  exact Nat.card_congr (Equiv.ofBijective _ (splitHom_bijective hq0 h2 h rfl))

include hq0 in
/-- At a non-split node, `|U| = |F| + 1`. -/
theorem card_U_of_not_square [Finite F] (h2 : (2 : F) ≠ 0) (hs : ¬ IsSquare q) :
    Nat.card (U q) = Nat.card F + 1 := by
  have hf : Fact (∀ r : F, r ^ 2 ≠ q + 0 * r) := ⟨fun r hr => hs ⟨r, by
    rw [← pow_two, hr]
    ring⟩⟩
  have h1 : Nat.card (Fib q)ˣ = Nat.card (Fib q) - 1 := Nat.card_units (Fib q)
  have h3 := card_units_fib (q := q) hq0 h2
  rw [h1, card_fib, Nat.card_units F] at h3
  have hn : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
  rw [hm] at h3 ⊢
  have hm0 : 0 < m := by omega
  simp only [Nat.add_sub_cancel] at h3
  have h4 : (m + 1) * (m + 1) - 1 = m * (m + 1 + 1) := by
    have : (m + 1) * (m + 1) = m * (m + 1 + 1) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  rw [h4] at h3
  exact (Nat.eq_of_mul_eq_mul_left hm0 h3).symm

/-! ### The size of `⟨-1, ρ⟩` -/

/-- `-1` as an element of `U`. -/
noncomputable def negU (hq0 : q ≠ 0) (hq1 : q ≠ 1) : U q := theta (epsU hq0 hq1 (uS q))

/-- `ρ` as an element of `U`. -/
noncomputable def rhoU (hq0 : q ≠ 0) (hq1 : q ≠ 1) : U q := theta (epsU hq0 hq1 (uS1 q))

theorem val_negU : ((negU hq0 hq1 : (Fib q)ˣ) : Fib q) = -1 := theta_eps_s hq0 hq1

theorem val_rhoU : ((rhoU hq0 hq1 : (Fib q)ˣ) : Fib q) * (1 + rE) = 1 - rE := theta_eps_s1 hq0 hq1

theorem negU_mem : negU hq0 hq1 ∈ gluing q :=
  Subgroup.subset_closure (Or.inl (val_negU hq0 hq1))

theorem rhoU_mem : rhoU hq0 hq1 ∈ gluing q :=
  Subgroup.subset_closure (Or.inr (val_rhoU hq0 hq1))

theorem rE_ne_zero (h2 : (2 : F) ≠ 0) : (2 : Fib q) * rE ≠ 0 := by
  intro h
  exact h2 (by simpa [rE] using congrArg QuadraticAlgebra.im h)

theorem two_fib_ne (h2 : (2 : F) ≠ 0) : (2 : Fib q) ≠ 0 := by
  intro h
  exact h2 (by simpa using congrArg QuadraticAlgebra.re h)

/-- `ρ ≠ 1`. -/
theorem rhoU_ne_one (h2 : (2 : F) ≠ 0) : rhoU hq0 hq1 ≠ 1 := by
  intro h
  have h1 := val_rhoU hq0 hq1
  rw [h] at h1
  apply rE_ne_zero (q := q) h2
  have h3 : (((1 : U q) : (Fib q)ˣ) : Fib q) = 1 := rfl
  rw [h3] at h1
  linear_combination h1

/-- `ρ ≠ -1`. -/
theorem rhoU_ne_neg (h2 : (2 : F) ≠ 0) : rhoU hq0 hq1 ≠ negU hq0 hq1 := by
  intro h
  have h1 := val_rhoU hq0 hq1
  rw [h, val_negU] at h1
  apply two_fib_ne (q := q) h2
  linear_combination -h1

theorem negU_ne_one (h2 : (2 : F) ≠ 0) : negU hq0 hq1 ≠ 1 := by
  intro h
  have h1 := val_negU hq0 hq1
  rw [h] at h1
  apply two_fib_ne (q := q) h2
  have h3 : (((1 : U q) : (Fib q)ˣ) : Fib q) = 1 := rfl
  rw [h3] at h1
  linear_combination h1

theorem negU_mul_self : negU hq0 hq1 * negU hq0 hq1 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  have h1 := val_negU hq0 hq1
  change ((negU hq0 hq1 : (Fib q)ˣ) : Fib q) * ((negU hq0 hq1 : (Fib q)ˣ) : Fib q) = 1
  rw [h1]
  ring

/-- `ρ² = -1` exactly when `q = -1`. -/
theorem rho_sq_iff (h2 : (2 : F) ≠ 0) :
    rhoU hq0 hq1 * rhoU hq0 hq1 = negU hq0 hq1 ↔ q = -1 := by
  have h1 := val_rhoU hq0 hq1
  have hr := rE_mul_self (q := q)
  have hu := isUnit_one_add_rE (q := q) hq1
  set p : Fib q := ((rhoU hq0 hq1 : (Fib q)ˣ) : Fib q) with hp
  -- `ρ² (1 + r)² = (1 - r)²`
  have hsq : p * p * ((1 + rE) * (1 + rE)) = (1 - rE) * (1 - rE) := by
    linear_combination (p * (1 + rE) + (1 - rE)) * h1
  have hval : ((rhoU hq0 hq1 * rhoU hq0 hq1 : U q) : (Fib q)ˣ).val = p * p := rfl
  constructor
  · intro h
    have h3 : p * p = -1 := by
      rw [← hval, h, val_negU]
    rw [h3] at hsq
    -- `2 + 2 q = 0`
    have h4 : (2 : Fib q) * (1 + algebraMap F (Fib q) q) = 0 := by
      linear_combination -hsq - 2 * hr
    have h5 : (2 : F) = 0 ∨ 1 + q = 0 := by
      simpa using congrArg QuadraticAlgebra.re h4
    rcases h5 with h5 | h5
    · exact absurd h5 h2
    · linear_combination h5
  · intro h
    refine Subtype.ext (Units.ext ?_)
    rw [hval, val_negU]
    have hu2 : IsUnit ((1 + rE) * (1 + rE) : Fib q) := hu.mul hu
    apply hu2.mul_left_inj.mp
    rw [hsq]
    have h6 : algebraMap F (Fib q) q = -1 := by rw [h, map_neg, map_one]
    linear_combination (2 : Fib q) * hr + (2 : Fib q) * h6

include hq0 hq1 in
/-- `⟨-1, ρ⟩` holds at least four elements, so at most `|U|/4` classes are glued; exactly four when
`q = -1`, and only then. -/
theorem card_gluing_bound [Finite F] (h2 : (2 : F) ≠ 0) :
    4 ≤ Nat.card (gluing q) ∧ (Nat.card (gluing q) = 4 ↔ q = -1) := by
  classical
  have hn1 := negU_ne_one hq0 hq1 h2
  have hr1 := rhoU_ne_one hq0 hq1 h2
  have hrn := rhoU_ne_neg hq0 hq1 h2
  have hnn := negU_mul_self hq0 hq1
  set n := negU hq0 hq1 with hn
  set p := rhoU hq0 hq1 with hp
  have hnm : n ∈ gluing q := negU_mem hq0 hq1
  have hpm : p ∈ gluing q := rhoU_mem hq0 hq1
  have hnp1 : n * p ≠ 1 := by
    intro h
    apply hrn
    calc p = n * n * p := by rw [hnn, one_mul]
      _ = n * (n * p) := mul_assoc _ _ _
      _ = n := by rw [h, mul_one]
  have hnpn : n * p ≠ n := fun h => hr1 (mul_left_cancel (a := n) (by rw [h, mul_one]))
  have hnpp : n * p ≠ p := fun h => hn1 (mul_right_cancel (b := p) (by rw [h, one_mul]))
  let s : Finset (U q) := {1, n, p, n * p}
  have hcard : s.card = 4 := by
    simp only [s]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hnpp.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hrn.symm, hnpn.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn1.symm, hr1.symm, hnp1.symm⟩
  have hsub : ∀ x ∈ s, x ∈ gluing q := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hnm
    · exact hpm
    · exact mul_mem hnm hpm
  have e : Nat.card (gluing q) = (gluing q : Set (U q)).ncard := Nat.card_coe_set_eq _
  have hsub' : (s : Set (U q)) ⊆ (gluing q : Set (U q)) := fun x hx => hsub x (by simpa using hx)
  have hle : 4 ≤ Nat.card (gluing q) := by
    rw [e, ← hcard, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub' (Set.toFinite _)
  refine ⟨hle, ?_, ?_⟩
  · -- `ρ²` lies among the four elements
    intro h4
    have heq : (s : Set (U q)) = (gluing q : Set (U q)) := by
      refine Set.eq_of_subset_of_ncard_le hsub' ?_ (Set.toFinite _)
      rw [← e, h4, Set.ncard_coe_finset, hcard]
    have hmem : p * p ∈ (s : Set (U q)) := by
      rw [heq]
      exact mul_mem hpm hpm
    have hmem' : p * p ∈ s := by simpa using hmem
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h | h | h | h
    · -- `ρ² = 1` would give `4 r = 0`
      exfalso
      have hv := val_rhoU hq0 hq1
      rw [← hp] at hv
      have hv1 : ((p : (Fib q)ˣ) : Fib q) * ((p : (Fib q)ˣ) : Fib q) = 1 := by
        have := congrArg (fun u : U q => ((u : (Fib q)ˣ) : Fib q)) h
        exact this
      have h5 : (2 : Fib q) * ((2 : Fib q) * rE) = 0 := by
        linear_combination (-(1 + rE) * (1 + rE)) * hv1 +
          (((p : (Fib q)ˣ) : Fib q) * (1 + rE) + (1 - rE)) * hv
      have h6 : (2 : F) = 0 := by
        simpa [rE] using congrArg QuadraticAlgebra.im h5
      exact h2 h6
    · exact (rho_sq_iff hq0 hq1 h2).mp h
    · exact absurd (mul_left_cancel (a := p) (h.trans (mul_one p).symm)) hr1
    · exact absurd (mul_right_cancel h) hrn
  · intro hq
    have hsq := (rho_sq_iff hq0 hq1 h2).mpr hq
    rw [← hp, ← hn] at hsq
    have hle2 : gluing q ≤ Subgroup.zpowers p := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro u (hu | hu)
      · have hun : u = n := Subtype.ext (Units.ext (hu.trans (val_negU hq0 hq1).symm))
        rw [hun, ← hsq]
        exact mul_mem (Subgroup.mem_zpowers p) (Subgroup.mem_zpowers p)
      · have hup : u = p := Subtype.ext (Units.ext
          ((isUnit_one_add_rE hq1).mul_left_inj.mp (hu.trans (val_rhoU hq0 hq1).symm)))
        rw [hup]
        exact Subgroup.mem_zpowers p
    have hord : orderOf p ≤ 4 := by
      refine orderOf_le_of_pow_eq_one (by norm_num) ?_
      calc p ^ 4 = (p * p) * (p * p) := by rw [pow_succ, pow_succ, pow_succ, pow_one]; group
        _ = 1 := by rw [hsq, hnn]
    have hc := Subgroup.card_le_of_le hle2
    rw [Nat.card_zpowers] at hc
    omega

include hq0 hq1 in
/-- When `-1` is a power of `ρ`, the subgroup `⟨-1, ρ⟩` has the order of `ρ`. -/
theorem card_gluing_of_rho (x : Fib q) (hx : x * (1 + rE) = 1 - rE) (k n : ℕ) (hk : x ^ k = -1)
    (hn : x ^ n = 1) (hn0 : 0 < n) (hm : ∀ m, 0 < m → m < n → x ^ m ≠ 1) :
    Nat.card (gluing q) = n := by
  have hp : ((rhoU hq0 hq1 : (Fib q)ˣ) : Fib q) = x :=
    (isUnit_one_add_rE hq1).mul_left_inj.mp ((val_rhoU hq0 hq1).trans hx.symm)
  have hpow : ∀ m : ℕ, ((rhoU hq0 hq1 ^ m : U q) : (Fib q)ˣ).val = x ^ m := by
    intro m
    rw [← hp]
    rfl
  have heq : gluing q = Subgroup.zpowers (rhoU hq0 hq1) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u (hu | hu)
      · have hun : u = rhoU hq0 hq1 ^ k :=
          Subtype.ext (Units.ext (hu.trans (by rw [hpow, hk])))
        rw [hun]
        exact pow_mem (Subgroup.mem_zpowers _) k
      · have hup : u = rhoU hq0 hq1 := Subtype.ext (Units.ext
          ((isUnit_one_add_rE hq1).mul_left_inj.mp (hu.trans (val_rhoU hq0 hq1).symm)))
        rw [hup]
        exact Subgroup.mem_zpowers _
    · exact (Subgroup.zpowers_le).mpr (rhoU_mem hq0 hq1)
  rw [heq, Nat.card_zpowers, orderOf_eq_iff hn0]
  refine ⟨Subtype.ext (Units.ext (by rw [hpow, hn]; rfl)), fun m hlt hpos h => ?_⟩
  apply hm m hpos hlt
  rw [← hpow, h]
  rfl

/-! ### The schemes -/

section Schemes

variable {S : Type*} [CommRing S]

theorem realize_KM (k m : S) : (realize [Step.kick k, Step.move m] : Matrix (Fin 2) (Fin 2) S) =
    !![1 + m * k, m; k, 1] := by
  simp only [realize_cons, realize_nil, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
    one_mul, Matrix.mul_fin_two]
  refine mat2_ext ?_ ?_ ?_ ?_ <;> ring

theorem realize_MK (k m : S) : (realize [Step.move m, Step.kick k] : Matrix (Fin 2) (Fin 2) S) =
    !![1, m; k, 1 + k * m] := by
  simp only [realize_cons, realize_nil, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
    one_mul, Matrix.mul_fin_two]
  refine mat2_ext ?_ ?_ ?_ ?_ <;> ring

theorem realize_KMK (k k' m : S) :
    (realize [Step.kick k, Step.move m, Step.kick k'] : Matrix (Fin 2) (Fin 2) S) =
      !![1 + m * k, m; k' * (1 + m * k) + k, k' * m + 1] := by
  simp only [realize_cons, realize_nil, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
    one_mul, Matrix.mul_fin_two]
  refine mat2_ext ?_ ?_ ?_ ?_ <;> ring

theorem realize_MKM (k m m' : S) :
    (realize [Step.move m, Step.kick k, Step.move m'] : Matrix (Fin 2) (Fin 2) S) =
      !![1 + m' * k, m + m' * (1 + k * m); k, 1 + k * m] := by
  simp only [realize_cons, realize_nil, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.mat,
    one_mul, Matrix.mul_fin_two]
  refine mat2_ext ?_ ?_ ?_ ?_ <;> ring

variable {F : Type*} [Field F] {A B : F → S} {f : Step F → Step S}

/-- The schemes have the phase `2 + A B`. -/
theorem phase_schemes (hA : A 2⁻¹ + A 2⁻¹ = A 1) (hB : B 2⁻¹ + B 2⁻¹ = B 1)
    (hk : ∀ w, f (Step.kick w) = Step.kick (A w)) (hm : ∀ w, f (Step.move w) = Step.move (B w))
    {w : Score F} (hw : w ∈ schemes F) : phase (realize (w.map f)) = 2 + A 1 * B 1 := by
  simp only [schemes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, hk, hm, phase, Matrix.trace_fin_two]
  · rw [realize_KM]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one]
    ring
  · rw [realize_MK]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one]
    ring
  · rw [realize_KMK, ← hA]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one]
    ring
  · rw [realize_MKM, ← hB]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one]
    ring

/-- The schemes have a vector with `det[v | L v] = A`. -/
theorem cyclic_schemes (hA : A 2⁻¹ + A 2⁻¹ = A 1)
    (hk : ∀ w, f (Step.kick w) = Step.kick (A w)) (hm : ∀ w, f (Step.move w) = Step.move (B w))
    {w : Score F} (hw : w ∈ schemes F) :
    ∃ v, (cyclicMatrix (realize (w.map f) : Matrix (Fin 2) (Fin 2) S) v).det = A 1 := by
  simp only [schemes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, hk, hm]
  · refine ⟨![1, 0], ?_⟩
    rw [realize_KM]
    simp [cyclicMatrix, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨![1, 0], ?_⟩
    rw [realize_MK]
    simp [cyclicMatrix, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨![1, A 2⁻¹], ?_⟩
    rw [realize_KMK, ← hA]
    simp [cyclicMatrix, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · refine ⟨![1, 0], ?_⟩
    rw [realize_MKM]
    simp [cyclicMatrix, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Each scheme has `A` or `B` as an entry off the diagonal. -/
theorem offdiag_schemes (hk : ∀ w, f (Step.kick w) = Step.kick (A w))
    (hm : ∀ w, f (Step.move w) = Step.move (B w)) {w : Score F} (hw : w ∈ schemes F) :
    (realize (w.map f) : Matrix (Fin 2) (Fin 2) S) 0 1 = B 1 ∨
      (realize (w.map f) : Matrix (Fin 2) (Fin 2) S) 1 0 = A 1 := by
  simp only [schemes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, hk, hm]
  · rw [realize_KM]; exact Or.inl rfl
  · rw [realize_MK]; exact Or.inl rfl
  · rw [realize_KMK]; exact Or.inl rfl
  · rw [realize_MKM]; exact Or.inr rfl

end Schemes

theorem half_add {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a : F) : 2⁻¹ * a + 2⁻¹ * a = a := by
  field_simp
  ring

/-- The stencils of the face form. -/
theorem face_hyps (h2 : (2 : F) ≠ 0) (κ ℓ : F) :
    (LaurentPolynomial.C (2⁻¹ * κ) + LaurentPolynomial.C (2⁻¹ * κ) =
      (LaurentPolynomial.C (1 * κ) : LaurentPolynomial F)) ∧
    (LaurentPolynomial.C (-(2⁻¹ * ℓ)) * stencilG F + LaurentPolynomial.C (-(2⁻¹ * ℓ)) * stencilG F =
      LaurentPolynomial.C (-(1 * ℓ)) * stencilG F) := by
  constructor
  · rw [← map_add, half_add h2, one_mul]
  · rw [← add_mul, ← map_add, ← neg_add, half_add h2, one_mul]

/-- The stencils of the link form. -/
theorem link_hyps (h2 : (2 : F) ≠ 0) (κ ℓ : F) :
    (LaurentPolynomial.C (2⁻¹ * κ) * diffDs F + LaurentPolynomial.C (2⁻¹ * κ) * diffDs F =
      (LaurentPolynomial.C (1 * κ) * diffDs F : LaurentPolynomial F)) ∧
    (LaurentPolynomial.C (-(2⁻¹ * ℓ)) * diffD F + LaurentPolynomial.C (-(2⁻¹ * ℓ)) * diffD F =
      LaurentPolynomial.C (-(1 * ℓ)) * diffD F) := by
  constructor
  · rw [← add_mul, ← map_add, half_add h2, one_mul]
  · rw [← add_mul, ← map_add, ← neg_add, half_add h2, one_mul]

theorem phase_face (h2 : (2 : F) ≠ 0) (κ ℓ : F) {w : Score F} (hw : w ∈ schemes F) :
    phase (realize (w.map (faceStep κ ℓ))) = phaseT (κ * ℓ) := by
  rw [phase_schemes (A := fun w => LaurentPolynomial.C (w * κ))
    (B := fun w => LaurentPolynomial.C (-(w * ℓ)) * stencilG F) (f := faceStep κ ℓ)
    (face_hyps h2 κ ℓ).1 (face_hyps h2 κ ℓ).2 (fun _ => rfl) (fun _ => rfl) hw, phaseT]
  simp only [one_mul, map_neg, map_mul]
  ring

theorem phase_link (h2 : (2 : F) ≠ 0) (κ ℓ : F) {w : Score F} (hw : w ∈ schemes F) :
    phase (realize (w.map (linkStep κ ℓ))) = phaseT (κ * ℓ) := by
  rw [phase_schemes (A := fun w => LaurentPolynomial.C (w * κ) * diffDs F)
    (B := fun w => LaurentPolynomial.C (-(w * ℓ)) * diffD F) (f := linkStep κ ℓ)
    (link_hyps h2 κ ℓ).1 (link_hyps h2 κ ℓ).2 (fun _ => rfl) (fun _ => rfl) hw, phaseT, stencilG_eq]
  simp only [one_mul, map_neg, map_mul]
  ring

theorem cyclic_face (h2 : (2 : F) ≠ 0) {κ : F} (hκ : κ ≠ 0) (ℓ : F) {w : Score F}
    (hw : w ∈ schemes F) : ∃ v, IsUnit (cyclicMatrix (realize (w.map (faceStep κ ℓ)) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det := by
  obtain ⟨v, hv⟩ := cyclic_schemes (A := fun w => LaurentPolynomial.C (w * κ))
    (B := fun w => LaurentPolynomial.C (-(w * ℓ)) * stencilG F) (f := faceStep κ ℓ)
    (face_hyps h2 κ ℓ).1 (fun _ => rfl) (fun _ => rfl) hw
  refine ⟨v, ?_⟩
  rw [hv, one_mul]
  exact (IsUnit.mk0 κ hκ).map LaurentPolynomial.C

/-! ### The theorems -/

/-- **T8** (the curve of the leapfrog phase). -/
@[ledger "T8"]
theorem leapfrogCurve : Statement.leapfrogCurve := by
  intro K _ q hq0 hq1
  refine ⟨?_, ?_, ?_⟩
  · intro s hs0 hs1 hsq
    have h1 : (1 : K) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h2 : s - q ≠ 0 := sub_ne_zero.mpr hsq
    refine ⟨div_ne_zero (mul_ne_zero hq0 h1) (mul_ne_zero hs0 h2),
      div_ne_zero (mul_ne_zero hs0 h1) h2, ?_, ?_⟩
    · field_simp
      ring
    · rw [div_eq_one_iff_eq (mul_ne_zero hs0 h2)]
      constructor
      · intro h
        linear_combination -h
      · intro h
        linear_combination -h
  · intro x l hx hl hc hx1
    have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    -- the curve in polynomial form
    have hE : x * ((l - 1) * (l - 1)) = q * ((x - 1) * (x - 1)) * l := by
      field_simp at hc
      linear_combination hc
    intro s
    have hl' : l = 1 + (x - 1) * s := by
      simp only [s]
      field_simp
      ring
    have hE' : x * (s * s) = q * (1 + (x - 1) * s) := by
      have hl2 : l - 1 = (x - 1) * s := by rw [hl']; ring
      rw [hl2] at hE
      apply mul_left_cancel₀ (mul_ne_zero hd hd)
      rw [← hl']
      linear_combination hE
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hE'
      exact hq0 (by linear_combination -hE')
    have hs1 : s ≠ 1 := by
      intro h0
      apply hq1
      rw [h0] at hE'
      have hxx : x * (1 - q) = 0 := by linear_combination hE'
      have := (mul_eq_zero.mp hxx).resolve_left hx
      linear_combination -this
    have hsq : s ≠ q := by
      intro h0
      apply hq1
      rw [h0] at hE'
      have hxx : q * (1 - q) = 0 := by linear_combination -hE'
      have := (mul_eq_zero.mp hxx).resolve_left hq0
      linear_combination -this
    have h2 : s - q ≠ 0 := sub_ne_zero.mpr hsq
    have hxs : x * (s * (s - q)) = q * (1 - s) := by linear_combination hE'
    refine ⟨hs0, hs1, hsq, ?_, ?_⟩
    · rw [eq_div_iff (mul_ne_zero hs0 h2)]
      exact hxs
    · rw [eq_div_iff h2, hl']
      linear_combination hxs
  · intro l hl hc
    have h0 : (2 : K) - 1 - 1⁻¹ = 0 := by norm_num
    rw [h0, mul_zero, sub_zero] at hc
    have h1 : (l - 1) * (l - 1) = 0 := by
      field_simp at hc
      linear_combination hc
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)

/-- **T8** (the classes of the leapfrog phase). -/
@[ledger "T8"]
theorem leapfrogClasses : Statement.leapfrogClasses := by
  intro F _ q h2 hq0 hq1
  refine ⟨nonSquareDisc_phase hq0 hq1 h2, phase_gluedLaw, phase_ungluedLaw, classMap hq0 hq1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L L' ht ht'
    exact classMap_eq_iff hq0 hq1 h2 ht ht'
  · intro w
    obtain ⟨L, ht, hc⟩ := exists_law hq0 hq1 h2 w
    exact ⟨L, ht, classMap_eq hq0 hq1 h2 ht hc⟩
  · intro L ht
    exact classOf_none_iff hq0 hq1 (classMap_spec hq0 hq1 ht)
  · intro L ht
    exact classMap_eq_some_one_iff hq0 hq1 h2 ht
  · intro L ht
    have hi : phase L⁻¹ = phaseT q := by rw [phase_inv, ht]
    exact classMap_eq hq0 hq1 h2 hi ((classMap_spec hq0 hq1 ht).inv hq0 hq1)
  · intro y z hz
    have hy : y * y ≠ q := by
      intro h0
      have hn := (z.isUnit.map (QuadraticAlgebra.norm : Fib q →* F)).ne_zero
      apply hn
      change QuadraticAlgebra.norm (z : Fib q) = 0
      rw [hz, QuadraticAlgebra.norm_def]
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_omega,
        QuadraticAlgebra.im_omega, rE, QuadraticAlgebra.algebraMap_re,
        QuadraticAlgebra.algebraMap_im]
      linear_combination h0
    have hzu : z = (isUnit_y_add_rE hy).unit := Units.ext hz
    rw [hzu]
    exact classMap_eq hq0 hq1 h2 (phase_gluedLaw y) (classOf_gluedLaw hq0 hq1 hy)
  · exact classMap_eq hq0 hq1 h2 phase_ungluedLaw (classOf_ungluedLaw hq0 hq1)

/-- **T8** (the count). -/
@[ledger "T8"]
theorem leapfrogCount : Statement.leapfrogCount := by
  intro F _ _ q h2 hq0 hq1
  refine ⟨?_, card_U_of_square hq0 h2, card_U_of_not_square hq0 h2,
    card_gluing_bound hq0 hq1 h2⟩
  let f : Quotient (processingSetoid (phaseT q)) → Option (U q ⧸ gluing q) :=
    Quotient.lift (fun L => classMap hq0 hq1 L.1)
      (fun L L' h => (classMap_eq_iff hq0 hq1 h2 L.2 L'.2).mpr h)
  have hbij : Function.Bijective f := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn with
      | h L =>
        induction b using Quotient.inductionOn with
        | h L' =>
          intro h
          exact Quotient.sound ((classMap_eq_iff hq0 hq1 h2 L.2 L'.2).mp h)
    · intro w
      obtain ⟨L, ht, hc⟩ := exists_law hq0 hq1 h2 w
      exact ⟨Quotient.mk _ ⟨L, ht⟩, classMap_eq hq0 hq1 h2 ht hc⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Finite.card_option]
  have h1 := Subgroup.card_mul_index (gluing q)
  have h3 : (gluing q).index = Nat.card (U q ⧸ gluing q) := rfl
  rw [h3] at h1
  have hpos : 0 < Nat.card (gluing q) := Nat.card_pos
  rw [← h1, Nat.mul_div_cancel_left _ hpos]

/-- **T8** (the split node). -/
@[ledger "T8"]
theorem leapfrogSplit : Statement.leapfrogSplit := by
  intro F _ q h h2 hq0 hq1 hh
  refine ⟨MulEquiv.ofBijective (splitHom h hh) (splitHom_bijective hq0 h2 h hh),
    fun u => rfl, ?_⟩
  have e : (MulEquiv.ofBijective (splitHom h hh)
      (splitHom_bijective hq0 h2 h hh)).toMonoidHom = splitHom h hh :=
    MonoidHom.ext fun _ => rfl
  rw [e]
  exact splitHom_gluing hq0 hq1 h hh

/-- **T8** (the schemes). -/
@[ledger "T8"]
theorem leapfrogSchemes : Statement.leapfrogSchemes := by
  intro F _ κ ℓ h2 hq0 hq1 w hw
  have hκ : κ ≠ 0 := left_ne_zero_of_mul hq0
  have ht := phase_face h2 κ ℓ hw
  have ht' := phase_link h2 κ ℓ hw
  refine ⟨ht, ?_, ht', ?_⟩
  · obtain ⟨v, hv⟩ := cyclic_face h2 hκ ℓ hw
    exact conj_of_classOf hq0 hq1 h2 (classOf_companionLaw hq0 hq1)
      (classOf_of_cyclic hq0 hq1 h2 ht hv)
  · have h1 := classMap_spec hq0 hq1 ht'
    have h3 := (classOf_none_iff hq0 hq1 h1).mpr (link_at_zero κ ℓ w)
    rw [h3] at h1
    exact conj_of_classOf hq0 hq1 h2 (classOf_ungluedLaw hq0 hq1) h1

end Artform.Scores.Leapfrog
