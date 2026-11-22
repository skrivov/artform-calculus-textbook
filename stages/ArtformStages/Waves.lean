import ArtformStages.Maxwell

/-!
# Light is a wave

Every orbit of Pair obeys the wave equation in steps, and on the torus the light across the
gauge is a sum of plane waves, each turning at its own angle per step (finding 443 of the research
ledger on a layered universe):

* `pair_wave`, `pair_wave_E` (LW1): `A'' - A' = (A' - A) - L S A'`, and the same for `E` with
  `S L`, over any commutative ring;
* `transverse_level` (LW2): a level of `C Cᵀ` on the squares gives, through `Cᵀ`, a level of the
  kick `Cᵀ diag κ C` on the lines at `κ` times its value;
* `Board.incidence_mulVec`, `Board.incidence_transpose_mulVec` (LW3): on every board, `C A` sums
  `A` round a square, and `Cᵀ y` is `y` at the square where a line runs along its turn less `y`
  where it runs against it;
* `torus_laplacian` (LW4): on the torus `C Cᵀ` is the five-point stencil;
* `stencil_plane_wave` (LW5): the plane waves are its levels, at `4 - 2 cos θ₁ - 2 cos θ₂`;
* `torus_transverse_wave` (LW6): so the real part of a plane wave gives a level of the kick;
* `cos_orbit` (LW7): with `μ = 2 - 2 cos ω`, `cos (k ω + φ)` obeys the recurrence of one place.
-/

open Matrix

open scoped Real

namespace Artform.Stages

section Wave

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- LW1. Every orbit of Pair obeys the wave equation in steps: `A'' - A' = (A' - A) - L S A'`. -/
theorem pair_wave (S L : Matrix n n R) (x : LightState R n) :
    (pair S L (pair S L x)).1 - (pair S L x).1 =
      ((pair S L x).1 - x.1) - L *ᵥ (S *ᵥ (pair S L x).1) := by
  obtain ⟨A, E⟩ := x
  simp only [pair, mulVec_add, mulVec_sub]
  abel

/-- LW1. The same for `E`: `E'' - E' = (E' - E) - S L E'`. -/
theorem pair_wave_E (S L : Matrix n n R) (x : LightState R n) :
    (pair S L (pair S L x)).2 - (pair S L x).2 =
      ((pair S L x).2 - x.2) - S *ᵥ (L *ᵥ (pair S L x).2) := by
  obtain ⟨A, E⟩ := x
  simp only [pair, mulVec_add, mulVec_sub]
  abel

/-- LW2. A level of `C Cᵀ` on the squares gives, through `Cᵀ`, a level of the kick on the lines. -/
theorem transverse_level {f : Type*} [Fintype f] [DecidableEq f] (C : Matrix f n R) (κ μ : R)
    (ψ : f → R) (h : (C * Cᵀ) *ᵥ ψ = μ • ψ) :
    (Cᵀ * diagonal (fun _ : f => κ) * C) *ᵥ (Cᵀ *ᵥ ψ) = (κ * μ) • (Cᵀ *ᵥ ψ) := by
  have hD : ∀ u : f → R, diagonal (fun _ : f => κ) *ᵥ u = κ • u := by
    intro u
    funext i
    simp [mulVec_diagonal]
  calc (Cᵀ * diagonal (fun _ : f => κ) * C) *ᵥ (Cᵀ *ᵥ ψ)
      = Cᵀ *ᵥ (diagonal (fun _ : f => κ) *ᵥ ((C * Cᵀ) *ᵥ ψ)) := by
        simp only [mulVec_mulVec, Matrix.mul_assoc]
    _ = (κ * μ) • (Cᵀ *ᵥ ψ) := by rw [h, hD, smul_smul, mulVec_smul]

end Wave

/-- LW3. On every board, `C A` at a square is `A` summed round it, each side with its sign. -/
theorem Board.incidence_mulVec {f e v : Type*} [Fintype e] [DecidableEq e] (B : Board f e v)
    (A : e → ℝ) (σ : f) :
    (B.incidence *ᵥ A) σ = ∑ i, Board.turnSign (B.along σ i) * A (B.side σ i) := by
  simp only [mulVec, dotProduct, Board.incidence_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- LW3. On every board, `Cᵀ y` at a line is `y` at the square where the line runs along its turn
less `y` at the square where it runs against it. -/
theorem Board.incidence_transpose_mulVec {f e v : Type*} [Fintype f] [DecidableEq e]
    (B : Board f e v) (y : f → ℝ) {ℓ : e} {σ τ : f} {i j : Fin 4} (hσ : B.side σ i = ℓ)
    (hσa : B.along σ i = true) (hτ : B.side τ j = ℓ) (hτa : B.along τ j = false) :
    (B.incidenceᵀ *ᵥ y) ℓ = y σ - y τ := by
  simp only [mulVec, dotProduct, transpose_apply, Board.incidence_apply, Finset.sum_mul, ite_mul,
    zero_mul]
  rw [← Fintype.sum_prod_type']
  have hne : ((σ, i) : f × Fin 4) ≠ (τ, j) := by
    intro hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [hσa] at hτa
    exact Bool.noConfusion hτa
  rw [Fintype.sum_eq_add (σ, i) (τ, j) hne]
  · simp [hσ, hτ, hσa, hτa, Board.turnSign]
    ring
  · rintro ⟨ρ, a⟩ ⟨h1, h2⟩
    refine ite_eq_right fun hρ => ?_
    dsimp only at hρ
    cases hb : B.along ρ a
    · obtain ⟨h', h''⟩ := B.flag_eq (hρ.trans hτ.symm) (hb.trans hτa.symm)
      exact h2 (Prod.ext h' h'')
    · obtain ⟨h', h''⟩ := B.flag_eq (hρ.trans hσ.symm) (hb.trans hσa.symm)
      exact h1 (Prod.ext h' h'')

/-- The five-point stencil on the squares of the torus. -/
def stencil {n m : ℕ} {R : Type*} [Ring R] (ψ : ZMod n × ZMod m → R) (w : ZMod n × ZMod m) : R :=
  4 * ψ w - ψ (w + (1, 0)) - ψ (w - (1, 0)) - ψ (w + (0, 1)) - ψ (w - (0, 1))

section Torus

variable (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]

theorem torus_transpose_mulVec_zero (y : ZMod n × ZMod m → ℝ) (w : ZMod n × ZMod m) :
    ((torus n m).incidenceᵀ *ᵥ y) (w, 0) = y w - y (w - (0, 1)) :=
  (torus n m).incidence_transpose_mulVec y (σ := w) (i := 0) (τ := w - (0, 1)) (j := 2)
    (by simp [torus]) (by simp [torus]) (by simp [torus]) (by simp [torus])

theorem torus_transpose_mulVec_one (y : ZMod n × ZMod m → ℝ) (w : ZMod n × ZMod m) :
    ((torus n m).incidenceᵀ *ᵥ y) (w, 1) = y (w - (1, 0)) - y w :=
  (torus n m).incidence_transpose_mulVec y (σ := w - (1, 0)) (i := 1) (τ := w) (j := 3)
    (by simp [torus]) (by simp [torus]) (by simp [torus]) (by simp [torus])

/-- LW4. On the torus, `C Cᵀ` is the five-point stencil. -/
theorem torus_laplacian (ψ : ZMod n × ZMod m → ℝ) :
    ((torus n m).incidence * (torus n m).incidenceᵀ) *ᵥ ψ = stencil ψ := by
  funext σ
  have s0 : (torus n m).side σ 0 = (σ, 0) := by simp [torus]
  have s1 : (torus n m).side σ 1 = (σ + (1, 0), 1) := by simp [torus]
  have s2 : (torus n m).side σ 2 = (σ + (0, 1), 0) := by simp [torus]
  have s3 : (torus n m).side σ 3 = (σ, 1) := by simp [torus]
  have a0 : (torus n m).along σ 0 = true := by simp [torus]
  have a1 : (torus n m).along σ 1 = true := by simp [torus]
  have a2 : (torus n m).along σ 2 = false := by simp [torus]
  have a3 : (torus n m).along σ 3 = false := by simp [torus]
  rw [← mulVec_mulVec, Board.incidence_mulVec, Fin.sum_univ_four, s0, s1, s2, s3, a0, a1, a2, a3]
  simp only [torus_transpose_mulVec_zero, torus_transpose_mulVec_one, add_sub_cancel_right,
    Board.turnSign, stencil]
  norm_num
  ring

end Torus

/-- The plane wave of wave numbers `p` and `q` on the squares of the torus. -/
noncomputable def planeWave {n m : ℕ} [NeZero n] [NeZero m] (p : ZMod n) (q : ZMod m)
    (w : ZMod n × ZMod m) : ℂ :=
  ZMod.stdAddChar (p * w.1) * ZMod.stdAddChar (q * w.2)

theorem planeWave_shift_one {n m : ℕ} [NeZero n] [NeZero m] (p : ZMod n) (q : ZMod m)
    (w : ZMod n × ZMod m) : planeWave p q (w + (1, 0)) = planeWave p q w * ZMod.stdAddChar p := by
  simp only [planeWave, Prod.fst_add, Prod.snd_add, add_zero, mul_add, mul_one,
    AddChar.map_add_eq_mul]
  ring

theorem planeWave_shift_two {n m : ℕ} [NeZero n] [NeZero m] (p : ZMod n) (q : ZMod m)
    (w : ZMod n × ZMod m) : planeWave p q (w + (0, 1)) = planeWave p q w * ZMod.stdAddChar q := by
  simp only [planeWave, Prod.fst_add, Prod.snd_add, add_zero, mul_add, mul_one,
    AddChar.map_add_eq_mul]
  ring

/-- A character and its value at the opposite add up to twice the cosine of its angle. -/
theorem stdAddChar_add_neg {N : ℕ} [NeZero N] (a : ZMod N) :
    ZMod.stdAddChar a + ZMod.stdAddChar (-a) =
      ((2 * Real.cos (2 * π * a.val / N) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_neg]
  have hx : 2 * (π : ℂ) * Complex.I * (a.val : ℂ) / (N : ℂ) =
      ((2 * π * a.val / N : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hx, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  push_cast
  ring

/-- LW5. The plane wave is a level of the five-point stencil at `4 - 2 cos θ₁ - 2 cos θ₂`. -/
theorem stencil_plane_wave {n m : ℕ} [NeZero n] [NeZero m] (p : ZMod n) (q : ZMod m) :
    stencil (planeWave p q) = fun w =>
      ((4 - 2 * Real.cos (2 * π * p.val / n) - 2 * Real.cos (2 * π * q.val / m) : ℝ) : ℂ) *
        planeWave p q w := by
  funext w
  have e1 := planeWave_shift_one p q w
  have e2 : planeWave p q (w - (1, 0)) = planeWave p q w * ZMod.stdAddChar (-p) := by
    have h := planeWave_shift_one p q (w - (1, 0))
    rw [sub_add_cancel] at h
    rw [h, mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  have e3 := planeWave_shift_two p q w
  have e4 : planeWave p q (w - (0, 1)) = planeWave p q w * ZMod.stdAddChar (-q) := by
    have h := planeWave_shift_two p q (w - (0, 1))
    rw [sub_add_cancel] at h
    rw [h, mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  have hp := stdAddChar_add_neg p
  have hq := stdAddChar_add_neg q
  rw [stencil, e1, e2, e3, e4]
  push_cast at hp hq ⊢
  linear_combination (-(planeWave p q w)) * hp - planeWave p q w * hq

/-- LW6. On the torus with one `κ`, the real part of a plane wave gives a level of the kick on the
lines, across the gauge, at `κ (4 - 2 cos θ₁ - 2 cos θ₂)`. -/
theorem torus_transverse_wave (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]
    (p : ZMod n) (q : ZMod m) (κ : ℝ) :
    ((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) * (torus n m).incidence) *ᵥ
        ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re) =
      (κ * (4 - 2 * Real.cos (2 * π * p.val / n) - 2 * Real.cos (2 * π * q.val / m))) •
        ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re) := by
  apply transverse_level
  rw [torus_laplacian]
  funext w
  have h := congrFun (stencil_plane_wave p q) w
  have hre := congrArg Complex.re h
  simp only [stencil, Complex.sub_re, Complex.re_ofReal_mul] at hre
  simp only [stencil, Pi.smul_apply, smul_eq_mul]
  rw [← hre]
  simp

/-- LW7. If `μ = 2 - 2 cos ω`, then `a k = cos (k ω + φ)` obeys
`a (k + 2) = (2 - μ) a (k + 1) - a k`: a level of `L S` at `μ` carries a sampled wave of `ω` per
step. -/
theorem cos_orbit (ω φ μ : ℝ) (hμ : μ = 2 - 2 * Real.cos ω) (k : ℕ) :
    Real.cos ((k + 2) * ω + φ) = (2 - μ) * Real.cos ((k + 1) * ω + φ) - Real.cos (k * ω + φ) := by
  subst hμ
  have h1 : ((k : ℝ) + 2) * ω + φ = ((k + 1) * ω + φ) + ω := by ring
  have h2 : (k : ℝ) * ω + φ = ((k + 1) * ω + φ) - ω := by ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

end Artform.Stages
