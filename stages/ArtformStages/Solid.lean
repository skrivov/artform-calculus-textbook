import ArtformStages.Maxwell

/-!
# Light in a solid of cubes

The cubic torus of side `n` has its corners at the points of `(ℤ/n)³`, a line `(w, i)` from `w`
to `w + e i`, a face `(w, k)` across each direction `k`, and a cube at each corner. Its three maps,
the gauge `G` (lines by corners), the incidence `C` (faces by lines) and the boundary `V` (cubes by
faces), close up at both steps, so Pair on it is the electrodynamics of finding 441 in three
dimensions, with no magnetic charge (finding 442 of the research ledger on a layered universe):

* `cubeGauge_mulVec`, `cubeIncidence_mulVec`, `cubeBoundary_mulVec` (SO1): the maps read as
  differences along a line, sums round a face and sums out of a cube;
* `cube_incidence_mul_gauge` (SO2): `C G = 0`;
* `cube_boundary_mul_incidence`, `cube_div_curl` (SO3): `V C = 0`, so `B = C A` has no magnetic
  charge;
* `faraday_keeps_magnetic_charge` (SO4): where `V C = 0`, Faraday's step keeps `V B` for every `B`;
* `cube_gauss_kept_iff`, `cube_divergence_sum` (SO5): Gauss's law with continuity, and no net
  charge, on the cubic torus.
-/

open Matrix

namespace Artform.Stages

/-- SO4. Where `V C = 0`, Faraday's step `B' = B - C L E'` keeps the magnetic charge `V B` of every
field `B` on the faces. -/
theorem faraday_keeps_magnetic_charge {c f m R : Type*} [Fintype f] [Fintype m] [CommRing R]
    (V : Matrix c f R) (C : Matrix f m R) (hVC : V * C = 0) (L : Matrix m m R) (B : f → R)
    (E : m → R) : V *ᵥ (B - (C * L) *ᵥ E) = V *ᵥ B := by
  rw [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, hVC, Matrix.zero_mul, zero_mulVec, sub_zero]

variable (n : ℕ)

/-- A corner of the cubic torus of side `n`: a point of `(ℤ/n)³`. -/
abbrev CubePoint := Fin 3 → ZMod n

/-- The step along the direction `k`. -/
def cubeStep (k : Fin 3) : CubePoint n := Pi.single k 1

/-- The gauge of the cubic torus, lines by corners: the line `(w, i)` runs from `w` to
`w + cubeStep n i`. -/
def cubeGauge : Matrix (CubePoint n × Fin 3) (CubePoint n) ℝ :=
  Matrix.of fun ℓ w => (if ℓ.1 + cubeStep n ℓ.2 = w then 1 else 0) - (if ℓ.1 = w then 1 else 0)

/-- The incidence of the cubic torus, faces by lines: the face `(w, k)` across the direction `k`
has the sides `(w, k + 1)` and `(w + e (k + 1), k + 2)` along its turn and `(w + e (k + 2), k + 1)`
and `(w, k + 2)` against it. -/
def cubeIncidence : Matrix (CubePoint n × Fin 3) (CubePoint n × Fin 3) ℝ :=
  Matrix.of fun σ ℓ =>
    ((if ℓ = (σ.1, σ.2 + 1) then 1 else 0) +
        (if ℓ = (σ.1 + cubeStep n (σ.2 + 1), σ.2 + 2) then 1 else 0)) -
      ((if ℓ = (σ.1 + cubeStep n (σ.2 + 2), σ.2 + 1) then 1 else 0) +
        (if ℓ = (σ.1, σ.2 + 2) then 1 else 0))

/-- The boundary of the cubic torus, cubes by faces: the cube `w` has the face `(w + e k, k)`
outward and the face `(w, k)` inward, for each direction `k`. -/
def cubeBoundary : Matrix (CubePoint n) (CubePoint n × Fin 3) ℝ :=
  Matrix.of fun c σ => (if σ.1 = c + cubeStep n σ.2 then 1 else 0) - (if σ.1 = c then 1 else 0)

variable [NeZero n]

/-- SO1. `G g` at the line `(w, i)` is `g (w + e i) - g w`. -/
theorem cubeGauge_mulVec (g : CubePoint n → ℝ) (ℓ : CubePoint n × Fin 3) :
    (cubeGauge n *ᵥ g) ℓ = g (ℓ.1 + cubeStep n ℓ.2) - g ℓ.1 := by
  simp [cubeGauge, mulVec, dotProduct, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- SO1. `C A` at the face `(w, k)` is `A` summed round it with the signs of its turn. -/
theorem cubeIncidence_mulVec (A : CubePoint n × Fin 3 → ℝ) (σ : CubePoint n × Fin 3) :
    (cubeIncidence n *ᵥ A) σ = A (σ.1, σ.2 + 1) + A (σ.1 + cubeStep n (σ.2 + 1), σ.2 + 2) -
      A (σ.1 + cubeStep n (σ.2 + 2), σ.2 + 1) - A (σ.1, σ.2 + 2) := by
  simp [cubeIncidence, mulVec, dotProduct, add_mul, sub_mul, ite_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- SO1. `V B` at the cube `w` is `B` summed out of it. -/
theorem cubeBoundary_mulVec (B : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) :
    (cubeBoundary n *ᵥ B) c = ∑ k, (B (c + cubeStep n k, k) - B (c, k)) := by
  simp only [cubeBoundary, mulVec, dotProduct, Matrix.of_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  simp [Finset.sum_ite_eq']

/-- The curl of a gradient is `0`. -/
theorem cube_curl_grad (g : CubePoint n → ℝ) : cubeIncidence n *ᵥ (cubeGauge n *ᵥ g) = 0 := by
  funext σ
  rw [cubeIncidence_mulVec]
  simp only [cubeGauge_mulVec, Pi.zero_apply]
  rw [add_right_comm σ.1 (cubeStep n (σ.2 + 2)) (cubeStep n (σ.2 + 1))]
  ring

/-- SO2. `C G = 0`: the edge of a face closes up. -/
theorem cube_incidence_mul_gauge : cubeIncidence n * cubeGauge n = 0 := by
  ext σ w
  have h := congrFun (cube_curl_grad n (Pi.single w 1)) σ
  rw [mulVec_mulVec] at h
  simpa [mulVec, dotProduct, Pi.single_apply] using h

/-- SO3. The divergence of a curl is `0`: every `B = C A` has no magnetic charge. -/
theorem cube_div_curl (A : CubePoint n × Fin 3 → ℝ) :
    cubeBoundary n *ᵥ (cubeIncidence n *ᵥ A) = 0 := by
  funext c
  have e1 : (0 : Fin 3) + 1 = 1 := by decide
  have e2 : (0 : Fin 3) + 2 = 2 := by decide
  have e3 : (1 : Fin 3) + 1 = 2 := by decide
  have e4 : (1 : Fin 3) + 2 = 0 := by decide
  have e5 : (2 : Fin 3) + 1 = 0 := by decide
  have e6 : (2 : Fin 3) + 2 = 1 := by decide
  rw [cubeBoundary_mulVec]
  simp only [cubeIncidence_mulVec, Fin.sum_univ_three, Pi.zero_apply, e1, e2, e3, e4, e5, e6]
  rw [add_right_comm c (cubeStep n 1) (cubeStep n 0),
    add_right_comm c (cubeStep n 2) (cubeStep n 0), add_right_comm c (cubeStep n 2) (cubeStep n 1)]
  ring

/-- SO3. `V C = 0`: the faces of a cube close up. -/
theorem cube_boundary_mul_incidence : cubeBoundary n * cubeIncidence n = 0 := by
  ext c ℓ
  have h := congrFun (cube_div_curl n (Pi.single ℓ 1)) c
  rw [mulVec_mulVec] at h
  simpa [mulVec, dotProduct, Pi.single_apply] using h

/-- SO5. On the cubic torus, Pair with a current keeps Gauss's law exactly when the charge moves by
continuity. -/
theorem cube_gauss_kept_iff (K L : Matrix (CubePoint n × Fin 3) (CubePoint n × Fin 3) ℝ)
    (J : CubePoint n × Fin 3 → ℝ) (ρ ρ' : CubePoint n → ℝ)
    (hρ : ∃ E₀, divergence (cubeGauge n) E₀ = ρ) :
    (∀ A E, divergence (cubeGauge n) E = ρ → divergence (cubeGauge n)
        (pairWith ((cubeIncidence n)ᵀ * K * cubeIncidence n) L J (A, E)).2 = ρ') ↔
      ρ' = ρ - divergence (cubeGauge n) J :=
  gauss_kept_iff _ _ K L (cube_incidence_mul_gauge n) J ρ ρ' hρ

/-- SO5. On the cubic torus the divergence of every `E` sums to `0` over the corners. -/
theorem cube_divergence_sum (E : CubePoint n × Fin 3 → ℝ) :
    ∑ w, divergence (cubeGauge n) E w = 0 := by
  simp only [divergence, Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero, mulVec, dotProduct,
    transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [← Finset.sum_mul]
  simp [cubeGauge, Finset.sum_sub_distrib]

end Artform.Stages
