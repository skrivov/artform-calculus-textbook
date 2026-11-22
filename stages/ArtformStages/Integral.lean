import ArtformStages.Waves

/-!
# Maxwell's equations in integral form

Over a set of cells, the laws of finding 441 become the laws of Maxwell in integral form: the
flux of `E` out of a set of corners is its charge, `B = C A` summed over a set of squares is the
circulation of `A` round its edge, and so in one step the flux of `B` changes by minus the
circulation of the electric field and the charge by minus the current out (finding 445 of the
research ledger on a layered universe):

* `gauss_theorem`, `Board.outward_eq` (IN1): Gauss's theorem, with the outward sign of a line on a
  board `[tail ∈ U] - [head ∈ U]`;
* `stokes_theorem`, `Board.edge_eq`, `Board.flux_total` (IN2): Stokes's theorem, the edge of a set
  of squares on a board, and no flux through the whole closed board;
* `faraday_integral` (IN3): Faraday's law of induction;
* `continuity_integral` (IN4): the charge in a set of corners changes by minus the current out;
* `magnetic_flux_out` (IN5): where `V C = 0`, no flux of `B = C A` leaves a set of cubes.
-/

open Matrix

namespace Artform.Stages

section Integral

variable {R : Type*} [CommRing R]

/-- The outward sign of a line for a set `U` of corners: `- ∑ w ∈ U, G ℓ w`. -/
def outward {n v : Type*} (G : Matrix n v R) (U : Finset v) (ℓ : n) : R := -∑ w ∈ U, G ℓ w

/-- The edge of a set `P` of squares at a line: `∑ σ ∈ P, C σ ℓ`. -/
def edge {f n : Type*} (C : Matrix f n R) (P : Finset f) (ℓ : n) : R := ∑ σ ∈ P, C σ ℓ

/-- IN1. Gauss's theorem: the divergence of `E` summed over `U` is the flux of `E` out of `U`. -/
theorem gauss_theorem {n v : Type*} [Fintype n] (G : Matrix n v R) (U : Finset v) (E : n → R) :
    ∑ w ∈ U, divergence G E w = ∑ ℓ, outward G U ℓ * E ℓ := by
  simp only [divergence, outward, Pi.neg_apply, mulVec, dotProduct, transpose_apply,
    Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- IN2. Stokes's theorem: `C A` summed over `P` is the circulation of `A` round the edge of `P`. -/
theorem stokes_theorem {f n : Type*} [Fintype n] (C : Matrix f n R) (P : Finset f) (A : n → R) :
    ∑ σ ∈ P, (C *ᵥ A) σ = ∑ ℓ, edge C P ℓ * A ℓ := by
  simp only [edge, mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- IN3. Faraday's law of induction: in one step of Pair with a current, the flux of `B = C A`
through `P` changes by minus the circulation of the electric field `L E'` round the edge of `P`. -/
theorem faraday_integral {f n : Type*} [Fintype f] [Fintype n] (C : Matrix f n R)
    (K : Matrix f f R) (L : Matrix n n R) (J : n → R) (P : Finset f) (x : LightState R n) :
    ∑ σ ∈ P, (C *ᵥ (pairWith (Cᵀ * K * C) L J x).1) σ - ∑ σ ∈ P, (C *ᵥ x.1) σ =
      -∑ ℓ, edge C P ℓ * (L *ᵥ (pairWith (Cᵀ * K * C) L J x).2) ℓ := by
  rw [faraday_pairWith, ← mulVec_mulVec]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  rw [stokes_theorem C P (L *ᵥ _)]
  ring

/-- IN4. With `C G = 0`, the charge in `U` changes in one step by minus the flux of the current out
of `U`. -/
theorem continuity_integral {f n v : Type*} [Fintype f] [Fintype n] (C : Matrix f n R)
    (G : Matrix n v R) (K : Matrix f f R) (L : Matrix n n R) (hCG : C * G = 0) (J : n → R)
    (U : Finset v) (x : LightState R n) :
    ∑ w ∈ U, divergence G (pairWith (Cᵀ * K * C) L J x).2 w - ∑ w ∈ U, divergence G x.2 w =
      -∑ ℓ, outward G U ℓ * J ℓ := by
  rw [divergence_pairWith C G K L hCG]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  rw [gauss_theorem G U J]
  ring

/-- IN5. Where `V C = 0`, no flux of `B = C A` leaves a set `Q` of cubes. -/
theorem magnetic_flux_out {c f n : Type*} [Fintype f] [Fintype n] (V : Matrix c f R)
    (C : Matrix f n R) (hVC : V * C = 0) (Q : Finset c) (A : n → R) :
    ∑ σ, (∑ k ∈ Q, V k σ) * (C *ᵥ A) σ = 0 := by
  have h : ∀ k, (V *ᵥ (C *ᵥ A)) k = 0 := fun k => by
    rw [mulVec_mulVec, hVC, zero_mulVec]
    rfl
  calc ∑ σ, (∑ k ∈ Q, V k σ) * (C *ᵥ A) σ = ∑ k ∈ Q, ∑ σ, V k σ * (C *ᵥ A) σ := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ k ∈ Q, (V *ᵥ (C *ᵥ A)) k := rfl
    _ = 0 := Finset.sum_eq_zero fun k _ => h k

end Integral

/-- IN1. On a board, the outward sign of a line is `1` if it leaves `U`, `-1` if it enters it. -/
theorem Board.outward_eq {f e v : Type*} [DecidableEq v] (B : Board f e v) (U : Finset v)
    (ℓ : e) :
    outward B.gauge U ℓ = (if B.tail ℓ ∈ U then 1 else 0) - (if B.head ℓ ∈ U then 1 else 0) := by
  simp [outward, Board.gauge, Finset.sum_sub_distrib]

/-- IN2. On a board, the edge of `P` at a line is `1` if its square along is in `P`, less `1` if its
square against is. -/
theorem Board.edge_eq {f e v : Type*} [Finite f] [DecidableEq f] [DecidableEq e] (B : Board f e v)
    (P : Finset f) {ℓ : e} {σ τ : f} {i j : Fin 4} (hσ : B.side σ i = ℓ)
    (hσa : B.along σ i = true) (hτ : B.side τ j = ℓ) (hτa : B.along τ j = false) :
    edge B.incidence P ℓ = (if σ ∈ P then 1 else 0) - (if τ ∈ P then 1 else 0) := by
  have := Fintype.ofFinite f
  have h := B.incidence_transpose_mulVec (fun ρ => if ρ ∈ P then (1 : ℝ) else 0) hσ hσa hτ hτa
  rw [← h]
  simp [edge, mulVec, dotProduct, transpose_apply, Finset.sum_ite_mem]

/-- IN2. A closed board has no edge, so the flux of every `B = C A` through it is `0`. -/
theorem Board.flux_total {f e v : Type*} [Fintype f] [Fintype e] [DecidableEq e]
    (B : Board f e v) (A : e → ℝ) : ∑ σ, (B.incidence *ᵥ A) σ = 0 := by
  rw [stokes_theorem]
  simp [edge, B.incidence_col_sum]

end Artform.Stages
