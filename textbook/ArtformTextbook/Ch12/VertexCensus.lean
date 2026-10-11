import ArtformTextbook.Ch12.VertexGamma
import ArtformTextbook.Ch12.GroupsCube
import ArtformTextbook.Ch11.ThereAndBack

/-!
# The colourless states of one vertex with two slots

* **The census at one vertex.** For a finite group with a triplet in `SU(3)`, the invariant
  tables of one vertex with two slots and `k` quarks number the average of the coefficient of
  `z^k` in `(1 + χ z + χ̄ z² + z³)²` (`Vertex.census`), by averaging the traces of `Γ(g)` on the
  tables with `k` quarks (Theorem 11.15, read at one vertex): `1, 2χ, χ² + 2χ̄, 2 + 2χχ̄,
  χ̄² + 2χ, 2χ̄, 1`.
* **The groups.** For the cube group and the icosahedral group `⟨χ⟩ = 0` and `⟨χ²⟩ = ⟨χχ̄⟩ = 1`,
  so the counts are `1, 0, 1, 4, 1, 0, 1`; for `C₃ × A₅` also `⟨χ²⟩ = 0`, so they are
  `1, 0, 0, 4, 0, 0, 1`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Polynomial

namespace Vertex

/-! ### The census at one vertex -/

/-- The coefficients of `(1 + a z + b z² + z³)²`. -/
theorem coeff_sq_cubic (a b : ℂ) (k : ℕ) :
    ((1 + C a * X + C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]).coeff k =
      if k = 0 then 1 else if k = 1 then 2 * a else if k = 2 then a ^ 2 + 2 * b
      else if k = 3 then 2 + 2 * a * b else if k = 4 then b ^ 2 + 2 * a
      else if k = 5 then 2 * b else if k = 6 then 1 else 0 := by
  have e : ((1 + C a * X + C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]) =
      C 1 + C (2 * a) * X + C (a ^ 2 + 2 * b) * X ^ 2 + C (2 + 2 * a * b) * X ^ 3 +
        C (b ^ 2 + 2 * a) * X ^ 4 + C (2 * b) * X ^ 5 + X ^ 6 := by
    simp only [map_one, map_mul, map_add, map_pow, map_ofNat]
    ring
  rw [e]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp

variable {G : Type*} [Group G] [Fintype G]

/-- **The census at one vertex** with two slots: the invariant tables with `k` quarks number the
average of the coefficient of `z^k` in `(1 + χ z + χ̄ z² + z³)²`. -/
theorem census (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Fin 3 × Fin 2))
    (k : ℕ) :
    (Module.finrank ℂ ↥(Edge.vertexInvariants ρ ord ⊓ Fock.numberSector (Fin 3 × Fin 2) k) :
      ℂ) = (Fintype.card G : ℂ)⁻¹ * ∑ g, ((1 + C (ρ g).trace * X +
        C (conj (ρ g).trace) * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]).coeff k := by
  rw [inf_comm, Edge.vertexInvariants_eq, Fock.finrank_inf_fixedSub (Edge.vertexHom ρ ord)
    (fun n => n.card = k) _ (fun v => Iff.rfl)]
  · congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [show Edge.vertexHom ρ ord g = Fock.vertexGamma ord (ρ g) from rfl, Fock.vertexGamma,
      Edge.filter_card_eq_powersetCard, Fock.sum_powersetCard_secondQuant_diag,
      Edge.kron_one_map_smul, Edge.det_one_add_kron_one, Fintype.card_fin,
      Edge.det_one_add_X_smul_of_mem_specialUnitaryGroup (hρ g)]
  · intro h n' n hne
    rw [Fock.secondQuant_card_eq ord _ hne]

/-- The census at one vertex from the averages `⟨χ⟩`, `⟨χ̄⟩`, `⟨χ²⟩`, `⟨χ̄²⟩` and `⟨χχ̄⟩`. -/
theorem census_of_sums (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Fin 3 × Fin 2))
    (s1 s1' s2 s2' s11 : ℂ) (h1 : ∑ g, (ρ g).trace = s1) (h1' : ∑ g, conj (ρ g).trace = s1')
    (h2 : ∑ g, (ρ g).trace ^ 2 = s2) (h2' : ∑ g, conj (ρ g).trace ^ 2 = s2')
    (h11 : ∑ g, (ρ g).trace * conj (ρ g).trace = s11) (k : ℕ) :
    (Module.finrank ℂ ↥(Edge.vertexInvariants ρ ord ⊓ Fock.numberSector (Fin 3 × Fin 2) k) :
      ℂ) = (Fintype.card G : ℂ)⁻¹ *
        (if k = 0 then (Fintype.card G : ℂ) else if k = 1 then 2 * s1
        else if k = 2 then s2 + 2 * s1' else if k = 3 then 2 * Fintype.card G + 2 * s11
        else if k = 4 then s2' + 2 * s1 else if k = 5 then 2 * s1'
        else if k = 6 then (Fintype.card G : ℂ) else 0) := by
  rw [census ρ hρ ord k]
  congr 1
  simp only [coeff_sq_cubic]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [← h1, ← h1', ← h2, ← h2', ← h11, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.card_univ, mul_assoc]
  ring

/-! ### The cube group -/

open ColourGroups Exact

theorem sum_cubeGroup (f : cubeGroup → ℂ) : ∑ g, f g = ∑ k : Fin 24, f (cubeElt k) :=
  (Fintype.sum_equiv cubeEquiv _ _ fun _ => rfl).symm

theorem cube_trace (k : Fin 24) :
    (cubeTriplet (cubeElt k)).trace = ZOP.toComplex (M3Z.trace (cubeE k)) :=
  char_cubeElt k

theorem cube_sum_trace : ∑ k : Fin 24, M3Z.trace (cubeE k) = 0 := by decide +kernel

theorem cube_sum_trace_sq : ∑ k : Fin 24, M3Z.trace (cubeE k) ^ 2 = ⟨24, 0, 0, 0⟩ := by
  decide +kernel

theorem cube_conj_trace (g : cubeGroup) : conj (cubeTriplet g).trace = (cubeTriplet g).trace := by
  simp only [Matrix.trace, Matrix.diag, map_sum]
  exact Finset.sum_congr rfl fun i _ => cubeTriplet_real g i i

theorem cube_sums : ∑ g, (cubeTriplet g).trace = 0 ∧ ∑ g, (cubeTriplet g).trace ^ 2 = 24 := by
  rw [sum_cubeGroup, sum_cubeGroup]
  simp only [cube_trace, ← ZOP.toComplex_pow, ← ColourGroups.toComplex_sum, cube_sum_trace,
    cube_sum_trace_sq]
  exact ⟨ZOP.toComplex_zero, by simp [ZOP.toComplex]⟩

/-- The census of the cube group at one vertex with two slots: `1, 0, 1, 4, 1, 0, 1`. -/
theorem cube_census (ord : LinearOrder (Fin 3 × Fin 2)) (k : ℕ) :
    Module.finrank ℂ ↥(Edge.vertexInvariants cubeTriplet ord ⊓
      Fock.numberSector (Fin 3 × Fin 2) k) =
      if k = 0 then 1 else if k = 2 then 1 else if k = 3 then 4 else if k = 4 then 1
      else if k = 6 then 1 else 0 := by
  have hcard : Fintype.card cubeGroup = 24 := by
    rw [← Nat.card_eq_fintype_card, card_cubeGroup]
  have h := census_of_sums cubeTriplet cubeTriplet_mem ord 0 0 24 24 24 cube_sums.1
    (by simp only [cube_conj_trace]; exact cube_sums.1) cube_sums.2
    (by simp only [cube_conj_trace]; exact cube_sums.2)
    (by simp only [cube_conj_trace, ← sq]; exact cube_sums.2) k
  rw [hcard] at h
  apply Nat.cast_injective (R := ℂ)
  rw [h]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> norm_num

end Vertex

end Artform
