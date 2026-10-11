import ArtformTextbook.Ch12.ModelsBridge
import ArtformTextbook.Ch12.OrderChange

/-!
# The spectra of the tally on the zero-flux sectors

The zero-flux values of the five models in the book's order are the spans of the sixty-four
products of the eight (Models I and II) and of the thirty-six products of the six (the three
`SU(3)`-type models), `Edge.zeroFluxValues_cube` and its companions. On them `3 Ω` is the matrix of
the certificate (`ModelsCheck.omega1_lc` and its companions), whose eigenvalues the kernel has
checked; the multiplicities of the values of `Ω` are counted from them (`sectorMult_book_one` and
its companions), and hold in every order of the modes by `Edge.sectorMult_change`.
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck

namespace Edge

/-! ### The zero-flux values in the book's order -/

theorem zeroFluxValues_of_range {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    {n : ℕ} (Φ : (Fin n → ℂ) →ₗ[ℂ] (Finset (Mode (Fin 3) (Fin 2)) → ℂ))
    (h : LinearMap.range (constLin G ∘ₗ Φ) = zeroFlux ρ bookOrd) :
    zeroFluxValues ρ bookOrd = LinearMap.range Φ := by
  rw [zeroFluxValues, ← h, ← LinearMap.range_comp]
  congr 1

theorem zeroFluxValues_cube : zeroFluxValues cubeTriplet bookOrd = LinearMap.range Φ64 :=
  zeroFluxValues_of_range cubeTriplet Φ64 zeroFlux_cube

theorem zeroFluxValues_ico : zeroFluxValues icoTriplet bookOrd = LinearMap.range Φ64 :=
  zeroFluxValues_of_range icoTriplet Φ64 zeroFlux_ico

theorem zeroFluxValues_c3a5 : zeroFluxValues c3a5Triplet bookOrd = LinearMap.range Φ36 :=
  zeroFluxValues_of_range c3a5Triplet Φ36 zeroFlux_c3a5

theorem zeroFluxValues_valentiner :
    zeroFluxValues valentinerTriplet bookOrd = LinearMap.range Φ36 :=
  zeroFluxValues_of_range valentinerTriplet Φ36 zeroFlux_valentiner

theorem zeroFluxValues_su3 : zeroFluxValues su3Triplet bookOrd = LinearMap.range Φ36 :=
  zeroFluxValues_of_range su3Triplet Φ36 zeroFlux_su3

/-- The same sector in every order: the zero-flux values of two models agree in every order when
they agree in the book's. -/
theorem zeroFluxValues_eq_of_book {G H : Type*} [Group G] [Group H]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (σ : H →* Matrix (Fin 3) (Fin 3) ℂ)
    (h : zeroFluxValues ρ bookOrd = zeroFluxValues σ bookOrd) (ord : LinearOrder EM) :
    zeroFluxValues ρ ord = zeroFluxValues σ ord := by
  rw [zeroFluxValues_change ρ bookOrd ord, zeroFluxValues_change σ bookOrd ord, h]

theorem finrank_zeroFluxValues_64 {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (h : zeroFluxValues ρ bookOrd = LinearMap.range Φ64) (ord : LinearOrder EM) :
    finrank ℂ ↥(zeroFluxValues ρ ord) = 64 := by
  rw [zeroFluxValues_change ρ bookOrd ord, LinearEquiv.finrank_map_eq, h,
    LinearMap.finrank_range_of_inj Φ64_injective, Module.finrank_fin_fun]

theorem finrank_zeroFluxValues_36 {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (h : zeroFluxValues ρ bookOrd = LinearMap.range Φ36) (ord : LinearOrder EM) :
    finrank ℂ ↥(zeroFluxValues ρ ord) = 36 := by
  rw [zeroFluxValues_change ρ bookOrd ord, LinearEquiv.finrank_map_eq, h,
    LinearMap.finrank_range_of_inj Φ36_injective, Module.finrank_fin_fun]

end Edge

namespace SpecCert

/-! ### Multiplicities from a certificate -/

theorem eigenspace_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) {c : ℂ}
    (hc : c ≠ 0) (μ : ℂ) :
    Module.End.eigenspace (c • T) (c * μ) = Module.End.eigenspace T μ := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, LinearMap.smul_apply,
    mul_smul]
  exact ⟨fun h => smul_right_injective V hc h, fun h => by rw [h]⟩

/-- The multiplicity of a value of `X` on a sector spanned by `Φ`, on which `c X` is the matrix of
a certificate. -/
theorem finrank_inf_of_cert {n d : ℕ} (hn : n ≤ 2 ^ d)
    (W : Submodule ℂ (Finset Edge.EM → ℂ)) (Φ : (Fin n → ℂ) →ₗ[ℂ] (Finset Edge.EM → ℂ))
    (hΦ : Function.Injective Φ) (hW : W = LinearMap.range Φ)
    (X : Matrix (Finset Edge.EM) (Finset Edge.EM) ℂ) {c : ℂ} (hc : c ≠ 0)
    (cols dcols : List Vec) (eigs : List (ℤ × Vec)) (dg : List ℤ)
    (hX : ∀ a, (c • X) *ᵥ Φ a = Φ (colMat d n cols *ᵥ a))
    (h1 : eigOK d n cols eigs = true) (h2 : invOK d n dcols eigs dg = true) (μ : ℂ) :
    finrank ℂ ↥(W ⊓ Module.End.eigenspace (Matrix.toLin' X) μ) =
      (Finset.univ.filter fun k : Fin n => ((eigs.getD k (0, [])).1 : ℂ) = c * μ).card := by
  rw [← eigenspace_smul _ hc, ← map_smul,
    finrank_inf_eigenspace W _ Φ hΦ hW.symm _ (fun a => by rw [Matrix.toLin'_apply, hX a]),
    finrank_eigenspace_colMat hn cols dcols eigs dg h1 h2]

theorem card_filter_cast {n : ℕ} (ν : Fin n → ℤ) {c μ : ℂ} {w : ℤ} (h : c * μ = w) :
    (Finset.univ.filter fun k => (ν k : ℂ) = c * μ).card =
      (Finset.univ.filter fun k => ν k = w).card := by
  rw [h]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Int.cast_inj]

theorem card_filter_cast_eq_zero {n : ℕ} (ν : Fin n → ℤ) (vals : List ℤ) (hv : ∀ k, ν k ∈ vals)
    {c μ : ℂ} (h : ∀ w ∈ vals, c * μ ≠ w) :
    (Finset.univ.filter fun k => (ν k : ℂ) = c * μ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  exact h _ (hv k) hk.symm

end SpecCert

namespace ModelsCheck

/-- The values of the certificate, `3 Ω` on its eigenvectors. -/
def nu (eigs : List (ℤ × Vec)) (n : ℕ) (k : Fin n) : ℤ := (eigs.getD k (0, [])).1

theorem nu1_vals : ∀ k, nu omega1Eig 64 k ∈ [0, 9, 12, 20, 24] := by decide +kernel

theorem nu0_vals : ∀ k, nu omega0Eig 64 k ∈ [0, 6, 8, 9, 10, 12, 18, 20, 24] := by
  decide +kernel

theorem nu36_vals : ∀ k, nu omega36Eig 36 k ∈ [0, 9, 12, 18, 20, 24] := by decide +kernel

theorem nu1_counts :
    (Finset.univ.filter fun k => nu omega1Eig 64 k = 0).card = 14 ∧
    (Finset.univ.filter fun k => nu omega1Eig 64 k = 9).card = 32 ∧
    (Finset.univ.filter fun k => nu omega1Eig 64 k = 12).card = 10 ∧
    (Finset.univ.filter fun k => nu omega1Eig 64 k = 20).card = 6 ∧
    (Finset.univ.filter fun k => nu omega1Eig 64 k = 24).card = 2 := by
  decide +kernel

theorem nu0_counts :
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 0).card = 9 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 6).card = 4 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 8).card = 2 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 9).card = 32 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 10).card = 2 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 12).card = 9 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 18).card = 2 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 20).card = 3 ∧
    (Finset.univ.filter fun k => nu omega0Eig 64 k = 24).card = 1 := by
  decide +kernel

theorem nu36_counts :
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 0).card = 9 ∧
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 9).card = 16 ∧
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 12).card = 5 ∧
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 18).card = 2 ∧
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 20).card = 3 ∧
    (Finset.univ.filter fun k => nu omega36Eig 36 k = 24).card = 1 := by
  decide +kernel

end ModelsCheck

namespace Edge

open ModelsCheck

/-! ### The multiplicities in the book's order -/

open Classical in
/-- Model I: `0¹⁴ 3³² 4¹⁰ (20/3)⁶ 8²`. -/
theorem sectorMult_book_one {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd = LinearMap.range Φ64) (μ : ℂ) :
    sectorMult ρ bookOrd (tally bookOrd 1) μ =
      if μ = 0 then 14 else if μ = 3 then 32 else if μ = 4 then 10 else if μ = 20 / 3 then 6
      else if μ = 8 then 2 else 0 := by
  rw [sectorMult, finrank_inf_of_cert (d := 6) (by norm_num) _ Φ64 Φ64_injective hρ _
    (three_ne_zero) omega1Cols omega1D omega1Eig omega1Dg omega1_lc omega1_eig omega1_inv]
  change (Finset.univ.filter fun k => (nu omega1Eig 64 k : ℂ) = 3 * μ).card = _
  obtain ⟨c0, c9, c12, c20, c24⟩ := nu1_counts
  split_ifs with h0 h3 h4 h20 h8
  · rw [card_filter_cast _ (w := 0) (by rw [h0]; norm_num), c0]
  · rw [card_filter_cast _ (w := 9) (by rw [h3]; norm_num), c9]
  · rw [card_filter_cast _ (w := 12) (by rw [h4]; norm_num), c12]
  · rw [card_filter_cast _ (w := 20) (by rw [h20]; norm_num), c20]
  · rw [card_filter_cast _ (w := 24) (by rw [h8]; norm_num), c24]
  · refine card_filter_cast_eq_zero _ _ nu1_vals fun w hw h => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact h0 (by linear_combination h / 3)
    · exact h3 (by linear_combination h / 3)
    · exact h4 (by linear_combination h / 3)
    · exact h20 (by linear_combination h / 3)
    · exact h8 (by linear_combination h / 3)

open Classical in
/-- The control, Model I without the pair hop:
`0⁹ 2⁴ (8/3)² 3³² (10/3)² 4⁹ 6² (20/3)³ 8¹`. -/
theorem sectorMult_book_control {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd = LinearMap.range Φ64) (μ : ℂ) :
    sectorMult ρ bookOrd (tally bookOrd 0) μ =
      if μ = 0 then 9 else if μ = 2 then 4 else if μ = 8 / 3 then 2 else if μ = 3 then 32
      else if μ = 10 / 3 then 2 else if μ = 4 then 9 else if μ = 6 then 2
      else if μ = 20 / 3 then 3 else if μ = 8 then 1 else 0 := by
  rw [sectorMult, finrank_inf_of_cert (d := 6) (by norm_num) _ Φ64 Φ64_injective hρ _
    (three_ne_zero) omega0Cols omega0D omega0Eig omega0Dg omega0_lc omega0_eig omega0_inv]
  change (Finset.univ.filter fun k => (nu omega0Eig 64 k : ℂ) = 3 * μ).card = _
  obtain ⟨c0, c6, c8, c9, c10, c12, c18, c20, c24⟩ := nu0_counts
  split_ifs with h0 h2 h83 h3 h103 h4 h6 h20 h8
  · rw [card_filter_cast _ (w := 0) (by rw [h0]; norm_num), c0]
  · rw [card_filter_cast _ (w := 6) (by rw [h2]; norm_num), c6]
  · rw [card_filter_cast _ (w := 8) (by rw [h83]; norm_num), c8]
  · rw [card_filter_cast _ (w := 9) (by rw [h3]; norm_num), c9]
  · rw [card_filter_cast _ (w := 10) (by rw [h103]; norm_num), c10]
  · rw [card_filter_cast _ (w := 12) (by rw [h4]; norm_num), c12]
  · rw [card_filter_cast _ (w := 18) (by rw [h6]; norm_num), c18]
  · rw [card_filter_cast _ (w := 20) (by rw [h20]; norm_num), c20]
  · rw [card_filter_cast _ (w := 24) (by rw [h8]; norm_num), c24]
  · refine card_filter_cast_eq_zero _ _ nu0_vals fun w hw h => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0 (by linear_combination h / 3)
    · exact h2 (by linear_combination h / 3)
    · exact h83 (by linear_combination h / 3)
    · exact h3 (by linear_combination h / 3)
    · exact h103 (by linear_combination h / 3)
    · exact h4 (by linear_combination h / 3)
    · exact h6 (by linear_combination h / 3)
    · exact h20 (by linear_combination h / 3)
    · exact h8 (by linear_combination h / 3)

open Classical in
/-- The `SU(3)`-type models: `0⁹ 3¹⁶ 4⁵ 6² (20/3)³ 8¹`. -/
theorem sectorMult_book_36 {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd = LinearMap.range Φ36) (μ : ℂ) :
    sectorMult ρ bookOrd (tally bookOrd 0) μ =
      if μ = 0 then 9 else if μ = 3 then 16 else if μ = 4 then 5 else if μ = 6 then 2
      else if μ = 20 / 3 then 3 else if μ = 8 then 1 else 0 := by
  rw [sectorMult, finrank_inf_of_cert (d := 6) (by norm_num) _ Φ36 Φ36_injective hρ _
    (three_ne_zero) omega36Cols omega36D omega36Eig omega36Dg omega36_lc omega36_eig
    omega36_inv]
  change (Finset.univ.filter fun k => (nu omega36Eig 36 k : ℂ) = 3 * μ).card = _
  obtain ⟨c0, c9, c12, c18, c20, c24⟩ := nu36_counts
  split_ifs with h0 h3 h4 h6 h20 h8
  · rw [card_filter_cast _ (w := 0) (by rw [h0]; norm_num), c0]
  · rw [card_filter_cast _ (w := 9) (by rw [h3]; norm_num), c9]
  · rw [card_filter_cast _ (w := 12) (by rw [h4]; norm_num), c12]
  · rw [card_filter_cast _ (w := 18) (by rw [h6]; norm_num), c18]
  · rw [card_filter_cast _ (w := 20) (by rw [h20]; norm_num), c20]
  · rw [card_filter_cast _ (w := 24) (by rw [h8]; norm_num), c24]
  · refine card_filter_cast_eq_zero _ _ nu36_vals fun w hw h => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0 (by linear_combination h / 3)
    · exact h3 (by linear_combination h / 3)
    · exact h4 (by linear_combination h / 3)
    · exact h6 (by linear_combination h / 3)
    · exact h20 (by linear_combination h / 3)
    · exact h8 (by linear_combination h / 3)

/-! ### In every order -/

theorem sectorMult_tally {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder EM) (m : ℕ) (μ : ℂ) :
    sectorMult ρ ord (tally ord m) μ = sectorMult ρ bookOrd (tally bookOrd m) μ := by
  rw [tally_change bookOrd ord, sectorMult_change]

end Edge

end Artform
