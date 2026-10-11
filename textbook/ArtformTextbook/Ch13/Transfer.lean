import ArtformTextbook.Ch13.TransferStates
import ArtformTextbook.Ch13.Statements.Transfer

/-!
# The third-order transfer: Theorem 13.9

For the four finite colour groups, `P V³ P` is the words of Theorem 13.8 on the zero-flux values,
for every orthogonal projector `P` onto the zero-flux sector (`Edge.transferVal_cube` and its
companions, `Ch13/TransferMoments.lean`: the third moment of the triplet is the
Levi-Civita product); for the `SU(3)` reference `L` is the words. The words act on the named
states as `Ch13/TransferStates.lean` computes, and have on the zero-flux sectors the table of
Figure `fig:ml-transfer-spectra` (`Ch13/TransferSpectra.lean`), in every order of the modes.
-/

namespace Artform

open scoped Matrix

open Module Edge ModelsData ModelsCheck ThereAndBack TransferMoments TransferSpectra
  TransferStates

namespace TransferStates

open Classical in
theorem table_cube (ord : LinearOrder EM)
    (P : (cubeGroup → Finset EM → ℂ) →ₗ[ℂ] (cubeGroup → Finset EM → ℂ))
    (hP : IsZeroFluxProj cubeTriplet ord P) :
    Table (zeroFluxValues cubeTriplet ord) (transferVal cubeTriplet ord P) true := by
  have h := table_words _ true tableR ord
  rw [← zeroFluxValues_cube, ← zeroFluxValues_change] at h
  exact h.congr fun v hv => by rw [Matrix.toLin'_apply, transferVal_cube ord P hP v hv]

open Classical in
theorem table_ico (ord : LinearOrder EM)
    (P : (icoGroup → Finset EM → ℂ) →ₗ[ℂ] (icoGroup → Finset EM → ℂ))
    (hP : IsZeroFluxProj icoTriplet ord P) :
    Table (zeroFluxValues icoTriplet ord) (transferVal icoTriplet ord P) true := by
  have h := table_words _ true tableR ord
  rw [← zeroFluxValues_ico, ← zeroFluxValues_change] at h
  exact h.congr fun v hv => by rw [Matrix.toLin'_apply, transferVal_ico ord P hP v hv]

open Classical in
theorem table_c3a5 (ord : LinearOrder EM)
    (P : (C3A5 → Finset EM → ℂ) →ₗ[ℂ] (C3A5 → Finset EM → ℂ))
    (hP : IsZeroFluxProj c3a5Triplet ord P) :
    Table (zeroFluxValues c3a5Triplet ord) (transferVal c3a5Triplet ord P) false := by
  have h := table_words _ false tableC ord
  rw [← zeroFluxValues_c3a5, ← zeroFluxValues_change] at h
  exact h.congr fun v hv => by rw [Matrix.toLin'_apply, transferVal_c3a5 ord P hP v hv]

open Classical in
theorem table_valentiner (ord : LinearOrder EM)
    (P : (valentiner → Finset EM → ℂ) →ₗ[ℂ] (valentiner → Finset EM → ℂ))
    (hP : IsZeroFluxProj valentinerTriplet ord P) :
    Table (zeroFluxValues valentinerTriplet ord) (transferVal valentinerTriplet ord P) false := by
  have h := table_words _ false tableC ord
  rw [← zeroFluxValues_valentiner, ← zeroFluxValues_change] at h
  exact h.congr fun v hv => by rw [Matrix.toLin'_apply, transferVal_valentiner ord P hP v hv]

open Classical in
theorem table_su3 (ord : LinearOrder EM) :
    Table (zeroFluxValues su3Triplet ord) (Matrix.toLin' (transferWords ord false)) false := by
  have h := table_words _ false tableC ord
  rwa [← zeroFluxValues_su3, ← zeroFluxValues_change] at h

/-- The average over the link and the gauge pairs is an orthogonal projector onto the zero-flux
sector, as the statement asks of `P`. -/
theorem zeroFluxProj_isProj {G : Type*} [Group G] [Fintype G]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (ord : LinearOrder EM) : IsZeroFluxProj ρ ord (zeroFluxProj ρ ord) :=
  ⟨zeroFluxProj_mem ρ ord, fun _ h => zeroFluxProj_fix ρ ord h,
    zeroFluxProj_adj (fun g => Vertex.mem_unitary (hρ g)) ord⟩

end TransferStates

/-! ## The book's statement -/

/-- **Theorem 13.9** (what the transfer does). -/
@[book "thm:ml-transfer-values"]
theorem mlTransferValues : Statement.mlTransferValues := by
  dsimp only [Statement.mlTransferValues]
  refine ⟨fun P hP => claims_real _ fun v hv => transferVal_cube bookOrd P hP v ?_,
    fun P hP => claims_real _ fun v hv => transferVal_ico bookOrd P hP v ?_,
    fun P hP => claims_complex _ fun v hv => transferVal_c3a5 bookOrd P hP v ?_,
    fun P hP => claims_complex _ fun v hv => transferVal_valentiner bookOrd P hP v ?_,
    claims_su3, fun ord => ⟨table_cube ord, table_ico ord, table_c3a5 ord,
      table_valentiner ord, table_su3 ord⟩, fun κ hκ => ?_⟩
  · rwa [zeroFluxValues_cube]
  · rwa [zeroFluxValues_ico]
  · rwa [zeroFluxValues_c3a5]
  · rwa [zeroFluxValues_valentiner]
  · field_simp
    ring

/-! ## Non-vacuity -/

/-- Theorem 13.9 for Model I with `P` the average over the link and the gauge pairs: the
quartet member `q_x(0)`, a nonzero state, hops to `6 q_y(0)`. -/
example : Edge.transferVal cubeTriplet Edge.bookOrd
      (ThereAndBack.zeroFluxProj cubeTriplet Edge.bookOrd) (Edge.quartetX 0) =
      (6 : ℂ) • Edge.quartetY 0 ∧ Edge.quartetX 0 ≠ 0 := by
  refine ⟨(mlTransferValues.1 _ (zeroFluxProj_isProj cubeTriplet cubeTriplet_mem _)).1 0 |>.1,
    ?_⟩
  rw [quartetX_eq_B64]
  exact B64_linearIndependent.ne_zero _

/-- Theorem 13.9 for `C₃ × A₅`: the singlet goes to the full vertices, with the projector of the
link and the gauge pairs. -/
example : Edge.transferVal c3a5Triplet Edge.bookOrd
      (ThereAndBack.zeroFluxProj c3a5Triplet Edge.bookOrd) Edge.singlet =
      (-12 : ℂ) • (Edge.fullX + Edge.fullY) :=
  (mlTransferValues.2.2.1 _ (zeroFluxProj_isProj c3a5Triplet Vertex.c3a5Triplet_mem _)).2.2.2.1
    rfl

end Artform
