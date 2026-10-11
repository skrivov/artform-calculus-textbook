import ArtformTextbook.Ch13.TransferSpectra

/-!
# What the transfer does to the named states

Items 1–3 of Theorem 13.9 for the words `L` of Theorem 13.8 in the book's order of the modes, read
from the kernel's checks of `Ch13/TransferCheck.lean`: the quartet hops as one assembly
(`TransferStates.words_quartet`), the singlet goes to the full vertices and, for the real triplets,
to the two chain states (`TransferStates.transferR_singlet`), and the two channels of the real
triplets (`TransferStates.words_channel`). Any operator that agrees with the words on these states
has the claims (`TransferStates.claims_of_agree`); for the four finite colour groups `P V³ P` does
(`Edge.transferVal_cube` and its companions), and for `SU(3)` the words themselves are `L`.
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge TransferCalc TransferData
  TransferCheck TransferSpectra

namespace TransferStates

/-- The claims of items 1–3 of Theorem 13.9 for an operator `L` (the body of the statement's
`claims`). -/
def Claims (L : Module.End ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ)) (real : Bool) : Prop :=
  (∀ m : Fin 4, L (Edge.quartetX m) = (6 : ℂ) • Edge.quartetY m ∧
    L (Edge.quartetY m) = (6 : ℂ) • Edge.quartetX m) ∧
  coeffPairing Edge.fullX (L Edge.singlet) = -12 ∧
  coeffPairing Edge.fullY (L Edge.singlet) = -12 ∧
  (real = false → L Edge.singlet = (-12 : ℂ) • (Edge.fullX + Edge.fullY)) ∧
  (real = true →
    (∀ m : Fin 4, L (Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m))
      = (-6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.pair Vertex.bookOrd)) ∧
    (∀ m : Fin 4,
      L (Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m)) =
        (6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.holes Vertex.bookOrd)) ∧
    L Edge.singlet =
      (-12 : ℂ) • (Edge.fullX + Edge.fullY + Edge.chain 1 + Edge.chain 2) ∧
    Fock.hilbertNorm (L Edge.singlet) = 24)

/-! ### The named states among the products -/

theorem pairQuartet_eq (m : Fin 4) :
    Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m) =
      B64 ⟨8 + (m + 2), by omega⟩ := by
  fin_cases m <;> rfl

theorem quartetPair_eq (m : Fin 4) :
    Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.pair Vertex.bookOrd) =
      B64 ⟨8 * (m + 2) + 1, by omega⟩ := by
  fin_cases m <;> rfl

theorem holesQuartet_eq (m : Fin 4) :
    Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m) =
      B64 ⟨48 + (m + 2), by omega⟩ := by
  fin_cases m <;> rfl

theorem quartetHoles_eq (m : Fin 4) :
    Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.holes Vertex.bookOrd) =
      B64 ⟨8 * (m + 2) + 6, by omega⟩ := by
  fin_cases m <;> rfl

theorem quartetX_eq_B36 (m : Fin 4) : quartetX m = B36 ⟨6 * (m + 1), by omega⟩ := by
  rw [quartetX_eq_B64, B36_eq_B64]
  congr 1
  apply Fin.ext
  revert m
  decide

theorem quartetY_eq_B36 (m : Fin 4) : quartetY m = B36 ⟨m + 1, by omega⟩ := by
  rw [quartetY_eq_B64, B36_eq_B64]
  congr 1
  apply Fin.ext
  revert m
  decide

/-! ### The words on the products -/

/-- `L` on a product, from the kernel's check of `6 L` on its list. -/
theorem words_B64 (real : Bool) (i j : Fin 64) (z : ℤ) (c : ℂ) (hc : (z : ℂ) = 6 * c)
    (h : (Vec.trie 12 (transfer6 real (basisVec i)) ==
      Vec.trie 12 (Vec.smul z (basisVec j))) = true) :
    transferWords bookOrd real *ᵥ B64 i = c • B64 j := by
  have h' := transfer_check real _ _ h
  rw [Vec.toFock_smul, hc] at h'
  rw [B64_eq, B64_eq]
  apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
  simp only
  rw [h', smul_smul]

/-- Item 1: the quartet hops as one assembly, with amplitude `6`. -/
theorem words_quartet (real : Bool) (m : Fin 4) :
    transferWords bookOrd real *ᵥ quartetX m = (6 : ℂ) • quartetY m ∧
      transferWords bookOrd real *ᵥ quartetY m = (6 : ℂ) • quartetX m := by
  obtain ⟨h1, h2, h3, h4⟩ := quartet_transfer m m.2
  rw [quartetX_eq_B64, quartetY_eq_B64]
  cases real
  · exact ⟨words_B64 false _ _ 36 6 (by norm_num) h3, words_B64 false _ _ 36 6 (by norm_num) h4⟩
  · exact ⟨words_B64 true _ _ 36 6 (by norm_num) h1, words_B64 true _ _ 36 6 (by norm_num) h2⟩

/-- Item 3: the two channels of the real triplets. -/
theorem words_channel (m : Fin 4) :
    transferWords bookOrd true *ᵥ
        Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m) =
      (-6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.pair Vertex.bookOrd) ∧
    transferWords bookOrd true *ᵥ
        Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m) =
      (6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.holes Vertex.bookOrd) := by
  obtain ⟨h1, h2⟩ := channel_transfer m m.2
  rw [pairQuartet_eq, quartetPair_eq, holesQuartet_eq, quartetHoles_eq]
  exact ⟨words_B64 true _ _ (-36) (-6) (by norm_num) h1, words_B64 true _ _ 36 6 (by norm_num) h2⟩

/-- Item 3: the singlet of the real triplets goes to the chain. -/
theorem transferR_singlet :
    transferWords bookOrd true *ᵥ singlet =
      (-12 : ℂ) • (fullX + fullY + chain 1 + chain 2) := by
  have h := transfer_check true singletVec _ singlet_transfer.2
  rw [Vec.toFock_combo] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [singlet_eq, Matrix.mulVec_smul, fullX_eq, fullY_eq, chain_one, chain_two]
  apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
  simp only
  rw [smul_comm, h]
  push_cast
  module

/-- The image of the singlet of the real triplets as a list. -/
def singletImageR : Vec :=
  Vec.combo [(-12, basisVec 56), (-12, basisVec 7), (4, basisVec 49), (4, basisVec 14)]

theorem transferR_singlet_toFock :
    transferWords bookOrd true *ᵥ singlet = Vec.toFock code singletImageR := by
  rw [transferR_singlet, singletImageR, Vec.toFock_combo, fullX_eq, fullY_eq, chain_one,
    chain_two]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  module

set_option maxRecDepth 100000 in
theorem singletImageR_sq :
    (∑ r ∈ Finset.range (2 ^ 12), Vec.sumAt 12 r singletImageR ^ 2 : ℤ) = 576 := by
  decide +kernel

theorem transferR_singlet_norm :
    Fock.hilbertNorm (transferWords bookOrd true *ᵥ singlet) = 24 := by
  rw [transferR_singlet_toFock, Vec.hilbertNorm_eq numbering, singletImageR_sq,
    show ((576 : ℤ) : ℝ) = 24 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ### The components along the full vertices -/

theorem basisVec_56 : basisVec 56 = [(63, 1)] := by decide

theorem basisVec_7 : basisVec 7 = [(4032, 1)] := by decide

theorem fullX_ket : fullX = Fock.ket (decode code 63) := by
  rw [fullX_eq, basisVec_56, Vec.toFock_cons, Vec.toFock_nil, add_zero, Int.cast_one, one_smul]

theorem fullY_ket : fullY = Fock.ket (decode code 4032) := by
  rw [fullY_eq, basisVec_7, Vec.toFock_cons, Vec.toFock_nil, add_zero, Int.cast_one, one_smul]

theorem coeffPairing_ket (n : Finset EM) (φ : Finset EM → ℂ) :
    coeffPairing (Fock.ket n) φ = φ n := by
  rw [coeffPairing, Finset.sum_eq_single n]
  · simp [Fock.ket]
  · intro b _ hb
    simp [Fock.ket, hb]
  · intro h
    exact absurd (Finset.mem_univ n) h

theorem coeffPairing_fullX (φ : Finset EM → ℂ) : coeffPairing fullX φ = φ (decode code 63) := by
  rw [fullX_ket, coeffPairing_ket]

theorem coeffPairing_fullY (φ : Finset EM → ℂ) :
    coeffPairing fullY φ = φ (decode code 4032) := by
  rw [fullY_ket, coeffPairing_ket]

theorem named_at : Vec.sumAt 12 63 (basisVec 56) = 1 ∧ Vec.sumAt 12 63 (basisVec 7) = 0 ∧
    Vec.sumAt 12 63 (basisVec 49) = 0 ∧ Vec.sumAt 12 63 (basisVec 14) = 0 ∧
    Vec.sumAt 12 4032 (basisVec 56) = 0 ∧ Vec.sumAt 12 4032 (basisVec 7) = 1 ∧
    Vec.sumAt 12 4032 (basisVec 49) = 0 ∧ Vec.sumAt 12 4032 (basisVec 14) = 0 := by
  decide +kernel

theorem eval_full : fullX (decode code 63) = 1 ∧ fullY (decode code 63) = 0 ∧
    chain 1 (decode code 63) = 0 ∧ chain 2 (decode code 63) = 0 ∧
    fullX (decode code 4032) = 0 ∧ fullY (decode code 4032) = 1 ∧
    chain 1 (decode code 4032) = 0 ∧ chain 2 (decode code 4032) = 0 := by
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := named_at
  rw [fullX_eq, fullY_eq, chain_one, chain_two]
  simp only [Pi.smul_apply, smul_eq_mul,
    Vec.toFock_apply numbering _ (by norm_num : 63 < 2 ^ 12),
    Vec.toFock_apply numbering _ (by norm_num : 4032 < 2 ^ 12), a1, a2, a3, a4, b1, b2, b3, b4]
  norm_num

/-! ### The claims -/

/-- An operator that agrees with the words on the named states has the claims of items 1–3. -/
theorem claims_of_agree (L : Module.End ℂ (Finset EM → ℂ)) (real : Bool)
    (hq : ∀ m, L (quartetX m) = transferWords bookOrd real *ᵥ quartetX m ∧
      L (quartetY m) = transferWords bookOrd real *ᵥ quartetY m)
    (hs : L singlet = transferWords bookOrd real *ᵥ singlet)
    (hc : real = true → ∀ m,
      L (Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m)) =
        transferWords bookOrd real *ᵥ
          Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m) ∧
      L (Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m)) =
        transferWords bookOrd real *ᵥ
          Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m)) :
    Claims L real := by
  obtain ⟨e1, e2, e3, e4, f1, f2, f3, f4⟩ := eval_full
  refine ⟨fun m => ⟨by rw [(hq m).1, (words_quartet real m).1],
    by rw [(hq m).2, (words_quartet real m).2]⟩, ?_, ?_, fun hr => ?_, fun hr => ?_⟩
  · rw [hs, coeffPairing_fullX]
    cases real
    · rw [transferC_singlet]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2]
      norm_num
    · rw [transferR_singlet]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2, e3, e4]
      norm_num
  · rw [hs, coeffPairing_fullY]
    cases real
    · rw [transferC_singlet]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, f1, f2]
      norm_num
    · rw [transferR_singlet]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, f1, f2, f3, f4]
      norm_num
  · subst hr
    rw [hs, transferC_singlet]
  · subst hr
    refine ⟨fun m => ?_, fun m => ?_, by rw [hs, transferR_singlet], by
      rw [hs, transferR_singlet_norm]⟩
    · rw [(hc rfl m).1, (words_channel m).1]
    · rw [(hc rfl m).2, (words_channel m).2]

/-- The `SU(3)` reference: the words themselves. -/
theorem claims_su3 : Claims (Matrix.toLin' (transferWords bookOrd false)) false :=
  claims_of_agree _ false (fun _ => ⟨Matrix.toLin'_apply _ _, Matrix.toLin'_apply _ _⟩)
    (Matrix.toLin'_apply _ _) (fun h => absurd h (by decide))

theorem quartetX_mem_Φ64 (m : Fin 4) : quartetX m ∈ LinearMap.range Φ64 := by
  rw [quartetX_eq_B64]
  exact B64_mem_range _

theorem quartetY_mem_Φ64 (m : Fin 4) : quartetY m ∈ LinearMap.range Φ64 := by
  rw [quartetY_eq_B64]
  exact B64_mem_range _

theorem quartetX_mem_Φ36 (m : Fin 4) : quartetX m ∈ LinearMap.range Φ36 := by
  rw [quartetX_eq_B36]
  exact B36_mem_range _

theorem quartetY_mem_Φ36 (m : Fin 4) : quartetY m ∈ LinearMap.range Φ36 := by
  rw [quartetY_eq_B36]
  exact B36_mem_range _

/-- A real triplet whose `P V³ P` is the words on the sixty-four products. -/
theorem claims_real (L : Module.End ℂ (Finset EM → ℂ))
    (hL : ∀ v ∈ LinearMap.range Φ64, L v = transferWords bookOrd true *ᵥ v) : Claims L true :=
  claims_of_agree L true (fun m => ⟨hL _ (quartetX_mem_Φ64 m), hL _ (quartetY_mem_Φ64 m)⟩)
    (hL _ singlet_mem_Φ64) fun _ m => ⟨hL _ (by rw [pairQuartet_eq]; exact B64_mem_range _),
      hL _ (by rw [holesQuartet_eq]; exact B64_mem_range _)⟩

/-- A complex triplet whose `P V³ P` is the words on the thirty-six products. -/
theorem claims_complex (L : Module.End ℂ (Finset EM → ℂ))
    (hL : ∀ v ∈ LinearMap.range Φ36, L v = transferWords bookOrd false *ᵥ v) : Claims L false :=
  claims_of_agree L false (fun m => ⟨hL _ (quartetX_mem_Φ36 m), hL _ (quartetY_mem_Φ36 m)⟩)
    (hL _ singlet_mem_Φ36) fun h => absurd h (by decide)

end TransferStates

end Artform
