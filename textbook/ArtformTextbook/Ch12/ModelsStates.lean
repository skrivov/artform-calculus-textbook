import ArtformTextbook.Ch12.ModelsSpectra

/-!
# Named states of one edge: the pairs, the quartets, the chain and the singlet

The states of Propositions 12.3, 12.6 and 12.7 written as lists of masks in the book's order
(`Edge.pairX_eq` and its companions), their norms (`FockCalc.Vec.sum_norm_sq`), the sectors with
a given number of quarks inside the zero-flux sector (`FockCalc.range_inf_eq_span`), and the
action of the tally, the total spin, the hole map and the parity on them, each checked by the
kernel on the lists.
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck

namespace FockCalc

variable {M : Type*} [Fintype M] [DecidableEq M] {code : M → ℕ}

/-! ### Supports and norms of the tables of lists -/

theorem Vec.exists_of_toFock_ne_zero {v : Vec} {t : Finset M} (h : Vec.toFock code v t ≠ 0) :
    ∃ p ∈ v, decode code p.1 = t := by
  induction v with
  | nil => exact absurd rfl h
  | cons p v ih =>
    rw [Vec.toFock_cons, Pi.add_apply, Pi.smul_apply, Fock.ket, Pi.single_apply] at h
    by_cases hp : t = decode code p.1
    · exact ⟨p, List.mem_cons_self, hp.symm⟩
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hp), smul_zero, zero_add] at h
      obtain ⟨q, hq, hqt⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hqt⟩

/-- A list whose masks all have a property gives a table supported on it. -/
theorem Vec.toFock_mem (v : Vec) (Z : Submodule ℂ (Finset M → ℂ)) (P : Finset M → Prop)
    (hZ : ∀ w, w ∈ Z ↔ ∀ t, w t ≠ 0 → P t) (h : ∀ p ∈ v, P (decode code p.1)) :
    Vec.toFock code v ∈ Z :=
  (hZ _).mpr fun _ ht => by
    obtain ⟨p, hp, rfl⟩ := Vec.exists_of_toFock_ne_zero ht
    exact h p hp

/-- A list none of whose masks has a property gives a table that vanishes where it holds. -/
theorem Vec.toFock_eq_zero_of (v : Vec) (P : Finset M → Prop)
    (h : ∀ p ∈ v, ¬ P (decode code p.1)) (t : Finset M) (ht : P t) :
    Vec.toFock code v t = 0 := by
  by_contra hne
  obtain ⟨p, hp, rfl⟩ := Vec.exists_of_toFock_ne_zero hne
  exact h p hp ht

variable {D : ℕ} {ord : LinearOrder M}

omit [DecidableEq M] in
theorem card_eq_of_numbering (hN : Numbering code D ord) : Fintype.card M = D := by
  have h : Finset.univ.image code = Finset.range D := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨m, hm⟩ => hm ▸ hN.lt m, fun hi => hN.surj i hi⟩
  rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hN.inj, h, Finset.card_range]

omit [DecidableEq M] in
/-- A sum over the occupation tables is a sum over the masks below `2^D`. -/
theorem sum_finset_eq_sum_range (hN : Numbering code D ord) {β : Type*} [AddCommMonoid β]
    (f : Finset M → β) : ∑ n, f n = ∑ r ∈ Finset.range (2 ^ D), f (decode code r) := by
  classical
  have hinj : Set.InjOn (decode code) (Finset.range (2 ^ D) : Set ℕ) := fun a ha b hb h =>
    decode_injOn hN (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h
  have himage : (Finset.range (2 ^ D)).image (decode code) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Fintype.card_finset,
      card_eq_of_numbering hN]
  rw [← Finset.sum_image fun a ha b hb h => hinj ha hb h, himage]

/-- The squared norm of the table of a list is the sum of the squares of its summed
coefficients. -/
theorem Vec.sum_norm_sq (hN : Numbering code D ord) (v : Vec) :
    ∑ n, ‖Vec.toFock code v n‖ ^ 2 =
      ((∑ r ∈ Finset.range (2 ^ D), Vec.sumAt D r v ^ 2 : ℤ) : ℝ) := by
  rw [sum_finset_eq_sum_range hN]
  push_cast
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Vec.toFock_apply hN v (Finset.mem_range.mp hr), Complex.norm_intCast, sq_abs]

theorem Vec.hilbertNorm_eq (hN : Numbering code D ord) (v : Vec) :
    Fock.hilbertNorm (Vec.toFock code v) =
      Real.sqrt ((∑ r ∈ Finset.range (2 ^ D), Vec.sumAt D r v ^ 2 : ℤ) : ℝ) := by
  rw [Fock.hilbertNorm, Vec.sum_norm_sq hN]

/-! ### Sectors inside a span of independent tables -/

omit [Fintype M] [DecidableEq M] in
/-- In the span of independent tables, each inside or outside a sector given by the support, the
part inside the sector is spanned by the tables inside it. -/
theorem range_inf_eq_span {n : ℕ} (B : Fin n → Finset M → ℂ) (hB : LinearIndependent ℂ B)
    (Z : Submodule ℂ (Finset M → ℂ)) (P : Finset M → Prop)
    (hZ : ∀ v, v ∈ Z ↔ ∀ t, v t ≠ 0 → P t) (s : Finset (Fin n))
    (hin : ∀ j ∈ s, B j ∈ Z) (hout : ∀ j ∉ s, ∀ t, P t → B j t = 0) :
    LinearMap.range (Fintype.linearCombination ℂ B) ⊓ Z =
      Submodule.span ℂ (B '' (s : Set (Fin n))) := by
  classical
  apply le_antisymm
  · rintro v ⟨⟨a, rfl⟩, hv⟩
    rw [Fintype.linearCombination_apply] at hv ⊢
    set vin : Finset M → ℂ := ∑ j ∈ s, a j • B j with hvin
    have hsplit : ∑ j, a j • B j = vin + ∑ j ∈ sᶜ, a j • B j := by
      rw [hvin, ← Finset.sum_add_sum_compl s]
    have hvin_mem : vin ∈ Z := Z.sum_mem fun j hj => Z.smul_mem _ (hin j hj)
    have hout_mem : ∑ j ∈ sᶜ, a j • B j ∈ Z := by
      have := Z.sub_mem hv hvin_mem
      rwa [hsplit, add_sub_cancel_left] at this
    have hout0 : ∑ j ∈ sᶜ, a j • B j = 0 := by
      funext t
      by_cases ht : P t
      · rw [Finset.sum_apply, Pi.zero_apply]
        exact Finset.sum_eq_zero fun j hj => by
          rw [Pi.smul_apply, hout j (Finset.mem_compl.mp hj) t ht, smul_zero]
      · by_contra hne
        exact ht (((hZ _).mp hout_mem) t hne)
    have hcoef : ∀ j ∉ s, a j = 0 := by
      have h0 : ∑ j, (if j ∈ s then 0 else a j) • B j = 0 := by
        rw [← hout0, ← Finset.sum_add_sum_compl s]
        have h1 : ∑ j ∈ s, (if j ∈ s then 0 else a j) • B j = 0 :=
          Finset.sum_eq_zero fun j hj => by rw [ite_eq_left hj, zero_smul]
        rw [h1, zero_add]
        exact Finset.sum_congr rfl fun j hj => by rw [ite_eq_right (Finset.mem_compl.mp hj)]
      intro j hj
      have := Fintype.linearIndependent_iff.mp hB _ h0 j
      rwa [ite_eq_right hj] at this
    rw [hsplit, hout0, add_zero]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨⟨Pi.single j 1, ?_⟩, hin j hj⟩
    rw [Fintype.linearCombination_apply_single, one_smul]

end FockCalc

namespace Edge

/-! ### The quark numbers of the products -/

/-- The quark numbers of the eight states of one vertex. -/
def nq (a : ℕ) : ℕ := [0, 2, 3, 3, 3, 3, 4, 6].getD a 0

theorem basisVec_masks : ∀ j < 64, (basisVec j).all (fun p =>
    (decode code p.1).toLeft.card == nq (j / 8) &&
    (decode code p.1).toRight.card == nq (j % 8)) = true := by
  decide +kernel

theorem basisVec_mask {j : Fin 64} {p : ℕ × ℤ} (hp : p ∈ basisVec j) :
    (decode code p.1).toLeft.card = nq (j / 8) ∧ (decode code p.1).toRight.card = nq (j % 8) := by
  have h := basisVec_masks j j.2
  rw [List.all_eq_true] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h p hp

theorem B64_mem_endSector (j : Fin 64) :
    B64 j ∈ endSector (Fin 3) (Fin 2) (nq (j / 8)) (nq (j % 8)) := by
  rw [B64_eq]
  exact Vec.toFock_mem _ _ (fun t => t.toLeft.card = nq (j / 8) ∧ t.toRight.card = nq (j % 8))
    (fun _ => Iff.rfl) fun p hp => basisVec_mask hp

theorem B64_mem_numberSector (j : Fin 64) :
    B64 j ∈ Fock.numberSector EM (nq (j / 8) + nq (j % 8)) := by
  rw [B64_eq]
  exact Vec.toFock_mem _ _ (fun t => t.card = nq (j / 8) + nq (j % 8)) (fun _ => Iff.rfl)
    fun p hp => by
      rw [← Finset.card_toLeft_add_card_toRight, (basisVec_mask hp).1, (basisVec_mask hp).2]

theorem B64_apply_endSector (j : Fin 64) {t : Finset EM}
    (ht : ¬ (t.toLeft.card = nq (j / 8) ∧ t.toRight.card = nq (j % 8))) : B64 j t = 0 := by
  rw [B64_eq]
  refine Vec.toFock_eq_zero_of _ (fun t => ¬ (t.toLeft.card = nq (j / 8) ∧
    t.toRight.card = nq (j % 8))) (fun p hp h => h (basisVec_mask hp)) t ht

theorem B64_apply_numberSector (j : Fin 64) {t : Finset EM}
    (ht : t.card ≠ nq (j / 8) + nq (j % 8)) : B64 j t = 0 := by
  rw [B64_eq]
  refine Vec.toFock_eq_zero_of _ (fun t => t.card ≠ nq (j / 8) + nq (j % 8))
    (fun p hp h => h ?_) t ht
  rw [← Finset.card_toLeft_add_card_toRight, (basisVec_mask hp).1, (basisVec_mask hp).2]

/-! ### Named states as lists -/

theorem pairX_eq : pairX = Vec.toFock code (basisVec 8) := B64_eq 8

theorem pairY_eq : pairY = Vec.toFock code (basisVec 1) := B64_eq 1

theorem pairX_eq_B64 : pairX = B64 8 := rfl

theorem pairY_eq_B64 : pairY = B64 1 := rfl

theorem quartetX_eq_B64 (m : Fin 4) : quartetX m = B64 ⟨8 * (m + 2), by omega⟩ := by
  fin_cases m <;> rfl

theorem quartetY_eq_B64 (m : Fin 4) : quartetY m = B64 ⟨m + 2, by omega⟩ := by
  fin_cases m <;> rfl

theorem B64_lit :
    B64 1 = Vec.toFock code (basisVec 1) ∧ B64 8 = Vec.toFock code (basisVec 8) ∧
    B64 7 = Vec.toFock code (basisVec 7) ∧ B64 14 = Vec.toFock code (basisVec 14) ∧
    B64 21 = Vec.toFock code (basisVec 21) ∧ B64 28 = Vec.toFock code (basisVec 28) ∧
    B64 35 = Vec.toFock code (basisVec 35) ∧ B64 42 = Vec.toFock code (basisVec 42) ∧
    B64 49 = Vec.toFock code (basisVec 49) ∧ B64 56 = Vec.toFock code (basisVec 56) :=
  ⟨B64_eq 1, B64_eq 8, B64_eq 7, B64_eq 14, B64_eq 21, B64_eq 28, B64_eq 35, B64_eq 42,
    B64_eq 49, B64_eq 56⟩

theorem chain_zero : chain 0 = Vec.toFock code (basisVec 56) := B64_lit.2.2.2.2.2.2.2.2.2

theorem chain_one : chain 1 = (-1 / 3 : ℂ) • Vec.toFock code (basisVec 49) := by
  rw [← B64_lit.2.2.2.2.2.2.2.2.1]
  rfl

theorem chain_two : chain 2 = (-1 / 3 : ℂ) • Vec.toFock code (basisVec 14) := by
  rw [← B64_lit.2.2.2.1]
  rfl

theorem chain_three : chain 3 = Vec.toFock code (basisVec 7) := B64_lit.2.2.1

/-- `6 c` for the chain's ground state `c = ½ (c₁ + c₂ + c₃ + c₄)`. -/
def chainVec : Vec :=
  Vec.combo [(3, basisVec 56), (-1, basisVec 49), (-1, basisVec 14), (3, basisVec 7)]

/-- `6 ψ₀` for the spin-singlet two-baryon state. -/
def singletVec : Vec :=
  Vec.combo [(3, basisVec 21), (-1, basisVec 28), (1, basisVec 35), (-3, basisVec 42)]

theorem chainGround_eq : chainGround = (1 / 6 : ℂ) • Vec.toFock code chainVec := by
  rw [chainGround, Fin.sum_univ_four, chain_zero, chain_one, chain_two, chain_three, chainVec,
    Vec.toFock_combo]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  module

theorem quartet_hilbertNorm_sq :
    (∑ r ∈ Finset.range (2 ^ 6), Vec.sumAt 6 r (Vertex.quartetVec 0) ^ 2 : ℤ) = 1 ∧
    (∑ r ∈ Finset.range (2 ^ 6), Vec.sumAt 6 r (Vertex.quartetVec 1) ^ 2 : ℤ) = 3 ∧
    (∑ r ∈ Finset.range (2 ^ 6), Vec.sumAt 6 r (Vertex.quartetVec 2) ^ 2 : ℤ) = 3 ∧
    (∑ r ∈ Finset.range (2 ^ 6), Vec.sumAt 6 r (Vertex.quartetVec 3) ^ 2 : ℤ) = 1 := by
  decide +kernel

theorem quartet_hilbertNorm_0 : Fock.hilbertNorm (Vertex.quartet Vertex.bookOrd 0) = 1 := by
  rw [Vertex.quartet_eq, Vec.hilbertNorm_eq Vertex.numbering, quartet_hilbertNorm_sq.1]
  simp

theorem quartet_hilbertNorm_1 :
    Fock.hilbertNorm (Vertex.quartet Vertex.bookOrd 1) = Real.sqrt 3 := by
  rw [Vertex.quartet_eq, Vec.hilbertNorm_eq Vertex.numbering, quartet_hilbertNorm_sq.2.1]
  simp

theorem quartet_hilbertNorm_2 :
    Fock.hilbertNorm (Vertex.quartet Vertex.bookOrd 2) = Real.sqrt 3 := by
  rw [Vertex.quartet_eq, Vec.hilbertNorm_eq Vertex.numbering, quartet_hilbertNorm_sq.2.2.1]
  simp

theorem quartet_hilbertNorm_3 : Fock.hilbertNorm (Vertex.quartet Vertex.bookOrd 3) = 1 := by
  rw [Vertex.quartet_eq, Vec.hilbertNorm_eq Vertex.numbering, quartet_hilbertNorm_sq.2.2.2]
  simp

theorem sqrt_three_inv_sq :
    ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = 1 / 3 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem singlet_eq : singlet = (1 / 6 : ℂ) • Vec.toFock code singletVec := by
  have t0 : prod (Fock.normalized (Vertex.quartet Vertex.bookOrd 0))
      (Fock.normalized (Vertex.quartet Vertex.bookOrd 3)) = Vec.toFock code (basisVec 21) := by
    rw [Fock.normalized, Fock.normalized, quartet_hilbertNorm_0, quartet_hilbertNorm_3,
      Complex.ofReal_one, inv_one, one_smul, one_smul]
    exact B64_lit.2.2.2.2.1
  have t1 : prod (Fock.normalized (Vertex.quartet Vertex.bookOrd 1))
      (Fock.normalized (Vertex.quartet Vertex.bookOrd 2)) =
        (1 / 3 : ℂ) • Vec.toFock code (basisVec 28) := by
    rw [Fock.normalized, Fock.normalized, quartet_hilbertNorm_1, quartet_hilbertNorm_2,
      prod_smul_left, prod_smul_right, smul_smul, sqrt_three_inv_sq]
    exact congrArg _ B64_lit.2.2.2.2.2.1
  have t2 : prod (Fock.normalized (Vertex.quartet Vertex.bookOrd 2))
      (Fock.normalized (Vertex.quartet Vertex.bookOrd 1)) =
        (1 / 3 : ℂ) • Vec.toFock code (basisVec 35) := by
    rw [Fock.normalized, Fock.normalized, quartet_hilbertNorm_1, quartet_hilbertNorm_2,
      prod_smul_left, prod_smul_right, smul_smul, sqrt_three_inv_sq]
    exact congrArg _ B64_lit.2.2.2.2.2.2.1
  have t3 : prod (Fock.normalized (Vertex.quartet Vertex.bookOrd 3))
      (Fock.normalized (Vertex.quartet Vertex.bookOrd 0)) = Vec.toFock code (basisVec 42) := by
    rw [Fock.normalized, Fock.normalized, quartet_hilbertNorm_0, quartet_hilbertNorm_3,
      Complex.ofReal_one, inv_one, one_smul, one_smul]
    exact B64_lit.2.2.2.2.2.2.2.1
  have r0 : (Fin.rev 0 : Fin 4) = 3 := rfl
  have r1 : (Fin.rev 1 : Fin 4) = 2 := rfl
  have r2 : (Fin.rev 2 : Fin 4) = 1 := rfl
  have r3 : (Fin.rev 3 : Fin 4) = 0 := rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [singlet, Fin.sum_univ_four, r0, r1, r2, r3, t0, t1, t2, t3, v0, v1, v2, v3, singletVec,
    Vec.toFock_combo]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  module

end Edge

namespace ModelsCheck

open Edge

/-! ### Operators on lists, checked by the kernel -/

/-- A compiled operator sends the list `v` to a list with the trie of `w`. -/
def opCheck (O : OpC) (v w : Vec) : Bool := Vec.trie 12 (OpC.act parB O v) == Vec.trie 12 w

theorem toFock_eq_of_check {a b : Vec} (h : (Vec.trie 12 a == Vec.trie 12 b) = true) :
    Vec.toFock code a = Vec.toFock code b :=
  Vec.toFock_eq_of_trie_eq numbering (by simpa only [beq_iff_eq] using h)

theorem eq_of_three_smul {V : Type*} [AddCommGroup V] [Module ℂ V] {x y : V}
    (h : (3 : ℂ) • x = (3 : ℂ) • y) : x = y :=
  smul_right_injective V three_ne_zero h

theorem tally1_toFock (v w : Vec) (h : opCheck tally1C v w = true) :
    (3 : ℂ) • (tally bookOrd 1 *ᵥ Vec.toFock code v) = Vec.toFock code w := by
  rw [← Matrix.smul_mulVec, ← tally3Op_one, Op.toMat_mulVec_compile numbering parB parB_spec]
  exact toFock_eq_of_check h

theorem tally0_toFock (v w : Vec) (h : opCheck tally0C v w = true) :
    (3 : ℂ) • (tally bookOrd 0 *ᵥ Vec.toFock code v) = Vec.toFock code w := by
  rw [← Matrix.smul_mulVec, ← tally3Op_zero, Op.toMat_mulVec_compile numbering parB parB_spec]
  exact toFock_eq_of_check h

/-- An eigenvector of the tally with the pair hop, from a check of `3 Ω v = c v`. -/
theorem tally1_eigen (v : Vec) (c : ℤ) (h : opCheck tally1C v (Vec.smul c v) = true) :
    tally bookOrd 1 *ᵥ Vec.toFock code v = ((c : ℂ) / 3) • Vec.toFock code v := by
  apply eq_of_three_smul
  rw [tally1_toFock v _ h, Vec.toFock_smul, smul_smul]
  congr 1
  ring

/-- An eigenvector of the tally without the pair hop, from a check of `3 Ω v = c v`. -/
theorem tally0_eigen (v : Vec) (c : ℤ) (h : opCheck tally0C v (Vec.smul c v) = true) :
    tally bookOrd 0 *ᵥ Vec.toFock code v = ((c : ℂ) / 3) • Vec.toFock code v := by
  apply eq_of_three_smul
  rw [tally0_toFock v _ h, Vec.toFock_smul, smul_smul]
  congr 1
  ring

theorem holeMap_toFock (v : Vec) :
    holeMap bookOrd *ᵥ Vec.toFock code v =
      Vec.toFock code ((OpC.act parB holeC v).map fun p => (p.1, upSignF p.1 * p.2)) := by
  rw [holeMap_eq, ← Matrix.mulVec_mulVec, Op.toMat_mulVec_compile numbering parB parB_spec,
    diagonal_mulVec_toFock _ upSignF upSignF_spec]
  rfl

theorem parityX_toFock (v : Vec) :
    parityX *ᵥ Vec.toFock code v = Vec.toFock code (v.map fun p => (p.1, parityF p.1 * p.2)) :=
  diagonal_mulVec_toFock _ parityF parityF_spec v

theorem spinSq_toFock (v : Vec) :
    (4 : ℂ) • (spinSq bookOrd *ᵥ Vec.toFock code v) =
      Vec.toFock code ((v.map fun p => (p.1, spinZ2 p.1 * (spinZ2 p.1 * p.2))) ++
        Vec.smul 2 (OpC.act parB spinPMC v)) := by
  have h4 : (4 : ℂ) • spinSq bookOrd = ((2 : ℂ) • spinZ) * ((2 : ℂ) • spinZ) +
      (2 : ℂ) • (spinPlus bookOrd * (spinPlus bookOrd)ᴴ +
        (spinPlus bookOrd)ᴴ * spinPlus bookOrd) := by
    rw [spinSq, smul_add, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
  have hpm : spinPlus bookOrd * (spinPlus bookOrd)ᴴ + (spinPlus bookOrd)ᴴ * spinPlus bookOrd =
      Op.toMat bookOrd (Op.mul spinPlusOp spinMinusOp ++ Op.mul spinMinusOp spinPlusOp) := by
    rw [Op.toMat_append, Op.toMat_mul, Op.toMat_mul, spinPlusOp_toMat, spinMinusOp_toMat]
  rw [← Matrix.smul_mulVec, h4, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, two_spinZ,
    diagonal_mulVec_toFock _ spinZ2 spinZ2_spec, diagonal_mulVec_toFock _ spinZ2 spinZ2_spec,
    Matrix.smul_mulVec, hpm, Op.toMat_mulVec_compile numbering parB parB_spec,
    Vec.toFock_append, Vec.toFock_smul, List.map_map]
  rfl

/-! ### The named states -/

theorem pairX_mem_cube : pairX ∈ zeroFluxValues cubeTriplet bookOrd := by
  rw [zeroFluxValues_cube, pairX_eq_B64]
  exact ⟨Pi.single 8 1, by rw [Φ64, Fintype.linearCombination_apply_single, one_smul]⟩

theorem pairY_mem_cube : pairY ∈ zeroFluxValues cubeTriplet bookOrd := by
  rw [zeroFluxValues_cube, pairY_eq_B64]
  exact ⟨Pi.single 1 1, by rw [Φ64, Fintype.linearCombination_apply_single, one_smul]⟩

theorem tally_one_pairX : tally bookOrd 1 *ᵥ pairX = (2 : ℂ) • pairX + (2 : ℂ) • pairY := by
  have h := tally1_toFock (basisVec 8) (Vec.combo [(6, basisVec 8), (6, basisVec 1)])
    (by decide +kernel)
  rw [Vec.toFock_combo] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [pairX_eq, pairY_eq]
  apply eq_of_three_smul
  rw [h]
  push_cast
  module

theorem tally_one_pairY : tally bookOrd 1 *ᵥ pairY = (2 : ℂ) • pairX + (2 : ℂ) • pairY := by
  have h := tally1_toFock (basisVec 1) (Vec.combo [(6, basisVec 8), (6, basisVec 1)])
    (by decide +kernel)
  rw [Vec.toFock_combo] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [pairX_eq, pairY_eq]
  apply eq_of_three_smul
  rw [h]
  push_cast
  module

theorem tally_zero_pairX : tally bookOrd 0 *ᵥ pairX = (2 : ℂ) • pairX := by
  rw [pairX_eq, tally0_eigen _ 6 (by decide +kernel)]
  norm_num

theorem tally_zero_pairY : tally bookOrd 0 *ᵥ pairY = (2 : ℂ) • pairY := by
  rw [pairY_eq, tally0_eigen _ 6 (by decide +kernel)]
  norm_num

theorem quartet_checks : ∀ i < 4,
    opCheck tally1C (basisVec (8 * (i + 2))) (Vec.smul 9 (basisVec (8 * (i + 2)))) = true ∧
    opCheck tally1C (basisVec (i + 2)) (Vec.smul 9 (basisVec (i + 2))) = true ∧
    opCheck tally0C (basisVec (8 * (i + 2))) (Vec.smul 9 (basisVec (8 * (i + 2)))) = true ∧
    opCheck tally0C (basisVec (i + 2)) (Vec.smul 9 (basisVec (i + 2))) = true := by
  decide +kernel

theorem quartetX_eq (m : Fin 4) : quartetX m = Vec.toFock code (basisVec (8 * (m + 2))) := by
  rw [quartetX_eq_B64, B64_eq]

theorem quartetY_eq (m : Fin 4) : quartetY m = Vec.toFock code (basisVec (m + 2)) := by
  rw [quartetY_eq_B64, B64_eq]

theorem tally_quartetX (m : Fin 4) :
    tally bookOrd 1 *ᵥ quartetX m = (3 : ℂ) • quartetX m ∧
      tally bookOrd 0 *ᵥ quartetX m = (3 : ℂ) • quartetX m := by
  rw [quartetX_eq, tally1_eigen _ 9 (quartet_checks m m.2).1,
    tally0_eigen _ 9 (quartet_checks m m.2).2.2.1]
  norm_num

theorem tally_quartetY (m : Fin 4) :
    tally bookOrd 1 *ᵥ quartetY m = (3 : ℂ) • quartetY m ∧
      tally bookOrd 0 *ᵥ quartetY m = (3 : ℂ) • quartetY m := by
  rw [quartetY_eq, tally1_eigen _ 9 (quartet_checks m m.2).2.1,
    tally0_eigen _ 9 (quartet_checks m m.2).2.2.2]
  norm_num

theorem tally_zero_chain (i : Fin 4) :
    tally bookOrd 0 *ᵥ chain i = (![6, 10 / 3, 10 / 3, 6] i : ℂ) • chain i := by
  fin_cases i
  · rw [Fin.zero_eta, chain_zero, tally0_eigen _ 18 (by decide +kernel)]
    norm_num
  · rw [Fin.mk_one, chain_one, Matrix.mulVec_smul, tally0_eigen _ 10 (by decide +kernel),
      smul_comm]
    norm_num
  · rw [show (⟨2, by norm_num⟩ : Fin 4) = 2 from rfl, chain_two, Matrix.mulVec_smul,
      tally0_eigen _ 10 (by decide +kernel), smul_comm]
    norm_num
  · rw [show (⟨3, by norm_num⟩ : Fin 4) = 3 from rfl, chain_three,
      tally0_eigen _ 18 (by decide +kernel)]
    norm_num

theorem tally_singlet :
    tally bookOrd 1 *ᵥ singlet = (8 : ℂ) • singlet ∧
      tally bookOrd 0 *ᵥ singlet = (8 : ℂ) • singlet := by
  rw [singlet_eq, Matrix.mulVec_smul, Matrix.mulVec_smul, tally1_eigen _ 24 (by decide +kernel),
    tally0_eigen _ 24 (by decide +kernel)]
  refine ⟨?_, ?_⟩ <;> norm_num <;> exact smul_comm _ _ _

theorem tally_chainGround : tally bookOrd 1 *ᵥ chainGround = (8 : ℂ) • chainGround := by
  rw [chainGround_eq, Matrix.mulVec_smul, tally1_eigen _ 24 (by decide +kernel), smul_comm]
  norm_num

theorem spinSq_singlet : spinSq bookOrd *ᵥ singlet = 0 := by
  have h := spinSq_toFock singletVec
  have h0 : Vec.toFock code ((singletVec.map fun p => (p.1, spinZ2 p.1 * (spinZ2 p.1 * p.2))) ++
      Vec.smul 2 (OpC.act parB spinPMC singletVec)) = Vec.toFock code [] :=
    toFock_eq_of_check (by decide +kernel)
  rw [h0, Vec.toFock_nil] at h
  have h' : spinSq bookOrd *ᵥ Vec.toFock code singletVec = 0 :=
    (smul_eq_zero.mp h).resolve_left (by norm_num)
  rw [singlet_eq, Matrix.mulVec_smul, h', smul_zero]

theorem holeMap_singlet : holeMap bookOrd *ᵥ singlet = chainGround := by
  rw [singlet_eq, chainGround_eq, Matrix.mulVec_smul, holeMap_toFock,
    toFock_eq_of_check (b := chainVec) (by decide +kernel)]

theorem holeMap_chainGround : holeMap bookOrd *ᵥ chainGround = singlet := by
  rw [singlet_eq, chainGround_eq, Matrix.mulVec_smul, holeMap_toFock,
    toFock_eq_of_check (b := singletVec) (by decide +kernel)]

theorem parityX_singlet : parityX *ᵥ singlet = -singlet := by
  rw [singlet_eq, Matrix.mulVec_smul, parityX_toFock,
    toFock_eq_of_check (b := Vec.smul (-1) singletVec) (by decide +kernel), Vec.toFock_smul]
  push_cast
  module

theorem parityX_chainGround : parityX *ᵥ chainGround = chainGround := by
  rw [chainGround_eq, Matrix.mulVec_smul, parityX_toFock,
    toFock_eq_of_check (b := chainVec) (by decide +kernel)]

end ModelsCheck

end Artform
