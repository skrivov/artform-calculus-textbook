import ArtformTextbook.Ch11.Colourless
import ArtformTextbook.Ch11.Statements.Tick

/-!
# The hop, its coin, and a native tick (Propositions 11.16, 11.17 and Theorem 11.18)

* **The hop is a second-quantized one-quark hop.** For a matrix `X` on the modes write
  `dΓ(X) = Σ_{m,m'} X_{mm'} a†_m a_{m'}`. The hop of the edge at a link value is
  `V_U = dΓ(K_U)` (`Edge.hopAt_eq_dGamma`), `K_U` the hop of one quark. A unitary `D` on the modes
  moves the creations by `D` and the annihilations by its conjugate
  (`Fock.secondQuant_conj_annihilation`), so `Γ(D) dΓ(X) Γ(D)⁻¹ = dΓ(D X D†)`
  (`Fock.secondQuant_conj_dGamma`); for the gauge pair, `D = diag(h_x, h_y) ⊗ 1_d` and
  `D K_U D† = K_{h_y U h_x⁻¹}` (`Edge.diag_mul_coinK`), which is Proposition 11.16.
* **The coin.** `K_U` is self-adjoint with `K_U² = 1` for a unitary `U`, so `W_U` is unitary;
  its second quantization has minors of `W_U` as coefficients (`Ch11/Minors.lean`), and for the
  cube group the entries of `W_U` lie in `R₈`, a ring closed under determinants.
* **The tick.** The read is a convolution by a class function and acts on the link only, so it
  commutes with the gauge action; the coin commutes with it because `D W_{U'} = W_U D` when
  `U = h_y U' h_x⁻¹`. Both keep the pairing of states: the read is unitary by Theorem 11.6 and
  each `Γ(W_U)` by Proposition 11.12.
-/

namespace Artform

open scoped Matrix ComplexConjugate

namespace Fock

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The second quantization of a one-quark operator `X`: `dΓ(X) = Σ_{m,m'} X_{mm'} a†_m a_{m'}`. -/
noncomputable def dGamma (ord : LinearOrder M) (X : Matrix M M ℂ) :
    Matrix (Finset M) (Finset M) ℂ :=
  ∑ m, ∑ m', X m m' • (creation ord m * annihilation ord m')

omit [Fintype M] in
theorem inv_eq_conjTranspose_of_mem {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℂ} (hA : A ∈ Matrix.unitaryGroup N ℂ) : A⁻¹ = Aᴴ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA
  exact Matrix.inv_eq_left_inv hA

omit [Fintype M] in
theorem isUnit_of_mem_unitaryGroup {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℂ} (hA : A ∈ Matrix.unitaryGroup N ℂ) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr
    (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hA))

/-- A unitary `D` moves the annihilations by its conjugate:
`Γ(D) a_m Γ(D)⁻¹ = Σ_l conj(D_{lm}) a_l`. -/
theorem secondQuant_conj_annihilation (ord : LinearOrder M) {D : Matrix M M ℂ}
    (hD : D ∈ Matrix.unitaryGroup M ℂ) (m : M) :
    secondQuant ord D * annihilation ord m * (secondQuant ord D)⁻¹ =
      ∑ l, conj (D l m) • annihilation ord l := by
  have hU := secondQuant_mem_unitaryGroup ord hD
  have hunit : IsUnit D := isUnit_of_mem_unitaryGroup hD
  have h := congrArg Matrix.conjTranspose (secondQuant_conj_creation ord hunit m)
  rw [inv_eq_conjTranspose_of_mem hU] at h ⊢
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    conjTranspose_creation, transformedCreation, Matrix.conjTranspose_sum] at h
  rw [mul_assoc, h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_smul, conjTranspose_creation]
  rfl

/-- Covariance of `dΓ`: `Γ(D) dΓ(X) Γ(D)⁻¹ = dΓ(D X D†)` for a unitary `D`. -/
theorem secondQuant_conj_dGamma (ord : LinearOrder M) {D : Matrix M M ℂ}
    (hD : D ∈ Matrix.unitaryGroup M ℂ) (X : Matrix M M ℂ) :
    secondQuant ord D * dGamma ord X * (secondQuant ord D)⁻¹ = dGamma ord (D * X * star D) := by
  have hunit : IsUnit D := isUnit_of_mem_unitaryGroup hD
  have hinv : (secondQuant ord D)⁻¹ * secondQuant ord D = 1 := by
    rw [secondQuant_inv ord hunit, secondQuant_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det D).mp hunit), secondQuant_one]
  have hpair : ∀ m m', secondQuant ord D * (creation ord m * annihilation ord m') *
      (secondQuant ord D)⁻¹ =
        ∑ k, ∑ l, (D k m * conj (D l m')) • (creation ord k * annihilation ord l) := by
    intro m m'
    calc secondQuant ord D * (creation ord m * annihilation ord m') * (secondQuant ord D)⁻¹
        = (secondQuant ord D * creation ord m * (secondQuant ord D)⁻¹) *
            (secondQuant ord D * annihilation ord m' * (secondQuant ord D)⁻¹) := by
          simp only [mul_assoc]
          rw [← mul_assoc (secondQuant ord D)⁻¹ (secondQuant ord D), hinv, one_mul]
      _ = _ := by
          rw [secondQuant_conj_creation ord hunit, secondQuant_conj_annihilation ord hD,
            transformedCreation, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_mul_smul_comm]
  have lhs : secondQuant ord D * dGamma ord X * (secondQuant ord D)⁻¹ =
      ∑ m, ∑ m', X m m' •
        (secondQuant ord D * (creation ord m * annihilation ord m') * (secondQuant ord D)⁻¹) := by
    simp only [dGamma, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have key : ∀ k l, (D * X * star D) k l = ∑ m, ∑ m', X m m' * (D k m * conj (D l m')) := by
    intro k l
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    rw [Complex.star_def]
    ring
  rw [lhs]
  simp only [hpair, Finset.smul_sum, smul_smul, dGamma, key, Finset.sum_smul]
  calc ∑ m, ∑ m', ∑ k, ∑ l, (X m m' * (D k m * conj (D l m'))) •
        (creation ord k * annihilation ord l)
      = ∑ p : M × M, ∑ q : M × M, (X p.1 p.2 * (D q.1 p.1 * conj (D q.2 p.2))) •
          (creation ord q.1 * annihilation ord q.2) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : M × M, ∑ p : M × M, (X p.1 p.2 * (D q.1 p.1 * conj (D q.2 p.2))) •
          (creation ord q.1 * annihilation ord q.2) := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

end Fock

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The hop is the second quantization of the one-quark hop: `V_U = dΓ(K_U)`. -/
theorem hopAt_eq_dGamma (ord : LinearOrder (Mode C S)) (U : Matrix C C ℂ) :
    hopAt ord U = Fock.dGamma ord (coinK U) := by
  simp only [Fock.dGamma, Fintype.sum_sum_type, coinK, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add, add_zero,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, ite_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.star_apply]
  rw [add_comm, hopAt]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact Finset.sum_comm
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun s _ => ?_
    rw [Complex.star_def]

omit [Fintype C] [DecidableEq C] [Fintype S] in
theorem star_kron_one (g : Matrix C C ℂ) :
    star (Matrix.kroneckerMap (· * ·) g (1 : Matrix S S ℂ)) =
      Matrix.kroneckerMap (· * ·) (star g) (1 : Matrix S S ℂ) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.star_eq_conjTranspose]

omit [Fintype C] [DecidableEq C] [Fintype S] in
theorem star_diag (gx gy : Matrix C C ℂ) :
    star (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ) = diag (star gx) (star gy) := by
  simp only [diag, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.conjTranspose_zero]

theorem diag_mem_unitaryGroup {gx gy : Matrix C C ℂ} (hx : gx ∈ Matrix.unitaryGroup C ℂ)
    (hy : gy ∈ Matrix.unitaryGroup C ℂ) :
    (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ) ∈ Matrix.unitaryGroup (Mode C S) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_diag, diag_mul_diag, Matrix.mem_unitaryGroup_iff'.mp hx,
    Matrix.mem_unitaryGroup_iff'.mp hy, diag_one]

omit [DecidableEq C] in
/-- `D K_U D† = K_{g_y U g_x†}` for `D = diag(g_x, g_y) ⊗ 1_d`. -/
theorem diag_mul_coinK (gx gy U : Matrix C C ℂ) :
    (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ) * coinK U * star (diag gx gy) =
      coinK (gy * U * star gx) := by
  rw [star_diag, diag, diag, coinK, coinK, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Fock.kron_one_mul,
    star_mul, star_star, mul_assoc]

omit [Fintype C] [DecidableEq C] [Fintype S] in
theorem coinK_conjTranspose (U : Matrix C C ℂ) :
    (coinK U : Matrix (Mode C S) (Mode C S) ℂ)ᴴ = coinK U := by
  rw [coinK, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_kron_one, star_kron_one,
    star_star]

theorem coinK_mul_self {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    (coinK U : Matrix (Mode C S) (Mode C S) ℂ) * coinK U = 1 := by
  rw [coinK, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Fock.kron_one_mul,
    Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mem_unitaryGroup_iff.mp hU,
    Matrix.one_kronecker_one, Matrix.fromBlocks_one]

theorem coinW_mem_unitaryGroup {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    (coinW U : Matrix (Mode C S) (Mode C S) ℂ) ∈ Matrix.unitaryGroup (Mode C S) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', coinW, star_smul, star_add, star_one, star_smul,
    Matrix.star_eq_conjTranspose (coinK U), coinK_conjTranspose]
  have hc : star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Exact.sqrt_two_mul_self]
    norm_num
  rw [hc, hI, smul_mul_smul_comm, h2]
  have hK := coinK_mul_self (S := S) hU
  have : (1 + -Complex.I • coinK U) * (1 + Complex.I • coinK U) =
      (2 : ℂ) • (1 : Matrix (Mode C S) (Mode C S) ℂ) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, hK]
    rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg]]
    rw [neg_smul, one_smul, two_smul]
    abel
  rw [this, smul_smul]
  norm_num

/-- `star(ρ g) = ρ(g⁻¹)` for a unitary triplet. -/
theorem star_eq_inv {G : Type*} [Group G] {ρ : G →* Matrix C C ℂ}
    (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ) (g : G) : star (ρ g) = ρ g⁻¹ := by
  calc star (ρ g) = star (ρ g) * (ρ g * ρ g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one,
          mul_one]
    _ = ρ g⁻¹ := by rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.mp (hρ g), one_mul]

variable {G : Type*} [Group G]

/-- Colourless states are the states that every gauge pair fixes. -/
theorem mem_colourless_iff_gaugeAct (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) :
    ψ ∈ colourless ρ ord ↔ ∀ hx hy, gaugeAct ρ ord hx hy ψ = ψ := by
  constructor
  · intro hψ hx hy
    funext V
    rw [gaugeAct, ← hψ hx hy (hy⁻¹ * V * hx)]
    congr 1
    group
  · intro h hx hy U
    have := congrFun (h hx hy) (hy * U * hx⁻¹)
    rw [← this, gaugeAct]
    congr 2
    group

/-- The covariance of the hop at one link value (the identity of Proposition 11.16). -/
theorem hopAt_covariant {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (hx hy U : G) :
    gammaX ord (ρ hx) * gammaY ord (ρ hy) * hopAt ord (ρ U) * (gammaY ord (ρ hy))⁻¹ *
        (gammaX ord (ρ hx))⁻¹ = hopAt ord (ρ (hy * U * hx⁻¹)) := by
  rw [mul_assoc _ (gammaY ord (ρ hy))⁻¹, ← Matrix.mul_inv_rev, gammaX_mul_gammaY,
    hopAt_eq_dGamma, Fock.secondQuant_conj_dGamma ord (diag_mem_unitaryGroup (hρ hx) (hρ hy)),
    diag_mul_coinK, hopAt_eq_dGamma, star_eq_inv hρ, ← map_mul, ← map_mul]

theorem gammaXY_mul_inv {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (hx hy : G) :
    (gammaX ord (ρ hx) * gammaY ord (ρ hy))⁻¹ * (gammaX ord (ρ hx) * gammaY ord (ρ hy)) = 1 := by
  rw [gammaX_mul_gammaY]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (Fock.isUnit_of_mem_unitaryGroup (Fock.secondQuant_mem_unitaryGroup ord
      (diag_mem_unitaryGroup (hρ hx) (hρ hy)))))

/-- The hop commutes with the gauge action. -/
theorem hop_gaugeAct {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (hx hy : G) (ψ : G → Finset (Mode C S) → ℂ) :
    hop ρ ord (gaugeAct ρ ord hx hy ψ) = gaugeAct ρ ord hx hy (hop ρ ord ψ) := by
  funext V
  simp only [hop, gaugeAct, Matrix.mulVec_mulVec]
  congr 1
  have h := hopAt_covariant hρ ord hx hy (hy⁻¹ * V * hx)
  rw [show hy * (hy⁻¹ * V * hx) * hx⁻¹ = V by group] at h
  rw [← h, mul_assoc _ (gammaY ord (ρ hy))⁻¹, ← Matrix.mul_inv_rev, mul_assoc,
    gammaXY_mul_inv hρ, mul_one]

end Edge

open Edge in
/-- **Proposition 11.16** (the hop is covariant). For all gauge pairs and link values,
`Γ_x(h_x) Γ_y(h_y) V_U Γ_y(h_y)⁻¹ Γ_x(h_x)⁻¹ = V_{h_y U h_x⁻¹}`. Hence `V` commutes with the gauge
action of `G × G` on link and matter together, and maps colourless states to colourless
states. -/
@[book "prop:mt-hop-covariant"]
theorem mtHopCovariant : Statement.mtHopCovariant := by
  intro G _ C S _ _ _ _ ρ hρ ord
  refine ⟨hopAt_covariant hρ ord, hop_gaugeAct hρ ord, fun ψ hψ => ?_⟩
  rw [mem_colourless_iff_gaugeAct] at hψ ⊢
  intro hx hy
  rw [← hop_gaugeAct hρ ord, hψ]

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- A ring is closed under determinants. -/
theorem det_mem_of_forall_mem {n : Type*} [Fintype n] [DecidableEq n] (R : Subring ℂ)
    {A : Matrix n n ℂ} (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (R.prod_mem fun i _ => h _ _) _

omit [Fintype C] [DecidableEq C] [Fintype S] in
/-- If `U` has integer entries, so does `K_U`. -/
theorem coinK_apply_int {U : Matrix C C ℂ} (hU : ∀ i j, ∃ z : ℤ, U i j = z) (m m' : Mode C S) :
    ∃ z : ℤ, (coinK U : Matrix (Mode C S) (Mode C S) ℂ) m m' = z := by
  rcases m with a | b <;> rcases m' with a' | b'
  · exact ⟨0, by simp [coinK]⟩
  · obtain ⟨z, hz⟩ := hU b'.1 a.1
    refine ⟨z * (if a.2 = b'.2 then 1 else 0), ?_⟩
    simp only [coinK, Matrix.fromBlocks_apply₁₂, Matrix.kroneckerMap_apply, Matrix.star_apply,
      hz, Matrix.one_apply]
    split_ifs <;> simp
  · obtain ⟨z, hz⟩ := hU b.1 a'.1
    refine ⟨z * (if b.2 = a'.2 then 1 else 0), ?_⟩
    simp only [coinK, Matrix.fromBlocks_apply₂₁, Matrix.kroneckerMap_apply, hz, Matrix.one_apply]
    split_ifs <;> simp
  · exact ⟨0, by simp [coinK]⟩

omit [Fintype C] [Fintype S] in
/-- If `U` has integer entries, the coin `W_U` has its entries in `R₈`. -/
theorem coinW_apply_mem_R8C {U : Matrix C C ℂ} (hU : ∀ i j, ∃ z : ℤ, U i j = z)
    (m m' : Mode C S) : (coinW U : Matrix (Mode C S) (Mode C S) ℂ) m m' ∈ Exact.R8C := by
  obtain ⟨z, hz⟩ := coinK_apply_int (S := S) hU m m'
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (1 : Matrix (Mode C S) (Mode C S) ℂ) m m' = w :=
    ⟨if m = m' then 1 else 0, by rw [Matrix.one_apply]; split_ifs <;> simp⟩
  simp only [coinW, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, hz, hw]
  exact Exact.R8C.mul_mem Exact.inv_sqrt_two_mem_R8C
    (Exact.R8C.add_mem (intCast_mem _ _) (Exact.R8C.mul_mem Exact.I_mem_R8C (intCast_mem _ _)))

/-- The coefficients of `Γ(W)` lie in a ring that contains the entries of `W`. -/
theorem secondQuant_apply_mem (ord : LinearOrder (Mode C S)) (R : Subring ℂ)
    {W : Matrix (Mode C S) (Mode C S) ℂ} (hW : ∀ m m', W m m' ∈ R) (n' n : Finset (Mode C S)) :
    Fock.secondQuant ord W n' n ∈ R := by
  by_cases hc : n'.card = n.card
  · rw [Fock.secondQuant_apply_eq_det ord W n n.card n' rfl hc]
    exact det_mem_of_forall_mem R fun i j => hW _ _
  · have : Fock.secondQuant ord W n' n = 0 := by
      by_contra h
      exact hc (Fock.secondQuant_card_eq ord W h)
    rw [this]
    exact R.zero_mem

end Edge

open Edge in
/-- **Proposition 11.17** (the coin's coefficients are minors). The coefficient of `Γ(W)` from
the `k`-quark state with occupied modes `m₁ < ⋯ < m_k` to the one with occupied modes
`m'₁ < ⋯ < m'_k` is the `k × k` minor of `W` with rows `m'₁, …, m'_k` and columns `m₁, …, m_k`.
Hence the coefficients of `Γ(W_U)` lie in `R₈` for every link value of the cube group, and
`Γ(W_U)` is unitary. -/
@[book "prop:mt-minors"]
theorem mtMinors : Statement.mtMinors := by
  refine ⟨fun M _ _ ord W k n n' hn hn' => Fock.secondQuant_apply_eq_det ord W n k n' hn hn',
    fun S _ _ ord U => ⟨fun n n' => ?_, ?_⟩⟩
  · obtain ⟨σ, s, hU⟩ := U.2
    refine secondQuant_apply_mem ord Exact.R8C
      (fun m m' => coinW_apply_mem_R8C (fun i j => ?_) m m') n' n
    rw [hU]
    refine ⟨if j = σ i then ((s i : ℤˣ) : ℤ) else 0, ?_⟩
    simp only [signedPermMatrix, Matrix.of_apply]
    split_ifs <;> simp
  · exact Fock.secondQuant_mem_unitaryGroup ord (coinW_mem_unitaryGroup
      (Matrix.mem_specialUnitaryGroup_iff.mp (U : Matrix.specialUnitaryGroup (Fin 3) ℂ).2).1)

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
  {G : Type*} [Group G]

theorem tableConv_apply [Fintype G] {A : Type*} [AddCommGroup A] [Module ℂ A] (k : G → ℂ)
    (ψ : G → A) (V : G) : tableConv k ψ V = ∑ h, k h • ψ (h⁻¹ * V) := by
  simp [tableConv, Finset.sum_apply]

/-- Convolution by a class function commutes with the gauge action. -/
theorem tableConv_gaugeAct [Fintype G] (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    {k : G → ℂ} (hk : IsClassFunction k) (hx hy : G) (ψ : G → Finset (Mode C S) → ℂ) :
    tableConv k (gaugeAct ρ ord hx hy ψ) = gaugeAct ρ ord hx hy (tableConv k ψ) := by
  funext V
  simp only [tableConv_apply, gaugeAct, Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine Fintype.sum_equiv (MulAut.conj hy⁻¹).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have h1 : k (hy⁻¹ * h * hy⁻¹⁻¹) = k h := hk hy⁻¹ h
  rw [h1]
  congr 3
  group

theorem responseKernel_isClassFunction {ι : Type*} [Fintype ι] {χ : ι → G → ℂ}
    (hχ : ∀ i, IsClassFunction (χ i)) (d r : ι → ℂ) : IsClassFunction (responseKernel χ d r) := by
  intro h U
  simp only [responseKernel, hχ _ h U]

/-- The coin and a gauge pair: `W_U D = D W_{U'}` for `U = h_y U' h_x⁻¹`. -/
theorem coinW_mul_diag {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (hx hy U' : G) :
    (coinW (ρ (hy * U' * hx⁻¹)) : Matrix (Mode C S) (Mode C S) ℂ) * diag (ρ hx) (ρ hy) =
      diag (ρ hx) (ρ hy) * coinW (ρ U') := by
  have hD := diag_mem_unitaryGroup (S := S) (hρ hx) (hρ hy)
  have hK : coinK (ρ (hy * U' * hx⁻¹)) * diag (ρ hx) (ρ hy) =
      (diag (ρ hx) (ρ hy) : Matrix (Mode C S) (Mode C S) ℂ) * coinK (ρ U') := by
    rw [map_mul, map_mul, ← star_eq_inv hρ, ← diag_mul_coinK, mul_assoc,
      Matrix.mem_unitaryGroup_iff'.mp hD, mul_one]
  simp only [coinW, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hK]

/-- The coin commutes with the gauge action. -/
theorem coin_gaugeAct {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (hx hy : G) (ψ : G → Finset (Mode C S) → ℂ) :
    coin ρ ord (gaugeAct ρ ord hx hy ψ) = gaugeAct ρ ord hx hy (coin ρ ord ψ) := by
  funext V
  simp only [coin, gaugeAct, Matrix.mulVec_mulVec, gammaX_mul_gammaY, Fock.secondQuant_mul]
  congr 2
  have := coinW_mul_diag (S := S) hρ hx hy (hy⁻¹ * V * hx)
  rwa [show hy * (hy⁻¹ * V * hx) * hx⁻¹ = V by group] at this

omit [Group G] in
/-- The pairing of states is the pairing of coefficient tables over the pairs `(U, n)`. -/
theorem statePairing_eq [Fintype G] {M : Type*} [Fintype M] (ψ φ : G → Finset M → ℂ) :
    statePairing ψ φ = coeffPairing (fun p : G × Finset M => ψ p.1 p.2)
      (fun p => φ p.1 p.2) := by
  simp only [statePairing, coeffPairing, Fintype.sum_prod_type]

omit [Group G] in
theorem statePairing_self_eq_zero [Fintype G] {M : Type*} [Fintype M]
    {ψ : G → Finset M → ℂ} (h : statePairing ψ ψ = 0) : ψ = 0 := by
  rw [statePairing_eq, Blocks.coeffPairing_self_eq_zero] at h
  funext U n
  exact congrFun h (U, n)

omit [Group G] in
/-- A family of unitary matrices, one at each link value, keeps the pairing of states. -/
theorem statePairing_mulVec [Fintype G] {M : Type*} [Fintype M] [DecidableEq M]
    (X : G → Matrix (Finset M) (Finset M) ℂ) (hX : ∀ U, X U ∈ Matrix.unitaryGroup (Finset M) ℂ)
    (ψ φ : G → Finset M → ℂ) :
    statePairing (fun U => X U *ᵥ ψ U) (fun U => X U *ᵥ φ U) = statePairing ψ φ := by
  simp only [statePairing]
  refine Finset.sum_congr rfl fun U _ => ?_
  exact (Blocks.mem_unitaryGroup_iff_pairing (X U)).mp (hX U) _ _

/-- Convolution by a kernel whose convolution matrix is unitary keeps the pairing of states. -/
theorem statePairing_tableConv [Fintype G] [DecidableEq G] {M : Type*} [Fintype M]
    {k : G → ℂ} (hk : convolution k ∈ Matrix.unitaryGroup G ℂ) (ψ φ : G → Finset M → ℂ) :
    statePairing (tableConv k ψ) (tableConv k φ) = statePairing ψ φ := by
  have hslice : ∀ (χ : G → Finset M → ℂ) (n : Finset M),
      (fun V => tableConv k χ V n) = convolution k *ᵥ (fun U => χ U n) := by
    intro χ n
    funext V
    rw [Blocks.convolution_mulVec_apply, Blocks.sum_conv_eq_sum_leftWrite, tableConv_apply,
      Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, leftWrite_apply]
  have hswap : ∀ χ ξ : G → Finset M → ℂ,
      statePairing χ ξ = ∑ n, coeffPairing (fun U => χ U n) (fun U => ξ U n) := by
    intro χ ξ
    simp only [statePairing, coeffPairing]
    exact Finset.sum_comm
  rw [hswap, hswap]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hslice, hslice]
  exact (Blocks.mem_unitaryGroup_iff_pairing _).mp hk _ _

end Edge

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
  {G : Type*} [Group G]

theorem coin_add (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ φ : G → Finset (Mode C S) → ℂ) : coin ρ ord (ψ + φ) = coin ρ ord ψ + coin ρ ord φ := by
  funext U
  simp [coin, Matrix.mulVec_add]

theorem coin_smul (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (c : ℂ)
    (ψ : G → Finset (Mode C S) → ℂ) : coin ρ ord (c • ψ) = c • coin ρ ord ψ := by
  funext U
  simp [coin, Matrix.mulVec_smul]

omit [Group G] in
theorem tableConv_add [Fintype G] [Group G] {A : Type*} [AddCommGroup A] [Module ℂ A]
    (k : G → ℂ) (ψ φ : G → A) : tableConv k (ψ + φ) = tableConv k ψ + tableConv k φ := by
  funext V
  simp [tableConv_apply, smul_add, Finset.sum_add_distrib]

omit [Group G] in
theorem tableConv_smul [Fintype G] [Group G] {A : Type*} [AddCommGroup A] [Module ℂ A]
    (k : G → ℂ) (c : ℂ) (ψ : G → A) : tableConv k (c • ψ) = c • tableConv k ψ := by
  funext V
  simp [tableConv_apply, Finset.smul_sum, smul_comm c]

variable [Fintype G] {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- The tick as a linear map of the states. -/
noncomputable def tickLin (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) :
    (G → Finset (Mode C S) → ℂ) →ₗ[ℂ] (G → Finset (Mode C S) → ℂ) where
  toFun := tick ρ ord σ r
  map_add' ψ φ := by simp only [tick, electricRead, tableConv_add, coin_add]
  map_smul' c ψ := by simp only [tick, electricRead, tableConv_smul, coin_smul, RingHom.id_apply]

omit [Fintype G] in
theorem electricKernel_isClassFunction (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (r : ι → ℂ) : IsClassFunction (electricKernel σ r) :=
  responseKernel_isClassFunction (fun i => Blocks.isClassFunction_character (σ i)) _ _

theorem tick_gaugeAct {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ)
    (hx hy : G) (ψ : G → Finset (Mode C S) → ℂ) :
    tick ρ ord σ r (gaugeAct ρ ord hx hy ψ) = gaugeAct ρ ord hx hy (tick ρ ord σ r ψ) := by
  rw [tick, electricRead, tableConv_gaugeAct ρ ord (electricKernel_isClassFunction σ r),
    coin_gaugeAct hρ, tick, electricRead]

/-- The electric kernel is the class function `charComb` of Theorem 11.6. -/
theorem electricKernel_eq_charComb (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (r : ι → ℂ) :
    electricKernel σ r = Blocks.charComb σ r := by
  funext U
  simp [electricKernel, responseKernel, Blocks.charComb, Nat.card_eq_fintype_card]

/-- The read of an electric response is unitary: its convolution matrix is in the unitary
group (Theorem 11.6). -/
theorem convolution_electricKernel_mem [DecidableEq G]
    {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}
    (hσ : IsCompleteFamily σ) {r : ι → ℂ} (hr : IsElectricResponse σ r) :
    convolution (electricKernel σ r) ∈ Matrix.unitaryGroup G ℂ := by
  rw [electricKernel_eq_charComb]
  exact (Blocks.mem_unitaryGroup_iff_of_blocks (fun i => block (σ i))
    (Blocks.block_orthogonal σ hσ.1 hσ.2.1) (Blocks.iSup_block_eq_top σ hσ.2.2)
    (fun i => by have := hσ.1 i; exact Blocks.block_ne_bot (σ i)) _ r
    (fun i _ hψ => Blocks.convolution_charComb σ hσ.1 hσ.2.1 r i hψ)).mpr hr.1

end Edge

open Edge in
/-- **Theorem 11.18** (the tick preserves the colourless sector). `T` commutes with the gauge
action of `G × G`. Hence it maps colourless states to colourless states, and is unitary on them. -/
@[book "thm:mt-tick-gauss"]
theorem mtTickGauss : Statement.mtTickGauss := by
  intro G _ _ C S _ _ _ _ ρ hρ ord ι _ d σ hσ r hr
  classical
  have hcomm := tick_gaugeAct hρ ord σ r
  have hmem : ∀ ψ ∈ colourless ρ ord, tick ρ ord σ r ψ ∈ colourless ρ ord := by
    intro ψ hψ
    rw [mem_colourless_iff_gaugeAct] at hψ ⊢
    intro hx hy
    rw [← hcomm, hψ]
  have hpair : ∀ ψ φ : G → Finset (Mode C S) → ℂ,
      statePairing (tick ρ ord σ r ψ) (tick ρ ord σ r φ) = statePairing ψ φ := by
    intro ψ φ
    exact (statePairing_mulVec (fun U => Fock.secondQuant ord (coinW (ρ U)))
      (fun U => Fock.secondQuant_mem_unitaryGroup ord (coinW_mem_unitaryGroup (hρ U)))
      (electricRead σ r ψ) (electricRead σ r φ)).trans
      (statePairing_tableConv (convolution_electricKernel_mem hσ hr) ψ φ)
  refine ⟨hcomm, hmem, fun ψ _ φ _ => hpair ψ φ, fun φ hφ => ?_⟩
  let T : colourless ρ ord →ₗ[ℂ] colourless ρ ord := (tickLin ρ ord σ r).restrict hmem
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : tick ρ ord σ r ψ.1 = 0 := congrArg Subtype.val hψ
    have hp : statePairing ψ.1 ψ.1 = 0 := by
      rw [← hpair, h0]
      simp [statePairing, coeffPairing]
    exact Subtype.ext (statePairing_self_eq_zero hp)
  obtain ⟨ψ, hψ⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨φ, hφ⟩
  exact ⟨ψ.1, ψ.2, congrArg Subtype.val hψ⟩

/-! ## Non-vacuity -/

section NonVacuity

open Edge

theorem cubeTriplet_unitary (g : cubeGroup) : cubeTriplet g ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (cubeTriplet_mem g)).1

/-- Proposition 11.16 on the book's running example, one edge with one slot over the cube group,
whose triplet is unitary: the hop maps colourless states to colourless states. -/
example : ∀ ψ ∈ colourless cubeTriplet oneSlotOrder,
    hop cubeTriplet oneSlotOrder ψ ∈ colourless cubeTriplet oneSlotOrder :=
  (mtHopCovariant cubeGroup (Fin 3) (Fin 1) cubeTriplet cubeTriplet_unitary oneSlotOrder).2.2

/-- Proposition 11.17 on the book's running example: at the identity link of the cube group, the
coin of one edge with one slot has its coefficients in `R₈` and is unitary. -/
example : (∀ n n', Fock.secondQuant oneSlotOrder
      (coinW (((1 : cubeGroup) : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ)) n' n ∈ Exact.R8C) ∧
    Fock.secondQuant oneSlotOrder (coinW (((1 : cubeGroup) : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ)) ∈ Matrix.unitaryGroup (Finset (Mode (Fin 3) (Fin 1))) ℂ :=
  mtMinors.2 (Fin 1) oneSlotOrder 1

/-- Theorem 11.18 on the book's running example: the cube group has a complete family of
distinct irreducible representations, the response `1` on every block is an electric response,
and the tick maps the colourless states of one edge with one slot to colourless states. -/
example : letI := CubeGroup.fintype
    ∃ (n : ℕ) (d : Fin n → ℕ) (σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ)),
      IsCompleteFamily σ ∧ IsElectricResponse σ (fun _ => 1) ∧
      ∀ ψ ∈ colourless cubeTriplet oneSlotOrder,
        tick cubeTriplet oneSlotOrder σ (fun _ => 1) ψ ∈ colourless cubeTriplet oneSlotOrder := by
  let := CubeGroup.fintype
  obtain ⟨n, d, σ, h1, h2, h3⟩ := (mtBlocks cubeGroup).1
  have hσ : IsCompleteFamily σ := ⟨h1, h2, h3⟩
  have hr : IsElectricResponse σ (fun _ => 1) := ⟨fun _ => by simp, fun _ _ => rfl⟩
  exact ⟨n, d, σ, hσ, hr, (mtTickGauss cubeGroup (Fin 3) (Fin 1) cubeTriplet cubeTriplet_unitary
    oneSlotOrder (Fin n) d σ hσ _ hr).2.1⟩

end NonVacuity

end Artform
