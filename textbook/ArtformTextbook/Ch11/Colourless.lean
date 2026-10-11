import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ArtformTextbook.Ch11.CubeGroup
import ArtformTextbook.Ch11.Minors
import ArtformTextbook.Ch11.Statements.Colourless

/-!
# Colourless states, and how to count them (Proposition 11.14, Theorem 11.15)

* **Gauge fixing.** Putting `h_x = 1` and `h_y = U` in the definition gives
  `ψ(U) = Γ_y(U) ψ(1)`, and putting `U = 1`, `h_x = h_y = h` shows that `ψ(1)` is fixed by the
  diagonal action; conversely `U ↦ Γ_y(U) φ` is colourless for a diagonal invariant `φ`, because
  second quantization is multiplicative (`Edge.mem_colourless_iff`). So `ψ ↦ ψ(1)` is a linear
  isomorphism of the colourless states onto the diagonal invariants (`Edge.colourlessEquiv`),
  and of the zero-flux states onto the vectors fixed by every gauge pair
  (`Edge.zeroFluxEquiv`).
* **Counting by averaging.** For a finite group acting by matrices `R(h)` that respect a set of
  occupation tables, the average of the `R(h)` times the projector onto those tables is an
  idempotent whose range is the space of invariant tables supported there; its trace is the
  dimension (`Fock.finrank_inf_fixedSub`), as in Proposition 11.5.
* **Traces of second quantizations.** By the minor formula, the trace of `Γ(W)` on the tables
  with `k` quarks is the sum of the principal `k × k` minors of `W`, the coefficient of `z^k` in
  `det(1 + z W)` (`Ch11/Minors.lean`); for `W = diag(g_x, g_y) ⊗ 1_d` this is
  `det(1 + z g_x)^d det(1 + z g_y)^d`, and the sum splits over the quarks at `x` and at `y`
  (`Edge.sum_endSector_secondQuant_diag`). For a unitary `g` of determinant one,
  `det(1 + z g) = 1 + χ(g) z + conj(χ(g)) z² + z³`, since the adjugate of `g` is `g⁻¹ = g†`
  (`Edge.det_one_add_X_smul_of_mem_specialUnitaryGroup`).
-/

namespace Artform

open scoped Matrix ComplexConjugate TensorProduct

open Polynomial

namespace Fock

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The vectors fixed by every matrix of a family. -/
def fixedSub {H : Type*} (R : H → Matrix N N ℂ) : Submodule ℂ (N → ℂ) where
  carrier := {v | ∀ h, R h *ᵥ v = v}
  add_mem' {v w} hv hw h := by
    simp only [Set.mem_ofPred_eq] at hv hw
    rw [Matrix.mulVec_add, hv, hw]
  zero_mem' h := Matrix.mulVec_zero _
  smul_mem' c v hv h := by
    simp only [Set.mem_ofPred_eq] at hv
    rw [Matrix.mulVec_smul, hv]

omit [DecidableEq N] in
theorem mem_fixedSub {H : Type*} {R : H → Matrix N N ℂ} {v : N → ℂ} :
    v ∈ fixedSub R ↔ ∀ h, R h *ᵥ v = v := Iff.rfl

/-- **Counting by averaging.** Let a finite group `H` act by matrices `R(h)`, and let `Z` be the
tables supported on a set `p` of labels, which every `R(h)` respects. Then the dimension of the
invariant tables of `Z` is `(1/|H|) Σ_h Σ_{n ∈ p} R(h)_{nn}`. -/
theorem finrank_inf_fixedSub {H : Type*} [Group H] [Fintype H] (R : H →* Matrix N N ℂ)
    (p : N → Prop) [DecidablePred p] (Z : Submodule ℂ (N → ℂ))
    (hZ : ∀ v, v ∈ Z ↔ ∀ n, v n ≠ 0 → p n)
    (hR : ∀ h n' n, R h n' n ≠ 0 → (p n' ↔ p n)) :
    (Module.finrank ℂ ↥(Z ⊓ fixedSub R) : ℂ) =
      (Fintype.card H : ℂ)⁻¹ * ∑ h, ∑ n ∈ Finset.univ.filter p, R h n n := by
  set A : Matrix N N ℂ := (Fintype.card H : ℂ)⁻¹ • ∑ h, R h with hA
  set E : Matrix N N ℂ := Matrix.diagonal fun n => if p n then 1 else 0 with hE
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hRA : ∀ a, R a * A = A := by
    intro a
    rw [hA, Matrix.mul_smul, Finset.mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => (map_mul R a h).symm
  have hAA : A * A = A := by
    nth_rw 1 [hA]
    rw [Matrix.smul_mul, Finset.sum_mul]
    simp only [hRA, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  have hER : ∀ h, E * R h = R h * E := by
    intro h
    ext n' n
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hz : R h n' n = 0
    · simp [hz]
    · have := hR h n' n hz
      by_cases hpn : p n
      · simp [hpn, this.mpr hpn]
      · simp [hpn, show ¬ p n' from fun h' => hpn (this.mp h')]
  have hEA : E * A = A * E := by
    rw [hA, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    simp only [hER]
  have hEE : E * E = E := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    congr 1
    funext n
    split_ifs <;> simp
  have hPP : E * A * (E * A) = E * A := by
    rw [mul_assoc, ← mul_assoc A E A, ← hEA, mul_assoc, hAA, ← mul_assoc, hEE]
  have hidem : IsIdempotentElem (Matrix.toLin' (E * A)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hEv : ∀ v : N → ℂ, E *ᵥ v = v ↔ ∀ n, v n ≠ 0 → p n := by
    intro v
    rw [hE]
    constructor
    · intro h n hn
      have := congrFun h n
      rw [Matrix.mulVec_diagonal] at this
      by_contra hp
      rw [ite_eq_right hp, zero_mul] at this
      exact hn this.symm
    · intro h
      funext n
      rw [Matrix.mulVec_diagonal]
      by_cases hp : p n
      · rw [ite_eq_left hp, one_mul]
      · rw [ite_eq_right hp, zero_mul]
        by_contra hn
        exact hp (h n (Ne.symm hn))
  have hrange : LinearMap.range (Matrix.toLin' (E * A)) = Z ⊓ fixedSub R := by
    ext v
    rw [LinearMap.mem_range, Submodule.mem_inf, hZ, mem_fixedSub]
    constructor
    · rintro ⟨w, rfl⟩
      rw [Matrix.toLin'_apply]
      refine ⟨(hEv _).mp ?_, fun h => ?_⟩
      · rw [Matrix.mulVec_mulVec, ← mul_assoc, hEE]
      · rw [Matrix.mulVec_mulVec, ← mul_assoc, ← hER, mul_assoc, hRA]
    · rintro ⟨hz, hfix⟩
      refine ⟨v, ?_⟩
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      have hAv : A *ᵥ v = v := by
        rw [hA, Matrix.smul_mulVec, Matrix.sum_mulVec]
        simp only [hfix, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
          smul_smul, inv_mul_cancel₀ hcard, one_smul]
      rw [hAv]
      exact (hEv v).mpr hz
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hidem).trace
  rw [Matrix.trace_toLin'_eq, hrange] at htr
  rw [← htr]
  have h1 : E * A = (Fintype.card H : ℂ)⁻¹ • ∑ h, E * R h := by
    rw [hA, Matrix.mul_smul, Finset.mul_sum]
  rw [h1, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Matrix.trace, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [hE, Matrix.diagonal_mul]

/-- `Γ(W)` keeps the number of quarks: its coefficient between tables with different numbers of
occupied modes is zero. -/
theorem secondQuant_card_eq (ord : LinearOrder N) (W : Matrix N N ℂ) {n' n : Finset N}
    (h : secondQuant ord W n' n ≠ 0) : n'.card = n.card := by
  have := secondQuant_apply_eq_zero_of_labels ord (fun _ => ()) (W := W) (fun _ _ h => absurd rfl h)
    n n' h ()
  simpa [labelCount] using this

omit [DecidableEq N] in
/-- A matrix whose coefficient `R_{n'n}` vanishes unless `p n' ↔ p n` maps the tables supported
on `p` to tables supported on `p`. -/
theorem mulVec_mem_of_respects (R : Matrix N N ℂ) (p : N → Prop)
    (hR : ∀ n' n, R n' n ≠ 0 → (p n' ↔ p n)) {v : N → ℂ} (hv : ∀ n, v n ≠ 0 → p n) :
    ∀ n', (R *ᵥ v) n' ≠ 0 → p n' := by
  intro n' hn'
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
  exact (hR n' n (left_ne_zero_of_mul hn)).mpr (hv n (right_ne_zero_of_mul hn))

omit [Fintype N] [DecidableEq N] in
theorem mem_numberSector {k : ℕ} {v : Finset N → ℂ} :
    v ∈ numberSector N k ↔ ∀ n, v n ≠ 0 → n.card = k := Iff.rfl

end Fock

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [DecidableEq C] in
theorem diag_mul_diag (gx gy gx' gy' : Matrix C C ℂ) :
    (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ) * diag gx' gy' = diag (gx * gx') (gy * gy') := by
  simp only [diag, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Fock.kron_one_mul]

omit [Fintype C] [Fintype S] in
theorem diag_one : (diag (1 : Matrix C C ℂ) 1 : Matrix (Mode C S) (Mode C S) ℂ) = 1 := by
  simp only [diag, Matrix.one_kronecker_one, Matrix.fromBlocks_one]

theorem gammaX_one (ord : LinearOrder (Mode C S)) : gammaX ord (1 : Matrix C C ℂ) = 1 := by
  rw [gammaX, diag_one, Fock.secondQuant_one]

theorem gammaY_one (ord : LinearOrder (Mode C S)) : gammaY ord (1 : Matrix C C ℂ) = 1 := by
  rw [gammaY, diag_one, Fock.secondQuant_one]

theorem gammaX_mul_gammaY (ord : LinearOrder (Mode C S)) (g g' : Matrix C C ℂ) :
    gammaX ord g * gammaY ord g' = Fock.secondQuant ord (diag g g') := by
  rw [gammaX, gammaY, Fock.secondQuant_mul, diag_mul_diag, mul_one, one_mul]

theorem secondQuant_diag_mul (ord : LinearOrder (Mode C S)) (gx gy gx' gy' : Matrix C C ℂ) :
    Fock.secondQuant ord (diag gx gy) * Fock.secondQuant ord (diag gx' gy') =
      Fock.secondQuant ord (diag (gx * gx') (gy * gy')) := by
  rw [Fock.secondQuant_mul, diag_mul_diag]

variable {G : Type*} [Group G]

/-- The action of the gauge pairs on the matter: `(h_x, h_y) ↦ Γ_x(h_x) Γ_y(h_y)`. -/
noncomputable def pairHom (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    G × G →* Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ where
  toFun h := Fock.secondQuant ord (diag (ρ h.1) (ρ h.2))
  map_one' := by simp [diag_one, Fock.secondQuant_one]
  map_mul' a b := by
    rw [secondQuant_diag_mul, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul]

/-- The diagonal action on the matter: `h ↦ Γ_x(h) Γ_y(h)`. -/
noncomputable def diagHom (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    G →* Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ where
  toFun h := Fock.secondQuant ord (diag (ρ h) (ρ h))
  map_one' := by simp [diag_one, Fock.secondQuant_one]
  map_mul' a b := by rw [secondQuant_diag_mul, map_mul]

theorem pairHom_apply (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (hx hy : G) :
    pairHom ρ ord (hx, hy) = gammaX ord (ρ hx) * gammaY ord (ρ hy) := by
  rw [gammaX_mul_gammaY]
  rfl

theorem diagHom_apply (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (h : G) :
    diagHom ρ ord h = gammaX ord (ρ h) * gammaY ord (ρ h) := by
  rw [gammaX_mul_gammaY]
  rfl

/-- Gauge fixing: a state is colourless exactly when `ψ(U) = Γ_y(U) ψ(1)` for every `U` and
`ψ(1)` is fixed by the diagonal action. -/
theorem mem_colourless_iff (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) :
    ψ ∈ colourless ρ ord ↔
      (∀ U, ψ U = gammaY ord (ρ U) *ᵥ ψ 1) ∧ ∀ h, diagHom ρ ord h *ᵥ ψ 1 = ψ 1 := by
  constructor
  · intro hψ
    refine ⟨fun U => ?_, fun h => ?_⟩
    · have := hψ 1 U 1
      rwa [mul_one, inv_one, mul_one, map_one, gammaX_one, one_mul] at this
    · have := hψ h h 1
      rw [mul_one, mul_inv_cancel] at this
      rw [diagHom_apply]
      exact this.symm
  · rintro ⟨hU, hd⟩ hx hy U
    have key : gammaX ord (ρ hx) * gammaY ord (ρ hy) * gammaY ord (ρ U) * diagHom ρ ord hx⁻¹ =
        gammaY ord (ρ (hy * U * hx⁻¹)) := by
      rw [show gammaX ord (ρ hx) = Fock.secondQuant ord (diag (ρ hx) 1) from rfl,
        show gammaY ord (ρ hy) = Fock.secondQuant ord (diag 1 (ρ hy)) from rfl,
        show gammaY ord (ρ U) = Fock.secondQuant ord (diag 1 (ρ U)) from rfl,
        show diagHom ρ ord hx⁻¹ = Fock.secondQuant ord (diag (ρ hx⁻¹) (ρ hx⁻¹)) from rfl,
        show gammaY ord (ρ (hy * U * hx⁻¹)) =
          Fock.secondQuant ord (diag 1 (ρ (hy * U * hx⁻¹))) from rfl,
        secondQuant_diag_mul, secondQuant_diag_mul, secondQuant_diag_mul]
      rw [mul_one, mul_one, ← map_mul, mul_inv_cancel, map_one, one_mul, map_mul, map_mul]
    rw [hU (hy * U * hx⁻¹), hU U, Matrix.mulVec_mulVec]
    conv_rhs => rw [← hd hx⁻¹, Matrix.mulVec_mulVec, key]

/-- A diagonal invariant `φ` gives the colourless state `U ↦ Γ_y(U) φ`. -/
theorem extend_mem_colourless (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    {φ : Finset (Mode C S) → ℂ} (hφ : ∀ h, diagHom ρ ord h *ᵥ φ = φ) :
    (fun U => gammaY ord (ρ U) *ᵥ φ) ∈ colourless ρ ord := by
  rw [mem_colourless_iff]
  refine ⟨fun U => ?_, fun h => ?_⟩
  · rw [map_one, gammaY_one, Matrix.one_mulVec]
  · rw [map_one, gammaY_one, Matrix.one_mulVec, hφ]

/-- `ψ ↦ ψ(1)`, restricted to the states whose tables lie in a subspace `Z` that every `Γ_y`
keeps, is a linear isomorphism of the colourless states onto the diagonal invariants of `Z`. -/
noncomputable def colourlessEquiv (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (Z : Submodule ℂ (Finset (Mode C S) → ℂ))
    (hZ : ∀ (g : G) (v : Finset (Mode C S) → ℂ), v ∈ Z → gammaY ord (ρ g) *ᵥ v ∈ Z) :
    ↥(colourless ρ ord ⊓ stateSector G Z) ≃ₗ[ℂ] ↥(Z ⊓ Fock.fixedSub (diagHom ρ ord)) where
  toFun ψ := ⟨ψ.1 1, (Submodule.mem_pi.mp (Submodule.mem_inf.mp ψ.2).2) 1 (Set.mem_univ _),
    ((mem_colourless_iff ρ ord ψ.1).mp (Submodule.mem_inf.mp ψ.2).1).2⟩
  invFun φ := ⟨fun U => gammaY ord (ρ U) *ᵥ φ.1,
    extend_mem_colourless ρ ord (Submodule.mem_inf.mp φ.2).2,
    Submodule.mem_pi.mpr fun U _ => hZ U _ (Submodule.mem_inf.mp φ.2).1⟩
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl
  left_inv ψ := by
    apply Subtype.ext
    funext U
    exact (((mem_colourless_iff ρ ord ψ.1).mp (Submodule.mem_inf.mp ψ.2).1).1 U).symm
  right_inv φ := by
    apply Subtype.ext
    change gammaY ord (ρ 1) *ᵥ φ.1 = φ.1
    rw [map_one, gammaY_one, Matrix.one_mulVec]

/-- The zero-flux states are the constant states whose value is fixed by every gauge pair. -/
theorem mem_zeroFlux_iff (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) :
    ψ ∈ zeroFlux ρ ord ↔ (∀ U, ψ U = ψ 1) ∧ ∀ h, pairHom ρ ord h *ᵥ ψ 1 = ψ 1 := by
  constructor
  · rintro ⟨hc, hconst⟩
    refine ⟨fun U => hconst U 1, fun h => ?_⟩
    have := hc h.1 h.2 1
    rw [pairHom_apply, ← this, hconst]
  · rintro ⟨hconst, hfix⟩
    refine ⟨fun hx hy U => ?_, fun U V => by rw [hconst U, hconst V]⟩
    rw [hconst, hconst U, ← pairHom_apply, hfix]

/-- `ψ ↦ ψ(1)` is a linear isomorphism of the zero-flux states whose tables lie in `Z` onto the
vectors of `Z` fixed by every gauge pair. -/
noncomputable def zeroFluxEquiv (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (Z : Submodule ℂ (Finset (Mode C S) → ℂ)) :
    ↥(zeroFlux ρ ord ⊓ stateSector G Z) ≃ₗ[ℂ] ↥(Z ⊓ Fock.fixedSub (pairHom ρ ord)) where
  toFun ψ := ⟨ψ.1 1, (Submodule.mem_pi.mp (Submodule.mem_inf.mp ψ.2).2) 1 (Set.mem_univ _),
    ((mem_zeroFlux_iff ρ ord ψ.1).mp (Submodule.mem_inf.mp ψ.2).1).2⟩
  invFun φ := ⟨fun _ => φ.1,
    (mem_zeroFlux_iff ρ ord _).mpr ⟨fun _ => rfl, (Submodule.mem_inf.mp φ.2).2⟩,
    Submodule.mem_pi.mpr fun _ _ => (Submodule.mem_inf.mp φ.2).1⟩
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl
  left_inv ψ := by
    apply Subtype.ext
    funext U
    exact (((mem_zeroFlux_iff ρ ord ψ.1).mp (Submodule.mem_inf.mp ψ.2).1).1 U).symm
  right_inv φ := rfl


section Traces

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [Fintype C] [DecidableEq C] [Fintype S] in
theorem kron_one_map_smul (g : Matrix C C ℂ) :
    (X : ℂ[X]) • (Matrix.kroneckerMap (· * ·) g (1 : Matrix S S ℂ)).map Polynomial.C =
      Matrix.kroneckerMap (· * ·) ((X : ℂ[X]) • g.map Polynomial.C) (1 : Matrix S S ℂ[X]) := by
  ext ⟨c, s⟩ ⟨c', s'⟩
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> simp

/-- `det(1 + A ⊗ 1_S) = det(1 + A)^{|S|}`. -/
theorem det_one_add_kron_one {R : Type*} [CommRing R] (A : Matrix C C R) :
    (1 + Matrix.kroneckerMap (· * ·) A (1 : Matrix S S R)).det = (1 + A).det ^ Fintype.card S := by
  have h1 : (1 : Matrix (C × S) (C × S) R) = Matrix.kroneckerMap (· * ·) (1 : Matrix C C R)
      (1 : Matrix S S R) := Matrix.one_kronecker_one.symm
  rw [h1, ← Matrix.add_kronecker, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
/-- `det(1 + diag(A, B)) = det(1 + A) det(1 + B)`. -/
theorem det_one_add_fromBlocks {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix α α R) (B : Matrix β β R) :
    (1 + Matrix.fromBlocks A 0 0 B).det = (1 + A).det * (1 + B).det := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add, add_zero, add_zero,
    Matrix.det_fromBlocks_zero₂₁]

/-- `det(1 + z (diag(g_x, g_y) ⊗ 1_d)) = det(1 + z g_x)^d det(1 + z g_y)^d`. -/
theorem det_one_add_X_smul_diag (gx gy : Matrix C C ℂ) :
    (1 + (X : ℂ[X]) • (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ).map Polynomial.C).det =
      (1 + (X : ℂ[X]) • gx.map Polynomial.C).det ^ Fintype.card S *
        (1 + (X : ℂ[X]) • gy.map Polynomial.C).det ^ Fintype.card S := by
  rw [diag, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_zero _ (map_zero _),
    smul_zero, kron_one_map_smul, kron_one_map_smul, det_one_add_fromBlocks, det_one_add_kron_one,
    det_one_add_kron_one]

theorem det_one_add_diag (gx gy : Matrix C C ℂ) :
    (1 + (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ)).det =
      (1 + gx).det ^ Fintype.card S * (1 + gy).det ^ Fintype.card S := by
  rw [diag, det_one_add_fromBlocks, det_one_add_kron_one, det_one_add_kron_one]

/-- The trace of `Γ(diag(g_x, g_y) ⊗ 1_d)` is `det(1 + g_x)^d det(1 + g_y)^d`. -/
theorem trace_secondQuant_diag (ord : LinearOrder (Mode C S)) (gx gy : Matrix C C ℂ) :
    (Fock.secondQuant ord (diag gx gy)).trace =
      (1 + gx).det ^ Fintype.card S * (1 + gy).det ^ Fintype.card S := by
  rw [Fock.trace_secondQuant, det_one_add_diag]

/-- The trace of the colour rotation `Γ(g)` of one vertex is `det(1 + g)^d`. -/
theorem trace_vertexGamma (ord : LinearOrder (C × S)) (g : Matrix C C ℂ) :
    (Fock.vertexGamma ord g).trace = (1 + g).det ^ Fintype.card S := by
  rw [Fock.vertexGamma, Fock.trace_secondQuant, det_one_add_kron_one]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem filter_card_eq_powersetCard {M : Type*} [Fintype M] (k : ℕ) :
    (Finset.univ.filter fun n : Finset M => n.card = k) = Finset.powersetCard k Finset.univ := by
  ext n
  simp

/-- The trace of `Γ(diag(g, g) ⊗ 1_d)` on the tables with `k` quarks is the coefficient of `z^k`
in `det(1 + z g)^{2d}`. -/
theorem sum_numberSector_secondQuant_diag (ord : LinearOrder (Mode C S)) (g : Matrix C C ℂ)
    (k : ℕ) :
    ∑ n ∈ Finset.univ.filter (fun n : Finset (Mode C S) => n.card = k),
        Fock.secondQuant ord (diag g g) n n =
      ((1 + (X : ℂ[X]) • g.map Polynomial.C).det ^ (2 * Fintype.card S)).coeff k := by
  rw [filter_card_eq_powersetCard, Fock.sum_powersetCard_secondQuant_diag, det_one_add_X_smul_diag,
    ← pow_add, two_mul]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
/-- The occupied modes of `s.disjSum t` are those of `s` and those of `t`. -/
def disjSumEquiv {α β : Type*} (s : Finset α) (t : Finset β) : (↥s ⊕ ↥t) ≃ ↥(s.disjSum t) where
  toFun := Sum.elim (fun a => ⟨Sum.inl a.1, Finset.inl_mem_disjSum.mpr a.2⟩)
    (fun b => ⟨Sum.inr b.1, Finset.inr_mem_disjSum.mpr b.2⟩)
  invFun x := match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, Finset.inl_mem_disjSum.mp h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, Finset.inr_mem_disjSum.mp h⟩
  left_inv x := by rcases x with ⟨a, h⟩ | ⟨b, h⟩ <;> rfl
  right_inv x := by rcases x with ⟨a | b, h⟩ <;> rfl

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
/-- A principal minor of a block-diagonal matrix is the product of the principal minors of its
blocks. -/
theorem det_fromBlocks_submatrix_disjSum {R : Type*} [CommRing R] {α β : Type*} [DecidableEq α]
    [DecidableEq β] (A : Matrix α α R) (B : Matrix β β R) (s : Finset α) (t : Finset β) :
    ((Matrix.fromBlocks A 0 0 B).submatrix (Subtype.val : ↥(s.disjSum t) → α ⊕ β)
        Subtype.val).det =
      (A.submatrix (Subtype.val : ↥s → α) Subtype.val).det *
        (B.submatrix (Subtype.val : ↥t → β) Subtype.val).det := by
  rw [← Matrix.det_submatrix_equiv_self (disjSumEquiv s t), Matrix.submatrix_submatrix]
  have h : (Matrix.fromBlocks A 0 0 B).submatrix
      ((Subtype.val : ↥(s.disjSum t) → α ⊕ β) ∘ disjSumEquiv s t)
      ((Subtype.val : ↥(s.disjSum t) → α ⊕ β) ∘ disjSumEquiv s t) =
      Matrix.fromBlocks (A.submatrix (Subtype.val : ↥s → α) Subtype.val) 0 0
        (B.submatrix (Subtype.val : ↥t → β) Subtype.val) := by
    ext (a | b) (a' | b') <;> rfl
  rw [h, Matrix.det_fromBlocks_zero₂₁]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
/-- A sum over the tables with `k_x` occupied modes on the left and `k_y` on the right is a
double sum over the left tables and the right tables. -/
theorem sum_filter_toLeft_toRight {α β : Type*} [Fintype α] [Fintype β]
    (F : Finset (α ⊕ β) → ℂ) (kx ky : ℕ) :
    ∑ n ∈ Finset.univ.filter (fun n : Finset (α ⊕ β) => n.toLeft.card = kx ∧ n.toRight.card = ky),
        F n =
      ∑ s ∈ Finset.powersetCard kx Finset.univ, ∑ t ∈ Finset.powersetCard ky Finset.univ,
        F (s.disjSum t) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun n => (n.toLeft, n.toRight)) (fun p => p.1.disjSum p.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp [Finset.mem_product, hn.1, hn.2]
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powersetCard_univ] at hp
    simp [hp.1, hp.2]
  · intro n _
    exact Finset.toLeft_disjSum_toRight
  · intro p _
    simp
  · intro n _
    rw [Finset.toLeft_disjSum_toRight]

/-- The trace of `Γ(diag(g_x, g_y) ⊗ 1_d)` on the tables with `k_x` quarks at `x` and `k_y` at `y`
is the coefficient of `z^{k_x}` in `det(1 + z g_x)^d` times that of `z^{k_y}` in
`det(1 + z g_y)^d`. -/
theorem sum_endSector_secondQuant_diag (ord : LinearOrder (Mode C S)) (gx gy : Matrix C C ℂ)
    (kx ky : ℕ) :
    ∑ n ∈ Finset.univ.filter
        (fun n : Finset (Mode C S) => n.toLeft.card = kx ∧ n.toRight.card = ky),
        Fock.secondQuant ord (diag gx gy) n n =
      ((1 + (X : ℂ[X]) • gx.map Polynomial.C).det ^ Fintype.card S).coeff kx *
        ((1 + (X : ℂ[X]) • gy.map Polynomial.C).det ^ Fintype.card S).coeff ky := by
  rw [sum_filter_toLeft_toRight]
  simp_rw [Fock.secondQuant_diag_eq_det, diag, det_fromBlocks_submatrix_disjSum]
  rw [← Finset.sum_mul_sum, ← Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    ← Matrix.coeff_det_one_add_X_smul_eq_sum_minors, kron_one_map_smul, kron_one_map_smul,
    det_one_add_kron_one, det_one_add_kron_one]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem labelCount_isLeft_true {α β : Type*}
    (n : Finset (α ⊕ β)) : Fock.labelCount Sum.isLeft n true = n.toLeft.card := by
  classical
  have : (n.filter fun m => m.isLeft = true) = n.toLeft.map Function.Embedding.inl := by
    ext (a | b) <;> simp
  rw [Fock.labelCount, this, Finset.card_map]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem labelCount_isLeft_false {α β : Type*}
    (n : Finset (α ⊕ β)) : Fock.labelCount Sum.isLeft n false = n.toRight.card := by
  classical
  have : (n.filter fun m => m.isLeft = false) = n.toRight.map Function.Embedding.inr := by
    ext (a | b) <;> simp
  rw [Fock.labelCount, this, Finset.card_map]

omit [Fintype C] [DecidableEq C] [Fintype S] in
theorem diag_apply_eq_zero (gx gy : Matrix C C ℂ) {m' m : Mode C S}
    (h : m'.isLeft ≠ m.isLeft) : (diag gx gy : Matrix (Mode C S) (Mode C S) ℂ) m' m = 0 := by
  rcases m' with a' | b' <;> rcases m with a | b <;> simp_all [diag]

/-- `Γ(diag(g_x, g_y) ⊗ 1_d)` keeps the numbers of quarks at `x` and at `y`. -/
theorem secondQuant_diag_ends (ord : LinearOrder (Mode C S)) (gx gy : Matrix C C ℂ)
    {n' n : Finset (Mode C S)} (h : Fock.secondQuant ord (diag gx gy) n' n ≠ 0) :
    n'.toLeft.card = n.toLeft.card ∧ n'.toRight.card = n.toRight.card := by
  have hl := Fock.secondQuant_apply_eq_zero_of_labels ord Sum.isLeft
    (W := diag gx gy) (fun _ _ h => diag_apply_eq_zero gx gy h) n n' h
  rw [← labelCount_isLeft_true, ← labelCount_isLeft_true, ← labelCount_isLeft_false,
    ← labelCount_isLeft_false]
  exact ⟨hl true, hl false⟩

end Traces

end Edge

namespace Edge

/-- `det(1 + z A) = 1 + Tr(A) z + Tr(adj A) z² + det(A) z³` for a `3 × 3` matrix. -/
theorem det_one_add_X_smul_fin_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    (1 + (X : ℂ[X]) • A.map Polynomial.C).det =
      1 + Polynomial.C A.trace * X + Polynomial.C A.adjugate.trace * X ^ 2 +
        Polynomial.C A.det * X ^ 3 := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  simp only [Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), zero_add, map_add, map_sub, map_mul]
  ring

/-- For a unitary `g` of determinant one, `det(1 + z g) = 1 + χ(g) z + conj(χ(g)) z² + z³`: the
adjugate of `g` is `g⁻¹ = g†`, whose trace is `conj(χ(g))`. -/
theorem det_one_add_X_smul_of_mem_specialUnitaryGroup {g : Matrix (Fin 3) (Fin 3) ℂ}
    (hg : g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    (1 + (X : ℂ[X]) • g.map Polynomial.C).det =
      1 + Polynomial.C g.trace * X + Polynomial.C (conj g.trace) * X ^ 2 + X ^ 3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hg
  have hu : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
  have hadj : g.adjugate = star g := by
    calc g.adjugate = star g * g * g.adjugate := by rw [hu, one_mul]
      _ = star g := by rw [mul_assoc, Matrix.mul_adjugate, hg.2, one_smul, mul_one]
  rw [det_one_add_X_smul_fin_three, hadj, hg.2, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose, map_one, one_mul]
  rfl

end Edge

namespace Fock

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The dimension of the invariants of a finite group acting by matrices is the average of the
traces. -/
theorem finrank_fixedSub {H : Type*} [Group H] [Fintype H] (R : H →* Matrix N N ℂ) :
    (Module.finrank ℂ ↥(fixedSub R) : ℂ) = (Fintype.card H : ℂ)⁻¹ * ∑ h, (R h).trace := by
  have h := finrank_inf_fixedSub R (fun _ => True) ⊤ (fun v => by simp) (fun _ _ _ _ => Iff.rfl)
  rw [top_inf_eq] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Matrix.trace, Finset.filter_true_of_mem fun _ _ => trivial]
  rfl

end Fock

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] {G : Type*}
  [Group G]

omit [Group G] in
theorem stateSector_top {M : Type*} :
    stateSector G (⊤ : Submodule ℂ (Finset M → ℂ)) = ⊤ := by
  ext ψ
  simp [stateSector]

/-- The colourless states are the diagonal invariants, `ψ ↦ ψ(1)`. -/
noncomputable def colourlessEquivTop (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    ↥(colourless ρ ord) ≃ₗ[ℂ] ↥(Fock.fixedSub (diagHom ρ ord)) :=
  (LinearEquiv.ofEq _ _ (by rw [stateSector_top, inf_top_eq])).symm ≪≫ₗ
    colourlessEquiv ρ ord ⊤ (fun _ _ _ => Submodule.mem_top) ≪≫ₗ
    LinearEquiv.ofEq _ _ (top_inf_eq _)

/-- The zero-flux states are the vectors fixed by every gauge pair, `ψ ↦ ψ(1)`. -/
noncomputable def zeroFluxEquivTop (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    ↥(zeroFlux ρ ord) ≃ₗ[ℂ] ↥(Fock.fixedSub (pairHom ρ ord)) :=
  (LinearEquiv.ofEq _ _ (by rw [stateSector_top, inf_top_eq])).symm ≪≫ₗ
    zeroFluxEquiv ρ ord ⊤ ≪≫ₗ LinearEquiv.ofEq _ _ (top_inf_eq _)

/-- The colour rotations of one vertex, `h ↦ Γ(ρ(h))`, as a homomorphism. -/
noncomputable def vertexHom (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (C × S)) :
    G →* Matrix (Finset (C × S)) (Finset (C × S)) ℂ where
  toFun h := Fock.vertexGamma ord (ρ h)
  map_one' := by
    rw [map_one, Fock.vertexGamma, Matrix.one_kronecker_one, Fock.secondQuant_one]
  map_mul' a b := by
    rw [map_mul, Fock.vertexGamma, Fock.vertexGamma, Fock.vertexGamma, Fock.secondQuant_mul,
      Fock.kron_one_mul]

theorem vertexInvariants_eq (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (C × S)) :
    vertexInvariants ρ ord = Fock.fixedSub (vertexHom ρ ord) := rfl

variable [Fintype G]

theorem finrank_colourless (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    (Module.finrank ℂ ↥(colourless ρ ord) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ h, (1 + ρ h).det ^ (2 * Fintype.card S) := by
  rw [LinearEquiv.finrank_eq (colourlessEquivTop ρ ord), Fock.finrank_fixedSub]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show diagHom ρ ord h = Fock.secondQuant ord (diag (ρ h) (ρ h)) from rfl,
    trace_secondQuant_diag, ← pow_add, two_mul]

theorem finrank_vertexInvariants {S' : Type*} [Fintype S'] [DecidableEq S']
    (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (C × S')) :
    (Module.finrank ℂ ↥(vertexInvariants ρ ord) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ h, (1 + ρ h).det ^ Fintype.card S' := by
  rw [vertexInvariants_eq, Fock.finrank_fixedSub]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show vertexHom ρ ord h = Fock.vertexGamma ord (ρ h) from rfl, trace_vertexGamma]

theorem finrank_zeroFlux (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    (Module.finrank ℂ ↥(zeroFlux ρ ord) : ℂ) =
      ((Fintype.card G : ℂ)⁻¹ * ∑ h, (1 + ρ h).det ^ Fintype.card S) *
        ((Fintype.card G : ℂ)⁻¹ * ∑ h, (1 + ρ h).det ^ Fintype.card S) := by
  rw [LinearEquiv.finrank_eq (zeroFluxEquivTop ρ ord), Fock.finrank_fixedSub, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
  simp only [show ∀ h : G × G, pairHom ρ ord h = Fock.secondQuant ord (diag (ρ h.1) (ρ h.2)) from
    fun h => rfl, trace_secondQuant_diag]
  rw [← Finset.sum_mul_sum]
  ring

end Edge

open Edge in
/-- **Proposition 11.14** (colourless states are the invariants of one vertex). A colourless
state is determined by its value at the identity link, `ψ(1)`, and `ψ(1)` can be any vector fixed
by the diagonal action `Γ_x(h) Γ_y(h)`. Hence the colourless states of one edge with `d` slots
correspond to the invariant occupation tables of one vertex with `2d` slots. The zero-flux space
is the tensor product of the invariant spaces at `x` and `y`. -/
@[book "prop:mt-gauge-fix"]
theorem mtGaugeFix : Statement.mtGaugeFix := by
  intro G _ _ C S _ _ _ _ ρ ord
  refine ⟨fun ψ hψ φ hφ h1 => ?_, fun ψ hψ h => ?_, fun φ hφ => ?_, fun ordv => ?_,
    fun ordx ordy => ?_⟩
  · funext U
    rw [((mem_colourless_iff ρ ord ψ).mp hψ).1 U, ((mem_colourless_iff ρ ord φ).mp hφ).1 U, h1]
  · rw [← diagHom_apply]
    exact ((mem_colourless_iff ρ ord ψ).mp hψ).2 h
  · refine ⟨fun U => gammaY ord (ρ U) *ᵥ φ, extend_mem_colourless ρ ord (φ := φ) fun h => ?_, ?_⟩
    · rw [diagHom_apply]
      exact hφ h
    · change gammaY ord (ρ 1) *ᵥ φ = φ
      rw [map_one, gammaY_one, Matrix.one_mulVec]
  · rw [FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq]
    apply Nat.cast_injective (R := ℂ)
    rw [finrank_colourless, finrank_vertexInvariants, Fintype.card_sum, two_mul]
  · rw [FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq, Module.finrank_tensorProduct]
    apply Nat.cast_injective (R := ℂ)
    rw [Nat.cast_mul, finrank_zeroFlux, finrank_vertexInvariants, finrank_vertexInvariants]

open Edge Polynomial in
/-- **Theorem 11.15** (census of colourless states). On one edge with `d` slots, the number of
colourless states with `k` quarks is the coefficient of `z^k` in
`(1/|G|) Σ_{g ∈ G} (1 + χ(g) z + conj(χ(g)) z² + z³)^{2d}`, a sum over conjugacy classes weighted
by their sizes. The zero-flux states with `k_x` quarks at `x` and `k_y` at `y` number the product
of the coefficients of `z^{k_x}` and `z^{k_y}` in the same average with exponent `d`. -/
@[book "thm:mt-census"]
theorem mtCensus : Statement.mtCensus := by
  intro G _ _ S _ _ ρ hρ ord χ term avg
  have hterm : ∀ e g, term e g = (1 + (X : ℂ[X]) • (ρ g).map Polynomial.C).det ^ e := by
    intro e g
    rw [det_one_add_X_smul_of_mem_specialUnitaryGroup (hρ g)]
  have hnum : ∀ (W : Matrix (Mode (Fin 3) S) (Mode (Fin 3) S) ℂ) (k : ℕ) (n' n : Finset _),
      Fock.secondQuant ord W n' n ≠ 0 → (n'.card = k ↔ n.card = k) := by
    intro W k n' n h
    rw [Fock.secondQuant_card_eq ord W h]
  have hcoeff : ∀ e k, (avg e).coeff k = (Fintype.card G : ℂ)⁻¹ *
      ∑ g, ((1 + (X : ℂ[X]) • (ρ g).map Polynomial.C).det ^ e).coeff k := by
    intro e k
    simp only [avg, Polynomial.coeff_smul, Polynomial.finsetSum_coeff, smul_eq_mul, hterm]
  refine ⟨fun k => ?_, fun e => ?_, fun kx ky => ?_⟩
  · have hZ : ∀ (g : G) (v : Finset (Mode (Fin 3) S) → ℂ),
        v ∈ Fock.numberSector (Mode (Fin 3) S) k →
          gammaY ord (ρ g) *ᵥ v ∈ Fock.numberSector (Mode (Fin 3) S) k :=
      fun g v hv => Fock.mulVec_mem_of_respects (gammaY ord (ρ g))
        (fun n : Finset (Mode (Fin 3) S) => n.card = k) (hnum _ k) hv
    rw [LinearEquiv.finrank_eq (colourlessEquiv ρ ord _ hZ),
      Fock.finrank_inf_fixedSub (diagHom ρ ord) (fun n => n.card = k) _ (fun v => Iff.rfl)
        (fun h => hnum _ k), hcoeff]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    exact sum_numberSector_secondQuant_diag ord (ρ h) k
  · classical
    simp only [avg]
    congr 1
    have hcl : ∀ g h : G, IsConj g h → term e g = term e h := by
      intro g h hgh
      obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
      have hχ : χ (c * g * c⁻¹) = χ g := by
        simp only [χ, map_mul]
        rw [Matrix.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      simp only [term, hχ]
    rw [← Finset.sum_fiberwise Finset.univ ConjClasses.mk (term e)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c
    rw [Finset.sum_congr rfl fun g hg => hcl g (Quotient.out c)
      (ConjClasses.mk_eq_mk_iff_isConj.mp (((Finset.mem_filter.mp hg).2).trans hc.symm)),
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    congr 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  · rw [LinearEquiv.finrank_eq (zeroFluxEquiv ρ ord _),
      Fock.finrank_inf_fixedSub (pairHom ρ ord)
        (fun n => n.toLeft.card = kx ∧ n.toRight.card = ky) _ (fun v => Iff.rfl)
        (fun h n' n hne => by
          obtain ⟨h1, h2⟩ := secondQuant_diag_ends ord (ρ h.1) (ρ h.2) hne
          rw [h1, h2]),
      hcoeff, hcoeff, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
    simp only [show ∀ h : G × G, pairHom ρ ord h = Fock.secondQuant ord (diag (ρ h.1) (ρ h.2)) from
      fun h => rfl, sum_endSector_secondQuant_diag]
    rw [← Finset.sum_mul_sum]
    ring

/-! ## Non-vacuity -/

section NonVacuity

open Edge

/-- An order of the six modes of one edge with one slot. -/
@[instance_reducible]
noncomputable def oneSlotOrder : LinearOrder (Mode (Fin 3) (Fin 1)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- Proposition 11.14 on the book's running example, one edge with one slot over the cube group:
the empty edge is colourless, and a colourless state is determined by its value at the identity
link. -/
example : (fun _ => Fock.ket ∅) ∈ colourless cubeTriplet oneSlotOrder ∧
    ∀ ψ ∈ colourless cubeTriplet oneSlotOrder, ∀ φ ∈ colourless cubeTriplet oneSlotOrder,
      ψ 1 = φ 1 → ψ = φ := by
  let := CubeGroup.fintype
  refine ⟨fun hx hy U => ?_, (mtGaugeFix cubeGroup (Fin 3) (Fin 1) cubeTriplet oneSlotOrder).1⟩
  rw [gammaX_mul_gammaY, Fock.secondQuant_mulVec_vacuum]

/-- Theorem 11.15 on the book's running example: the triplet of the cube group takes values in
`SU(3)`, and the census gives one colourless state with no quark on an edge with one slot, the
empty edge. -/
example : letI := CubeGroup.fintype
    Module.finrank ℂ ↥(colourless cubeTriplet oneSlotOrder ⊓
      stateSector cubeGroup (Fock.numberSector (Mode (Fin 3) (Fin 1)) 0)) = 1 := by
  let := CubeGroup.fintype
  have h := (mtCensus cubeGroup (Fin 1) cubeTriplet cubeTriplet_mem oneSlotOrder).1 0
  have hcard : Fintype.card cubeGroup = 24 := by
    rw [← Nat.card_eq_fintype_card, CubeGroup.card]
  simp only [hcard, Nat.cast_ofNat, Fintype.card_unique, mul_one,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_smul, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    smul_eq_mul, inv_mul_cancel₀, Nat.cast_eq_one] at h
  exact h

end NonVacuity

end Artform
