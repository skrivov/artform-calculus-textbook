import ArtformStages.JointUniverse
import ArtformStages.EnergyTick

/-!
# The joint universe and the kick that carries light

The kick of light is a phase on the potentials, carried onto the fillings by the Fourier transform
(finding 474, `QuantumLight.lean`). Here it is shown, on every map of lines and dots, that a kick
whose phase is blind to gauge changes keeps every Gauss sector of the fillings, and that a kick of
a phase of size `1` keeps the sum of the squares (finding 487 of the research ledger). This closes,
for every kick that reads the fluxes, the step that finding 478 left on paper: the joint universe
with the kick that carries light is one law.

The ends of a filling `E` are `M E` for a table `M` from the lines to the dots; a gauge change moves
the potentials by `Mᵀ φ`; the turn by the ends of `φ` is the Weyl operation `W(0, Mᵀ φ)`.

* `endsTurn`, `endsTurn_apply`, `InSector`, `inSector_iff` (GB1): a wave lies in the Gauss sector
  of the ends `ρ` exactly when every turn by the ends multiplies it by `χ(φ ⬝ ρ)`;
* `inSector_of_comm` (GB2): a table that passes every turn by the ends keeps every Gauss sector;
* `fourier_turn`, `phaseMul_comm_move`, `blindKick`, `blindKick_comm` (GB3): the Fourier transform
  carries the turn by `x` to the move by `-x`, so the kick `F⁻¹ (phase k) F` passes every turn by
  the ends when `k (A + Mᵀ φ) = k A`;
* `blindKick_sector` (GB4): such a kick keeps every Gauss sector;
* `fluxPhase_blind`, `fluxKick_sector`, `energyFluxPhase`, `energyKick_sector` (GB5): on a map
  where no gauge change has a flux, a phase that reads the potentials through their fluxes `C A`
  is blind to gauge changes, the product over the faces of the signed kicks of finding 484 among
  them;
* `fourier_sum_sq`, `fourierInv_sum_sq`, `blindKick_sum_sq` (GB6): the Fourier transform keeps the
  sum of the squares up to the number of configurations, so a kick of a phase of size `1` keeps it.

None of this is new: it is Gauss's law as the gauge symmetry's sectors, and Plancherel's theorem.
-/

open Matrix ComplexConjugate

namespace Artform.Stages

section GaugeBlindKick

variable {L D : Type*} [Fintype L] [DecidableEq L] [Fintype D] {n : ℕ} [NeZero n]

omit [DecidableEq L] [NeZero n] in
/-- The turn by the ends: `(Mᵀ φ) ⬝ E = φ ⬝ (M E)`. -/
theorem transpose_dotProduct (M : Matrix D L (ZMod n)) (φ : D → ZMod n) (E : L → ZMod n) :
    (Mᵀ *ᵥ φ) ⬝ᵥ E = φ ⬝ᵥ (M *ᵥ E) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- **The turn by the ends** of `φ`: the Weyl operation `W(0, Mᵀ φ)`. -/
noncomputable def endsTurn (M : Matrix D L (ZMod n)) (φ : D → ZMod n) :
    Module.End ℂ (LightWave L n) :=
  weyl ((0 : L → ZMod n), Mᵀ *ᵥ φ)

omit [DecidableEq L] in
/-- The turn by the ends of `φ` turns the wave at `E` by `φ ⬝ (M E)`. -/
theorem endsTurn_apply (M : Matrix D L (ZMod n)) (φ : D → ZMod n) (ψ : LightWave L n)
    (E : L → ZMod n) : endsTurn M φ ψ E = ZMod.stdAddChar (φ ⬝ᵥ (M *ᵥ E)) * ψ E := by
  simp [endsTurn, weyl_apply, transpose_dotProduct]

/-- **The Gauss sector** of the ends `ρ`: the waves that are `0` at every filling whose ends are not
`ρ`. -/
def InSector (M : Matrix D L (ZMod n)) (ρ : D → ZMod n) (ψ : LightWave L n) : Prop :=
  ∀ E, M *ᵥ E ≠ ρ → ψ E = 0

omit [DecidableEq L] in
/-- GB1. A wave lies in the Gauss sector of `ρ` exactly when every turn by the ends multiplies it
by `χ(φ ⬝ ρ)`. -/
theorem inSector_iff (M : Matrix D L (ZMod n)) (ρ : D → ZMod n) (ψ : LightWave L n) :
    InSector M ρ ψ ↔ ∀ φ, endsTurn M φ ψ = (ZMod.stdAddChar (φ ⬝ᵥ ρ) : ℂ) • ψ := by
  constructor
  · intro h φ
    funext E
    rw [endsTurn_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hE : M *ᵥ E = ρ
    · rw [hE]
    · rw [h E hE, mul_zero, mul_zero]
  · intro h E hE
    by_contra hψ
    apply hE
    apply eq_of_turn_dotProduct
    intro b
    have := congrFun (h b) E
    rw [endsTurn_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [dotProduct_comm, mul_right_cancel₀ hψ this, dotProduct_comm]

omit [DecidableEq L] in
/-- GB2. A table that passes every turn by the ends keeps every Gauss sector. -/
theorem inSector_of_comm (M : Matrix D L (ZMod n)) (K : Module.End ℂ (LightWave L n))
    (hK : ∀ φ, K * endsTurn M φ = endsTurn M φ * K) {ρ : D → ZMod n} {ψ : LightWave L n}
    (h : InSector M ρ ψ) : InSector M ρ (K ψ) := by
  rw [inSector_iff] at h ⊢
  intro φ
  have := congrArg (fun T => T ψ) (hK φ)
  simp only [Module.End.mul_apply] at this
  rw [← this, h φ, map_smul]

/-- GB3. The Fourier transform carries the turn by `x` to the move by `-x`. -/
theorem fourier_turn (x : L → ZMod n) :
    (waveFourier (V := L) (n := n) : Module.End ℂ (LightWave L n)) * weyl (0, x) =
      weyl (-x, 0) * ↑(waveFourier (V := L) (n := n)) := by
  have := fourier_mul_weyl (V := L) (n := n) 0 x
  simpa using this

omit [DecidableEq L] in
/-- A phase that does not change under the move by `b0` passes the move. -/
theorem phaseMul_comm_move (k : (L → ZMod n) → ℂ) (b0 : L → ZMod n) (h : ∀ A, k (A + b0) = k A) :
    phaseMul k * weyl (b0, 0) = weyl (b0, 0) * phaseMul k := by
  refine LinearMap.ext fun ψ => funext fun A => ?_
  simp [weyl_apply, h A]

/-- **The kick of a phase** `k` on the potentials, carried onto the fillings: `F⁻¹ (phase k) F`. -/
noncomputable def blindKick (k : (L → ZMod n) → ℂ) : Module.End ℂ (LightWave L n) :=
  ↑(waveFourier (V := L) (n := n))⁻¹ * phaseMul k * ↑(waveFourier (V := L) (n := n))

/-- GB3. The kick of a phase blind to gauge changes passes every turn by the ends. -/
theorem blindKick_comm (M : Matrix D L (ZMod n)) (k : (L → ZMod n) → ℂ)
    (hk : ∀ A φ, k (A + Mᵀ *ᵥ φ) = k A) (φ : D → ZMod n) :
    blindKick k * endsTurn M φ = endsTurn M φ * blindKick k := by
  set F := waveFourier (V := L) (n := n)
  set x := Mᵀ *ᵥ φ with hx
  have hF : (F : Module.End ℂ (LightWave L n)) * weyl (0, x) = weyl (-x, 0) * ↑F := fourier_turn x
  have hP : phaseMul k * weyl (-x, 0) = weyl (-x, 0) * phaseMul k := by
    refine phaseMul_comm_move k (-x) fun A => ?_
    have := hk A (-φ)
    rwa [Matrix.mulVec_neg, ← hx] at this
  have h1 : (↑F⁻¹ : Module.End ℂ (LightWave L n)) * weyl (-x, 0) = weyl (0, x) * ↑F⁻¹ := by
    calc (↑F⁻¹ : Module.End ℂ (LightWave L n)) * weyl (-x, 0)
        = ↑F⁻¹ * weyl (-x, 0) * (↑F * ↑F⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = ↑F⁻¹ * (weyl (-x, 0) * ↑F) * ↑F⁻¹ := by simp only [mul_assoc]
      _ = ↑F⁻¹ * (↑F * weyl (0, x)) * ↑F⁻¹ := by rw [hF]
      _ = weyl (0, x) * ↑F⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  unfold blindKick endsTurn
  calc (↑F⁻¹ : Module.End ℂ (LightWave L n)) * phaseMul k * ↑F * weyl (0, x)
      = ↑F⁻¹ * phaseMul k * (↑F * weyl (0, x)) := by simp only [mul_assoc]
    _ = ↑F⁻¹ * phaseMul k * (weyl (-x, 0) * ↑F) := by rw [hF]
    _ = ↑F⁻¹ * (phaseMul k * weyl (-x, 0)) * ↑F := by simp only [mul_assoc]
    _ = ↑F⁻¹ * (weyl (-x, 0) * phaseMul k) * ↑F := by rw [hP]
    _ = ↑F⁻¹ * weyl (-x, 0) * phaseMul k * ↑F := by simp only [mul_assoc]
    _ = weyl (0, x) * ↑F⁻¹ * phaseMul k * ↑F := by rw [h1]
    _ = weyl (0, x) * (↑F⁻¹ * phaseMul k * ↑F) := by simp only [mul_assoc]

/-- GB4. **The kick of a phase blind to gauge changes keeps every Gauss sector.** -/
theorem blindKick_sector (M : Matrix D L (ZMod n)) (k : (L → ZMod n) → ℂ)
    (hk : ∀ A φ, k (A + Mᵀ *ᵥ φ) = k A) {ρ : D → ZMod n} {ψ : LightWave L n}
    (h : InSector M ρ ψ) : InSector M ρ (blindKick k ψ) :=
  inSector_of_comm M _ (blindKick_comm M k hk) h

omit [DecidableEq L] [NeZero n] in
/-- GB5. On a map where no gauge change has a flux, `C (Mᵀ φ) = 0`, a phase that reads the
potentials through their fluxes is blind to gauge changes. -/
theorem fluxPhase_blind {Fc : Type*} (M : Matrix D L (ZMod n)) (C : Matrix Fc L (ZMod n))
    (hC : ∀ φ, C *ᵥ (Mᵀ *ᵥ φ) = 0) (f : (Fc → ZMod n) → ℂ) (A : L → ZMod n) (φ : D → ZMod n) :
    f (C *ᵥ (A + Mᵀ *ᵥ φ)) = f (C *ᵥ A) := by
  rw [Matrix.mulVec_add, hC, add_zero]

/-- GB5. So the kick of such a phase keeps every Gauss sector. -/
theorem fluxKick_sector {Fc : Type*} (M : Matrix D L (ZMod n)) (C : Matrix Fc L (ZMod n))
    (hC : ∀ φ, C *ᵥ (Mᵀ *ᵥ φ) = 0) (f : (Fc → ZMod n) → ℂ) {ρ : D → ZMod n}
    {ψ : LightWave L n} (h : InSector M ρ ψ) :
    InSector M ρ (blindKick (fun A => f (C *ᵥ A)) ψ) :=
  blindKick_sector M _ (fun A φ => fluxPhase_blind M C hC f A φ) h

/-- **The energy kick on the faces**: the product over the faces of the signed kicks of weight `κ`
of their fluxes (finding 484). -/
noncomputable def energyFluxPhase {Fc : Type*} [Fintype Fc] (κ : ℝ) (b : Fc → ZMod n) : ℂ :=
  ∏ f, signedPhase n κ (b f)

/-- GB5. R4's energy kick keeps every Gauss sector of the fillings. -/
theorem energyKick_sector {Fc : Type*} [Fintype Fc] (M : Matrix D L (ZMod n))
    (C : Matrix Fc L (ZMod n)) (hC : ∀ φ, C *ᵥ (Mᵀ *ᵥ φ) = 0) (κ : ℝ) {ρ : D → ZMod n}
    {ψ : LightWave L n}
    (h : InSector M ρ ψ) :
    InSector M ρ (blindKick (fun A => energyFluxPhase κ (C *ᵥ A)) ψ) :=
  fluxKick_sector M C hC (energyFluxPhase κ) h

/-- GB6. **Plancherel**: the Fourier transform keeps the sum of the squares up to the number of
configurations. -/
theorem fourier_sum_sq (ψ : LightWave L n) :
    ∑ k, ‖fourierMap ψ k‖ ^ 2 = (Fintype.card (L → ZMod n) : ℝ) * ∑ c, ‖ψ c‖ ^ 2 := by
  have hconj : ∀ a : ZMod n, conj (ZMod.stdAddChar (-a) : ℂ) = ZMod.stdAddChar a := by
    intro a
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  have key : (∑ k, conj (fourierMap ψ k) * fourierMap ψ k : ℂ) =
      (Fintype.card (L → ZMod n) : ℂ) * ∑ c, conj (ψ c) * ψ c := by
    have expand : ∀ k, conj (fourierMap ψ k) * fourierMap ψ k =
        ∑ c', ∑ c, (ZMod.stdAddChar (k ⬝ᵥ (c' - c)) : ℂ) * (conj (ψ c') * ψ c) := by
      intro k
      rw [fourierMap_apply, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, hconj, dotProduct_sub]
      have : (ZMod.stdAddChar (k ⬝ᵥ c' - k ⬝ᵥ c) : ℂ) =
          ZMod.stdAddChar (k ⬝ᵥ c') * ZMod.stdAddChar (-(k ⬝ᵥ c)) := by
        rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
      rw [this]
      ring
    simp only [expand]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hsum : ∀ c, ∑ k : L → ZMod n, (ZMod.stdAddChar (k ⬝ᵥ (c' - c)) : ℂ) =
        if c' - c = 0 then (Fintype.card (L → ZMod n) : ℂ) else 0 := fun c =>
      sum_turn_dotProduct (c' - c)
    simp only [hsum, sub_eq_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have hre : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = conj z * z := fun z => by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  apply Complex.ofReal_injective
  push_cast
  simp only [hre]
  exact key

/-- GB6. The inverse transform keeps the sum of the squares divided by the number of
configurations. -/
theorem fourierInv_sum_sq (χ : LightWave L n) :
    ∑ c, ‖fourierInvMap χ c‖ ^ 2 = (Fintype.card (L → ZMod n) : ℝ)⁻¹ * ∑ k, ‖χ k‖ ^ 2 := by
  have h := fourier_sum_sq (fourierInvMap χ)
  have hF : fourierMap (fourierInvMap χ) = χ := by
    have := congrArg (fun T => T χ) (fourier_fourierInv (V := L) (n := n))
    simpa using this
  rw [hF] at h
  have hN : (Fintype.card (L → ZMod n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h, inv_mul_cancel_left₀ hN]

/-- GB6. **A kick of a phase of size `1` keeps the sum of the squares.** -/
theorem blindKick_sum_sq (k : (L → ZMod n) → ℂ) (hk : ∀ A, ‖k A‖ = 1) (ψ : LightWave L n) :
    ∑ E, ‖blindKick k ψ E‖ ^ 2 = ∑ E, ‖ψ E‖ ^ 2 := by
  have hN : (Fintype.card (L → ZMod n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hK : blindKick k ψ = fourierInvMap (phaseMul k (fourierMap ψ)) := rfl
  rw [hK, fourierInv_sum_sq]
  have hp : ∑ A, ‖phaseMul k (fourierMap ψ) A‖ ^ 2 = ∑ A, ‖fourierMap ψ A‖ ^ 2 := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [phaseMul_apply, norm_mul, hk A, one_mul]
  rw [hp, fourier_sum_sq, inv_mul_cancel_left₀ hN]

end GaugeBlindKick

end Artform.Stages
