import ArtformStages.EnergyTick
import ArtformStages.GaugeBlindKick

/-!
# R4 on many cells: its drift and its tick (finding 491)

Wave N1 of campaign 15 of road DP. Finding 484 proved R4, the likeness A17 read on energies, on one
cell: a phase that is `1` at `0` and carries the move of one click as the classical kick does on the
real values, at every count but the top, is the signed kick `exp(-π i κ s(b)² / n)`. It left on
paper the drift on the electric patterns and the tick on many cells. Here they are proved, on the
waves of `QuantumLight.lean`: a complex number on every configuration of the potentials.

* `eq_smul_signedPhase_of_realLike` (MC1): on one cell, a phase like the classical kick at every
  count but the top is its value at `0` times the signed kick, `0` included;
* `cellsPhase`, `CellsLike`, `cellsPhase_like`, `eq_cellsPhase_of_like`,
  `energyFluxPhase_eq_cellsPhase` (MC2): on many cells, a phase like the classical kick in the count
  of each cell, the others held, is its value at `0` times the product of the cells' signed kicks,
  and that product is so like; finding 487's energy phase is the product at one weight;
* `energyDrift`, `cellsPhase_neg`, `energyDrift_pattern`, `eq_energyDrift_of_pattern` (MC3): R4's
  drift multiplies the electric pattern of `e` by the product of the lines' signed kicks at the
  counts of `e`, and it is the only table that does;
* `energyKick`, `energyTick`, `cellsPhase_norm`, `energyTick_sum_sq` (MC4): R4's kick reads the
  fluxes `C b`, and R4's tick, the drift after the kick, keeps the sum of the squares;
* `cellsPhase_eq_turn_of_even`, `energyKick_eq_qkick`, `energyDrift_eq_qdrift`,
  `energyTick_eq_qtick` (MC5): on an odd dial at even whole weights R4's tick is finding 474's tick
  of `Cᵀ K C` and `L`.

None of this is new: it is Villain's form of the field's energy read as phases, and its Trotter
step.
-/

open Complex Matrix
open scoped Real

namespace Artform.Stages

section ManyCells

variable {n : ℕ} [NeZero n]

/-! ### MC1: one cell, at every value at `0` -/

/-- MC1. **On one cell**, a phase like the classical kick of weight `κ` at every count but the top
is its value at `0` times the signed kick. -/
theorem eq_smul_signedPhase_of_realLike (κ : ℝ) (φ : ZMod n → ℂ)
    (h : ∀ b, b ≠ dialTop n → RealLike κ φ b) : φ = φ 0 • signedPhase n κ := by
  set ψ : ZMod n → ℂ := fun b => φ b - φ 0 * signedPhase n κ b + signedPhase n κ b with hψ
  have hs0 : signedPhase n κ 0 = 1 := by simp [signedPhase]
  have h0 : ψ 0 = 1 := by simp only [hψ, hs0]; ring
  have hl : ∀ b, b ≠ dialTop n → RealLike κ ψ b := by
    intro b hb
    have h1 := h b hb
    have h2 := signedPhase_realLike κ b hb
    unfold RealLike at h1 h2 ⊢
    simp only [hψ]
    linear_combination h1 + (1 - φ 0) * h2
  have hψs := eq_signedPhase_of_realLike κ ψ h0 hl
  funext b
  have hb := congrFun hψs b
  simp only [hψ] at hb
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination hb

/-! ### MC2: many cells -/

variable {V : Type*} [Fintype V]

/-- **The signed kicks of many cells**, the weight `κ v` on the cell `v`: their product. -/
noncomputable def cellsPhase (κ : V → ℝ) (b : V → ZMod n) : ℂ :=
  ∏ v, signedPhase n (κ v) (b v)

/-- A phase of the configurations is **like the classical kick on every cell** when, read along any
one cell with the other counts held, it is like the classical kick of that cell's weight at every
count of the cell but the top. -/
def CellsLike [DecidableEq V] (κ : V → ℝ) (φ : (V → ZMod n) → ℂ) : Prop :=
  ∀ (b : V → ZMod n) (v : V), b v ≠ dialTop n →
    RealLike (κ v) (fun t => φ (Function.update b v t)) (b v)

/-- The product, with the count of one cell changed. -/
theorem cellsPhase_update [DecidableEq V] (κ : V → ℝ) (b : V → ZMod n) (v : V) (t : ZMod n) :
    cellsPhase κ (Function.update b v t) =
      signedPhase n (κ v) t * ∏ u ∈ Finset.univ.erase v, signedPhase n (κ u) (b u) := by
  rw [cellsPhase, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]

/-- MC2. **The product of the signed kicks is like the classical kick on every cell.** -/
theorem cellsPhase_like [DecidableEq V] (κ : V → ℝ) : CellsLike κ (cellsPhase (n := n) κ) := by
  intro b v hb
  have h := signedPhase_realLike (κ v) (b v) hb
  unfold RealLike at h ⊢
  simp only [cellsPhase_update]
  rw [h]
  ring

/-- MC2. **The likeness on every cell forces the product**: a phase like the classical kick on
every cell is its value at `0` times the product of the cells' signed kicks. -/
theorem eq_cellsPhase_of_like [DecidableEq V] (κ : V → ℝ) (φ : (V → ZMod n) → ℂ)
    (h : CellsLike κ φ) : φ = φ 0 • cellsPhase κ := by
  have key : ∀ S : Finset V, ∀ b : V → ZMod n, (∀ v, v ∉ S → b v = 0) →
      φ b = φ 0 * ∏ v ∈ S, signedPhase n (κ v) (b v) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro b hb
      have hb0 : b = 0 := funext fun v => hb v (Finset.notMem_empty v)
      subst hb0
      simp
    | insert w S hw ih =>
      intro b hb
      have hslice : ∀ t, t ≠ dialTop n →
          RealLike (κ w) (fun t => φ (Function.update b w t)) t := by
        intro t ht
        have h1 := h (Function.update b w t) w (by rw [Function.update_self]; exact ht)
        simpa only [Function.update_idem, Function.update_self] using h1
      have h2 := congrFun (eq_smul_signedPhase_of_realLike (κ w) _ hslice) (b w)
      simp only [Function.update_eq_self, Pi.smul_apply, smul_eq_mul] at h2
      have h3 := ih (Function.update b w 0) (by
        intro v hv
        by_cases hvw : v = w
        · subst hvw
          rw [Function.update_self]
        · rw [Function.update_of_ne hvw]
          exact hb v (by simp [hvw, hv]))
      have h4 : ∏ v ∈ S, signedPhase n (κ v) (Function.update b w 0 v) =
          ∏ v ∈ S, signedPhase n (κ v) (b v) :=
        Finset.prod_congr rfl fun v hv => by
          rw [Function.update_of_ne (by rintro rfl; exact hw hv)]
      rw [h2, h3, h4, Finset.prod_insert hw]
      ring
  funext b
  rw [key Finset.univ b (fun v hv => absurd (Finset.mem_univ v) hv)]
  simp only [Pi.smul_apply, smul_eq_mul, cellsPhase]

omit [NeZero n] in
/-- MC2. Finding 487's energy phase on the faces is the product at one weight. -/
theorem energyFluxPhase_eq_cellsPhase [NeZero n] (κ : ℝ) (b : V → ZMod n) :
    energyFluxPhase κ b = cellsPhase (fun _ => κ) b := rfl

/-! ### MC3: the drift on the electric patterns -/

/-- The signed kick does not see the sign of a count. -/
theorem signedPhase_neg (κ : ℝ) (b : ZMod n) : signedPhase n κ (-b) = signedPhase n κ b := by
  have h : ((-b).valMinAbs) ^ 2 = (b.valMinAbs) ^ 2 := by
    rw [← Int.natAbs_sq, ZMod.natAbs_valMinAbs_neg, Int.natAbs_sq]
  have hc : (((-b).valMinAbs : ℤ) : ℂ) ^ 2 = ((b.valMinAbs : ℤ) : ℂ) ^ 2 := by
    exact_mod_cast h
  rw [signedPhase, signedPhase, hc]

/-- The product of the signed kicks does not see the signs of the counts. -/
theorem cellsPhase_neg (κ : V → ℝ) (b : V → ZMod n) : cellsPhase κ (-b) = cellsPhase κ b := by
  simp only [cellsPhase, Pi.neg_apply, signedPhase_neg]

/-- **R4's drift** of the weights `l` on the lines: the Fourier transform undone, after the product
of the lines' signed kicks, after the transform. -/
noncomputable def energyDrift [DecidableEq V] (l : V → ℝ) : Module.End ℂ (LightWave V n) :=
  blindKick (cellsPhase (n := n) l)

/-- MC3. **R4's drift turns each electric pattern** by the product of the lines' signed kicks at
its counts. -/
theorem energyDrift_pattern [DecidableEq V] (l : V → ℝ) (e : V → ZMod n) :
    energyDrift l (electricPattern e) = cellsPhase l e • electricPattern e := by
  have hF : fourierMap (electricPattern e) =
      (Fintype.card (V → ZMod n) : ℂ) • (Pi.single (-e) 1 : LightWave V n) := by
    funext k
    rw [fourierMap_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ∀ c, (ZMod.stdAddChar (-(k ⬝ᵥ c)) : ℂ) * electricPattern e c =
        ZMod.stdAddChar (c ⬝ᵥ (-(k + e))) := by
      intro c
      rw [electricPattern_apply, turn_mul_turn, dotProduct_neg, dotProduct_add,
        dotProduct_comm c k, dotProduct_comm c e, neg_add]
    rw [Finset.sum_congr rfl fun c _ => h1 c, sum_turn_dotProduct]
    by_cases hk : k = -e
    · subst hk
      simp
    · have hk' : -(k + e) ≠ 0 := fun h0 => hk (eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h0))
      rw [ite_eq_right hk', Pi.single_eq_of_ne hk, mul_zero]
  have hK : phaseMul (cellsPhase l) (Pi.single (-e) 1 : LightWave V n) =
      cellsPhase l e • Pi.single (-e) 1 := by
    funext k
    rw [phaseMul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = -e
    · subst hk
      rw [cellsPhase_neg]
    · rw [Pi.single_eq_of_ne hk, mul_zero, mul_zero]
  have hFi : fourierInvMap (Pi.single (-e) 1 : LightWave V n) =
      (Fintype.card (V → ZMod n) : ℂ)⁻¹ • electricPattern e := by
    funext b
    rw [fourierInvMap_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_eq_single (-e)]
    · rw [Pi.single_eq_same, mul_one, electricPattern_apply, dotProduct_neg, dotProduct_comm]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change fourierInvMap (phaseMul (cellsPhase (n := n) l) (fourierMap (electricPattern e))) = _
  rw [hF, map_smul, hK, map_smul, map_smul, hFi, smul_smul, smul_smul,
    mul_comm _ (cellsPhase l e), mul_assoc, mul_inv_cancel₀ card_config_ne_zero, mul_one]

/-- MC3. **R4's drift is the only table** that turns each electric pattern by the product of the
lines' signed kicks at its counts. -/
theorem eq_energyDrift_of_pattern [DecidableEq V] (l : V → ℝ) (M : Module.End ℂ (LightWave V n))
    (hM : ∀ e, M (electricPattern e) = cellsPhase l e • electricPattern e) :
    M = energyDrift l := by
  refine LinearMap.ext fun ψ => ?_
  rw [eq_sum_electricPattern ψ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, hM, energyDrift_pattern]

/-! ### MC4: the kick and the tick -/

/-- **R4's kick** of the weights `κ` on the faces: the wave at `b` times the product of the faces'
signed kicks of the fluxes `C b`. -/
noncomputable def energyKick {Fc : Type*} [Fintype Fc] (C : Matrix Fc V (ZMod n)) (κ : Fc → ℝ) :
    Module.End ℂ (LightWave V n) :=
  phaseMul fun b => cellsPhase κ (C *ᵥ b)

/-- **R4's tick**: the drift after the kick. -/
noncomputable def energyTick [DecidableEq V] {Fc : Type*} [Fintype Fc] (C : Matrix Fc V (ZMod n))
    (κ : Fc → ℝ) (l : V → ℝ) : Module.End ℂ (LightWave V n) :=
  energyDrift l * energyKick C κ

/-- The product of the signed kicks has size `1`. -/
theorem cellsPhase_norm (κ : V → ℝ) (b : V → ZMod n) : ‖cellsPhase κ b‖ = 1 := by
  rw [cellsPhase, norm_prod]
  exact Finset.prod_eq_one fun v _ => signedPhase_norm _ _

/-- MC4. **R4's tick keeps the sum of the squares** of every wave. -/
theorem energyTick_sum_sq [DecidableEq V] {Fc : Type*} [Fintype Fc] (C : Matrix Fc V (ZMod n))
    (κ : Fc → ℝ) (l : V → ℝ) (ψ : LightWave V n) :
    ∑ b, ‖energyTick C κ l ψ b‖ ^ 2 = ∑ b, ‖ψ b‖ ^ 2 := by
  have hD : energyDrift (n := n) l = blindKick (cellsPhase l) := rfl
  rw [energyTick, Module.End.mul_apply, hD, blindKick_sum_sq _ (cellsPhase_norm l)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [energyKick, phaseMul_apply, norm_mul, cellsPhase_norm, one_mul]

/-! ### MC5: at even whole weights, finding 474's tick -/

/-- The turn of a sum is the product of the turns. -/
theorem turn_sum {ι : Type*} (s : Finset ι) (x : ι → ZMod n) :
    (ZMod.stdAddChar (∑ i ∈ s, x i) : ℂ) = ∏ i ∈ s, (ZMod.stdAddChar (x i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- MC5. **On an odd dial at even whole weights the product of the signed kicks is the dial's
turn** by `-half · Σ k x²`. -/
theorem cellsPhase_eq_turn_of_even (hodd : Odd n) (k : V → ℤ)
    (hk : ∀ v, Even (k v)) (b : V → ZMod n) :
    cellsPhase (fun v => (k v : ℝ)) b =
      (ZMod.stdAddChar (-(half n * ∑ v, (k v : ZMod n) * (b v * b v))) : ℂ) := by
  rw [cellsPhase,
    Finset.prod_congr rfl fun v _ => signedPhase_eq_dialPhase_of_even hodd (hk v) (b v),
    ← turn_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

omit [NeZero n] in
/-- The kick's quadratic form read on the faces: `b ⬝ (Cᵀ D C) b = Σ d (C b)²`. -/
theorem dotProduct_faces {Fc : Type*} [Fintype Fc] [DecidableEq Fc] (C : Matrix Fc V (ZMod n))
    (d : Fc → ZMod n) (b : V → ZMod n) :
    b ⬝ᵥ ((Cᵀ * diagonal d * C) *ᵥ b) = ∑ f, d f * ((C *ᵥ b) f * (C *ᵥ b) f) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- MC5. **R4's kick at even whole weights is finding 474's kick** of `Cᵀ K C`. -/
theorem energyKick_eq_qkick {Fc : Type*} [Fintype Fc] [DecidableEq Fc] (hodd : Odd n)
    (C : Matrix Fc V (ZMod n)) (k : Fc → ℤ) (hk : ∀ f, Even (k f)) :
    energyKick C (fun f => (k f : ℝ)) =
      ↑(qkick (Cᵀ * diagonal (fun f => (k f : ZMod n)) * C)) := by
  refine LinearMap.ext fun ψ => funext fun b => ?_
  rw [energyKick, phaseMul_apply, qkick_apply, cellsPhase_eq_turn_of_even hodd k hk,
    dotProduct_faces]

/-- MC5. **R4's drift at even whole weights is finding 474's drift** of `-L`. -/
theorem energyDrift_eq_qdrift [DecidableEq V] (hodd : Odd n) (l : V → ℤ) (hl : ∀ v, Even (l v)) :
    energyDrift (n := n) (fun v => (l v : ℝ)) =
      (qdrift (-diagonal (fun v => (l v : ZMod n))) : Module.End ℂ (LightWave V n)) := by
  refine (eq_qdrift_of_pattern _ _ fun e => ?_)
  rw [energyDrift_pattern, cellsPhase_eq_turn_of_even hodd l hl]
  have h : -(half n * ∑ v, (l v : ZMod n) * (e v * e v)) =
      half n * (e ⬝ᵥ (-diagonal (fun v => (l v : ZMod n)) *ᵥ e)) := by
    rw [Matrix.neg_mulVec, dotProduct_neg, mul_neg, dotProduct]
    congr 2
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.mulVec_diagonal]
    ring
  rw [h]

/-- MC5. **R4's tick at even whole weights is finding 474's tick** of `Cᵀ K C` and `L`. -/
theorem energyTick_eq_qtick [DecidableEq V] {Fc : Type*} [Fintype Fc] [DecidableEq Fc]
    (hodd : Odd n) (C : Matrix Fc V (ZMod n)) (k : Fc → ℤ) (hk : ∀ f, Even (k f)) (l : V → ℤ)
    (hl : ∀ v, Even (l v)) :
    energyTick C (fun f => (k f : ℝ)) (fun v => (l v : ℝ)) =
      ↑(qtick (Cᵀ * diagonal (fun f => (k f : ZMod n)) * C)
        (diagonal fun v => (l v : ZMod n))) := by
  rw [energyTick, energyKick_eq_qkick hodd C k hk, energyDrift_eq_qdrift hodd l hl, qtick,
    Units.val_mul]

end ManyCells

end Artform.Stages
