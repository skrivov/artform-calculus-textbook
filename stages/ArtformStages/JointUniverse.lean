import ArtformStages.FillingWaves
import ArtformStages.QuantumLight
import ArtformStages.TheWalk

/-!
# The joint universe

Light and charges run together (finding 478 of the research ledger on a layered universe). The
charges live in *modes*, each with a base dot of the stage and a charge in `ℤ/n`; an *occupation*
puts `0` or `1` on each mode, and the charge it puts at a dot is the sum of the charges of the
occupied modes based there. A *joint configuration* is a filling on the dial of `n`, as in
`KeepField.lean`, with an occupation; it is a *joint law* when the filling's ends are, at every dot,
the occupation's charge there. *Joint waves* are complex numbers on joint configurations, and the
*waves on joint laws* are those that are `0` off the joint laws: at each occupation, a wave of the
charge sector of `FillingWaves.lean` (`mem_jointWaves_iff`).

The letters of a tick act on joint waves: a *kick*, a sum with complex coefficients of the kept
laws of `FillingWaves.lean` acting on the filling; a *drift*, a phase on the filling; a *matter hop*
along a line, from a mode based at its tail to a mode of the same charge based at its head, which
moves the occupation and puts the charge on the line, times a sign that may depend on the
occupation; and the hop's *gate* of angle `θ`, the identity off the hop's two ends and, on them,
`cos θ` less `i sin θ` times the hop and its reverse.

* `jointLaw`, `exists_jointLaw_iff` (JU1): an occupation is the occupation of some joint law exactly
  when the charges it puts at all dots add up to `0` in `ℤ/n`: a closed space is neutral, up to the
  dial;
* `jointWaves`, `kick_jointWave`, `drift_jointWave`, `hop_jointWave`, `hopReverse_jointWave`
  (JU2): each letter takes waves on joint laws to waves on joint laws, and so does a gate
  (`gate_jointWave`);
* `hop_books`, `hop_makes_pair` (JU3): a matter hop puts its charge `q` on its line, and changes
  the filling's ends and the occupation's charges both by `q` at the line's head and `-q` at its
  tail;
* `drift_norm`, `kept_norm`, `gate_norm`, `gate_neg_gate` (JU4): a drift whose phases have size
  `1`, a kept law and a gate keep the sum of the squares of the sizes, and the gate of `-θ` undoes
  the gate of `θ`; the kept law of `-z` undoes that of `z`, and the drift of the inverse phases
  that of the phases (`kept_neg_kept`, `drift_inv_drift`);
* `qdriftPhase`, `qdrift_electricPattern`, `qdrift_jointWave`, `qdrift_norm`: the phase by which
  the quantum drift of `QuantumLight.lean` multiplies the electric pattern of a filling,
  `χ(half · c ⬝ A c)`, is such a drift, read on the filling as the electric field.

The proofs of JU4 pair each end of a hop with the other end: on each pair the gate acts by the
link gate of `TheWalk.lean`, `coin (s θ) = cos θ · 1 - i s sin θ · σx`, with `s = ±1` the hop's
sign (`gate_pair`), which keeps the sum of the squares by `exchange_unitary_iff`.
-/

noncomputable section

open Complex Matrix

namespace Artform.Stages

variable {α : Type*} {S : Stage α} {n : ℕ} {M : Type*}

/-- Modes of the charges: each mode has a base dot of the stage and a charge in `ℤ/n`. -/
structure Modes (S : Stage α) (n : ℕ) (M : Type*) where
  /-- The dot where a mode is based. -/
  base : M → S.World
  /-- The charge of a mode. -/
  charge : M → ZMod n

namespace Modes

/-- The charge that an occupation puts at the dots: the sum of the charges of the occupied modes,
each at its base. -/
def occCharge [Fintype M] [DecidableEq S.World] (μ : Modes S n M) (o : M → Bool) :
    S.World → ZMod n :=
  ∑ m, if o m then μ.charge m • Pi.single (μ.base m) 1 else 0

/-- Changing the occupation of one mode changes the charges by that mode's charge at its base. -/
theorem occCharge_update [Fintype M] [DecidableEq M] [DecidableEq S.World] (μ : Modes S n M)
    (o : M → Bool) (i : M) (b : Bool) :
    μ.occCharge (Function.update o i b) =
      μ.occCharge o - (if o i then μ.charge i • Pi.single (μ.base i) 1 else 0) +
        (if b then μ.charge i • Pi.single (μ.base i) 1 else 0) := by
  have h : ∑ m ∈ Finset.univ.erase i,
      (if Function.update o i b m then μ.charge m • Pi.single (μ.base m) 1 else 0) =
      ∑ m ∈ Finset.univ.erase i, (if o m then μ.charge m • Pi.single (μ.base m) 1 else 0) :=
    Finset.sum_congr rfl fun m hm => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  simp only [occCharge]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self, h]
  abel

end Modes

/-- A joint configuration: a filling on the dial of `n` and an occupation of the modes. -/
abbrev JointConf (S : Stage α) (n : ℕ) (M : Type*) : Type _ :=
  (α × S.World → ZMod n) × (M → Bool)

/-- Joint waves: a complex number on every joint configuration. -/
abbrev JointWave (S : Stage α) (n : ℕ) (M : Type*) : Type _ := JointConf S n M → ℂ

/-! ### Joint laws -/

/-- **JU1.** A joint law: a joint configuration whose filling's ends are, at every dot, the
occupation's charge there. -/
def jointLaw [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M] (μ : Modes S n M)
    (κ : JointConf S n M) : Prop :=
  S.endsDial n κ.1 = μ.occCharge κ.2

/-- **JU1.** A closed space is neutral, up to the dial: an occupation is the occupation of some
joint law exactly when the charges it puts at all dots add up to `0` in `ℤ/n`. -/
theorem exists_jointLaw_iff [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) (o : M → Bool) :
    (∃ c, jointLaw μ (c, o)) ↔ ∑ g, μ.occCharge o g = 0 := by
  rw [← S.endsDial_mem_range_iff n (μ.occCharge o), AddMonoidHom.mem_range]
  rfl

/-- **JU2.** The waves on joint laws: the joint waves that are `0` off the joint laws. -/
def jointWaves [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) : Submodule ℂ (JointWave S n M) where
  carrier := {Ψ | ∀ κ, ¬ jointLaw μ κ → Ψ κ = 0}
  add_mem' {Ψ Φ} hΨ hΦ κ hκ := by
    simp only [Pi.add_apply, hΨ κ hκ, hΦ κ hκ, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' a Ψ hΨ κ hκ := by
    simp only [Pi.smul_apply, hΨ κ hκ, smul_zero]

/-- A wave on joint laws is, at each occupation, a wave of the charge sector of the occupation's
charge (`Stage.waveSector`). -/
theorem mem_jointWaves_iff [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) (Ψ : JointWave S n M) :
    Ψ ∈ jointWaves μ ↔ ∀ o, (fun c => Ψ (c, o)) ∈ S.waveSector n (μ.occCharge o) :=
  ⟨fun h o c hc => h (c, o) hc, fun h κ hκ => h κ.2 κ.1 hκ⟩

/-! ### Kicks and drifts -/

/-- The kept law of a closed filling `z` acting on the filling of the joint waves. -/
def jointKept [Fintype α] [Fintype S.World] [DecidableEq S.World] (z : (S.endsDial n).ker) :
    Module.End ℂ (JointWave S n M) :=
  LinearMap.funLeft ℂ ℂ fun κ => (κ.1 - z, κ.2)

/-- The kept law on the joint waves is `Stage.waveKept` at each occupation. -/
theorem jointKept_apply [Fintype α] [Fintype S.World] [DecidableEq S.World]
    (z : (S.endsDial n).ker) (Ψ : JointWave S n M) (κ : JointConf S n M) :
    jointKept z Ψ κ = S.waveKept n z (fun c => Ψ (c, κ.2)) κ.1 := rfl

/-- **JU2.** A kick: a sum, with complex coefficients, of kept laws acting on the filling. -/
def jointKick [Fintype α] [Fintype S.World] [DecidableEq S.World]
    (a : (S.endsDial n).ker →₀ ℂ) : Module.End ℂ (JointWave S n M) :=
  a.sum fun z w => w • jointKept z

/-- **JU2.** A drift: the phase `φ` on the filling. -/
def jointDrift (φ : (α × S.World → ZMod n) → ℂ) : Module.End ℂ (JointWave S n M) where
  toFun Ψ κ := φ κ.1 * Ψ κ
  map_add' Ψ Φ := funext fun κ => mul_add _ _ _
  map_smul' a Ψ := funext fun κ => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A kept law takes waves on joint laws to waves on joint laws. -/
theorem kept_jointWave [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) (z : (S.endsDial n).ker) {Ψ : JointWave S n M} (hΨ : Ψ ∈ jointWaves μ) :
    jointKept z Ψ ∈ jointWaves μ := by
  intro κ hκ
  apply hΨ
  intro h
  apply hκ
  change S.endsDial n (κ.1 - z) = μ.occCharge κ.2 at h
  rw [map_sub, AddMonoidHom.mem_ker.mp z.2, sub_zero] at h
  exact h

/-- **JU2.** A kick takes waves on joint laws to waves on joint laws. -/
theorem kick_jointWave [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) (a : (S.endsDial n).ker →₀ ℂ) {Ψ : JointWave S n M}
    (hΨ : Ψ ∈ jointWaves μ) : jointKick a Ψ ∈ jointWaves μ := by
  rw [jointKick, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (kept_jointWave μ z hΨ)

/-- **JU2.** A drift takes waves on joint laws to waves on joint laws. -/
theorem drift_jointWave [Fintype α] [Fintype S.World] [DecidableEq S.World] [Fintype M]
    (μ : Modes S n M) (φ : (α × S.World → ZMod n) → ℂ) {Ψ : JointWave S n M}
    (hΨ : Ψ ∈ jointWaves μ) : jointDrift φ Ψ ∈ jointWaves μ := by
  intro κ hκ
  change φ κ.1 * Ψ κ = 0
  rw [hΨ κ hκ, mul_zero]

/-- The kept law of `-z` undoes the kept law of `z`. -/
theorem kept_neg_kept [Fintype α] [Fintype S.World] [DecidableEq S.World]
    (z : (S.endsDial n).ker) :
    (jointKept (-z) : Module.End ℂ (JointWave S n M)) * jointKept z = 1 := by
  refine LinearMap.ext fun Ψ => funext fun κ => ?_
  change Ψ ((κ.1 - ((-z : (S.endsDial n).ker) : α × S.World → ZMod n)) - z, κ.2) = Ψ κ
  congr 1
  exact Prod.ext (by simp) rfl

/-- A drift whose phases have size `1` is undone by the drift of the inverse phases. -/
theorem drift_inv_drift (φ : (α × S.World → ZMod n) → ℂ) (hφ : ∀ c, ‖φ c‖ = 1) :
    (jointDrift (fun c => (φ c)⁻¹) : Module.End ℂ (JointWave S n M)) * jointDrift φ = 1 := by
  refine LinearMap.ext fun Ψ => funext fun κ => ?_
  have h0 : φ κ.1 ≠ 0 := fun h => by simpa [h] using hφ κ.1
  change (φ κ.1)⁻¹ * (φ κ.1 * Ψ κ) = Ψ κ
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-! ### Matter hops -/

/-- **JU3.** A matter hop along the line `line`, from the mode `src` based at its tail to the mode
`dst` of the same charge based at its head, with a sign that may depend on the occupation. -/
structure MatterHop (μ : Modes S n M) where
  /-- The line of the hop. -/
  line : α × S.World
  /-- The mode the charge leaves, based at the line's tail. -/
  src : M
  /-- The mode the charge enters, based at the line's head. -/
  dst : M
  /-- The sign of the hop, at each occupation it starts from. -/
  sign : (M → Bool) → ℤˣ
  base_src : μ.base src = line.2
  base_dst : μ.base dst = S.head line
  charge_dst : μ.charge dst = μ.charge src

namespace MatterHop

variable {μ : Modes S n M} (H : MatterHop μ)

/-- The charge that the hop moves. -/
def q : ZMod n := μ.charge H.src

/-- The hop starts from an occupation with `src` occupied and `dst` empty. -/
def isSrc (o : M → Bool) : Bool := o H.src && !o H.dst

/-- The hop ends at an occupation with `dst` occupied and `src` empty. -/
def isDst (o : M → Bool) : Bool := o H.dst && !o H.src

/-- The occupation after the hop: `src` empty and `dst` occupied. -/
def moveOcc [DecidableEq M] (o : M → Bool) : M → Bool :=
  Function.update (Function.update o H.src false) H.dst true

/-- The occupation before the hop: `dst` empty and `src` occupied. -/
def unmoveOcc [DecidableEq M] (o : M → Bool) : M → Bool :=
  Function.update (Function.update o H.dst false) H.src true

/-- The joint configuration after the hop: `q` more on the line, and the occupation moved. -/
def hopConf [DecidableEq α] [DecidableEq S.World] [DecidableEq M] (κ : JointConf S n M) :
    JointConf S n M :=
  (κ.1 + H.q • Pi.single H.line 1, H.moveOcc κ.2)

/-- The joint configuration before the hop. -/
def unhopConf [DecidableEq α] [DecidableEq S.World] [DecidableEq M] (κ : JointConf S n M) :
    JointConf S n M :=
  (κ.1 - H.q • Pi.single H.line 1, H.unmoveOcc κ.2)

/-- The sign, as a real number. -/
def signR (o : M → Bool) : ℝ := ((H.sign o : ℤ) : ℝ)

/-- **JU2.** The matter hop on the joint waves: it takes each configuration with `src` occupied and
`dst` empty to the one after the hop, times the sign. Its value at a configuration with `dst`
occupied and `src` empty is the sign times the old value at the configuration before the hop. -/
def hop [DecidableEq α] [DecidableEq S.World] [DecidableEq M] :
    Module.End ℂ (JointWave S n M) where
  toFun Ψ κ := if H.isDst κ.2 then (H.signR (H.unmoveOcc κ.2) : ℂ) * Ψ (H.unhopConf κ) else 0
  map_add' Ψ Φ := funext fun κ => by
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a Ψ := funext fun κ => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **JU2.** The reverse of the matter hop: it takes the configuration after the hop back, times
the same sign. -/
def hopReverse [DecidableEq α] [DecidableEq S.World] [DecidableEq M] :
    Module.End ℂ (JointWave S n M) where
  toFun Ψ κ := if H.isSrc κ.2 then (H.signR κ.2 : ℂ) * Ψ (H.hopConf κ) else 0
  map_add' Ψ Φ := funext fun κ => by
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a Ψ := funext fun κ => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **JU4.** The gate of the matter hop at the angle `θ`: the identity off the hop's two ends, and
on them `cos θ` less `i sin θ` times the hop and its reverse. -/
def gate [DecidableEq α] [DecidableEq S.World] [DecidableEq M] (θ : ℝ) :
    Module.End ℂ (JointWave S n M) where
  toFun Ψ κ := if H.isSrc κ.2 || H.isDst κ.2 then
      (Real.cos θ : ℂ) * Ψ κ - I * Real.sin θ * (H.hop Ψ κ + H.hopReverse Ψ κ) else Ψ κ
  map_add' Ψ Φ := funext fun κ => by
    simp only [Pi.add_apply, map_add]
    split_ifs <;> ring
  map_smul' a Ψ := funext fun κ => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_smul]
    split_ifs <;> ring

theorem isSrc_iff (o : M → Bool) : H.isSrc o = true ↔ o H.src = true ∧ o H.dst = false := by
  simp [isSrc]

theorem isDst_iff (o : M → Bool) : H.isDst o = true ↔ o H.dst = true ∧ o H.src = false := by
  simp [isDst]

theorem isSrc_isDst_false {o : M → Bool} (h : H.isSrc o = true) : H.isDst o = false := by
  rw [isSrc_iff] at h
  simp [isDst, h.1, h.2]

section Moves

variable [DecidableEq M]

theorem moveOcc_isDst {o : M → Bool} (h : H.isSrc o = true) : H.isDst (H.moveOcc o) = true := by
  rw [isSrc_iff] at h
  have hne : H.dst ≠ H.src := fun e => by simp [e, h.1] at h
  rw [isDst_iff, moveOcc, Function.update_self, Function.update_of_ne hne.symm,
    Function.update_self]
  exact ⟨rfl, rfl⟩

theorem moveOcc_isSrc {o : M → Bool} (h : H.isSrc o = true) : H.isSrc (H.moveOcc o) = false := by
  have h' := H.moveOcc_isDst h
  rw [isDst_iff] at h'
  simp [isSrc, h'.2]

theorem unmoveOcc_isSrc {o : M → Bool} (h : H.isDst o = true) :
    H.isSrc (H.unmoveOcc o) = true := by
  rw [isDst_iff] at h
  have hne : H.src ≠ H.dst := fun e => by simp [e, h.1] at h
  rw [isSrc_iff, unmoveOcc, Function.update_self, Function.update_of_ne hne.symm,
    Function.update_self]
  exact ⟨rfl, rfl⟩

theorem unmoveOcc_isDst {o : M → Bool} (h : H.isDst o = true) :
    H.isDst (H.unmoveOcc o) = false := by
  have h' := H.unmoveOcc_isSrc h
  rw [isSrc_iff] at h'
  simp [isDst, h'.2]

theorem unmoveOcc_moveOcc {o : M → Bool} (h : H.isSrc o = true) :
    H.unmoveOcc (H.moveOcc o) = o := by
  rw [isSrc_iff] at h
  have hne : H.dst ≠ H.src := fun e => by simp [e, h.1] at h
  funext m
  simp only [unmoveOcc, moveOcc, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem moveOcc_unmoveOcc {o : M → Bool} (h : H.isDst o = true) :
    H.moveOcc (H.unmoveOcc o) = o := by
  rw [isDst_iff] at h
  have hne : H.src ≠ H.dst := fun e => by simp [e, h.1] at h
  funext m
  simp only [unmoveOcc, moveOcc, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- The hop moves the occupation's charges by `q` at the line's head and `-q` at its tail. -/
theorem occCharge_moveOcc [Fintype M] [DecidableEq S.World] {o : M → Bool}
    (h : H.isSrc o = true) :
    μ.occCharge (H.moveOcc o) =
      μ.occCharge o + H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) := by
  rw [isSrc_iff] at h
  have hne : H.dst ≠ H.src := fun e => by simp [e, h.1] at h
  rw [moveOcc, Modes.occCharge_update, Modes.occCharge_update, Function.update_of_ne hne, h.1,
    h.2, H.base_src, H.base_dst, H.charge_dst, q]
  simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero, smul_sub]
  abel

theorem occCharge_unmoveOcc [Fintype M] [DecidableEq S.World] {o : M → Bool}
    (h : H.isDst o = true) :
    μ.occCharge (H.unmoveOcc o) =
      μ.occCharge o - H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) := by
  rw [isDst_iff] at h
  have hne : H.src ≠ H.dst := fun e => by simp [e, h.1] at h
  rw [unmoveOcc, Modes.occCharge_update, Modes.occCharge_update, Function.update_of_ne hne, h.1,
    h.2, H.base_src, H.base_dst, H.charge_dst, q]
  simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero, smul_sub]
  abel

end Moves

section Conf

variable [DecidableEq α] [DecidableEq S.World] [DecidableEq M]

theorem unhopConf_hopConf {κ : JointConf S n M} (h : H.isSrc κ.2 = true) :
    H.unhopConf (H.hopConf κ) = κ :=
  Prod.ext (add_sub_cancel_right _ _) (H.unmoveOcc_moveOcc h)

theorem hopConf_unhopConf {κ : JointConf S n M} (h : H.isDst κ.2 = true) :
    H.hopConf (H.unhopConf κ) = κ :=
  Prod.ext (sub_add_cancel _ _) (H.moveOcc_unmoveOcc h)

/-- **JU3.** So a hop between two dots with no charge on them is the making of a pair: after it
the head has the charge `q`, the tail `-q`, and the line `q` more. -/
theorem hop_makes_pair [Fintype M] {κ : JointConf S n M} (h : H.isSrc κ.2 = true)
    (hne : S.head H.line ≠ H.line.2) (h1 : μ.occCharge κ.2 (S.head H.line) = 0)
    (h2 : μ.occCharge κ.2 H.line.2 = 0) :
    μ.occCharge (H.hopConf κ).2 (S.head H.line) = H.q ∧
      μ.occCharge (H.hopConf κ).2 H.line.2 = -H.q ∧
      (H.hopConf κ).1 H.line = κ.1 H.line + H.q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (H.hopConf κ).2 = H.moveOcc κ.2 from rfl, H.occCharge_moveOcc h]
    simp [h1, hne]
  · rw [show (H.hopConf κ).2 = H.moveOcc κ.2 from rfl, H.occCharge_moveOcc h]
    simp [h2, hne.symm]
  · simp [hopConf]

variable [Fintype α] [Fintype S.World]

/-- The ends of the filling after the hop: `q` more at the line's head and `q` less at its tail. -/
theorem endsDial_hopConf (κ : JointConf S n M) :
    S.endsDial n (H.hopConf κ).1 =
      S.endsDial n κ.1 + H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) := by
  rw [hopConf, map_add, ZMod.map_smul, S.endsDial_single n]

theorem endsDial_unhopConf (κ : JointConf S n M) :
    S.endsDial n (H.unhopConf κ).1 =
      S.endsDial n κ.1 - H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) := by
  rw [unhopConf, map_sub, ZMod.map_smul, S.endsDial_single n]

variable [Fintype M]

/-- **JU3.** What a hop moves, it books: the hop puts `q` more on its line, and changes the
filling's ends and the occupation's charges both by `q` at the line's head and `-q` at its tail. -/
theorem hop_books {κ : JointConf S n M} (h : H.isSrc κ.2 = true) :
    (H.hopConf κ).1 = κ.1 + H.q • Pi.single H.line 1 ∧
      S.endsDial n (H.hopConf κ).1 =
        S.endsDial n κ.1 + H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) ∧
      μ.occCharge (H.hopConf κ).2 =
        μ.occCharge κ.2 + H.q • (Pi.single (S.head H.line) 1 - Pi.single H.line.2 1) :=
  ⟨rfl, H.endsDial_hopConf κ, H.occCharge_moveOcc h⟩

/-- A joint configuration with `src` occupied and `dst` empty is a joint law exactly when the
configuration after the hop is. -/
theorem jointLaw_hopConf {κ : JointConf S n M} (h : H.isSrc κ.2 = true) :
    jointLaw μ (H.hopConf κ) ↔ jointLaw μ κ := by
  rw [jointLaw, jointLaw, H.endsDial_hopConf κ]
  change _ = μ.occCharge (H.moveOcc κ.2) ↔ _
  rw [H.occCharge_moveOcc h, add_left_inj]

theorem jointLaw_unhopConf {κ : JointConf S n M} (h : H.isDst κ.2 = true) :
    jointLaw μ (H.unhopConf κ) ↔ jointLaw μ κ := by
  rw [jointLaw, jointLaw, H.endsDial_unhopConf κ]
  change _ = μ.occCharge (H.unmoveOcc κ.2) ↔ _
  rw [H.occCharge_unmoveOcc h, sub_left_inj]

/-- **JU2.** A matter hop takes waves on joint laws to waves on joint laws. -/
theorem hop_jointWave {Ψ : JointWave S n M} (hΨ : Ψ ∈ jointWaves μ) :
    H.hop Ψ ∈ jointWaves μ := by
  intro κ hκ
  change (if H.isDst κ.2 then (H.signR (H.unmoveOcc κ.2) : ℂ) * Ψ (H.unhopConf κ) else 0) = 0
  split_ifs with hd
  · rw [hΨ _ (by rwa [H.jointLaw_unhopConf hd]), mul_zero]
  · rfl

/-- **JU2.** The reverse of a matter hop takes waves on joint laws to waves on joint laws. -/
theorem hopReverse_jointWave {Ψ : JointWave S n M} (hΨ : Ψ ∈ jointWaves μ) :
    H.hopReverse Ψ ∈ jointWaves μ := by
  intro κ hκ
  change (if H.isSrc κ.2 then (H.signR κ.2 : ℂ) * Ψ (H.hopConf κ) else 0) = 0
  split_ifs with hs
  · rw [hΨ _ (by rwa [H.jointLaw_hopConf hs]), mul_zero]
  · rfl

/-- A gate takes waves on joint laws to waves on joint laws. -/
theorem gate_jointWave (θ : ℝ) {Ψ : JointWave S n M} (hΨ : Ψ ∈ jointWaves μ) :
    H.gate θ Ψ ∈ jointWaves μ := by
  intro κ hκ
  have h1 := H.hop_jointWave hΨ κ hκ
  have h2 := H.hopReverse_jointWave hΨ κ hκ
  change (if H.isSrc κ.2 || H.isDst κ.2 then (Real.cos θ : ℂ) * Ψ κ -
      I * Real.sin θ * (H.hop Ψ κ + H.hopReverse Ψ κ) else Ψ κ) = 0
  rw [h1, h2, hΨ κ hκ]
  split_ifs <;> ring

end Conf

/-! ### The gate, pair by pair -/

section Pair

variable [DecidableEq α] [DecidableEq S.World] [DecidableEq M]

/-- The other end of the hop's pair: after the hop for a start, before it for an end, and the
configuration itself off the hop's ends. -/
def pairConf (κ : JointConf S n M) : JointConf S n M :=
  if H.isSrc κ.2 then H.hopConf κ else if H.isDst κ.2 then H.unhopConf κ else κ

/-- The sign of the hop's pair: the sign at its start. -/
def pairSign (κ : JointConf S n M) : ℝ :=
  if H.isSrc κ.2 then H.signR κ.2 else H.signR (H.unmoveOcc κ.2)

theorem pairConf_of_isSrc {κ : JointConf S n M} (hs : H.isSrc κ.2 = true) :
    H.pairConf κ = H.hopConf κ := by
  rw [pairConf, ite_eq_left hs]

theorem pairConf_of_isDst {κ : JointConf S n M} (hd : H.isDst κ.2 = true) :
    H.pairConf κ = H.unhopConf κ := by
  have hs : H.isSrc κ.2 = false := by
    have := H.isSrc_isDst_false (o := κ.2)
    cases h : H.isSrc κ.2
    · rfl
    · simp [this h] at hd
  rw [pairConf, ite_eq_right (by simp [hs]), ite_eq_left hd]

theorem pairConf_of_off {κ : JointConf S n M} (hs : H.isSrc κ.2 = false)
    (hd : H.isDst κ.2 = false) : H.pairConf κ = κ := by
  rw [pairConf, ite_eq_right (by simp [hs]), ite_eq_right (by simp [hd])]

theorem pairConf_pairConf (κ : JointConf S n M) : H.pairConf (H.pairConf κ) = κ := by
  cases hs : H.isSrc κ.2
  · cases hd : H.isDst κ.2
    · rw [H.pairConf_of_off hs hd, H.pairConf_of_off hs hd]
    · rw [H.pairConf_of_isDst hd, H.pairConf_of_isSrc (H.unmoveOcc_isSrc hd),
        H.hopConf_unhopConf hd]
  · rw [H.pairConf_of_isSrc hs, H.pairConf_of_isDst (H.moveOcc_isDst hs), H.unhopConf_hopConf hs]

theorem isEnd_pairConf (κ : JointConf S n M) :
    (H.isSrc (H.pairConf κ).2 || H.isDst (H.pairConf κ).2) = (H.isSrc κ.2 || H.isDst κ.2) := by
  cases hs : H.isSrc κ.2
  · cases hd : H.isDst κ.2
    · rw [H.pairConf_of_off hs hd, hs, hd]
    · rw [H.pairConf_of_isDst hd]
      change (H.isSrc (H.unmoveOcc κ.2) || H.isDst (H.unmoveOcc κ.2)) = _
      rw [H.unmoveOcc_isSrc hd, Bool.true_or, Bool.false_or]
  · rw [H.pairConf_of_isSrc hs]
    change (H.isSrc (H.moveOcc κ.2) || H.isDst (H.moveOcc κ.2)) = _
    rw [H.moveOcc_isDst hs, Bool.or_true, Bool.true_or]

theorem pairSign_pairConf (κ : JointConf S n M) : H.pairSign (H.pairConf κ) = H.pairSign κ := by
  cases hs : H.isSrc κ.2
  · cases hd : H.isDst κ.2
    · rw [H.pairConf_of_off hs hd]
    · rw [H.pairConf_of_isDst hd, pairSign, pairSign, hs]
      change (if H.isSrc (H.unmoveOcc κ.2) = true then H.signR (H.unmoveOcc κ.2)
        else H.signR (H.unmoveOcc (H.unmoveOcc κ.2))) = _
      rw [ite_eq_left (H.unmoveOcc_isSrc hd)]
      rfl
  · rw [H.pairConf_of_isSrc hs, pairSign, pairSign, ite_eq_left hs]
    change (if H.isSrc (H.moveOcc κ.2) = true then H.signR (H.moveOcc κ.2)
      else H.signR (H.unmoveOcc (H.moveOcc κ.2))) = _
    rw [H.moveOcc_isSrc hs, H.unmoveOcc_moveOcc hs]
    rfl

omit [DecidableEq α] [DecidableEq S.World] in
theorem pairSign_sq (κ : JointConf S n M) : H.pairSign κ * H.pairSign κ = 1 := by
  have key : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  unfold pairSign signR
  split_ifs <;> exact key _

/-- On the hop's ends the gate is `cos θ` times the wave less `i s sin θ` times the wave at the
other end of the pair. -/
theorem gate_apply_end (θ : ℝ) (Ψ : JointWave S n M) {κ : JointConf S n M}
    (h : (H.isSrc κ.2 || H.isDst κ.2) = true) :
    H.gate θ Ψ κ = (Real.cos θ : ℂ) * Ψ κ - I * Real.sin θ * H.pairSign κ * Ψ (H.pairConf κ) := by
  change (if H.isSrc κ.2 || H.isDst κ.2 then (Real.cos θ : ℂ) * Ψ κ -
      I * Real.sin θ * (H.hop Ψ κ + H.hopReverse Ψ κ) else Ψ κ) = _
  rw [ite_eq_left h]
  change (Real.cos θ : ℂ) * Ψ κ - I * Real.sin θ *
      ((if H.isDst κ.2 then (H.signR (H.unmoveOcc κ.2) : ℂ) * Ψ (H.unhopConf κ) else 0) +
        (if H.isSrc κ.2 then (H.signR κ.2 : ℂ) * Ψ (H.hopConf κ) else 0)) = _
  cases hs : H.isSrc κ.2
  · have hd : H.isDst κ.2 = true := by simpa [hs] using h
    rw [H.pairConf_of_isDst hd, pairSign, hs, hd]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    ring
  · rw [H.pairConf_of_isSrc hs, pairSign, hs, H.isSrc_isDst_false hs]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    ring

/-- Off the hop's ends the gate is the identity. -/
theorem gate_apply_off (θ : ℝ) (Ψ : JointWave S n M) {κ : JointConf S n M}
    (h : (H.isSrc κ.2 || H.isDst κ.2) = false) : H.gate θ Ψ κ = Ψ κ := by
  change (if H.isSrc κ.2 || H.isDst κ.2 then (Real.cos θ : ℂ) * Ψ κ -
      I * Real.sin θ * (H.hop Ψ κ + H.hopReverse Ψ κ) else Ψ κ) = _
  rw [h]
  rfl

omit [DecidableEq α] [DecidableEq S.World] in
theorem pairSign_eq_one_or (κ : JointConf S n M) : H.pairSign κ = 1 ∨ H.pairSign κ = -1 := by
  have key : ∀ u : ℤˣ, ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  unfold pairSign signR
  split_ifs
  · exact key _
  · exact key _

/-- On each pair of joint configurations that the hop joins, the gate acts by the link gate of
`TheWalk.lean` at the angle `s θ`, `s` the pair's sign: `cos θ · 1 - i s sin θ · σx`. -/
theorem gate_pair (θ : ℝ) (Ψ : JointWave S n M) {κ : JointConf S n M}
    (h : (H.isSrc κ.2 || H.isDst κ.2) = true) :
    ![H.gate θ Ψ κ, H.gate θ Ψ (H.pairConf κ)] =
      coin (H.pairSign κ * θ) *ᵥ ![Ψ κ, Ψ (H.pairConf κ)] := by
  have h' : (H.isSrc (H.pairConf κ).2 || H.isDst (H.pairConf κ).2) = true := by
    rw [H.isEnd_pairConf, h]
  have hcs : Real.cos (H.pairSign κ * θ) = Real.cos θ ∧
      Real.sin (H.pairSign κ * θ) = H.pairSign κ * Real.sin θ := by
    rcases H.pairSign_eq_one_or κ with e | e <;> simp [e]
  rw [H.gate_apply_end _ _ h, H.gate_apply_end _ _ h', H.pairConf_pairConf, H.pairSign_pairConf]
  ext i
  fin_cases i <;>
    simp [coin, pauliX, mulVec, dotProduct, Fin.sum_univ_two, hcs.1, hcs.2] <;> ring

/-- **JU4.** The gate of `-θ` undoes the gate of `θ`. -/
theorem gate_neg_gate (θ : ℝ) : H.gate (-θ) * H.gate θ = 1 := by
  refine LinearMap.ext fun Ψ => funext fun κ => ?_
  rw [Module.End.mul_apply, Module.End.one_apply]
  cases h : (H.isSrc κ.2 || H.isDst κ.2)
  · rw [H.gate_apply_off _ _ h, H.gate_apply_off _ _ h]
  · have h' : (H.isSrc (H.pairConf κ).2 || H.isDst (H.pairConf κ).2) = true := by
      rw [H.isEnd_pairConf, h]
    rw [H.gate_apply_end _ _ h, H.gate_apply_end _ _ h, H.gate_apply_end _ _ h',
      H.pairConf_pairConf, H.pairSign_pairConf, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    have hs' : (H.pairSign κ : ℂ) * H.pairSign κ = 1 := by exact_mod_cast H.pairSign_sq κ
    have hc' : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    linear_combination Ψ κ * hc' - (Real.sin θ : ℂ) ^ 2 * Ψ κ * (H.pairSign κ : ℂ) ^ 2 * I_sq +
      (Real.sin θ : ℂ) ^ 2 * Ψ κ * hs'

end Pair

/-! ### The sum of squares -/

section Norm

variable [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
  [Fintype M] [DecidableEq M]

/-- **JU4.** A gate keeps the sum of the squares of the sizes of a joint wave's numbers: on each
pair of configurations that the hop joins it acts by the link gate `coin (± θ)`, which keeps it
by `exchange_unitary_iff`, and off them it is the identity. -/
theorem gate_norm (θ : ℝ) (Ψ : JointWave S n M) :
    ∑ κ, ‖H.gate θ Ψ κ‖ ^ 2 = ∑ κ, ‖Ψ κ‖ ^ 2 := by
  have hinv : Function.Involutive H.pairConf := H.pairConf_pairConf
  -- the link gate of every angle keeps the sum of the squares of two numbers (`TheWalk.lean`)
  have hcoin : ∀ μ : ℝ, ∀ v : Fin 2 → ℂ, ∑ i, ‖(coin μ *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    intro μ v
    have e : coin μ = (Real.cos μ : ℂ) • 1 + (-(I * Real.sin μ)) • pauliX := by
      rw [coin, neg_smul, sub_eq_add_neg]
    rw [e]
    refine ((exchange_unitary_iff _ _).2.mpr ⟨1, -μ, by simp, ?_, ?_⟩) v
    · simp [Real.cos_neg]
    · simp [Real.sin_neg]
  have hpair : ∀ κ, ‖H.gate θ Ψ κ‖ ^ 2 + ‖H.gate θ Ψ (H.pairConf κ)‖ ^ 2 =
      ‖Ψ κ‖ ^ 2 + ‖Ψ (H.pairConf κ)‖ ^ 2 := by
    intro κ
    cases h : (H.isSrc κ.2 || H.isDst κ.2)
    · have hs : H.isSrc κ.2 = false := by simp_all
      have hd : H.isDst κ.2 = false := by simp_all
      rw [H.pairConf_of_off hs hd, H.gate_apply_off _ _ h]
    · have hp := congrArg (fun v : Fin 2 → ℂ => ∑ i, ‖v i‖ ^ 2) (H.gate_pair θ Ψ h)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rw [hp]
      have := hcoin (H.pairSign κ * θ) ![Ψ κ, Ψ (H.pairConf κ)]
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using this
  have e1 : ∑ κ, ‖H.gate θ Ψ (H.pairConf κ)‖ ^ 2 = ∑ κ, ‖H.gate θ Ψ κ‖ ^ 2 :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have e2 : ∑ κ, ‖Ψ (H.pairConf κ)‖ ^ 2 = ∑ κ, ‖Ψ κ‖ ^ 2 :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have e3 := Finset.sum_congr rfl fun κ (_ : κ ∈ Finset.univ) => hpair κ
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2] at e3
  linarith

end Norm

end MatterHop

section Norm

variable [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
  [Fintype M] [DecidableEq M]

/-- **JU4.** A drift whose phases have size `1` keeps the sum of the squares of the sizes of a
joint wave's numbers. -/
theorem drift_norm (φ : (α × S.World → ZMod n) → ℂ) (hφ : ∀ c, ‖φ c‖ = 1)
    (Ψ : JointWave S n M) : ∑ κ, ‖jointDrift φ Ψ κ‖ ^ 2 = ∑ κ, ‖Ψ κ‖ ^ 2 := by
  refine Finset.sum_congr rfl fun κ _ => ?_
  change ‖φ κ.1 * Ψ κ‖ ^ 2 = _
  rw [norm_mul, hφ, one_mul]

/-- **JU4.** A kept law keeps the sum of the squares of the sizes of a joint wave's numbers. -/
theorem kept_norm (z : (S.endsDial n).ker) (Ψ : JointWave S n M) :
    ∑ κ, ‖jointKept z Ψ κ‖ ^ 2 = ∑ κ, ‖Ψ κ‖ ^ 2 :=
  Fintype.sum_equiv ((Equiv.subRight (z : α × S.World → ZMod n)).prodCongr (Equiv.refl _)) _ _
    fun _ => rfl

end Norm

/-! ### The quantum drift's phase -/

/-- The phase of the quantum drift of `QuantumLight.lean` at the filling `c`, read as the electric
field: `χ(half · c ⬝ A c)`. -/
noncomputable def qdriftPhase [Fintype α] [Fintype S.World] [NeZero n]
    (A : Matrix (α × S.World) (α × S.World) (ZMod n)) (c : α × S.World → ZMod n) : ℂ :=
  ZMod.stdAddChar (half n * (c ⬝ᵥ (A *ᵥ c)))

/-- The quantum drift of `A` multiplies the electric pattern of `c` by the phase
`qdriftPhase A c` (`qdrift_pattern`). -/
theorem qdrift_electricPattern [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World]
    [NeZero n] (A : Matrix (α × S.World) (α × S.World) (ZMod n)) (c : α × S.World → ZMod n) :
    (qdrift A : Module.End ℂ (LightWave (α × S.World) n)) (electricPattern c) =
      qdriftPhase A c • electricPattern c :=
  qdrift_pattern A c

/-- **JU2**, for the quantum drift: its phase, as a drift on the filling, takes waves on joint laws
to waves on joint laws. -/
theorem qdrift_jointWave [Fintype α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
    [Fintype M] (μ : Modes S n M) (A : Matrix (α × S.World) (α × S.World) (ZMod n))
    {Ψ : JointWave S n M} (hΨ : Ψ ∈ jointWaves μ) : jointDrift (qdriftPhase A) Ψ ∈ jointWaves μ :=
  drift_jointWave μ _ hΨ

/-- **JU4**, for the quantum drift: its phases have size `1`, so as a drift on the filling it keeps
the sum of the squares of the sizes. -/
theorem qdrift_norm [Fintype α] [DecidableEq α] [Fintype S.World] [DecidableEq S.World] [NeZero n]
    [Fintype M] [DecidableEq M] (A : Matrix (α × S.World) (α × S.World) (ZMod n))
    (Ψ : JointWave S n M) :
    ∑ κ, ‖jointDrift (qdriftPhase A) Ψ κ‖ ^ 2 = ∑ κ, ‖Ψ κ‖ ^ 2 :=
  drift_norm _ (fun _ => stdAddChar_norm _) Ψ

end Artform.Stages
