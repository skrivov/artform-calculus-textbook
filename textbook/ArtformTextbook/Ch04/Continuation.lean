import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import ArtformTextbook.Ch04.Statements.Continuation

/-!
# One continuing experiment (Section 4.10)

The proof of Proposition 4.5, along the book's proof.
* Consistency makes the laws `P_n` one finitely additive mass on the algebra of
  cylinder sets (Mathlib's `projectiveFamilyContent` of the projective family
  the laws form).
* Over finite alphabets the sequence space is compact and every cylinder set is
  closed, so a decreasing sequence of cylinder sets with empty intersection is
  eventually empty. The mass is therefore continuous at `∅`, hence countably
  additive, and Carathéodory's theorem extends it to a measure on `𝒜_∞`.
* Two probability measures that agree on the cylinders agree on `𝒜_∞`, because
  the cylinders form a π-system that generates it.

Mathlib indexes the finite marginals by `Finset.Iic m`; `toIic` translates a word
`h : (i : Fin (m + 1)) → Y i` to that indexing.
-/

namespace Artform

open MeasureTheory Filter Topology Preorder Set
open scoped ENNReal NNReal

namespace HistoryExtension

section Words

variable {Y : ℕ → Type*}

/-- A word with its last letter dropped. -/
def dropLast {n : ℕ} (h : (i : Fin (n + 1)) → Y i) : (i : Fin n) → Y i := fun i => h i.castSucc

/-- A word of length `n + 1` is a last letter and a word of length `n`. -/
def snocEquiv (n : ℕ) : Y n × ((i : Fin n) → Y i) ≃ ((i : Fin (n + 1)) → Y i) :=
  Fin.snocEquiv fun i : Fin (n + 1) => Y i

lemma snocEquiv_apply {n : ℕ} (y : Y n) (h : (i : Fin n) → Y i) :
    snocEquiv n (y, h) = Fin.snoc h y := rfl

lemma dropLast_snoc {n : ℕ} (h : (i : Fin n) → Y i) (y : Y n) :
    dropLast (Fin.snoc h y : (i : Fin (n + 1)) → Y i) = h := by
  funext i
  simp [dropLast]

/-- The first `m` letters of a word of length `n ≥ m`. -/
def restrictPrefix {m n : ℕ} (hmn : m ≤ n) (h : (i : Fin n) → Y i) : (i : Fin m) → Y i :=
  fun i => h (Fin.castLE hmn i)

/-- A word of length `m + 1`, indexed by `Finset.Iic m` as Mathlib's projective
families are. -/
def toIic (m : ℕ) (h : (i : Fin (m + 1)) → Y i) : (i : Finset.Iic m) → Y i :=
  fun i => h ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩

lemma toIic_injective (m : ℕ) : Function.Injective (toIic (Y := Y) m) := by
  intro h h' hh
  funext i
  exact congrFun hh ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ i.2)⟩

lemma prefixCylinder_zero (h : (i : Fin 0) → Y i) : prefixCylinder h = univ := by
  ext ω
  simp [prefixCylinder]

/-- The cylinder `[h]` of a word of length `m + 1` is Mathlib's cylinder over
`Finset.Iic m` with the single base point `h`. -/
lemma prefixCylinder_eq {m : ℕ} (h : (i : Fin (m + 1)) → Y i) :
    prefixCylinder h = cylinder (Finset.Iic m) {toIic m h} := by
  ext ω
  simp only [prefixCylinder, mem_ofPred_eq, mem_cylinder, mem_singleton_iff]
  constructor
  · intro hω
    funext i
    exact hω ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩
  · intro hω i
    exact congrFun hω ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ i.2)⟩

/-- The cylinders of finite prefixes form a π-system: two of them meet only when
one prefix extends the other, and then they meet in the longer cylinder. -/
lemma isPiSystem_prefixCylinders :
    IsPiSystem {s : Set ((t : ℕ) → Y t) | ∃ (n : ℕ) (h : (i : Fin n) → Y i),
      s = prefixCylinder h} := by
  rintro _ ⟨m, h, rfl⟩ _ ⟨n, h', rfl⟩ ⟨ω, hω, hω'⟩
  rcases le_total m n with hmn | hnm
  · refine ⟨n, h', Set.inter_eq_right.2 fun ω'' hω'' i => ?_⟩
    exact (hω'' ⟨i, lt_of_lt_of_le i.2 hmn⟩).trans
      ((hω' ⟨i, lt_of_lt_of_le i.2 hmn⟩).symm.trans (hω i))
  · refine ⟨m, h, Set.inter_eq_left.2 fun ω'' hω'' i => ?_⟩
    exact (hω'' ⟨i, lt_of_lt_of_le i.2 hnm⟩).trans
      ((hω ⟨i, lt_of_lt_of_le i.2 hnm⟩).symm.trans (hω' i))

end Words

section Cylinders

variable {Y : ℕ → Type*} [∀ t, MeasurableSpace (Y t)] [∀ t, MeasurableSingletonClass (Y t)]

lemma prefixCylinder_mem {n : ℕ} (h : (i : Fin n) → Y i) :
    prefixCylinder h ∈ measurableCylinders Y := by
  cases n with
  | zero =>
    rw [prefixCylinder_zero, ← cylinder_univ (Finset.Iic 0)]
    exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
  | succ m =>
    rw [prefixCylinder_eq]
    exact cylinder_mem_measurableCylinders _ _ (measurableSet_singleton _)

lemma cylinderAlgebra_le :
    cylinderAlgebra Y ≤ MeasurableSpace.generateFrom (measurableCylinders Y) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨n, h, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom (prefixCylinder_mem h)

omit [∀ t, MeasurableSingletonClass (Y t)] in
/-- Over finite alphabets, a decreasing sequence of cylinder sets with empty
intersection is eventually empty, so every additive content on the cylinder sets
tends to `0` along it: the book's compactness argument, with the discrete
topology on each alphabet. -/
lemma tendsto_zero_of_antitone [∀ t, Finite (Y t)]
    (m : AddContent ℝ≥0∞ (measurableCylinders Y))
    {s : ℕ → Set ((t : ℕ) → Y t)} (hs : ∀ n, s n ∈ measurableCylinders Y) (anti : Antitone s)
    (inter : ⋂ n, s n = ∅) : Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
  let _ : ∀ t, TopologicalSpace (Y t) := fun _ => ⊥
  have _ : ∀ t, DiscreteTopology (Y t) := fun _ => ⟨rfl⟩
  have hclosed : ∀ n, IsClosed (s n) := by
    intro n
    obtain ⟨J, S, -, hJS⟩ := (mem_measurableCylinders _).1 (hs n)
    rw [hJS]
    exact IsClosed.cylinder J (isClosed_discrete S)
  obtain ⟨n₀, hn₀⟩ : ∃ n, s n = ∅ := by
    by_contra! hne
    have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
      (fun i => anti (Nat.le_succ i)) hne (hclosed 0).isCompact hclosed
    rw [inter] at this
    exact Set.not_nonempty_empty this
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hsub : s n ⊆ ∅ := hn₀ ▸ anti hn
  rw [Set.subset_empty_iff.1 hsub, addContent_empty]

end Cylinders

section Laws

variable {Y : ℕ → Type*} [∀ t, Fintype (Y t)] [∀ t, MeasurableSpace (Y t)]
  [∀ t, MeasurableSingletonClass (Y t)]

/-- The law `P_n` as a measure on the words of length `n`. -/
noncomputable def law (P : (n : ℕ) → ((i : Fin n) → Y i) → ℝ≥0) (n : ℕ) :
    Measure ((i : Fin n) → Y i) :=
  ∑ h, (P n h : ℝ≥0∞) • Measure.dirac h

variable (P : (n : ℕ) → ((i : Fin n) → Y i) → ℝ≥0)

lemma law_apply (n : ℕ) (s : Set ((i : Fin n) → Y i)) :
    law P n s = ∑ h, (P n h : ℝ≥0∞) * s.indicator 1 h := by
  rw [law, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma law_singleton (n : ℕ) (h : (i : Fin n) → Y i) : law P n {h} = P n h := by
  classical
  rw [law_apply]
  simp [Pi.single_apply]

instance (n : ℕ) : IsFiniteMeasure (law P n) := by
  refine ⟨?_⟩
  rw [law_apply]
  exact ENNReal.sum_lt_top.2 fun h _ =>
    ENNReal.mul_lt_top ENNReal.coe_lt_top (by simp)

/-- Compatibility: dropping the last letter pushes `P_{n+1}` forward to `P_n`. -/
lemma law_map_dropLast (hP : ∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i,
      ∑ y : Y n, P (n + 1) (Fin.snoc h y) = P n h)
    {n : ℕ} (hn : 1 ≤ n) : (law P (n + 1)).map dropLast = law P n := by
  classical
  rw [Measure.ext_iff_singleton]
  intro h
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton h), law_singleton,
    ← hP n hn h, law_apply, ← (snocEquiv n).sum_comp, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single h]
  · simp [snocEquiv_apply, dropLast_snoc]
  · intro b _ hb
    simp [snocEquiv_apply, dropLast_snoc, hb]
  · simp

/-- Repeated compatibility: dropping letters pushes `P_n` forward to `P_m`. -/
lemma law_map_restrictPrefix (hP : ∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i,
      ∑ y : Y n, P (n + 1) (Fin.snoc h y) = P n h)
    {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hmn : m ≤ n) :
    (law P n).map (restrictPrefix hmn) = law P m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have : (restrictPrefix (le_refl m) : ((i : Fin m) → Y i) → _) = id := rfl
    rw [this, Measure.map_id]
  | succ n hmn ih =>
    have : (restrictPrefix (hmn.trans n.le_succ) : ((i : Fin (n + 1)) → Y i) → _) =
        restrictPrefix hmn ∘ dropLast := rfl
    rw [this, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
      law_map_dropLast P hP (hm.trans hmn), ih]

/-- The law `P_{m+1}` on words indexed by `Finset.Iic m`. -/
noncomputable def lawIic (m : ℕ) : Measure ((i : Finset.Iic m) → Y i) :=
  (law P (m + 1)).map (toIic m)

instance (m : ℕ) : IsFiniteMeasure (lawIic P m) := by
  rw [lawIic]
  infer_instance

/-- The laws form a projective family. -/
lemma lawIic_map (hP : ∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i,
      ∑ y : Y n, P (n + 1) (Fin.snoc h y) = P n h)
    (a b : ℕ) (hab : a ≤ b) : (lawIic P b).map (frestrictLe₂ hab) = lawIic P a := by
  rw [lawIic, lawIic, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  have : frestrictLe₂ hab ∘ toIic (Y := Y) b = toIic a ∘ restrictPrefix (Nat.succ_le_succ hab) :=
    rfl
  rw [this, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    law_map_restrictPrefix P hP (Nat.succ_pos a) (Nat.succ_le_succ hab)]

variable (hP : ∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i,
  ∑ y : Y n, P (n + 1) (Fin.snoc h y) = P n h)

include hP in
lemma isProjective : IsProjectiveMeasureFamily (inducedFamily (lawIic P)) :=
  isProjectiveMeasureFamily_inducedFamily _ (lawIic_map P hP)

/-- The finitely additive mass that the laws `P_n` give the cylinder sets. -/
noncomputable def content : AddContent ℝ≥0∞ (measurableCylinders Y) :=
  projectiveFamilyContent (isProjective P hP)

/-- Continuity at `∅` makes the mass countably additive, hence σ-subadditive. -/
lemma content_sigmaSubadditive : (content P hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders
    (fun f hf hf_Union hf' => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders _
    (fun _ _ => projectiveFamilyContent_ne_top _)
    (fun _ hs anti inter => tendsto_zero_of_antitone _ hs anti inter) hf hf_Union hf'

/-- The measure on `(Ω_∞, 𝒜_∞)`: Carathéodory's extension of the mass. -/
noncomputable def extension : @Measure ((t : ℕ) → Y t) (cylinderAlgebra Y) :=
  @AddContent.measure _ _ (cylinderAlgebra Y) (content P hP) isSetSemiring_measurableCylinders
    cylinderAlgebra_le (content_sigmaSubadditive P hP)

lemma extension_apply {s : Set ((t : ℕ) → Y t)} (hs : MeasurableSet[cylinderAlgebra Y] s)
    (hsC : s ∈ measurableCylinders Y) : extension P hP s = content P hP s := by
  unfold extension AddContent.measure
  exact (trim_measurableSet_eq _ hs).trans (AddContent.measureCaratheodory_eq _ _ _ hsC)

/-- The extension gives the cylinder `[h]` the mass `P_n(h)`. -/
lemma extension_prefixCylinder {m : ℕ} (h : (i : Fin (m + 1)) → Y i) :
    extension P hP (prefixCylinder h) = P (m + 1) h := by
  rw [extension_apply P hP (MeasurableSpace.measurableSet_generateFrom ⟨m + 1, h, rfl⟩)
      (prefixCylinder_mem h), content,
    projectiveFamilyContent_congr _ _ (prefixCylinder_eq h) (measurableSet_singleton _),
    inducedFamily_Iic, lawIic, Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    ← Set.image_singleton, (toIic_injective m).preimage_image, law_singleton]

/-- The extension has total mass `1`, the mass of `P_1`. -/
lemma extension_univ (hnorm : ∀ n, 1 ≤ n → ∑ h, P n h = 1) : extension P hP univ = 1 := by
  have hmem : (univ : Set ((t : ℕ) → Y t)) ∈ measurableCylinders Y := by
    rw [← cylinder_univ (Finset.Iic 0)]
    exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
  rw [extension_apply P hP MeasurableSet.univ hmem, content,
    projectiveFamilyContent_congr _ univ (cylinder_univ (Finset.Iic 0)).symm MeasurableSet.univ,
    inducedFamily_Iic, lawIic, Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ, law_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, hnorm 1 le_rfl, ENNReal.coe_one]

end Laws

end HistoryExtension

/-- **Proposition 4.5** (extension of compatible finite histories). Suppose
normalized nonnegative laws `P_n` on the first `n` report alphabets satisfy
`∑_{y ∈ Y_{n+1}} P_{n+1}(h, y) = P_n(h)`. There is exactly one probability
measure on `(Ω_∞, 𝒜_∞)` assigning mass `P_n(h)` to `[h]`. -/
@[book "probbook:history-extension"]
theorem historyExtension : Statement.historyExtension := by
  intro Y _ _ P hnorm hP
  -- Each finite alphabet carries the σ-algebra of all its subsets.
  let _ : ∀ t, MeasurableSpace (Y t) := fun _ => ⊤
  have _ : ∀ t, MeasurableSingletonClass (Y t) :=
    fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hprob : @IsProbabilityMeasure _ (cylinderAlgebra Y) (HistoryExtension.extension P hP) :=
    ⟨HistoryExtension.extension_univ P hP hnorm⟩
  refine ⟨HistoryExtension.extension P hP, ⟨hprob, fun n hn h => ?_⟩, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact HistoryExtension.extension_prefixCylinder P hP h
  · -- Uniqueness: the cylinders form a π-system generating `𝒜_∞`.
    rintro ν ⟨hν, hνP⟩
    refine @ext_of_generate_finite _ (cylinderAlgebra Y) _ _ _ rfl
      HistoryExtension.isPiSystem_prefixCylinders _ ?_ ?_
    · rintro _ ⟨n, h, rfl⟩
      cases n with
      | zero =>
        rw [HistoryExtension.prefixCylinder_zero, measure_univ, measure_univ]
      | succ m =>
        rw [hνP (m + 1) (Nat.succ_pos m) h, HistoryExtension.extension_prefixCylinder P hP h]
    · rw [measure_univ, measure_univ]

/-! ## Non-vacuity -/

namespace ExitWords

/-- `K(y | x)` of Section 4.6, with values in `ℝ≥0`. -/
noncomputable def k (y x : Fin 2) : ℝ≥0 := if y = x then 3 / 4 else 1 / 4

/-- The current exit after a word of exits: its last letter, or the initial exit
`x_0 = 0` after the empty word. -/
def current : (n : ℕ) → (Fin n → Fin 2) → Fin 2
  | 0, _ => 0
  | n + 1, h => h (Fin.last n)

/-- The law of the first `n` exits from `x_0 = 0` (Section 4.7):
`P_n(x_1, …, x_n) = ∏_t K(x_t | x_{t-1})`. -/
noncomputable def law : (n : ℕ) → (Fin n → Fin 2) → ℝ≥0
  | 0, _ => 1
  | n + 1, h => law n (Fin.init h) * k (h (Fin.last n)) (current n (Fin.init h))

lemma sum_k (x : Fin 2) : ∑ y, k y x = 1 := by
  rw [Fin.sum_univ_two]
  fin_cases x <;> norm_num [k]

lemma law_snoc (n : ℕ) (h : Fin n → Fin 2) (y : Fin 2) :
    law (n + 1) (Fin.snoc h y) = law n h * k y (current n h) := by
  simp [law, Fin.init_snoc, Fin.snoc_last]

/-- Prefix consistency (Section 4.10): summing over the last exit gives the
shorter law. -/
lemma sum_law_snoc (n : ℕ) (h : Fin n → Fin 2) : ∑ y, law (n + 1) (Fin.snoc h y) = law n h := by
  simp only [law_snoc, ← Finset.mul_sum, sum_k, mul_one]

/-- Each law is normalized. -/
lemma sum_law (n : ℕ) : ∑ h, law n h = 1 := by
  induction n with
  | zero => simp [law]
  | succ n ih =>
    rw [← (Fin.snocEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type_right]
    have hsnoc : ∀ (y : Fin 2) (h : Fin n → Fin 2),
        (Fin.snocEquiv fun _ => Fin 2) (y, h) = Fin.snoc h y := fun _ _ => rfl
    simp only [hsnoc, sum_law_snoc, ih]

end ExitWords

/-- The book's exit laws (Sections 4.7 and 4.10) over the alphabets `Y_t = B`,
from `x_0 = 0`, are normalized and prefix-consistent, so they meet the
hypotheses of Proposition 4.5. The measure they extend to gives the cylinder
`[01]` the book's mass `P(01) = 3/16`. -/
example :
    letI := cylinderAlgebra fun _ : ℕ => Fin 2
    ∃ μ : Measure (ℕ → Fin 2), IsProbabilityMeasure μ ∧ μ (prefixCylinder ![0, 1]) = 3 / 16 := by
  obtain ⟨μ, ⟨hμ, hcyl⟩, -⟩ := historyExtension (fun _ => Fin 2) ExitWords.law
    (fun n _ => ExitWords.sum_law n) (fun n _ h => ExitWords.sum_law_snoc n h)
  refine ⟨μ, hμ, ?_⟩
  rw [hcyl 2 (by norm_num) ![0, 1]]
  have : ExitWords.law 2 ![0, 1] = 3 / 16 := by
    simp [ExitWords.law, ExitWords.k, ExitWords.current, Fin.init]
    norm_num
  rw [this]
  norm_num

end Artform
