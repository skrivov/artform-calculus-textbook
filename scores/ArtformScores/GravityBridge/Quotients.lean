import ArtformScores.GravityBridge.QuotientStatements

/-! # Quotients require compatible evolution, sources and boundary forms -/

namespace Artform.Scores.GravityBridge

variable {K X W : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W]

lemma evolution_descends_iff (N : Submodule K X) (T : X →ₗ[K] X) :
    (∃ Tq : X ⧸ N →ₗ[K] X ⧸ N, Tq.comp N.mkQ = N.mkQ.comp T) ↔
      N ≤ N.comap T := by
  constructor
  · rintro ⟨Tq, h⟩ n hn
    have he := LinearMap.congr_fun h n
    have hz : N.mkQ n = 0 := by simpa using hn
    have hz' : N.mkQ (T n) = 0 := by simpa [hz] using he.symm
    simpa using hz'
  · intro h
    exact ⟨N.mapQ N T h, N.mapQ_mkQ N T⟩

lemma output_descends_iff (N : Submodule K X) (O : X →ₗ[K] W) :
    (∃ Oq : X ⧸ N →ₗ[K] W, Oq.comp N.mkQ = O) ↔ N ≤ LinearMap.ker O := by
  constructor
  · rintro ⟨Oq, h⟩ n hn
    have he := LinearMap.congr_fun h n
    have hz : N.mkQ n = 0 := by simpa using hn
    simpa [hz] using he.symm
  · intro h
    exact ⟨N.liftQ O h, N.liftQ_mkQ O h⟩

lemma bilinear_descends_iff (N : Submodule K X) (ω : LinearMap.BilinForm K X) :
    (∃ ωq : LinearMap.BilinForm K (X ⧸ N),
      ∀ x y, ωq (N.mkQ x) (N.mkQ y) = ω x y) ↔
      (∀ n ∈ N, ∀ x, ω n x = 0) ∧ (∀ n ∈ N, ∀ x, ω x n = 0) := by
  constructor
  · rintro ⟨ωq, hω⟩
    constructor
    · intro n hn x
      have hz : N.mkQ n = 0 := by simpa using hn
      rw [← hω, hz, map_zero, LinearMap.zero_apply]
    · intro n hn x
      have hz : N.mkQ n = 0 := by simpa using hn
      rw [← hω, hz, map_zero]
  · rintro ⟨hl, hr⟩
    have hleft : N ≤ LinearMap.ker ω := by
      intro n hn
      apply LinearMap.ext
      intro x
      exact hl n hn x
    have hright : N ≤ LinearMap.ker ω.flip := by
      intro n hn
      apply LinearMap.ext
      intro x
      exact hr n hn x
    exact ⟨ω.liftQ₂ N N hleft hright, fun _ _ => rfl⟩

lemma bilinear_representative_iff (N : Submodule K X) (ω : LinearMap.BilinForm K X) :
    (∀ x y n m, n ∈ N → m ∈ N → ω (x + n) (y + m) = ω x y) ↔
      (∀ n ∈ N, ∀ x, ω n x = 0) ∧ (∀ n ∈ N, ∀ x, ω x n = 0) := by
  constructor
  · intro h
    constructor
    · intro n hn x
      simpa using h 0 x n 0 hn N.zero_mem
    · intro n hn x
      simpa using h x 0 0 n N.zero_mem hn
  · rintro ⟨hl, hr⟩ x y n m hn hm
    simp [map_add, hl n hn, hr m hm]

lemma affine_source_respects_quotient (N : Submodule K X) (T : X →ₗ[K] X)
    (h : N ≤ N.comap T) (b x y : X) (hxy : N.mkQ x = N.mkQ y) :
    N.mkQ (T x + b) = N.mkQ (T y + b) := by
  have ht := congrArg (N.mapQ N T h) hxy
  simpa [map_add] using congrArg (fun q => q + N.mkQ b) ht

/-- **GAC:quotient-compatibility** (separate dynamic, source and form descent tests). -/
@[ledger "GAC:quotient-compatibility"]
theorem quotientCompatibility : Statement.quotientCompatibility := by
  intro K X W _ _ _ _ _ N
  refine ⟨evolution_descends_iff N, output_descends_iff N, ?_,
    bilinear_descends_iff N, affine_source_respects_quotient N⟩
  intro J S
  exact forall_congr' (fun j => output_descends_iff N (S j))

/-! ## Non-vacuity -/

abbrev GaugeSpace := ℚ × ℚ × ℚ

def gaugeNull : Submodule ℚ GaugeSpace where
  carrier := {x | x.1 = 0 ∧ x.2.1 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro c a ha; simp_all

def gaugeStep : GaugeSpace →ₗ[ℚ] GaugeSpace where
  toFun x := (x.1 + x.2.1, x.2.1, x.2.2 + x.1)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' c x := by ext <;> simp <;> ring

def gaugeForm : LinearMap.BilinForm ℚ GaugeSpace where
  toFun x :=
    { toFun := fun y => x.1 * y.2.1 - x.2.1 * y.1
      map_add' := by intro y z; simp; ring
      map_smul' := by intro c y; simp; ring }
  map_add' x y := by apply LinearMap.ext; intro z; dsimp; ring
  map_smul' c x := by apply LinearMap.ext; intro z; dsimp; ring

def gaugeRead : GaugeSpace →ₗ[ℚ] (ℚ × ℚ) where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def visibleSource (j : ℚ) : GaugeSpace →ₗ[ℚ] ℚ where
  toFun x := j * x.1
  map_add' x y := by dsimp; ring
  map_smul' c x := by dsimp; ring

example : gaugeNull ≤ LinearMap.ker gaugeRead := by
  intro x hx
  change x.1 = 0 ∧ x.2.1 = 0 at hx
  change (x.1, x.2.1) = 0
  simp [hx.1, hx.2]

example (j : ℚ) : gaugeNull ≤ LinearMap.ker (visibleSource j) := by
  intro x hx
  change x.1 = 0 ∧ x.2.1 = 0 at hx
  change j * x.1 = 0
  simp [hx.1]

example : gaugeNull ≤ gaugeNull.comap gaugeStep := by
  intro x hx
  change x.1 = 0 ∧ x.2.1 = 0 at hx
  change x.1 + x.2.1 = 0 ∧ x.2.1 = 0
  simp [hx.1, hx.2]

example : (∀ n ∈ gaugeNull, ∀ x, gaugeForm n x = 0) ∧
    (∀ n ∈ gaugeNull, ∀ x, gaugeForm x n = 0) := by
  constructor <;> intro n hn x <;>
    change n.1 = 0 ∧ n.2.1 = 0 at hn <;>
    simp [gaugeForm, hn.1, hn.2]

example : gaugeForm (1, 0, 0) (0, 1, 0) = 1 := by norm_num [gaugeForm]

example : (0, 1, 0) ∈ LinearMap.ker (visibleSource 1) ∧
    gaugeForm (0, 1, 0) (1, 0, 0) ≠ 0 := by
  norm_num [visibleSource, gaugeForm]

example : (1, 0, 1) ∉ gaugeNull := by
  change ¬ ((1 : ℚ) = 0 ∧ 0 = 0)
  norm_num

example : gaugeForm (0, 1, 0) (1, 0, 0) ≠ 0 := by norm_num [gaugeForm]

end Artform.Scores.GravityBridge
