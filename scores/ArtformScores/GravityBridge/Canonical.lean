import ArtformScores.GravityBridge.CanonicalStatements
import ArtformScores.GravityBridge.Constraints

/-! # Canonical composition preserves the actual relation, with singular examples -/

namespace Artform.Scores.GravityBridge

noncomputable section

variable {K X Y Z : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]

lemma canonical_compose [FiniteDimensional K Y]
    (BX : LinearMap.BilinForm K X) (BY : LinearMap.BilinForm K Y)
    (BZ : LinearMap.BilinForm K Z) (hBY : BY.Nondegenerate)
    (R : Submodule K (X × Y)) (S : Submodule K (Y × Z))
    (hR : CanonicalLinear BX BY R) (hS : CanonicalLinear BY BZ S) :
    CanonicalLinear BX BZ (linearRelationCompose R S) := by
  intro a c
  constructor
  · rintro ⟨b, hab, hbc⟩ u w ⟨v, huv, hvw⟩
    exact ((hR a b).mp hab u v huv).trans ((hS b c).mp hbc v w hvw)
  · intro hac
    let PR := R.comap (tripleXY : (X × Y × Z) →ₗ[K] (X × Y))
    let PS := S.comap (tripleYZ : (X × Y × Z) →ₗ[K] (Y × Z))
    let phi : Module.Dual K (X × Y × Z) :=
      (BZ c).comp tripleZ - (BX a).comp tripleX
    have hphi : phi ∈ (PR ⊓ PS).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      rintro ⟨u, v, w⟩ hp
      have huv : (u, v) ∈ R := hp.1
      have hvw : (v, w) ∈ S := hp.2
      have he := hac u w ⟨v, huv, hvw⟩
      change BZ c w - BX a u = 0
      exact sub_eq_zero.mpr he.symm
    rw [Subspace.dualAnnihilator_inf_eq, Submodule.mem_sup] at hphi
    obtain ⟨f, hf, g, hg, hfg⟩ := hphi
    rw [Submodule.mem_dualAnnihilator] at hf hg
    let lam : Module.Dual K Y := f.comp insertY
    obtain ⟨b, hb⟩ := (BY.toDual hBY).surjective lam
    have hby (v : Y) : BY b v = f (0, v, 0) := by
      have he := congrArg (fun l : Module.Dual K Y => l v) hb
      exact he
    have hfz (w : Z) : f (0, 0, w) = 0 := hf _ (by exact R.zero_mem)
    have hgx (u : X) : g (u, 0, 0) = 0 := hg _ (by exact S.zero_mem)
    have hfx (u : X) : f (u, 0, 0) = -BX a u := by
      have he := LinearMap.congr_fun hfg (u, 0, 0)
      change f (u, 0, 0) + g (u, 0, 0) = BZ c 0 - BX a u at he
      simpa [hgx] using he
    have hgy (v : Y) : g (0, v, 0) = -f (0, v, 0) := by
      have he := LinearMap.congr_fun hfg (0, v, 0)
      change f (0, v, 0) + g (0, v, 0) = BZ c 0 - BX a 0 at he
      have hz : f (0, v, 0) + g (0, v, 0) = 0 := by simpa using he
      linear_combination hz
    have hgz (w : Z) : g (0, 0, w) = BZ c w := by
      have he := LinearMap.congr_fun hfg (0, 0, w)
      change f (0, 0, w) + g (0, 0, w) = BZ c w - BX a 0 at he
      simpa [hfz] using he
    refine ⟨b, (hR a b).mpr ?_, (hS b c).mpr ?_⟩
    · intro u v huv
      have he := hf (u, v, 0) (by exact huv)
      have hd : (u, v, (0 : Z)) = (u, 0, 0) + (0, v, 0) := by simp
      rw [hd, map_add, hfx, ← hby] at he
      exact eq_of_sub_eq_zero (by linear_combination -he)
    · intro v w hvw
      have he := hg (0, v, w) (by exact hvw)
      have hd : ((0 : X), v, w) = (0, v, 0) + (0, 0, w) := by simp
      rw [hd, map_add, hgy, ← hby, hgz] at he
      exact eq_of_sub_eq_zero (by linear_combination -he)

@[simp] lemma phaseForm_apply (x y : SingularPhase) :
    phaseForm x y = boundaryPair x.1 y.2 - boundaryPair x.2 y.1 := rfl

lemma singular_linear_iff (a b : SingularPhase) :
    (a, b) ∈ singularLinearRelation ↔ singularRelation a b := by
  rcases a with ⟨x, p⟩
  rcases b with ⟨y, q⟩
  rw [singular_relation_iff]
  change momentumConstraints ((x, p), (y, q)) = 0 ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    dsimp [momentumConstraints] at h0 h1 h2 h3
    exact ⟨h0, h1, by linarith, by linarith⟩
  · rintro ⟨hp, hq, hqp, hy⟩
    ext i
    fin_cases i <;> simp [momentumConstraints, hp, hq, hqp, hy]

lemma singular_param (a b c d : ℚ) :
    ((((a, b), (c, 0)), ((a + c, d), (c, 0))) : SingularPhase × SingularPhase) ∈
      singularLinearRelation := by
  rw [singular_linear_iff, singular_relation_iff]
  simp

lemma phase_alt : phaseForm.IsAlt := by
  intro x
  simp only [phaseForm_apply, boundaryPair]
  ring

lemma phase_separating : phaseForm.SeparatingLeft := by
  intro x h
  have h1 := h ((0, 0), (1, 0))
  have h2 := h ((0, 0), (0, 1))
  have h3 := h ((1, 0), (0, 0))
  have h4 := h ((0, 1), (0, 0))
  norm_num [phaseForm_apply, boundaryPair] at h1 h2 h3 h4
  ext <;> dsimp <;> linarith

lemma phase_nondegenerate : phaseForm.Nondegenerate := by
  refine ⟨phase_separating, ?_⟩
  intro x h
  apply phase_separating x
  intro y
  have he := phase_alt.neg_eq x y
  rw [h y] at he
  exact neg_eq_zero.mp he

lemma singular_canonical :
    ∀ a b : SingularPhase, (a, b) ∈ singularLinearRelation ↔
      ∀ u v : SingularPhase, (u, v) ∈ singularLinearRelation →
        phaseForm a u = phaseForm b v := by
  intro a b
  constructor
  · intro hab u v huv
    have hab' := (singular_relation_iff a.1 a.2 b.1 b.2).mp
      ((singular_linear_iff a b).mp hab)
    have huv' := (singular_relation_iff u.1 u.2 v.1 v.2).mp
      ((singular_linear_iff u v).mp huv)
    rcases hab' with ⟨hpa, hpb, hp, hq⟩
    rcases huv' with ⟨hpu, hpv, hpuv, hquv⟩
    simp only [phaseForm_apply, boundaryPair]
    rw [hpa, hpb, hp, hq, hpu, hpv, hpuv, hquv]
    ring
  · intro h
    rw [singular_linear_iff, singular_relation_iff]
    have h1 := h _ _ (singular_param 0 1 0 0)
    have h2 := h _ _ (singular_param 0 0 0 1)
    have h3 := h _ _ (singular_param 1 0 0 0)
    have h4 := h _ _ (singular_param 0 0 1 0)
    norm_num [phaseForm_apply, boundaryPair] at h1 h2 h3 h4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma cotangent_param_injective : Function.Injective quadraticCotangent := by
  intro a b h
  have hp := congrArg (fun p : Plane × Plane => p.1.2) h
  have ht := congrArg (fun p : Plane × Plane => p.2.1) h
  exact Prod.ext ht hp

lemma cotangent_tangent_injective (a : Plane) : Function.Injective (quadraticTangent a) := by
  intro u v h
  have hp := congrArg (fun p : Plane × Plane => p.1.2) h
  have ht := congrArg (fun p : Plane × Plane => p.2.1) h
  exact Prod.ext ht hp

lemma cotangent_tangent_isotropic (a u v : Plane) :
    -areaForm (quadraticTangent a u).1 (quadraticTangent a v).1 +
      areaForm (quadraticTangent a u).2 (quadraticTangent a v).2 = 0 := by
  dsimp [quadraticTangent, areaForm]
  ring

lemma cotangent_exact_variation (a u : Plane) (e : ℝ) :
    quadraticCotangent (a + e • u) = quadraticCotangent a + e • quadraticTangent a u +
      e ^ 2 • (((u.1 ^ 2, 0), (0, 2 * u.1 * u.2)) : Plane × Plane) := by
  ext <;> dsimp [quadraticCotangent, quadraticTangent] <;> ring

lemma vertical_composition (z : Plane) :
    (∃ y : Plane, y.1 = 0 ∧ cotangentRelation y z) ↔ z = 0 := by
  constructor
  · rintro ⟨y, hy, t, p, rfl, rfl⟩
    change t ^ 2 = 0 at hy
    have ht : t = 0 := sq_eq_zero_iff.mp hy
    simp [ht]
  · rintro rfl
    refine ⟨0, rfl, 0, 0, ?_, ?_⟩ <;> norm_num <;> rfl

lemma failed_clean_linearization (p : ℝ) :
    (quadraticTangent (0, p) (1, 0)).1.1 = 0 ∧
    (quadraticTangent (0, p) (1, 0)).2.1 = 1 ∧
    ¬ ∃ e : ℝ, e ≠ 0 ∧ (quadraticCotangent ((0, p) + e • (1, 0))).1.1 = 0 := by
  constructor
  · norm_num [quadraticTangent]
  constructor
  · rfl
  · rintro ⟨e, he, hh⟩
    have heq : e ^ 2 = 0 := by simpa [quadraticCotangent] using hh
    exact he (sq_eq_zero_iff.mp heq)

/-- **GAC:canonical-composition** (linear composition and a non-clean polynomial test). -/
@[ledger "GAC:canonical-composition"]
theorem canonicalLaw : Statement.canonicalLaw := by
  refine ⟨?_, ⟨phase_alt, phase_nondegenerate, singular_canonical⟩,
    cotangent_param_injective, ?_, cotangent_exact_variation,
    vertical_composition, failed_clean_linearization⟩
  · intro K X Y Z _ _ _ _ _ _ _ _ BX BY BZ hBY R S hR hS
    exact canonical_compose BX BY BZ hBY R S hR hS
  · intro a
    exact ⟨cotangent_tangent_injective a, cotangent_tangent_isotropic a⟩

/-! ## Non-vacuity -/

example : CanonicalLinear phaseForm phaseForm
    (linearRelationCompose singularLinearRelation singularLinearRelation) :=
  canonical_compose phaseForm phaseForm phaseForm phase_nondegenerate
    singularLinearRelation singularLinearRelation singular_canonical singular_canonical

end

end Artform.Scores.GravityBridge
