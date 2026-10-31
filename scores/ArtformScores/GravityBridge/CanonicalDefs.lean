import ArtformScores.GravityBridge.ConstraintDefs

/-! # Linear canonical relations and polynomial intersection data -/

namespace Artform.Scores.GravityBridge

noncomputable section

variable {K X Y Z : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]

def linearRelationCompose (R : Submodule K (X × Y)) (S : Submodule K (Y × Z)) :
    Submodule K (X × Z) where
  carrier := {p | ∃ y, (p.1, y) ∈ R ∧ (y, p.2) ∈ S}
  zero_mem' := ⟨0, R.zero_mem, S.zero_mem⟩
  add_mem' := by
    rintro a b ⟨y, hyR, hyS⟩ ⟨v, hvR, hvS⟩
    exact ⟨y + v, R.add_mem hyR hvR, S.add_mem hyS hvS⟩
  smul_mem' := by
    rintro c a ⟨y, hyR, hyS⟩
    exact ⟨c • y, R.smul_mem c hyR, S.smul_mem c hyS⟩

def CanonicalLinear (BX : LinearMap.BilinForm K X) (BY : LinearMap.BilinForm K Y)
    (R : Submodule K (X × Y)) : Prop :=
  ∀ x y, (x, y) ∈ R ↔ ∀ u v, (u, v) ∈ R → BX x u = BY y v

def tripleXY : (X × Y × Z) →ₗ[K] (X × Y) where
  toFun p := (p.1, p.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tripleYZ : (X × Y × Z) →ₗ[K] (Y × Z) := LinearMap.snd K X (Y × Z)

def tripleX : (X × Y × Z) →ₗ[K] X := LinearMap.fst K X (Y × Z)

def tripleZ : (X × Y × Z) →ₗ[K] Z :=
  (LinearMap.snd K Y Z).comp (LinearMap.snd K X (Y × Z))

def insertX : X →ₗ[K] (X × Y × Z) where
  toFun x := (x, 0, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def insertY : Y →ₗ[K] (X × Y × Z) where
  toFun y := (0, y, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def insertZ : Z →ₗ[K] (X × Y × Z) where
  toFun z := (0, 0, z)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def phaseForm : LinearMap.BilinForm ℚ SingularPhase where
  toFun x :=
    { toFun := fun y => boundaryPair x.1 y.2 - boundaryPair x.2 y.1
      map_add' := by intro y z; dsimp [boundaryPair]; ring
      map_smul' := by intro c y; dsimp [boundaryPair]; ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change boundaryPair (x + y).1 z.2 - boundaryPair (x + y).2 z.1 =
      (boundaryPair x.1 z.2 - boundaryPair x.2 z.1) +
        (boundaryPair y.1 z.2 - boundaryPair y.2 z.1)
    dsimp [boundaryPair]
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    change boundaryPair (c • x).1 z.2 - boundaryPair (c • x).2 z.1 =
      c * (boundaryPair x.1 z.2 - boundaryPair x.2 z.1)
    dsimp [boundaryPair]
    ring

def momentumConstraints : (SingularPhase × SingularPhase) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun a := ![a.1.2.2, a.2.2.2, a.2.2.1 - a.1.2.1, a.2.1.1 - a.1.1.1 - a.1.2.1]
  map_add' a b := by ext i; fin_cases i <;> dsimp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> dsimp <;> ring

def singularLinearRelation : Submodule ℚ (SingularPhase × SingularPhase) :=
  LinearMap.ker momentumConstraints

abbrev Plane := ℝ × ℝ

def areaForm (x y : Plane) : ℝ := x.1 * y.2 - x.2 * y.1

def quadraticCotangent (a : Plane) : Plane × Plane := ((a.1 ^ 2, a.2), (a.1, 2 * a.1 * a.2))

def quadraticTangent (a u : Plane) : Plane × Plane :=
  ((2 * a.1 * u.1, u.2), (u.1, 2 * a.2 * u.1 + 2 * a.1 * u.2))

def cotangentRelation (y z : Plane) : Prop :=
  ∃ t p : ℝ, y = (t ^ 2, p) ∧ z = (t, 2 * t * p)

end

end Artform.Scores.GravityBridge
