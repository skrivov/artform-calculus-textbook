import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RepresentationTheory.Basic
import ArtformTextbook.Meta.Book

/-!
# Reflections create perpendicularity (Section 3.6)

A finite group acting linearly on a real vector space, an inner product averaged over the group,
and the reflections among its elements. The linear action is a `Representation`: each group
element acts by a linear map, compatibly with the multiplication.
-/

namespace Artform

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A positive-definite inner product on a real vector space: a symmetric bilinear form
`⟨-,-⟩` with `⟨v, v⟩ > 0` for every `v ≠ 0`. -/
def IsInnerProduct (B : LinearMap.BilinForm ℝ V) : Prop :=
  B.IsSymm ∧ ∀ v : V, v ≠ 0 → 0 < B v v

/-- The averaged form of Section 3.6. For a finite group `G` acting linearly on `V` by `ρ` and a
starting inner product `⟨-,-⟩₀`, `⟨u, v⟩_G = (1/|G|) Σ_{g ∈ G} ⟨g u, g v⟩₀`. -/
noncomputable def averagedForm {G : Type*} [Monoid G] [Fintype G] (ρ : Representation ℝ G V)
    (B₀ : LinearMap.BilinForm ℝ V) : LinearMap.BilinForm ℝ V :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, B₀.compl₁₂ (ρ g) (ρ g)

/-- A reflection (Section 3.6): an element `s` with `s² = 1` whose `-1` eigenspace is
one-dimensional. Its `+1` eigenspace is its mirror hyperplane, and its `-1` eigenspace, the
reversed line, is its normal line. -/
def IsReflection {G : Type*} [Monoid G] (ρ : Representation ℝ G V) (s : G) : Prop :=
  s ^ 2 = 1 ∧ Module.finrank ℝ (Module.End.eigenspace (ρ s) (-1)) = 1

end Artform
