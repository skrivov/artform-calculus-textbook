import ArtformTextbook.Ch03.Defs.Metric

/-!
# Statements of Chapter 3: metrics

Each statement of the book is a proposition here, tagged with the book's label. Its proof, in
`Ch03/Metric.lean`, is a theorem whose type is exactly this proposition.
-/

namespace Artform.Statement

/-- **Theorem 3.25** (averaged invariant metric). Let a finite group `G` act linearly on a real
vector space `V`, and let `⟨-,-⟩₀` be a positive-definite inner product on `V`. The averaged form
`⟨u, v⟩_G = (1/|G|) Σ_{g ∈ G} ⟨g u, g v⟩₀` is a positive-definite inner product and is
`G`-invariant: `⟨h u, h v⟩_G = ⟨u, v⟩_G` for every `h ∈ G`. -/
@[book "nolabel:03-pattern-geometry:averaged-invariant-metric"]
def averagedInvariantMetric : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : Type) [AddCommGroup V] [Module ℝ V]
    (ρ : Representation ℝ G V) (B₀ : LinearMap.BilinForm ℝ V), IsInnerProduct B₀ →
    IsInnerProduct (averagedForm ρ B₀) ∧
    ∀ (h : G) (u v : V), averagedForm ρ B₀ (ρ h u) (ρ h v) = averagedForm ρ B₀ u v

/-- **Proposition 3.26** (perpendicularity from symmetry). Let a group `G` act linearly on a real
vector space. For a `G`-invariant inner product, the `+1` and `-1` eigenspaces of a reflection
`s ∈ G` are perpendicular. The book's group is finite; Lean states it for every group. -/
@[book "nolabel:03-pattern-geometry:perpendicularity-from-symmetry"]
def perpendicularityFromSymmetry : Prop :=
  ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℝ V]
    (ρ : Representation ℝ G V) (B : LinearMap.BilinForm ℝ V), IsInnerProduct B →
    (∀ (h : G) (u v : V), B (ρ h u) (ρ h v) = B u v) →
    ∀ s : G, IsReflection ρ s →
      ∀ u ∈ Module.End.eigenspace (ρ s) 1, ∀ v ∈ Module.End.eigenspace (ρ s) (-1), B u v = 0

end Artform.Statement
