import ArtformTextbook.Ch11.Defs.Tick

/-!
# From a phase to an energy (Section 11.3)

An electric energy table declares a rational level `E(ρ)` for every irreducible representation
of the link's group, zero on the trivial one and positive on the others; the electric energy of
the link multiplies the block `B_ρ` by `E(ρ)`: it is convolution by the class function
`(1/|G|) Σ_ρ E(ρ) d_ρ χ_ρ`. The irreducible representations are the members of a complete family
`σ` of distinct irreducible representations (`Ch11/Defs/Response.lean`).

The energy law of one edge is `H = κ H_E + V` (`eq:mt-energy-law`), with a declared coupling
`κ > 0` and `V` the hop of Section 11.6.
-/

namespace Artform

variable {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- **Definition 11.9** (declared electric energy). An electric energy table is a function
`E : Irr(G) → ℚ` with `E(1) = 0` and `E(ρ) > 0` otherwise: here `E` is defined on the members
of a complete family `σ` of distinct irreducible representations, `1` being the member on which
every element acts as the identity. -/
@[book "def:mt-energy"]
def IsEnergyTable (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) : Prop :=
  ∀ i, ((σ i).IsTrivial → E i = 0) ∧ (¬ (σ i).IsTrivial → 0 < E i)

/-- **Definition 11.9** (declared electric energy). The electric energy of a link is the operator
`H_E` that multiplies the block `B_ρ` by `E(ρ)`: convolution by
`(1/|G|) Σ_ρ E(ρ) d_ρ χ_ρ`, here on tables with values in any complex vector space (on the
states of an edge it acts on the link). -/
@[book "def:mt-energy"]
noncomputable def electricEnergy {A : Type*} [AddCommGroup A] [Module ℂ A]
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) (ψ : G → A) : G → A :=
  tableConv (responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ)) fun i => (E i : ℂ)) ψ

namespace Edge

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The energy law of one edge (`eq:mt-energy-law`): `H = κ H_E + V`, with `κ` a declared
coupling, `H_E` the electric energy of the link (Definition 11.9) and `V` the hop of the edge,
which moves quarks along the edge. -/
noncomputable def energyLaw (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) (κ : ℝ)
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  (κ : ℂ) • electricEnergy σ E ψ + hop ρ ord ψ

end Edge

end Artform
