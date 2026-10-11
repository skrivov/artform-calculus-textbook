import Mathlib.LinearAlgebra.UnitaryGroup
import ArtformTextbook.Ch11.Defs.Energy
import ArtformTextbook.Ch11.Defs.Tick
import ArtformTextbook.Ch12.Defs.ColourGroups
import ArtformTextbook.Exact.R8

/-!
# Statements of Chapter 11: the hop, its coin, and a native tick

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.

The setting is that of `Ch11/Defs/Colourless.lean` and `Ch11/Defs/Tick.lean`: one edge `x → y`
over a group `G` whose triplet is a homomorphism `ρ : G →* Matrix C C ℂ`, with the slots `S` and
the modes of the edge in any order. Operators on the states of the edge are maps of the states;
the pairing of states is `Edge.statePairing`, and the norm of a state is the norm of Lean's
function spaces, the largest size of a coefficient.
-/

namespace Artform.Statement

open scoped Matrix ComplexConjugate

/-- **Proposition 11.16** (the hop is covariant). For all gauge pairs and link values,
`Γ_x(h_x) Γ_y(h_y) V_U Γ_y(h_y)⁻¹ Γ_x(h_x)⁻¹ = V_{h_y U h_x⁻¹}`. Hence `V` commutes with the gauge
action of `G × G` on link and matter together, and maps colourless states to colourless states.

The triplet `ρ` takes unitary values, as the book's colour groups do (its proof uses that `h_x` is
unitary); the inverses are matrix inverses. -/
@[book "prop:mt-hop-covariant"]
def mtHopCovariant : Prop :=
  ∀ (G : Type) [Group G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
    (ρ : G →* Matrix C C ℂ), (∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ) →
    ∀ ord : LinearOrder (Edge.Mode C S),
    (∀ hx hy U : G, Edge.gammaX ord (ρ hx) * Edge.gammaY ord (ρ hy) * Edge.hopAt ord (ρ U) *
        (Edge.gammaY ord (ρ hy))⁻¹ * (Edge.gammaX ord (ρ hx))⁻¹ =
      Edge.hopAt ord (ρ (hy * U * hx⁻¹))) ∧
    (∀ (hx hy : G) (ψ : G → Finset (Edge.Mode C S) → ℂ),
      Edge.hop ρ ord (Edge.gaugeAct ρ ord hx hy ψ) =
        Edge.gaugeAct ρ ord hx hy (Edge.hop ρ ord ψ)) ∧
    ∀ ψ ∈ Edge.colourless ρ ord, Edge.hop ρ ord ψ ∈ Edge.colourless ρ ord

/-- **Proposition 11.17** (the coin's coefficients are minors). The coefficient of `Γ(W)` from
the `k`-quark state with occupied modes `m₁ < ⋯ < m_k` to the one with occupied modes
`m'₁ < ⋯ < m'_k` is the `k × k` minor of `W` with rows `m'₁, …, m'_k` and columns `m₁, …, m_k`.
Hence the coefficients of `Γ(W_U)` lie in `R₈` for every link value of the cube group, and
`Γ(W_U)` is unitary.

The first part is for any finite set of modes in any order and any matrix `W`; the minor is the
determinant of the `k × k` matrix whose `(i, j)` entry is `W_{m'_i m_j}`, the modes listed in
ascending order (`Finset.orderEmbOfFin`). The second part is for the edge with three colours and
any slots `S`, in any order of its modes, and every element `U` of the cube group (Model I,
`cubeGroup`); `R₈` is read in `ℂ` (`Exact.R8C`). -/
@[book "prop:mt-minors"]
def mtMinors : Prop :=
  (∀ (M : Type) [Fintype M] [DecidableEq M] (ord : LinearOrder M) (W : Matrix M M ℂ) (k : ℕ)
      (n n' : Finset M) (hn : n.card = k) (hn' : n'.card = k),
      Fock.secondQuant ord W n' n =
        (W.submatrix (@Finset.orderEmbOfFin M ord n' k hn')
          (@Finset.orderEmbOfFin M ord n k hn)).det) ∧
  ∀ (S : Type) [Fintype S] [DecidableEq S] (ord : LinearOrder (Edge.Mode (Fin 3) S))
    (U : cubeGroup),
    (∀ n n', Fock.secondQuant ord
        (Edge.coinW (((U : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
          Matrix (Fin 3) (Fin 3) ℂ))) n' n ∈ Exact.R8C) ∧
      Fock.secondQuant ord (Edge.coinW (((U : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
          Matrix (Fin 3) (Fin 3) ℂ))) ∈
        Matrix.unitaryGroup (Finset (Edge.Mode (Fin 3) S)) ℂ

/-- **Theorem 11.18** (the tick preserves the colourless sector). `T` commutes with the gauge
action of `G × G`. Hence it maps colourless states to colourless states, and is unitary on them.

The group `G` is finite, its triplet takes unitary values, and `T = 𝒞 𝒦` is the tick of
`eq:mt-tick` with the electric read `𝒦` of any electric response `r` (Definition 11.7) on a
complete family `σ` of distinct irreducible representations. "Unitary on them" is read as: `T`
keeps the pairing of colourless states, and every colourless state is `T` of a colourless
state. -/
@[book "thm:mt-tick-gauss"]
def mtTickGauss : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S]
    [DecidableEq S] (ρ : G →* Matrix C C ℂ), (∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ) →
    ∀ (ord : LinearOrder (Edge.Mode C S)) (ι : Type) [Fintype ι] (d : ι → ℕ)
      (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)), IsCompleteFamily σ →
    ∀ r : ι → ℂ, IsElectricResponse σ r →
    (∀ (hx hy : G) (ψ : G → Finset (Edge.Mode C S) → ℂ),
      Edge.tick ρ ord σ r (Edge.gaugeAct ρ ord hx hy ψ) =
        Edge.gaugeAct ρ ord hx hy (Edge.tick ρ ord σ r ψ)) ∧
    (∀ ψ ∈ Edge.colourless ρ ord, Edge.tick ρ ord σ r ψ ∈ Edge.colourless ρ ord) ∧
    (∀ ψ ∈ Edge.colourless ρ ord, ∀ φ ∈ Edge.colourless ρ ord,
      Edge.statePairing (Edge.tick ρ ord σ r ψ) (Edge.tick ρ ord σ r φ) =
        Edge.statePairing ψ φ) ∧
    ∀ φ ∈ Edge.colourless ρ ord, ∃ ψ ∈ Edge.colourless ρ ord, Edge.tick ρ ord σ r ψ = φ

/-- **Proposition 11.19** (link moments). For an irreducible triplet of a finite subgroup of
`SU(3)`, using a real orthonormal basis when the triplet is real,
`(1/|G|) Σ_U U = 0`, `(1/|G|) Σ_U U_{ij} conj(U_{kl}) = δ_{ik} δ_{jl} / 3`,
`(1/|G|) Σ_U U_{ij} U_{kl}` is `δ_{ik} δ_{jl} / 3` if the triplet is real and `0` if `3 ⊗ 3`
has no invariant, and when `3^{⊗3}` has exactly one invariant,
`(1/|G|) Σ_U U_{ij} U_{kl} U_{mn} = ε_{ikm} ε_{jln} / 6`.

The group is any finite group `G` with a triplet `ρ : G → SU(3)` (a subgroup of `SU(3)` with its
inclusion is the book's case), irreducible as a representation on `ℂ³`; `U_{ij}` is
`ρ(U)_{ij}`. "The triplet is real, in a real orthonormal basis" is read as: every `ρ(U)` has real
entries in the basis used. "`3 ⊗ 3` has no invariant": the only `T` with `U T Uᵀ = T` for all `U`
(the action of `U ⊗ U` on `T ∈ ℂ³ ⊗ ℂ³`) is `0`. "`3^{⊗3}` has exactly one invariant": the space
of invariant tensors (`Edge.tripleInvariants`) has dimension one. `ε` is the Levi-Civita
symbol. -/
@[book "prop:mt-moments"]
def mtMoments : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ),
    (∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) → (Edge.tripletRep ρ).IsIrreducible →
    (Fintype.card G : ℂ)⁻¹ • ∑ U, ρ U = 0 ∧
    (∀ i j k l, (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * conj (ρ U k l) =
      (if i = k ∧ j = l then 1 else 0) / 3) ∧
    ((∀ U i j, conj (ρ U i j) = ρ U i j) →
      ∀ i j k l, (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * ρ U k l =
        (if i = k ∧ j = l then 1 else 0) / 3) ∧
    ((∀ T : Matrix (Fin 3) (Fin 3) ℂ, (∀ U, ρ U * T * (ρ U)ᵀ = T) → T = 0) →
      ∀ i j k l, (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * ρ U k l = 0) ∧
    (Module.finrank ℂ (Edge.tripleInvariants ρ) = 1 →
      ∀ i j k l m n, (Fintype.card G : ℂ)⁻¹ * ∑ U, ρ U i j * ρ U k l * ρ U m n =
        leviCivita i k m * leviCivita j l n / 6)

/-- **Theorem 11.20** (the there-and-back tally). Let `P` be the projector onto the zero-flux
sector, and `A_{cc'} = Σ_s a†_{ycs} a_{xc's}`. Then `P V P = 0`, the hop moves the link's table
into the triplet block or its conjugate, and `P V² P = Ω`,
`Ω = (1/3) Σ_{c,c'} (A†_{cc'} A_{cc'} + A_{cc'} A†_{cc'})
  + (m/3) Σ_{c,c'} (A_{cc'} A_{cc'} + A†_{cc'} A†_{cc'})`,
with `m = 1` for a real triplet and `m = 0` when `3 ⊗ 3` has no invariant, both sides restricted
to the sector. Consequently the family of coins `Γ(e^{iθ K_U}) = e^{iθ V_U}`, of which the native
coin is the member `θ = π/4`, returns to the sector as `P 𝒞_θ P = P - (θ²/2) Ω + O(θ³)`, and the
second-order shift of the energy law `H = κ H_E + V` on the sector is `-Ω/(κ E₃)`.

The setting is that of Proposition 11.19: a finite group `G` with an irreducible triplet
`ρ : G → SU(3)`, real (in the basis used) when `m = 1`. The irreducible representations are a
complete family `σ`; `E` is an electric energy table (Definition 11.9), `κ > 0`, and `E₃` is
the level of the triplet, which the conjugate triplet shares (as the book declares for every
group of this part). The modes of the edge are in any order.
* `P` is any orthogonal projector onto the zero-flux sector: its values lie in the sector, it
  fixes the sector, and it is self-adjoint for the pairing of states.
* "The hop moves the link's table into the triplet block or its conjugate": for a zero-flux
  state `ψ` and every occupation table `n`, the table `U ↦ (Vψ)(U)(n)` lies in the sum of the
  blocks (Definition 11.3) of the triplet and of the conjugate triplet.
* `O(θ³)` is a bound `C |θ|³ ‖ψ‖` for all `θ` and all `ψ` in the sector.
* The second-order shift is `-P V Q (κ H_E|_Q)⁻¹ Q V P` with `Q = 1 - P`, as the book's proof
  computes it: for `ψ` in the sector, `(κ H_E|_Q)⁻¹ Q V P ψ` is a state `χ` in the range of `Q`
  (`χ - P χ = χ`) with `κ H_E χ = Q V P ψ`; such a `χ` exists, and for every such `χ`,
  `-P V Q χ = -Ω ψ/(κ E₃)`. -/
@[book "thm:mt-there-and-back"]
def mtThereAndBack : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (S : Type) [Fintype S] [DecidableEq S]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ), (∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) →
    (Edge.tripletRep ρ).IsIrreducible →
    ∀ (ord : LinearOrder (Edge.Mode (Fin 3) S)) (ι : Type) [Fintype ι] (d : ι → ℕ)
      (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)), IsCompleteFamily σ →
    ∀ E : ι → ℚ, IsEnergyTable σ E → ∀ E₃ : ℚ,
      (∀ i, (Nonempty ((Edge.tripletRep ρ).Equiv (σ i)) ∨
        Nonempty ((Edge.conjTripletRep ρ).Equiv (σ i))) → E i = E₃) →
    ∀ κ : ℝ, 0 < κ →
    ∀ m : ℕ, (m = 1 ∧ ∀ U i j, conj (ρ U i j) = ρ U i j) ∨
      (m = 0 ∧ ∀ T : Matrix (Fin 3) (Fin 3) ℂ, (∀ U, ρ U * T * (ρ U)ᵀ = T) → T = 0) →
    ∀ P : (G → Finset (Edge.Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Edge.Mode (Fin 3) S) → ℂ),
      (∀ ψ, P ψ ∈ Edge.zeroFlux ρ ord) → (∀ ψ ∈ Edge.zeroFlux ρ ord, P ψ = ψ) →
      (∀ ψ φ, Edge.statePairing (P ψ) φ = Edge.statePairing ψ (P φ)) →
    (∀ ψ, P (Edge.hop ρ ord (P ψ)) = 0) ∧
    (∀ ψ ∈ Edge.zeroFlux ρ ord, ∀ n, (fun U => Edge.hop ρ ord ψ U n) ∈
      block (Edge.tripletRep ρ) ⊔ block (Edge.conjTripletRep ρ)) ∧
    (∀ ψ ∈ Edge.zeroFlux ρ ord,
      P (Edge.hop ρ ord (Edge.hop ρ ord ψ)) = Edge.atEachLink (Edge.tally ord m) ψ) ∧
    (∀ (θ : ℝ) (U : G),
      Fock.secondQuant ord (NormedSpace.exp (((θ : ℂ) * Complex.I) • Edge.coinK (ρ U))) =
        NormedSpace.exp (((θ : ℂ) * Complex.I) • Edge.hopAt ord (ρ U))) ∧
    (∀ U : G, NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • Edge.coinK (ρ U)) =
      (Edge.coinW (ρ U) : Matrix (Edge.Mode (Fin 3) S) (Edge.Mode (Fin 3) S) ℂ)) ∧
    (∃ K : ℝ, ∀ θ : ℝ, ∀ ψ ∈ Edge.zeroFlux ρ ord,
      ‖P (Edge.coinFamily ρ ord θ ψ) -
          (ψ - ((θ : ℂ) ^ 2 / 2) • Edge.atEachLink (Edge.tally ord m) ψ)‖ ≤
        K * |θ| ^ 3 * ‖ψ‖) ∧
    ∀ ψ ∈ Edge.zeroFlux ρ ord,
      (∃ χ, χ - P χ = χ ∧ (κ : ℂ) • electricEnergy σ E χ =
        Edge.hop ρ ord (P ψ) - P (Edge.hop ρ ord (P ψ))) ∧
      ∀ χ, χ - P χ = χ → (κ : ℂ) • electricEnergy σ E χ =
          Edge.hop ρ ord (P ψ) - P (Edge.hop ρ ord (P ψ)) →
        -P (Edge.hop ρ ord (χ - P χ)) =
          -(((κ * E₃ : ℝ) : ℂ)⁻¹ • Edge.atEachLink (Edge.tally ord m) ψ)

end Artform.Statement
