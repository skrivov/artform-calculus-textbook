import ArtformTextbook.Ch13.Defs.Transfer

/-!
# The third-order term of the energy law (Section 13.3)

On the zero-flux sector of one edge the energy law `κ H_E + V` (`eq:mt-energy-law`) has energy
zero, and the book's proof of Theorem 13.8 takes its third-order term as `P V R V R V P`, with
`R = -(κ H_E)⁻¹` off the sector; the further third-order terms carry the factor `P V P`, which is
zero (Theorem 11.20).

`R` is written with the electric energy of Definition 11.9 for the table `1/E`: on a block of
level `E(ρ) > 0` it multiplies by `-1/(κ E(ρ))`, and on the trivial block, the tables constant in
the link value, it is zero (the inverse of `0` is `0`). On the colourless states, where the
perturbation series runs, the trivial block is the zero-flux sector, so this is `-(κ H_E)⁻¹` off
the sector and zero on it.
-/

namespace Artform

namespace Edge

variable {G : Type*} [Group G] [Fintype G] {S : Type*} [Fintype S] [DecidableEq S]
  {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- The reduced resolvent `R = -(κ H_E)⁻¹` off the zero-flux sector: `-1/κ` times the electric
energy (Definition 11.9) of the table `1/E`, which is `0` on the trivial member. -/
noncomputable def reducedResolvent (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ)
    (κ : ℝ) (ψ : G → Finset (Mode (Fin 3) S) → ℂ) : G → Finset (Mode (Fin 3) S) → ℂ :=
  (-((κ : ℂ)⁻¹)) • electricEnergy σ (fun i => (E i)⁻¹) ψ

/-- The third-order term `H⁽³⁾ = P V R V R V P` of the energy law `κ H_E + V` on the zero-flux
sector, with `P` a projector onto the sector, `V` the hop and `R` the reduced resolvent. -/
noncomputable def thirdOrder (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S)) (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (E : ι → ℚ) (κ : ℝ)
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ))
    (ψ : G → Finset (Mode (Fin 3) S) → ℂ) : G → Finset (Mode (Fin 3) S) → ℂ :=
  P (hop ρ ord (reducedResolvent σ E κ (hop ρ ord (reducedResolvent σ E κ (hop ρ ord (P ψ))))))

end Edge

end Artform
