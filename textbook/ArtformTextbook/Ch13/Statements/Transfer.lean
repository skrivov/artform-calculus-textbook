import ArtformTextbook.Ch12.Groups
import ArtformTextbook.Ch13.Defs.Transfer

/-!
# Statements of Chapter 13: the third-order transfer

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of `Ch12/Defs/Models.lean` and `Ch13/Defs/Transfer.lean`: one edge with two
slots per colour read as spin, the five colour groups of Chapter 12, and the third-order term
`L = P V³ P` of Theorem 13.8.

* **`L` for the five models.** For the four finite colour groups `L = P V³ P` literally, for every
  orthogonal projector `P` onto the zero-flux sector (as in Theorem 11.20); its zero-flux states
  are constant in the link value, and `L` is read on their values (`Edge.transferVal`). For the
  `SU(3)` reference the projector `P` is the average over the link with the invariant measure of
  `SU(3)`, which is not used here: `L` is the form Theorem 13.8 gives it for a complex triplet,
  the words `Edge.transferWords ord false`.
* **Orders of the modes.** Theorem 13.9 orders the modes "`x` before `y`"; within an end the book's
  order is colour before spin (the verifier's `6 v + 2 c + s`, `Edge.bookOrd`), in which the named
  states of Chapter 12 are written. The spectra hold in every order of the modes.
-/

namespace Artform.Statement

open scoped Matrix

open Module

open Classical in
/-- **Theorem 13.9** (what the transfer does). Let `q_x(m)` be the four members of the quartet of
Figure `fig:mm-two-slot-invariants` at `x`, with spin `m = 3/2, 1/2, -1/2, -3/2`, let `|full_x⟩` be
the full vertex, `D_x` the pair and `H_x` the paired holes, and likewise at `y`; the modes are
ordered `x` before `y`.
1. In all five models a baryon hops as one assembly: `L q_x(m) = 6 q_y(m)` and
   `L q_y(m) = 6 q_x(m)`, the same spin and nothing else, with amplitude `6` for every `m`. Under
   the law the transfer amplitude is `6/(κ E₃)² = 27/(8 κ²)`.
2. Let `ψ₀ = ½ Σ_m (-1)^{3/2 - m} q̂_x(m) q̂_y(-m)` be the spin-singlet two-baryon state, with
   `q̂` the normalized quartet members. In all five models its transfer has full-vertex component
   `-12` at each end. For a complex triplet this is the whole image:
   `L ψ₀ = -12 (|full_x⟩ + |full_y⟩)`.
3. For the real triplets two channels are added. A pair at `x` with a baryon at `y` becomes a
   baryon at `x` with the pair at `y`, `L (D_x q_y(m)) = ±6 q_x(m) D_y` for every `m`, with its
   mirror in the holes; and `L ψ₀` acquires the two chain states `c₂`, `c₃` of Figure
   `fig:mm-chain` with amplitude `12` beside the full vertices, so that `‖L ψ₀‖ = 24`.
4. On the sixty-four zero-flux states of the real triplets and the thirty-six of the complex ones,
   `L` has the values of Figure `fig:ml-transfer-spectra`, and is zero outside the sectors listed
   there.

`L` is read as in the module docstring; the states are the tables of `Ch12/Defs/Models.lean`
(`D_x q_y(m)` is the product `D ⊗ q(m)`, "a product fills the ends in the order written"), in the
book's order. The component of a table along the unit table `|full_x⟩` is the pairing with it.
The signs `±` and the amplitude `12` are the computed ones: `L (D_x q_y(m)) = -6 q_x(m) D_y`, its
mirror `L (H_x q_y(m)) = 6 q_x(m) H_y`, and `L ψ₀ = -12 (c₁ + c₂ + c₃ + c₄)` with
`c₁ = |full_x⟩`, `c₄ = |full_y⟩`. The table of Figure `fig:ml-transfer-spectra` gives, by the total
number `N` of quarks: `(-6)⁴ 6⁴` at `N = 3` and `N = 9`; at `N = 5` and `N = 7` the same for the
real triplets and no states for the complex ones; at `N = 6` the values `(-24)¹ 0¹⁸ 24¹` for the
real triplets and `(-12√2)¹ 0¹⁶ (12√2)¹` for the complex ones; and `0` on every other sector. The
law's transfer amplitude uses the declared level `E₃ = 4/3` of the triplet (Section 12.1); "under
the law" the coefficient of `L` in `H⁽³⁾ = L/(κ E₃)²` is `1/(κ E₃)²` (Theorem 13.8), for every
coupling `κ ≠ 0`. -/
@[book "thm:ml-transfer-values"]
def mlTransferValues : Prop :=
  let claims : Module.End ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) → Bool → Prop :=
    fun L real =>
      (∀ m : Fin 4, L (Edge.quartetX m) = (6 : ℂ) • Edge.quartetY m ∧
        L (Edge.quartetY m) = (6 : ℂ) • Edge.quartetX m) ∧
      coeffPairing Edge.fullX (L Edge.singlet) = -12 ∧
      coeffPairing Edge.fullY (L Edge.singlet) = -12 ∧
      (real = false → L Edge.singlet = (-12 : ℂ) • (Edge.fullX + Edge.fullY)) ∧
      (real = true →
        (∀ m : Fin 4, L (Edge.prod (Vertex.pair Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m))
          = (-6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.pair Vertex.bookOrd)) ∧
        (∀ m : Fin 4,
          L (Edge.prod (Vertex.holes Vertex.bookOrd) (Vertex.quartet Vertex.bookOrd m)) =
            (6 : ℂ) • Edge.prod (Vertex.quartet Vertex.bookOrd m) (Vertex.holes Vertex.bookOrd)) ∧
        L Edge.singlet =
          (-12 : ℂ) • (Edge.fullX + Edge.fullY + Edge.chain 1 + Edge.chain 2) ∧
        Fock.hilbertNorm (L Edge.singlet) = 24)
  let table : Submodule ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) →
      Module.End ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) → Bool → Prop := fun Z L real =>
    let sec : ℕ → Submodule ℂ (Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) := fun N =>
      Z ⊓ Fock.numberSector (Edge.Mode (Fin 3) (Fin 2)) N
    (∀ N ∈ ({3, 9} : Set ℕ), ∀ μ : ℂ,
      finrank ℂ ↥(sec N ⊓ End.eigenspace L μ) = if μ = 6 ∨ μ = -6 then 4 else 0) ∧
    (∀ N ∈ ({5, 7} : Set ℕ), if real then ∀ μ : ℂ,
      finrank ℂ ↥(sec N ⊓ End.eigenspace L μ) = if μ = 6 ∨ μ = -6 then 4 else 0
      else sec N = ⊥) ∧
    (∀ μ : ℂ, finrank ℂ ↥(sec 6 ⊓ End.eigenspace L μ) =
      if real then (if μ = 24 ∨ μ = -24 then 1 else if μ = 0 then 18 else 0)
      else (if μ = ((12 * Real.sqrt 2 : ℝ) : ℂ) ∨ μ = -((12 * Real.sqrt 2 : ℝ) : ℂ) then 1
        else if μ = 0 then 16 else 0)) ∧
    ∀ N, N ∉ ({3, 5, 6, 7, 9} : Set ℕ) → ∀ v ∈ sec N, L v = 0
  (∀ P, Edge.IsZeroFluxProj cubeTriplet Edge.bookOrd P →
    claims (Edge.transferVal cubeTriplet Edge.bookOrd P) true) ∧
  (∀ P, Edge.IsZeroFluxProj icoTriplet Edge.bookOrd P →
    claims (Edge.transferVal icoTriplet Edge.bookOrd P) true) ∧
  (∀ P, Edge.IsZeroFluxProj c3a5Triplet Edge.bookOrd P →
    claims (Edge.transferVal c3a5Triplet Edge.bookOrd P) false) ∧
  (∀ P, Edge.IsZeroFluxProj valentinerTriplet Edge.bookOrd P →
    claims (Edge.transferVal valentinerTriplet Edge.bookOrd P) false) ∧
  claims (Matrix.toLin' (Edge.transferWords Edge.bookOrd false)) false ∧
  (∀ ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)),
    (∀ P, Edge.IsZeroFluxProj cubeTriplet ord P →
      table (Edge.zeroFluxValues cubeTriplet ord) (Edge.transferVal cubeTriplet ord P) true) ∧
    (∀ P, Edge.IsZeroFluxProj icoTriplet ord P →
      table (Edge.zeroFluxValues icoTriplet ord) (Edge.transferVal icoTriplet ord P) true) ∧
    (∀ P, Edge.IsZeroFluxProj c3a5Triplet ord P →
      table (Edge.zeroFluxValues c3a5Triplet ord) (Edge.transferVal c3a5Triplet ord P) false) ∧
    (∀ P, Edge.IsZeroFluxProj valentinerTriplet ord P →
      table (Edge.zeroFluxValues valentinerTriplet ord)
        (Edge.transferVal valentinerTriplet ord P) false) ∧
    table (Edge.zeroFluxValues su3Triplet ord) (Matrix.toLin' (Edge.transferWords ord false))
      false) ∧
  ∀ κ : ℝ, κ ≠ 0 → (6 : ℝ) / (κ * (4 / 3)) ^ 2 = 27 / (8 * κ ^ 2)

open Classical in
/-- **Proposition 13.10** (a baryon on a ring and on the cube). One baryon on a ring of four
vertices has, to third order, the levels
`-6/(κ E₃) + 6/(κ E₃)² {2, 0, 0, -2} = -9/(2κ) + {27/(4κ²), 0, 0, -27/(4κ²)}`,
each four times over, once per spin state; on the cube of `ml:cube`, whose vertices have three
neighbours, `-9/(κ E₃) + 6/(κ E₃)² {3, 1, 1, 1, -1, -1, -1, -3}`, each four times over. The braces
hold the eigenvalues of the adjacency matrix of the ring and of the cube.

The energy law to third order is the book's `H_eff = Σ_e (-Ω_e/(κ E₃) + L_e/(κ E₃)²)` on the
canvas (`Canvas.Heff`), with the tally of each edge and its transfer in the form of Theorem 13.8,
as the book's proof computes "the transfer matrices from the words of Theorem 13.8 on every edge";
the pair hop and the mixed words are those of a real triplet (`real = true`) or absent (`false`),
and both are covered. The canvases are the ring of four (`Canvas.ringFour`) and the cube of
Section 13.4 (`Canvas.cube`), with their vertices numbered as given and the modes in the book's
order `6 v + 2 c + s`; every edge points from the lower vertex to the higher. "One baryon and
nothing else" is the span of the baryons `q_v(m)` (`Canvas.oneBaryon`); `H_eff` keeps it, and "the
levels, each four times over" is: every value `μ` has on it the multiplicity `4` times the number
of listed levels equal to `μ`, for all `κ` and `E₃` with `κ E₃ ≠ 0`. The second form of the ring's
levels uses the declared `E₃ = 4/3`. "The eigenvalues of the adjacency matrix": every `λ` has as
eigenvalue of `Canvas.adjacency` the multiplicity of `λ` in the braces. -/
@[book "prop:ml-walk"]
def mlWalk : Prop :=
  let ring := Canvas.ringFour
  let ringOrd := ring.bookOrd (Equiv.refl (Fin 4))
  let cubeOrd := Canvas.cube.bookOrd (Equiv.refl (Fin 8))
  let ringAdj : Fin 4 → ℂ := ![2, 0, 0, -2]
  let cubeAdj : Fin 8 → ℂ := ![3, 1, 1, 1, -1, -1, -1, -3]
  (∀ (κ E₃ : ℝ), κ * E₃ ≠ 0 → ∀ real : Bool,
    (∀ v ∈ ring.oneBaryon ringOrd, ring.Heff ringOrd κ E₃ real *ᵥ v ∈ ring.oneBaryon ringOrd) ∧
    (∀ μ : ℂ, finrank ℂ ↥(ring.oneBaryon ringOrd ⊓
        End.eigenspace (Matrix.toLin' (ring.Heff ringOrd κ E₃ real)) μ) =
      4 * (Finset.univ.filter fun j : Fin 4 =>
        -6 / ((κ * E₃ : ℝ) : ℂ) + 6 / ((κ * E₃ : ℝ) : ℂ) ^ 2 * ringAdj j = μ).card) ∧
    (∀ v ∈ Canvas.cube.oneBaryon cubeOrd,
      Canvas.cube.Heff cubeOrd κ E₃ real *ᵥ v ∈ Canvas.cube.oneBaryon cubeOrd) ∧
    (∀ μ : ℂ, finrank ℂ ↥(Canvas.cube.oneBaryon cubeOrd ⊓
        End.eigenspace (Matrix.toLin' (Canvas.cube.Heff cubeOrd κ E₃ real)) μ) =
      4 * (Finset.univ.filter fun j : Fin 8 =>
        -9 / ((κ * E₃ : ℝ) : ℂ) + 6 / ((κ * E₃ : ℝ) : ℂ) ^ 2 * cubeAdj j = μ).card)) ∧
  (∀ κ : ℝ, κ ≠ 0 → -6 / (κ * (4 / 3)) = -9 / (2 * κ) ∧
    6 / (κ * (4 / 3)) ^ 2 * 2 = 27 / (4 * κ ^ 2)) ∧
  (∀ lam : ℂ, finrank ℂ ↥(End.eigenspace (Matrix.toLin' ring.adjacency) lam) =
    (Finset.univ.filter fun j : Fin 4 => ringAdj j = lam).card) ∧
  ∀ lam : ℂ, finrank ℂ ↥(End.eigenspace (Matrix.toLin' Canvas.cube.adjacency) lam) =
    (Finset.univ.filter fun j : Fin 8 => cubeAdj j = lam).card

end Artform.Statement
