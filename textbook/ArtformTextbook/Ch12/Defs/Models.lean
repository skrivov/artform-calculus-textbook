import ArtformTextbook.Ch11.Defs.Energy
import ArtformTextbook.Ch11.CubeGroup

/-!
# The models of Chapter 12: states, sectors and symmetries of one edge with two slots

The setting is that of `Ch11/Defs/Colourless.lean` with three colours and two slots per colour,
`S = Fin 2`, read as spin: slot `0` is up (`↑`) and slot `1` is down (`↓`) (Section 12.1, "The
two slots, read as spin"). One vertex has the six modes `(c, s)`, and one edge `x → y` the twelve
modes `Edge.Mode (Fin 3) (Fin 2)`, those of `x` on the left.

* **The order of the modes.** The book fixes it where a sign depends on it: "the modes are ordered
  `x` before `y`" (Theorem 13.9), and, within an end, "colour before spin" (exercise
  `ex:13-baryon`); its verifier numbers the mode `(v, c, s)` as `6 v + 2 c + s`. These are
  `Vertex.bookOrd` and `Edge.bookOrd`.
* **The eight states of one vertex** (Figure `fig:mm-two-slot-invariants`), written in creations as
  the figure prints them, in any order `ord` of the six modes: the empty vertex, the pair, the
  four members of the quartet, the paired holes and the full vertex (`Vertex.eight`); the six
  of them that the figure marks as fixed by `SU(3)` are `Vertex.six`.
* **Products.** A table `u` at `x` and a table `w` at `y` give the table `u ⊗ w` of the edge,
  `(u ⊗ w)(n) = u(n_x) w(n_y)` (`Edge.prod`). With the modes of `x` before those of `y`, and each
  end ordered as one vertex, this is the state `U_x W_y |0⟩` in which the operator `U_x` that fills
  `x` acts after the operator `W_y` that fills `y`: a creation at `x` passes no occupied mode of
  `y`. This is the book's "a product fills the ends in the order written", and the product of its
  verifier.
* **The chain** of Figure `fig:mm-chain`, `c₁ = |full_x⟩`, `c₂ = -⅓ H_x D_y`, `c₃ = -⅓ D_x H_y`,
  `c₄ = |full_y⟩`; the spin-singlet two-baryon state `ψ₀` of Theorem 13.9.
* **Operators.** `S_z`, the raising operator `S₊` of Section 12.1 and the total spin
  `S² = S_z² + ½ (S₊ S₋ + S₋ S₊)`; the parity `(-1)^{N_x}`; the hole map `𝒮` of Section 12.2
  ("Why the ground value is shared").
* **The colour groups as triplets** `ρ : G →* Matrix (Fin 3) (Fin 3) ℂ`: the inclusions of the
  icosahedral group, of `C₃ × A₅` (by its triplet), of Valentiner's group and of `SU(3)` itself
  (the cube group's is `cubeTriplet`).
* **Sectors and spectra.** The zero-flux sector of a model read in the Fock space, as the values
  `ψ(1)` of its zero-flux states (they are constant), and an operator `X` on the coefficient tables
  applied at every link value, as a linear map of the states, whose eigenspaces the spectra of
  the chapter count.
-/

namespace Artform

open scoped Matrix ComplexConjugate

/-! ### Slots read as spin -/

namespace Spin

/-- The up slot `↑`. -/
abbrev up : Fin 2 := 0

/-- The down slot `↓`. -/
abbrev down : Fin 2 := 1

end Spin

open Spin

/-! ### The book's order of the modes -/

namespace Vertex

/-- The number of the mode `(c, s)` of one vertex, colour before spin: `2 c + s`. -/
def code (m : Fin 3 × Fin 2) : ℕ := 2 * (m.1 : ℕ) + m.2

theorem code_injective : Function.Injective code := by
  rintro ⟨c, s⟩ ⟨c', s'⟩ h
  simp only [code] at h
  have hs := s.2
  have hs' := s'.2
  have hc : (c : ℕ) = c' := by omega
  have hs'' : (s : ℕ) = s' := by omega
  exact Prod.ext (Fin.ext hc) (Fin.ext hs'')

/-- The book's order of the six modes of one vertex: colour before spin, up before down
(exercise `ex:13-baryon`; the verifier's `2 c + s`). -/
@[instance_reducible]
def bookOrd : LinearOrder (Fin 3 × Fin 2) := LinearOrder.lift' code code_injective

end Vertex

namespace Edge

/-- The number of a mode of one edge, `x` before `y` and colour before spin: `2 c + s` at `x` and
`6 + 2 c + s` at `y`. -/
def code : Mode (Fin 3) (Fin 2) → ℕ := Sum.elim Vertex.code fun m => 6 + Vertex.code m

theorem code_injective : Function.Injective code := by
  have hlt : ∀ m, Vertex.code m < 6 := by
    rintro ⟨c, s⟩
    have := c.2
    have := s.2
    simp only [Vertex.code]
    omega
  rintro (a | a) (b | b) h <;> simp only [code, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Vertex.code_injective h]
  · have := hlt a
    omega
  · have := hlt b
    omega
  · rw [Vertex.code_injective (by omega : Vertex.code a = Vertex.code b)]

/-- The book's order of the twelve modes of one edge: the modes of `x` before those of `y`
(Theorem 13.9), and within an end colour before spin, up before down (exercise `ex:13-baryon`;
the verifier's `6 v + 2 c + s`). -/
@[instance_reducible]
def bookOrd : LinearOrder (Mode (Fin 3) (Fin 2)) := LinearOrder.lift' code code_injective

end Edge

/-! ### The eight states of one vertex (Figure `fig:mm-two-slot-invariants`) -/

noncomputable section

namespace Vertex

variable (ord : LinearOrder (Fin 3 × Fin 2))

/-- The empty vertex `|0⟩`. -/
def empty : Finset (Fin 3 × Fin 2) → ℂ := Fock.ket ∅

/-- The full vertex `|full⟩`: every mode occupied. -/
def full : Finset (Fin 3 × Fin 2) → ℂ := Fock.ket Finset.univ

/-- The pair, spins opposed: `Σ_c a†_{c↑} a†_{c↓} |0⟩`. -/
def pair : Finset (Fin 3 × Fin 2) → ℂ :=
  ∑ c : Fin 3, (Fock.creation ord (c, up) * Fock.creation ord (c, down)) *ᵥ Fock.ket ∅

/-- `Σ_{abc} ε_{abc} a†_{a s₁} a†_{b s₂} a†_{c s₃} |0⟩`, the three colours combined with the
Levi-Civita symbol in the slots `s₁, s₂, s₃`. -/
def epsState (s₁ s₂ s₃ : Fin 2) : Finset (Fin 3 × Fin 2) → ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, leviCivita a b c •
    ((Fock.creation ord (a, s₁) * Fock.creation ord (b, s₂) * Fock.creation ord (c, s₃)) *ᵥ
      Fock.ket ∅)

/-- The four members of the quartet, by `S_z = 3/2 - m` for `m = 0, 1, 2, 3`, as the figure
writes them: `a†_{1↑} a†_{2↑} a†_{3↑} |0⟩`, `½ Σ_{abc} ε_{abc} a†_{a↑} a†_{b↑} a†_{c↓} |0⟩`,
`½ Σ_{abc} ε_{abc} a†_{a↑} a†_{b↓} a†_{c↓} |0⟩` and `a†_{1↓} a†_{2↓} a†_{3↓} |0⟩` (the colours
`1, 2, 3` of the book are `0, 1, 2` here). -/
def quartet : Fin 4 → Finset (Fin 3 × Fin 2) → ℂ :=
  ![(Fock.creation ord (0, up) * Fock.creation ord (1, up) * Fock.creation ord (2, up)) *ᵥ
      Fock.ket ∅,
    (1 / 2 : ℂ) • epsState ord up up down,
    (1 / 2 : ℂ) • epsState ord up down down,
    (Fock.creation ord (0, down) * Fock.creation ord (1, down) * Fock.creation ord (2, down)) *ᵥ
      Fock.ket ∅]

/-- The two holes paired: `Σ_c a_{c↑} a_{c↓} |full⟩`. -/
def holes : Finset (Fin 3 × Fin 2) → ℂ :=
  ∑ c : Fin 3, (Fock.annihilation ord (c, up) * Fock.annihilation ord (c, down)) *ᵥ full

/-- The eight states of Figure `fig:mm-two-slot-invariants`, in its order: the empty vertex, the
pair, the quartet with `S_z = 3/2, 1/2, -1/2, -3/2`, the paired holes and the full vertex. -/
def eight : Fin 8 → Finset (Fin 3 × Fin 2) → ℂ :=
  ![empty, pair ord, quartet ord 0, quartet ord 1, quartet ord 2, quartet ord 3, holes ord, full]

/-- The six of the eight that the figure marks as fixed by `SU(3)`: all but the pair and the
paired holes. -/
def six : Fin 6 → Finset (Fin 3 × Fin 2) → ℂ :=
  ![empty, quartet ord 0, quartet ord 1, quartet ord 2, quartet ord 3, full]

end Vertex

/-! ### Norms -/

namespace Fock

variable {M : Type*} [Fintype M]

/-- The norm of a coefficient table for the pairing of `qr:hilbert`,
`‖v‖ = (Σ_n |v(n)|²)^{1/2}` (not the largest size of a coefficient, which is Lean's norm on
functions). -/
noncomputable def hilbertNorm (v : Finset M → ℂ) : ℝ := Real.sqrt (∑ n, ‖v n‖ ^ 2)

/-- The table `v` scaled to unit norm, `v / ‖v‖`. -/
noncomputable def normalized (v : Finset M → ℂ) : Finset M → ℂ :=
  ((hilbertNorm v : ℝ) : ℂ)⁻¹ • v

end Fock

/-! ### States of one edge -/

namespace Edge

/-- The product `u ⊗ w` of a table `u` at `x` and a table `w` at `y`:
`(u ⊗ w)(n) = u(n_x) w(n_y)`. With the modes of `x` before those of `y` (`bookOrd`) and each end
ordered as one vertex (`Vertex.bookOrd`), it is the state `U_x W_y |0⟩` for `u = U |0⟩` and
`w = W |0⟩`: "a product fills the ends in the order written". -/
def prod {C S : Type*} (u w : Finset (C × S) → ℂ) : Finset (Mode C S) → ℂ :=
  fun n => u n.toLeft * w n.toRight

/-- The pair at `x`, `D_x`. -/
def pairX : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod (Vertex.pair Vertex.bookOrd) Vertex.empty

/-- The pair at `y`, `D_y`. -/
def pairY : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod Vertex.empty (Vertex.pair Vertex.bookOrd)

/-- The paired holes at `x` with `y` empty, `H_x`. -/
def holesX : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod (Vertex.holes Vertex.bookOrd) Vertex.empty

/-- The paired holes at `y` with `x` empty, `H_y`. -/
def holesY : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod Vertex.empty (Vertex.holes Vertex.bookOrd)

/-- The full vertex at `x`, `|full_x⟩`, with `y` empty. -/
def fullX : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod Vertex.full Vertex.empty

/-- The full vertex at `y`, `|full_y⟩`, with `x` empty. -/
def fullY : Finset (Mode (Fin 3) (Fin 2)) → ℂ := prod Vertex.empty Vertex.full

/-- The member `m` of the quartet at `x`, `q_x(m)`, `S_z = 3/2 - m`, with `y` empty. -/
def quartetX (m : Fin 4) : Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  prod (Vertex.quartet Vertex.bookOrd m) Vertex.empty

/-- The member `m` of the quartet at `y`, `q_y(m)`, `S_z = 3/2 - m`, with `x` empty. -/
def quartetY (m : Fin 4) : Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  prod Vertex.empty (Vertex.quartet Vertex.bookOrd m)

/-- The products of the eight states of one vertex at `x` and at `y`, indexed by the pair of
their places in Figure `fig:mm-two-slot-invariants`. -/
def eightProd (i : Fin 8 × Fin 8) : Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  prod (Vertex.eight Vertex.bookOrd i.1) (Vertex.eight Vertex.bookOrd i.2)

/-- The products of the six `SU(3)`-fixed states at `x` and at `y`. -/
def sixProd (i : Fin 6 × Fin 6) : Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  prod (Vertex.six Vertex.bookOrd i.1) (Vertex.six Vertex.bookOrd i.2)

/-- The chain of pairs at six quarks (Figure `fig:mm-chain`), with unit norm:
`c₁ = |full_x⟩`, `c₂ = -⅓ H_x D_y`, `c₃ = -⅓ D_x H_y`, `c₄ = |full_y⟩`, where `H_x D_y` is the
product of the paired holes at `x` and the pair at `y`. -/
def chain : Fin 4 → Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  ![fullX, (-1 / 3 : ℂ) • prod (Vertex.holes Vertex.bookOrd) (Vertex.pair Vertex.bookOrd),
    (-1 / 3 : ℂ) • prod (Vertex.pair Vertex.bookOrd) (Vertex.holes Vertex.bookOrd), fullY]

/-- The uniform vector `½ (c₁ + c₂ + c₃ + c₄)` on the chain, the second ground state. -/
def chainGround : Finset (Mode (Fin 3) (Fin 2)) → ℂ := (1 / 2 : ℂ) • ∑ i, chain i

/-- The spin-singlet two-baryon state of Theorem 13.9,
`ψ₀ = ½ Σ_m (-1)^{3/2 - m} q̂_x(m) q̂_y(-m)`, with `q̂` the normalized quartet members: the member
of index `i` has `S_z = 3/2 - i`, and `-m` is the member of index `3 - i`. -/
noncomputable def singlet : Finset (Mode (Fin 3) (Fin 2)) → ℂ :=
  (1 / 2 : ℂ) • ∑ i : Fin 4, ((-1 : ℂ) ^ (i : ℕ)) •
    prod (Fock.normalized (Vertex.quartet Vertex.bookOrd i))
      (Fock.normalized (Vertex.quartet Vertex.bookOrd (Fin.rev i)))

/-! ### Operators on the occupations of one edge -/

/-- The slot (spin) of a mode of the edge. -/
def spinOf {C : Type*} : Mode C (Fin 2) → Fin 2 := Sum.elim Prod.snd Prod.snd

/-- `S_z = ½ Σ (n_{c↑} - n_{c↓})`, summed over the colours of both ends: half the number of up
quarks minus half the number of down quarks, a diagonal operator. -/
noncomputable def spinZ :
    Matrix (Finset (Mode (Fin 3) (Fin 2))) (Finset (Mode (Fin 3) (Fin 2))) ℂ :=
  Matrix.diagonal fun n =>
    (((n.filter fun m => spinOf m = up).card : ℂ) - (n.filter fun m => spinOf m = down).card) / 2

/-- The total raising operator of Section 12.1, `S₊ = Σ_{v,c} a†_{vc↑} a_{vc↓}`, over both ends of
the edge. -/
noncomputable def spinPlus (ord : LinearOrder (Mode (Fin 3) (Fin 2))) :
    Matrix (Finset (Mode (Fin 3) (Fin 2))) (Finset (Mode (Fin 3) (Fin 2))) ℂ :=
  ∑ c : Fin 3, (Fock.creation ord (Sum.inl (c, up)) * Fock.annihilation ord (Sum.inl (c, down)) +
    Fock.creation ord (Sum.inr (c, up)) * Fock.annihilation ord (Sum.inr (c, down)))

/-- The total spin `S² = S_z² + ½ (S₊ S₋ + S₋ S₊)`, `S₋ = S₊†`; a state of spin `S` is one with
`S² ψ = S (S + 1) ψ`. -/
noncomputable def spinSq (ord : LinearOrder (Mode (Fin 3) (Fin 2))) :
    Matrix (Finset (Mode (Fin 3) (Fin 2))) (Finset (Mode (Fin 3) (Fin 2))) ℂ :=
  spinZ * spinZ + (1 / 2 : ℂ) •
    (spinPlus ord * (spinPlus ord)ᴴ + (spinPlus ord)ᴴ * spinPlus ord)

/-- The parity `(-1)^{N_x}` of the number of quarks at `x`, a diagonal operator. -/
noncomputable def parityX :
    Matrix (Finset (Mode (Fin 3) (Fin 2))) (Finset (Mode (Fin 3) (Fin 2))) ℂ :=
  Matrix.diagonal fun n => (-1 : ℂ) ^ n.toLeft.card

/-- The hole map `𝒮` of Section 12.2 ("Why the ground value is shared"), which turns up quarks
into holes and holes into up quarks, with a sign at `y`, and leaves the down quarks alone:
`a_{xc↑} ↦ a†_{xc↑}`, `a_{yc↑} ↦ -a†_{yc↑}`. It is the operator of the book's verifier: apply
`a_{xc↑} + a†_{xc↑}` for `c = 1, 2, 3`, then `a_{yc↑} - a†_{yc↑}` for `c = 1, 2, 3`, then multiply
by `(-1)` to the number of up quarks. -/
noncomputable def holeMap (ord : LinearOrder (Mode (Fin 3) (Fin 2))) :
    Matrix (Finset (Mode (Fin 3) (Fin 2))) (Finset (Mode (Fin 3) (Fin 2))) ℂ :=
  Matrix.diagonal (fun n => (-1 : ℂ) ^ (n.filter fun m => spinOf m = up).card) *
    ((Fock.annihilation ord (Sum.inr (2, up)) - Fock.creation ord (Sum.inr (2, up))) *
      (Fock.annihilation ord (Sum.inr (1, up)) - Fock.creation ord (Sum.inr (1, up))) *
      (Fock.annihilation ord (Sum.inr (0, up)) - Fock.creation ord (Sum.inr (0, up)))) *
    ((Fock.annihilation ord (Sum.inl (2, up)) + Fock.creation ord (Sum.inl (2, up))) *
      (Fock.annihilation ord (Sum.inl (1, up)) + Fock.creation ord (Sum.inl (1, up))) *
      (Fock.annihilation ord (Sum.inl (0, up)) + Fock.creation ord (Sum.inl (0, up))))

/-! ### Sectors and eigenspaces -/

variable {G : Type*} [Group G] {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S]
  [DecidableEq S]

/-- The zero-flux sector read in the space of coefficient tables: the values `ψ(1)` of the
zero-flux states, which are constant in the link value. -/
noncomputable def zeroFluxValues (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    Submodule ℂ (Finset (Mode C S) → ℂ) :=
  (zeroFlux ρ ord).map (LinearMap.proj (1 : G))

/-- The multiplicity of the value `μ` of an operator `X` on the zero-flux sector of the model
`ρ`: the dimension of the zero-flux values `v` with `X v = μ v`. When `X` keeps the sector, these
are the multiplicities of the eigenvalues of `X` restricted to it. -/
noncomputable def sectorMult (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (X : Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ) (μ : ℂ) : ℕ :=
  Module.finrank ℂ ↥(zeroFluxValues ρ ord ⊓ Module.End.eigenspace (Matrix.toLin' X) μ)

/-- An operator `X` on the coefficient tables applied at every link value, `(X ψ)(U) = X ψ(U)`
(`atEachLink`), as a linear map of the states. -/
noncomputable def atEachLinkLin (X : Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ) :
    Module.End ℂ (G → Finset (Mode C S) → ℂ) where
  toFun ψ := atEachLink X ψ
  map_add' ψ φ := by
    funext U
    simp only [atEachLink, Pi.add_apply, Matrix.mulVec_add]
  map_smul' c ψ := by
    funext U
    simp only [atEachLink, Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]

end Edge

end

/-! ### The colour groups as triplets -/

/-- The triplet `3` of Model II, the icosahedral group: each rotation acts on the colours by its
matrix. -/
noncomputable def icoTriplet : icoGroup →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp icoGroup.subtype

/-- The triplet of Refinement I, `(ω^j, g) ↦ ω^j g` (Definition 12.11), as matrices. -/
noncomputable def c3a5Triplet : C3A5 →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp C3A5.triplet

/-- The triplet of Refinement II, Valentiner's group: each element acts by its matrix. -/
noncomputable def valentinerTriplet : valentiner →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp valentiner.subtype

/-- The `SU(3)` reference: every matrix of `SU(3)` acts on the colours by itself. -/
noncomputable def su3Triplet : Matrix.specialUnitaryGroup (Fin 3) ℂ →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype

end Artform
