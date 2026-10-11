import Mathlib.Data.Finset.Sum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.RepresentationTheory.Basic
import ArtformTextbook.Ch11.Defs.Occupation
import ArtformTextbook.Ch11.Defs.Tables

/-!
# Colourless states of one edge (Section 11.5)

One oriented edge `x → y` carries a link value `U` in a group `G`, and its two ends carry
quarks. The colour group acts on one quark by the triplet, here a homomorphism
`ρ : G →* Matrix C C ℂ` into the `C × C` matrices (the book's colour groups are subgroups of
`SU(3)`, with `C = Fin 3` and `ρ` the inclusion); a link value `U` acts on a quark by the matrix
`ρ(U)`, with entries `U_{cc'} = ρ(U)_{cc'}`.

* **Modes.** A mode of the edge is a colour `c ∈ C` and a slot `s ∈ S` at `x` or at `y`:
  `Edge.Mode C S = (C × S) ⊕ (C × S)`, `x` on the left. With `|S| = d` and three colours the
  edge has `6d` modes. An occupation table is a finite set of occupied modes, and the
  coefficient tables over the occupation tables are the functions `Finset (Mode C S) → ℂ`
  (Section 11.4, `Ch11/Defs/Occupation.lean`); `n.toLeft` and `n.toRight` are the occupied modes
  at `x` and at `y`.
* **States.** A state of the edge is a coefficient table over the link values and the
  occupation tables of both ends, a function `ψ : G → Finset (Mode C S) → ℂ`, one coefficient
  for each `(U, n_x, n_y)`.
* **Colour rotations at the ends.** `Γ_x(g)` is the second quantization (`Fock.secondQuant`) of
  the one-quark matrix `diag(g, 1) ⊗ 1_d`, which transforms every creation at `x` by `g` and
  leaves the creations at `y` alone; `Γ_y(g)` is that of `diag(1, g) ⊗ 1_d`. Both depend on the
  chosen order of the `6d` modes, which Proposition 11.11 shows to be a presentation.
* **The gauge action.** The gauge group `G × G` acts on the link by `U ↦ h_y U h_x⁻¹`
  (`eq:gauge-action`) and on the matter by `Γ_x(h_x) Γ_y(h_y)`; the moved state assigns to the
  moved link the transformed matter (`Edge.gaugeAct`).
-/

namespace Artform

namespace Edge

open scoped Matrix ComplexConjugate

/-- The modes of one edge `x → y` with colours `C` and slots `S`: a pair `(c, s)` at `x`
(`Sum.inl`) or at `y` (`Sum.inr`). -/
abbrev Mode (C S : Type*) : Type _ := (C × S) ⊕ (C × S)

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The one-quark matrix `diag(g_x, g_y) ⊗ 1_d` on the modes of the edge: `g_x` on the colours at
`x`, `g_y` on the colours at `y`, the identity on the slots. -/
def diag (gx gy : Matrix C C ℂ) : Matrix (Mode C S) (Mode C S) ℂ :=
  Matrix.fromBlocks (Matrix.kroneckerMap (· * ·) gx (1 : Matrix S S ℂ)) 0 0
    (Matrix.kroneckerMap (· * ·) gy (1 : Matrix S S ℂ))

/-- `Γ_x(g)`: the colour rotation `g` at the end `x`, the second quantization of
`diag(g, 1) ⊗ 1_d` in the chosen order `ord` of the modes. -/
noncomputable def gammaX (ord : LinearOrder (Mode C S)) (g : Matrix C C ℂ) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  Fock.secondQuant ord (diag g 1)

/-- `Γ_y(g)`: the colour rotation `g` at the end `y`, the second quantization of
`diag(1, g) ⊗ 1_d` in the chosen order `ord` of the modes. -/
noncomputable def gammaY (ord : LinearOrder (Mode C S)) (g : Matrix C C ℂ) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  Fock.secondQuant ord (diag 1 g)

variable {G : Type*} [Group G]

/-- The gauge action of `(h_x, h_y) ∈ G × G` on a state of the edge, on the link and the matter
together: the link moves by `U ↦ h_y U h_x⁻¹` and the matter by `Γ_x(h_x) Γ_y(h_y)`, so the
moved state assigns to the moved link `h_y U h_x⁻¹` the transformed matter of `U`:
`(h · ψ)(U) = Γ_x(h_x) Γ_y(h_y) ψ(h_y⁻¹ U h_x)`. -/
noncomputable def gaugeAct (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (hx hy : G)
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  fun U => (gammaX ord (ρ hx) * gammaY ord (ρ hy)) *ᵥ ψ (hy⁻¹ * U * hx)

/-- **Definition 11.13** (colourless states of one edge). A state `ψ` is colourless when every
gauge pair fixes it,
`ψ(h_y U h_x⁻¹) = Γ_x(h_x) Γ_y(h_y) ψ(U)` for all `h_x`, `h_y`, `U`.
The colourless states form a subspace of the states. -/
@[book "def:mt-colourless"]
noncomputable def colourless (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    Submodule ℂ (G → Finset (Mode C S) → ℂ) where
  carrier := {ψ | ∀ hx hy U, ψ (hy * U * hx⁻¹) = (gammaX ord (ρ hx) * gammaY ord (ρ hy)) *ᵥ ψ U}
  add_mem' {ψ φ} hψ hφ hx hy U := by
    simp only [Set.mem_ofPred_eq] at hψ hφ
    simp only [Pi.add_apply, hψ, hφ, Matrix.mulVec_add]
  zero_mem' hx hy U := by simp
  smul_mem' c ψ hψ hx hy U := by
    simp only [Set.mem_ofPred_eq] at hψ
    simp only [Pi.smul_apply, hψ, Matrix.mulVec_smul]

/-- **Definition 11.13** (the zero-flux sector). A state lies in the zero-flux sector when it is
colourless and, in addition, constant in `U`: the link's table lies in the trivial block. -/
@[book "def:mt-colourless"]
noncomputable def zeroFlux (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    Submodule ℂ (G → Finset (Mode C S) → ℂ) where
  carrier := {ψ | ψ ∈ colourless ρ ord ∧ ∀ U V, ψ U = ψ V}
  add_mem' {ψ φ} hψ hφ := ⟨(colourless ρ ord).add_mem hψ.1 hφ.1, fun U V => by
    simp only [Pi.add_apply, hψ.2 U V, hφ.2 U V]⟩
  zero_mem' := ⟨(colourless ρ ord).zero_mem, fun _ _ => rfl⟩
  smul_mem' c ψ hψ := ⟨(colourless ρ ord).smul_mem c hψ.1, fun U V => by
    simp only [Pi.smul_apply, hψ.2 U V]⟩

/-- The invariant occupation tables of one vertex with colours `C` and slots `S`: the
coefficient tables fixed by the colour rotation `Γ(ρ(h))` of every `h ∈ G`
(`Fock.vertexGamma`, Proposition 11.12), in the chosen order `ord` of the vertex modes. -/
noncomputable def vertexInvariants (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (C × S)) :
    Submodule ℂ (Finset (C × S) → ℂ) where
  carrier := {v | ∀ h, Fock.vertexGamma ord (ρ h) *ᵥ v = v}
  add_mem' {v w} hv hw h := by
    simp only [Set.mem_ofPred_eq] at hv hw
    rw [Matrix.mulVec_add, hv, hw]
  zero_mem' h := Matrix.mulVec_zero _
  smul_mem' c v hv h := by
    simp only [Set.mem_ofPred_eq] at hv
    rw [Matrix.mulVec_smul, hv]

end Edge

namespace Fock

variable {M : Type*}

/-- The coefficient tables with exactly `k` quarks: those whose coefficients vanish on every
occupation table with a number of occupied modes other than `k`. -/
def numberSector (M : Type*) (k : ℕ) : Submodule ℂ (Finset M → ℂ) where
  carrier := {v | ∀ n, v n ≠ 0 → n.card = k}
  add_mem' {v w} hv hw n hn := by
    by_cases h : v n = 0
    · exact hw n (by simpa [h] using hn)
    · exact hv n h
  zero_mem' n hn := absurd rfl hn
  smul_mem' c v hv n hn := hv n (right_ne_zero_of_mul hn)

end Fock

namespace Edge

variable {C S : Type*}

/-- The coefficient tables of one edge with exactly `k_x` quarks at `x` and `k_y` at `y`. -/
def endSector (C S : Type*) (kx ky : ℕ) : Submodule ℂ (Finset (Mode C S) → ℂ) where
  carrier := {v | ∀ n, v n ≠ 0 → n.toLeft.card = kx ∧ n.toRight.card = ky}
  add_mem' {v w} hv hw n hn := by
    by_cases h : v n = 0
    · exact hw n (by simpa [h] using hn)
    · exact hv n h
  zero_mem' n hn := absurd rfl hn
  smul_mem' c v hv n hn := hv n (right_ne_zero_of_mul hn)

/-- The states of the edge whose every coefficient table `ψ(U)` lies in the subspace `Z` of
coefficient tables over the occupations (for example, the tables with `k` quarks). -/
def stateSector (G : Type*) {M : Type*} (Z : Submodule ℂ (Finset M → ℂ)) :
    Submodule ℂ (G → Finset M → ℂ) :=
  Submodule.pi Set.univ fun _ => Z

/-- The pairing of two states of the edge, the pairing of `qr:hilbert` on coefficient tables
over the pairs `(U, n)`: `⟨ψ, φ⟩ = Σ_U Σ_n conj(ψ(U)(n)) φ(U)(n)`. -/
def statePairing {G : Type*} [Fintype G] {M : Type*} [Fintype M]
    (ψ φ : G → Finset M → ℂ) : ℂ :=
  ∑ U, coeffPairing (ψ U) (φ U)

variable {G : Type*} [Group G] [Fintype C] [DecidableEq C]

/-- The triplet as a representation of `G` on the colour space `C → ℂ`: `U` acts by the matrix
`ρ(U)`. -/
noncomputable def tripletRep (ρ : G →* Matrix C C ℂ) : Representation ℂ G (C → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix C C ℂ ≃ₐ[ℂ] Module.End ℂ (C → ℂ)).toMonoidHom.comp ρ

/-- The conjugate triplet, a representation of `G` on `C → ℂ`: `U` acts by the complex conjugate
matrix of `ρ(U)`, whose entries are `conj(U_{cc'})`. -/
noncomputable def conjTripletRep (ρ : G →* Matrix C C ℂ) : Representation ℂ G (C → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix C C ℂ ≃ₐ[ℂ] Module.End ℂ (C → ℂ)).toMonoidHom.comp
    ((RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp ρ)

end Edge

end Artform
