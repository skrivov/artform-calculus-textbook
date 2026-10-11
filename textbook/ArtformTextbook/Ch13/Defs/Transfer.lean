import ArtformTextbook.Ch12.Defs.Models
import ArtformTextbook.Ch13.Defs.Census

/-!
# The third-order transfer (Section 13.3)

* **The words of Theorem 13.8.** For hops `A_{cc'}` from colour `c'` at one end to colour `c` at
  the other, `L = (1/6) Σ_{c, c'} sgn(c) sgn(c') A_{c₃c'₃} A_{c₂c'₂} A_{c₁c'₁} + h.c.` for a
  complex triplet, the sum over the orderings `c` and `c'` of the colours; for a real triplet the
  same weight multiplies each of the eight words in which every factor is `A` or `A†`
  (`transferOf`). A sum over the orderings with the sign of each is a sum over all triples of
  colours weighted by the Levi-Civita symbol. The tally of Theorem 11.20 is written the same way
  (`tallyOf`).
* **`L = P V³ P` on one edge.** For a finite colour group and a projector `P` of the states onto
  the zero-flux sector, whose states are constant in the link value, `L` is read on the
  coefficient tables: the value at the identity link of `P V³ P` applied to the constant state
  (`Edge.transferVal`).
* **A canvas** (Section 13.3, "A baryon on a ring"). The modes of a canvas are those of
  `Canvas.Mode`, a colour and a slot (spin) at a vertex, ordered vertex first and then colour
  before spin (`Canvas.bookOrd`, the book's `6 v + 2 c + s`). Each edge hops from its source to its
  target (`Canvas.hopA`); its tally and its transfer are those of one edge, and the energy law to
  third order is `H_eff = Σ_e (-Ω_e/(κ E₃) + L_e/(κ E₃)²)` (`Canvas.Heff`). A baryon at a vertex is
  a member of the quartet of Figure `fig:mm-two-slot-invariants` there, every other vertex empty
  (`Canvas.baryon`). The ring of four is `Canvas.ringFour`.
-/

namespace Artform

open scoped Matrix

noncomputable section

/-! ### Words in the hops -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The tally of Theorem 11.20 in hops `A_{cc'}`:
`(1/3) Σ_{c,c'} (A†_{cc'} A_{cc'} + A_{cc'} A†_{cc'})
  + (m/3) Σ_{c,c'} (A_{cc'} A_{cc'} + A†_{cc'} A†_{cc'})`. -/
def tallyOf (A : Fin 3 → Fin 3 → Matrix N N ℂ) (m : ℕ) : Matrix N N ℂ :=
  (1 / 3 : ℂ) • (∑ c, ∑ c', ((A c c')ᴴ * A c c' + A c c' * (A c c')ᴴ)) +
    ((m : ℂ) / 3) • (∑ c, ∑ c', (A c c' * A c c' + (A c c')ᴴ * (A c c')ᴴ))

/-- The words of Theorem 13.8 in hops `A_{cc'}`. For a complex triplet (`real = false`),
`L = W + W†` with `W = (1/6) Σ ε_{c₁c₂c₃} ε_{c'₁c'₂c'₃} A_{c₃c'₃} A_{c₂c'₂} A_{c₁c'₁}`; for a real
triplet (`real = true`) the weight `ε ε / 6` multiplies each of the eight words in which every
factor is `A` or `A†`, `(1/6) Σ ε ε (A + A†)_{c₃c'₃} (A + A†)_{c₂c'₂} (A + A†)_{c₁c'₁}`. -/
def transferOf (A : Fin 3 → Fin 3 → Matrix N N ℂ) (real : Bool) : Matrix N N ℂ :=
  if real then
    (1 / 6 : ℂ) • ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
      (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
        ((A c₃ c₃' + (A c₃ c₃')ᴴ) * (A c₂ c₂' + (A c₂ c₂')ᴴ) * (A c₁ c₁' + (A c₁ c₁')ᴴ))
  else
    (1 / 6 : ℂ) • (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
      (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') • (A c₃ c₃' * A c₂ c₂' * A c₁ c₁')) +
    ((1 / 6 : ℂ) • (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
      (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') • (A c₃ c₃' * A c₂ c₂' * A c₁ c₁')))ᴴ

namespace Edge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The words of Theorem 13.8 on one edge, with `A_{cc'} = Σ_s a†_{ycs} a_{xc's}`. -/
def transferWords (ord : LinearOrder (Mode (Fin 3) S)) (real : Bool) :
    Matrix (Finset (Mode (Fin 3) S)) (Finset (Mode (Fin 3) S)) ℂ :=
  transferOf (hopA ord) real

/-- The third-order term `L = P V³ P` of Theorem 13.8 for a finite colour group and a projector
`P` of the states, read on the coefficient tables: the value at the identity link of
`P V³ P` applied to the constant state with value `v`. -/
def transferVal {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S))
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ)) :
    Module.End ℂ (Finset (Mode (Fin 3) S) → ℂ) where
  toFun v := P (hop ρ ord (hop ρ ord (hop ρ ord (P fun _ => v)))) 1
  map_add' v w := by
    have hadd : ∀ ψ φ : G → Finset (Mode (Fin 3) S) → ℂ,
        hop ρ ord (ψ + φ) = hop ρ ord ψ + hop ρ ord φ := fun ψ φ => by
      funext U
      simp only [hop, Pi.add_apply, Matrix.mulVec_add]
    have hc : (fun _ : G => v + w) = (fun _ => v) + fun _ => w := rfl
    rw [hc, map_add, hadd, hadd, hadd, map_add]
    rfl
  map_smul' c v := by
    have hsmul : ∀ ψ : G → Finset (Mode (Fin 3) S) → ℂ,
        hop ρ ord (c • ψ) = c • hop ρ ord ψ := fun ψ => by
      funext U
      simp only [hop, Pi.smul_apply, Matrix.mulVec_smul]
    have hc : (fun _ : G => c • v) = c • fun _ => v := rfl
    rw [hc, map_smul, hsmul, hsmul, hsmul, map_smul]
    rfl

/-- `P` is an orthogonal projector onto the zero-flux sector, as in Theorem 11.20: its values lie in
the sector, it fixes the sector, and it is self-adjoint for the pairing of states. -/
def IsZeroFluxProj {G : Type*} [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S))
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ)) : Prop :=
  (∀ ψ, P ψ ∈ zeroFlux ρ ord) ∧ (∀ ψ ∈ zeroFlux ρ ord, P ψ = ψ) ∧
    ∀ ψ φ, statePairing (P ψ) φ = statePairing ψ (P φ)

end Edge

/-! ### Canvases -/

namespace Canvas

variable (K : Canvas)

/-- The number of a mode `((c, s), v)` of a canvas whose vertices are numbered: the book's
`6 v + 2 c + s`, vertex first, then colour before spin. -/
def code {n : ℕ} (e : K.V ≃ Fin n) (m : K.Mode (Fin 3) (Fin 2)) : ℕ :=
  6 * (e m.2 : ℕ) + 2 * (m.1.1 : ℕ) + m.1.2

theorem code_injective {n : ℕ} (e : K.V ≃ Fin n) : Function.Injective (K.code e) := by
  rintro ⟨⟨c, s⟩, v⟩ ⟨⟨c', s'⟩, v'⟩ h
  simp only [code] at h
  have hc := c.2
  have hc' := c'.2
  have hs := s.2
  have hs' := s'.2
  have hv : (e v : ℕ) = e v' := by omega
  have hcc : (c : ℕ) = c' := by omega
  have hss : (s : ℕ) = s' := by omega
  rw [Fin.ext hcc, Fin.ext hss, e.injective (Fin.ext hv)]

/-- The book's order of the modes of a canvas with numbered vertices: `6 v + 2 c + s`. -/
@[instance_reducible]
def bookOrd {n : ℕ} (e : K.V ≃ Fin n) : LinearOrder (K.Mode (Fin 3) (Fin 2)) :=
  LinearOrder.lift' (K.code e) (K.code_injective e)

/-- `A^e_{cc'} = Σ_s a†_{t(e)cs} a_{s(e)c's}`: the hop of one quark along the edge `e`, from colour
`c'` at its source to colour `c` at its target. -/
def hopA (ord : LinearOrder (K.Mode (Fin 3) (Fin 2))) (e : K.E) (c c' : Fin 3) :
    Matrix (Finset (K.Mode (Fin 3) (Fin 2))) (Finset (K.Mode (Fin 3) (Fin 2))) ℂ :=
  ∑ s, Fock.creation ord ((c, s), K.tgt e) * Fock.annihilation ord ((c', s), K.src e)

/-- The energy law to third order on a canvas (Section 13.3):
`H_eff = Σ_e (-Ω_e/(κ E₃) + L_e/(κ E₃)²)`, with the tally `Ω_e` (pair hop `m = 1` for a real
triplet, `m = 0` otherwise) and the transfer `L_e` of each edge. -/
def Heff (ord : LinearOrder (K.Mode (Fin 3) (Fin 2))) (κ E₃ : ℝ) (real : Bool) :
    Matrix (Finset (K.Mode (Fin 3) (Fin 2))) (Finset (K.Mode (Fin 3) (Fin 2))) ℂ :=
  ∑ e, (-(((κ * E₃ : ℝ) : ℂ)⁻¹) • tallyOf (K.hopA ord e) (if real then 1 else 0) +
    (((κ * E₃ : ℝ) : ℂ) ^ 2)⁻¹ • transferOf (K.hopA ord e) real)

/-- The baryon at the vertex `v`: the member `m` of the quartet of Figure
`fig:mm-two-slot-invariants` (`S_z = 3/2 - m`) at `v`, written in creations as the figure writes
it, every other vertex empty. -/
def baryon (ord : LinearOrder (K.Mode (Fin 3) (Fin 2))) (v : K.V) (m : Fin 4) :
    Finset (K.Mode (Fin 3) (Fin 2)) → ℂ :=
  let a := fun (c : Fin 3) (s : Fin 2) => Fock.creation ord ((c, s), v)
  let eps := fun (s₁ s₂ s₃ : Fin 2) => ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, leviCivita x y z •
    ((a x s₁ * a y s₂ * a z s₃) *ᵥ Fock.ket ∅)
  ![(a 0 0 * a 1 0 * a 2 0) *ᵥ Fock.ket ∅, (1 / 2 : ℂ) • eps 0 0 1, (1 / 2 : ℂ) • eps 0 1 1,
    (a 0 1 * a 1 1 * a 2 1) *ᵥ Fock.ket ∅] m

/-- The states with one baryon on the canvas and nothing else: the span of the baryons at the
vertices. -/
def oneBaryon (ord : LinearOrder (K.Mode (Fin 3) (Fin 2))) :
    Submodule ℂ (Finset (K.Mode (Fin 3) (Fin 2)) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : K.V × Fin 4 => K.baryon ord p.1 p.2)

/-- The adjacency matrix of a canvas: the number of edges between two vertices. -/
def adjacency : Matrix K.V K.V ℂ :=
  Matrix.of fun v w => ((Finset.univ.filter fun e : K.E =>
    (K.src e = v ∧ K.tgt e = w) ∨ (K.src e = w ∧ K.tgt e = v)).card : ℂ)

/-- The ring of four vertices (Section 13.3, the ring of `ql:walk`): the vertices `0, 1, 2, 3`
and the edges `0 → 1`, `1 → 2`, `2 → 3`, `0 → 3`, without faces. -/
def ringFour : Canvas where
  V := Fin 4
  E := Fin 4
  F := Fin 0
  src := ![0, 1, 2, 0]
  tgt := ![1, 2, 3, 3]
  boundary := Fin.elim0
  closed f := f.elim0

end Canvas

end

end Artform
