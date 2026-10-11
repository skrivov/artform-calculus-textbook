import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Block
import ArtformTextbook.Ch05.Defs.Curvature
import ArtformTextbook.Ch11.Defs.Colourless

/-!
# Colourless states of a canvas (Section 13.4)

A canvas `K` carries a link value at every edge and, at every vertex, the occupation tables of
`d = |S|` slots of each colour. The gauge group `G^V` acts on the link tables of the transport
skeleton by `U^h_e = h_{t(e)} U_e h_{s(e)}⁻¹` (`eq:gauge-action`, `Skeleton.gaugeAct`) and on the
matter by the colour rotation `ρ(h_v)` at every vertex. A state is a coefficient table over the
link tables and the occupation tables of all the vertices, and it is colourless when every gauge
change fixes it: the condition of Definition 11.13, the Gauss constraint, at every vertex.

* **Modes.** A mode of the canvas is a colour and a slot at a vertex, `((c, s), v)`; an
  occupation table is a finite set of occupied modes (Section 11.4).
* **The gauge action on the matter.** The one-quark matrix of a gauge change `h` is
  `ρ(h_v) ⊗ 1_S` on the modes of each vertex `v` (`gaugeMatrix`), and the matter moves by its
  second quantization (`Fock.secondQuant`, `matterGauge`), in a chosen order of the modes.
* **Without matter** a state is a coefficient table over the link tables alone, and it is
  colourless when `ψ(U^h) = ψ(U)` for every gauge change (`gaugeInvariants`).

The canvas of Section 13.4 is the boundary of the cube (`Canvas.cube`).
-/

namespace Artform

namespace Canvas

open scoped Matrix

variable (K : Canvas) {G : Type*} [Group G] {C S : Type*} [Fintype C] [DecidableEq C]
  [Fintype S] [DecidableEq S]

/-- The modes of a canvas with colours `C` and `d = |S|` slots at every vertex: a colour and a
slot, `(c, s)`, at a vertex `v`. -/
abbrev Mode (C S : Type*) : Type _ := (C × S) × K.V

/-- The one-quark gauge matrix of a gauge change `h = (h_v)`: on the modes of each vertex `v` it
is `ρ(h_v) ⊗ 1_S`, which turns the colour of a quark at `v` by `ρ(h_v)` and keeps its slot and
its vertex. -/
noncomputable def gaugeMatrix (ρ : G →* Matrix C C ℂ) (h : K.V → G) :
    Matrix (K.Mode C S) (K.Mode C S) ℂ :=
  Matrix.blockDiagonal fun v => Matrix.kroneckerMap (· * ·) (ρ (h v)) (1 : Matrix S S ℂ)

/-- The colour rotation `Γ(h)` of the matter of a canvas: the second quantization of the
one-quark gauge matrix, in the chosen order `ord` of the modes. -/
noncomputable def matterGauge (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (K.Mode C S))
    (h : K.V → G) : Matrix (Finset (K.Mode C S)) (Finset (K.Mode C S)) ℂ :=
  Fock.secondQuant ord (K.gaugeMatrix ρ h)

/-- The colourless states of a canvas with `d = |S|` slots at every vertex: the coefficient
tables `ψ` over the link tables and the occupation tables that every gauge change `h ∈ G^V`
fixes, `ψ(U^h) = Γ(h) ψ(U)` for all `h` and `U`. This is the condition of Definition 11.13 at
every vertex of the canvas. -/
noncomputable def colourless (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (K.Mode C S)) :
    Submodule ℂ (K.skeleton.LinkTable G → Finset (K.Mode C S) → ℂ) where
  carrier := {ψ | ∀ (h : K.V → G) (U : K.skeleton.LinkTable G),
    ψ (Skeleton.gaugeAct h U) = K.matterGauge ρ ord h *ᵥ ψ U}
  add_mem' {ψ φ} hψ hφ h U := by
    simp only [Set.mem_ofPred_eq] at hψ hφ
    simp only [Pi.add_apply, hψ, hφ, Matrix.mulVec_add]
  zero_mem' h U := by simp
  smul_mem' c ψ hψ h U := by
    simp only [Set.mem_ofPred_eq] at hψ
    simp only [Pi.smul_apply, hψ, Matrix.mulVec_smul]

/-- The zero-flux states of a canvas: the colourless states that are constant in the link
table, so that every link's table lies in the trivial block (Definition 11.13). -/
noncomputable def zeroFlux (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (K.Mode C S)) :
    Submodule ℂ (K.skeleton.LinkTable G → Finset (K.Mode C S) → ℂ) where
  carrier := {ψ | ψ ∈ K.colourless ρ ord ∧ ∀ U V, ψ U = ψ V}
  add_mem' {ψ φ} hψ hφ := ⟨(K.colourless ρ ord).add_mem hψ.1 hφ.1, fun U V => by
    simp only [Pi.add_apply, hψ.2 U V, hφ.2 U V]⟩
  zero_mem' := ⟨(K.colourless ρ ord).zero_mem, fun _ _ => rfl⟩
  smul_mem' c ψ hψ := ⟨(K.colourless ρ ord).smul_mem c hψ.1, fun U V => by
    simp only [Pi.smul_apply, hψ.2 U V]⟩

/-- The colourless states of a canvas without matter: the coefficient tables `ψ` over the link
tables that every gauge change fixes, `ψ(U^h) = ψ(U)`. -/
def gaugeInvariants (G : Type*) [Group G] : Submodule ℂ (K.skeleton.LinkTable G → ℂ) where
  carrier := {ψ | ∀ (h : K.V → G) (U : K.skeleton.LinkTable G),
    ψ (Skeleton.gaugeAct h U) = ψ U}
  add_mem' {ψ φ} hψ hφ h U := by
    simp only [Set.mem_ofPred_eq] at hψ hφ
    simp only [Pi.add_apply, hψ, hφ]
  zero_mem' h U := rfl
  smul_mem' c ψ hψ h U := by
    simp only [Set.mem_ofPred_eq] at hψ
    simp only [Pi.smul_apply, hψ]

/-! ### The cube -/

/-- The boundary of the cube as a canvas (Section 13.4, the cubical boundary of
Section 3.2). The vertex `4x + 2y + z` is the corner `(x, y, z)` with `x, y, z ∈ {0, 1}`. The
twelve edges point along the axes: `0`–`3` along `x`, `4`–`7` along `y`, `8`–`11` along `z`.
The six faces are `x = 0`, `x = 1`, `y = 0`, `y = 1`, `z = 0`, `z = 1`, each read
anticlockwise as seen from outside the cube. -/
def cube : Canvas where
  V := Fin 8
  E := Fin 12
  F := Fin 6
  src := ![0, 1, 2, 3, 0, 1, 4, 5, 0, 2, 4, 6]
  tgt := ![4, 5, 6, 7, 2, 3, 6, 7, 1, 3, 5, 7]
  boundary := ![[(8, true), (5, true), (9, false), (4, false)],
    [(6, true), (11, true), (7, false), (10, false)],
    [(0, true), (10, true), (1, false), (8, false)],
    [(9, true), (3, true), (11, false), (2, false)],
    [(4, true), (2, true), (6, false), (0, false)],
    [(1, true), (7, true), (3, false), (5, false)]]
  closed f := by
    unfold IsClosedWalk
    fin_cases f <;> decide

end Canvas

end Artform
