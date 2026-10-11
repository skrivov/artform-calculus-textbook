import ArtformTextbook.Ch12.Statements
import ArtformTextbook.Exact.QPhi

/-!
# The sixty rotations of the icosahedron

The proof of Proposition 12.8 (`prop:mm-icosahedron`).

The computation is done exactly, in `ℤ[φ]` (`ArtformTextbook.Exact.QPhi`):
the twelve vertices `vE`, and the sixty rotations `gE` doubled, so that their
entries lie in `ℤ[φ]`. Rotation `k` carries the base edge, the vertices
`(0, 1, φ)` and `(φ, 0, 1)`, to the `k`-th directed edge, and `perm k` is the
permutation it makes of the vertices. The data are written by
`scripts/certificates/icosahedron.py`, and every claim about them is checked
here by `decide +kernel`; `toReal` carries the checks to the real numbers.

The rest is linear algebra over `ℝ`. A rotation `M` keeps dot products and
satisfies `M (a ⨯₃ b) = M a ⨯₃ M b`, and for two neighbours `a, b` the frame
`a, b, a ⨯₃ b` is a basis, since `(a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) = 4 φ + 4`. So a rotation of
the icosahedron is fixed by the images of the base edge, which form an edge,
and it is one of the sixty.
-/

namespace Artform

open Real Matrix

namespace Icosahedron

open Exact

/-- A vector of `ℤ[φ]³` from its six integers: `(a + b φ, c + d φ, e + f φ)`. -/
def v (a b c d e f : ℤ) : V3 := ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩

/-- A `3 × 3` matrix of `ℤ[φ]` from its eighteen integers, row by row, two for
each entry `a + b φ`. -/
def m (a₀₀ b₀₀ a₀₁ b₀₁ a₀₂ b₀₂ a₁₀ b₁₀ a₁₁ b₁₁ a₁₂ b₁₂ a₂₀ b₂₀ a₂₁ b₂₁ a₂₂ b₂₂ : ℤ) : M3 :=
  ⟨v a₀₀ b₀₀ a₀₁ b₀₁ a₀₂ b₀₂, v a₁₀ b₁₀ a₁₁ b₁₁ a₁₂ b₁₂, v a₂₀ b₂₀ a₂₁ b₂₁ a₂₂ b₂₂⟩

/-- The twelve vertices, in the order of `icoVertices`. -/
def vE : Fin 12 → V3 := ![
  v 0 0 1 0 0 1, v 0 0 1 0 0 (-1), v 0 0 (-1) 0 0 1, v 0 0 (-1) 0 0 (-1), v 0 1 0 0 1 0,
  v 0 1 0 0 (-1) 0, v 0 (-1) 0 0 1 0, v 0 (-1) 0 0 (-1) 0, v 1 0 0 1 0 0, v 1 0 0 (-1) 0 0,
  v (-1) 0 0 1 0 0, v (-1) 0 0 (-1) 0 0]

/-- The sixty rotations, doubled: rotation `k` is `(gE k).toRealHalf`. It carries
the base edge `(vE 0, vE 4)` to the `k`-th directed edge in lexicographic order. -/
def gE : Fin 60 → M3 := ![
  m (-1) 1 0 1 (-1) 0 0 (-1) 1 0 (-1) 1 1 0 (-1) 1 0 1, m 2 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 2 0,
  m 0 (-1) 1 0 1 (-1) (-1) 0 1 (-1) 0 1 (-1) 1 0 1 1 0,
  m (-1) 1 0 (-1) 1 0 0 1 1 0 (-1) 1 (-1) 0 (-1) 1 0 1,
  m 0 (-1) (-1) 0 (-1) 1 1 0 1 (-1) 0 1 1 (-1) 0 1 1 0,
  m 1 (-1) 0 (-1) 1 0 0 (-1) 1 0 (-1) 1 (-1) 0 1 (-1) 0 (-1),
  m 0 1 (-1) 0 (-1) 1 (-1) 0 1 (-1) 0 1 1 (-1) 0 (-1) (-1) 0,
  m (-2) 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 (-2) 0, m 0 1 1 0 1 (-1) 1 0 1 (-1) 0 1 (-1) 1 0 (-1) (-1) 0,
  m 1 (-1) 0 1 (-1) 0 0 1 1 0 (-1) 1 1 0 1 (-1) 0 (-1),
  m 1 (-1) 0 (-1) 1 0 0 1 (-1) 0 1 (-1) 1 0 (-1) 1 0 1,
  m 0 1 (-1) 0 (-1) 1 1 0 (-1) 1 0 (-1) (-1) 1 0 1 1 0, m (-2) 0 0 0 0 0 0 0 (-2) 0 0 0 0 0 0 0 2 0,
  m 0 1 1 0 1 (-1) (-1) 0 (-1) 1 0 (-1) 1 (-1) 0 1 1 0,
  m 1 (-1) 0 1 (-1) 0 0 (-1) (-1) 0 1 (-1) (-1) 0 (-1) 1 0 1,
  m (-1) 1 0 1 (-1) 0 0 1 (-1) 0 1 (-1) (-1) 0 1 (-1) 0 (-1),
  m 2 0 0 0 0 0 0 0 (-2) 0 0 0 0 0 0 0 (-2) 0,
  m 0 (-1) 1 0 1 (-1) 1 0 (-1) 1 0 (-1) 1 (-1) 0 (-1) (-1) 0,
  m (-1) 1 0 (-1) 1 0 0 (-1) (-1) 0 1 (-1) 1 0 1 (-1) 0 (-1),
  m 0 (-1) (-1) 0 (-1) 1 (-1) 0 (-1) 1 0 (-1) (-1) 1 0 (-1) (-1) 0,
  m (-1) 0 (-1) 1 0 1 (-1) 1 0 (-1) 1 0 0 1 1 0 (-1) 1,
  m 1 (-1) 0 1 1 0 0 (-1) (-1) 0 (-1) 1 1 0 1 (-1) 0 1,
  m 1 0 (-1) 1 0 1 (-1) 1 0 1 (-1) 0 0 (-1) 1 0 (-1) 1, m 0 0 0 0 2 0 2 0 0 0 0 0 0 0 2 0 0 0,
  m (-1) 1 0 1 1 0 0 (-1) 1 0 1 (-1) (-1) 0 1 (-1) 0 1,
  m 1 (-1) 0 1 1 0 0 1 1 0 1 (-1) (-1) 0 (-1) 1 0 (-1),
  m (-1) 0 (-1) 1 0 1 1 (-1) 0 1 (-1) 0 0 (-1) (-1) 0 1 (-1),
  m 1 0 (-1) 1 0 1 1 (-1) 0 (-1) 1 0 0 1 (-1) 0 1 (-1),
  m (-1) 1 0 1 1 0 0 1 (-1) 0 (-1) 1 1 0 (-1) 1 0 (-1), m 0 0 0 0 2 0 (-2) 0 0 0 0 0 0 0 (-2) 0 0 0,
  m (-1) 1 0 (-1) (-1) 0 0 1 1 0 1 (-1) 1 0 1 (-1) 0 1,
  m 1 0 1 (-1) 0 (-1) 1 (-1) 0 1 (-1) 0 0 1 1 0 (-1) 1,
  m (-1) 0 1 (-1) 0 (-1) 1 (-1) 0 (-1) 1 0 0 (-1) 1 0 (-1) 1,
  m 1 (-1) 0 (-1) (-1) 0 0 1 (-1) 0 (-1) 1 (-1) 0 1 (-1) 0 1,
  m 0 0 0 0 (-2) 0 (-2) 0 0 0 0 0 0 0 2 0 0 0,
  m 1 0 1 (-1) 0 (-1) (-1) 1 0 (-1) 1 0 0 (-1) (-1) 0 1 (-1),
  m (-1) 1 0 (-1) (-1) 0 0 (-1) (-1) 0 (-1) 1 (-1) 0 (-1) 1 0 (-1),
  m (-1) 0 1 (-1) 0 (-1) (-1) 1 0 1 (-1) 0 0 1 (-1) 0 1 (-1),
  m 0 0 0 0 (-2) 0 2 0 0 0 0 0 0 0 (-2) 0 0 0,
  m 1 (-1) 0 (-1) (-1) 0 0 (-1) 1 0 1 (-1) 1 0 (-1) 1 0 (-1), m 0 0 2 0 0 0 0 0 0 0 2 0 2 0 0 0 0 0,
  m (-1) 0 1 (-1) 0 1 (-1) 1 0 1 1 0 0 (-1) 1 0 1 (-1),
  m 0 1 1 0 (-1) 1 (-1) 0 (-1) 1 0 1 (-1) 1 0 (-1) 1 0,
  m 1 0 1 (-1) 0 1 1 (-1) 0 1 1 0 0 (-1) (-1) 0 (-1) 1,
  m 0 (-1) 1 0 (-1) 1 1 0 (-1) 1 0 1 (-1) 1 0 1 (-1) 0,
  m (-1) 0 1 (-1) 0 1 1 (-1) 0 (-1) (-1) 0 0 1 (-1) 0 (-1) 1,
  m 0 0 2 0 0 0 0 0 0 0 (-2) 0 (-2) 0 0 0 0 0, m 1 0 1 (-1) 0 1 (-1) 1 0 (-1) (-1) 0 0 1 1 0 1 (-1),
  m 0 1 1 0 (-1) 1 1 0 1 (-1) 0 (-1) 1 (-1) 0 1 (-1) 0,
  m 0 (-1) 1 0 (-1) 1 (-1) 0 1 (-1) 0 (-1) 1 (-1) 0 (-1) 1 0,
  m 1 0 (-1) 1 0 (-1) (-1) 1 0 1 1 0 0 1 (-1) 0 (-1) 1, m 0 0 (-2) 0 0 0 0 0 0 0 2 0 (-2) 0 0 0 0 0,
  m (-1) 0 (-1) 1 0 (-1) 1 (-1) 0 1 1 0 0 1 1 0 1 (-1),
  m 0 (-1) (-1) 0 1 (-1) (-1) 0 (-1) 1 0 1 1 (-1) 0 1 (-1) 0,
  m 0 1 (-1) 0 1 (-1) 1 0 (-1) 1 0 1 1 (-1) 0 (-1) 1 0, m 0 0 (-2) 0 0 0 0 0 0 0 (-2) 0 2 0 0 0 0 0,
  m 1 0 (-1) 1 0 (-1) 1 (-1) 0 (-1) (-1) 0 0 (-1) 1 0 1 (-1),
  m 0 (-1) (-1) 0 1 (-1) 1 0 1 (-1) 0 (-1) (-1) 1 0 (-1) 1 0,
  m (-1) 0 (-1) 1 0 (-1) (-1) 1 0 (-1) (-1) 0 0 (-1) (-1) 0 (-1) 1,
  m 0 1 (-1) 0 1 (-1) (-1) 0 1 (-1) 0 (-1) (-1) 1 0 1 (-1) 0]

/-- `perm k i`: the vertex to which rotation `k` carries vertex `i`. -/
def perm : Fin 60 → Fin 12 → Fin 12 := ![
  ![0, 5, 6, 3, 2, 9, 10, 1, 4, 11, 8, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  ![0, 9, 10, 3, 6, 11, 8, 5, 2, 7, 4, 1], ![0, 7, 4, 3, 8, 1, 2, 11, 10, 5, 6, 9],
  ![0, 11, 8, 3, 10, 7, 4, 9, 6, 1, 2, 5], ![1, 6, 5, 2, 3, 11, 8, 0, 7, 9, 10, 4],
  ![1, 11, 8, 2, 5, 9, 10, 6, 3, 4, 7, 0], ![1, 0, 3, 2, 7, 6, 5, 4, 10, 11, 8, 9],
  ![1, 9, 10, 2, 8, 4, 7, 11, 5, 0, 3, 6], ![1, 4, 7, 2, 10, 0, 3, 9, 8, 6, 5, 11],
  ![2, 7, 4, 1, 0, 10, 9, 3, 6, 8, 11, 5], ![2, 10, 9, 1, 4, 8, 11, 7, 0, 5, 6, 3],
  ![2, 3, 0, 1, 6, 7, 4, 5, 11, 10, 9, 8], ![2, 8, 11, 1, 9, 5, 6, 10, 4, 3, 0, 7],
  ![2, 5, 6, 1, 11, 3, 0, 8, 9, 7, 4, 10], ![3, 4, 7, 0, 1, 8, 11, 2, 5, 10, 9, 6],
  ![3, 2, 1, 0, 5, 4, 7, 6, 9, 8, 11, 10], ![3, 8, 11, 0, 7, 10, 9, 4, 1, 6, 5, 2],
  ![3, 6, 5, 0, 9, 2, 1, 10, 11, 4, 7, 8], ![3, 10, 9, 0, 11, 6, 5, 8, 7, 2, 1, 4],
  ![4, 11, 8, 7, 0, 6, 5, 3, 2, 10, 9, 1], ![4, 3, 0, 7, 2, 11, 8, 1, 9, 6, 5, 10],
  ![4, 10, 9, 7, 5, 1, 2, 6, 8, 3, 0, 11], ![4, 6, 5, 7, 8, 10, 9, 11, 0, 1, 2, 3],
  ![4, 1, 2, 7, 9, 3, 0, 10, 5, 11, 8, 6], ![5, 0, 3, 6, 1, 10, 9, 2, 8, 7, 4, 11],
  ![5, 10, 9, 6, 3, 7, 4, 0, 1, 11, 8, 2], ![5, 11, 8, 6, 4, 2, 1, 7, 9, 0, 3, 10],
  ![5, 2, 1, 6, 8, 0, 3, 11, 4, 10, 9, 7], ![5, 7, 4, 6, 9, 11, 8, 10, 3, 2, 1, 0],
  ![6, 1, 2, 5, 0, 8, 11, 3, 10, 4, 7, 9], ![6, 8, 11, 5, 2, 4, 7, 1, 0, 9, 10, 3],
  ![6, 9, 10, 5, 7, 3, 0, 4, 11, 1, 2, 8], ![6, 3, 0, 5, 10, 1, 2, 9, 7, 8, 11, 4],
  ![6, 4, 7, 5, 11, 9, 10, 8, 2, 3, 0, 1], ![7, 9, 10, 4, 1, 5, 6, 2, 3, 8, 11, 0],
  ![7, 2, 1, 4, 3, 9, 10, 0, 11, 5, 6, 8], ![7, 8, 11, 4, 6, 0, 3, 5, 10, 2, 1, 9],
  ![7, 5, 6, 4, 10, 8, 11, 9, 1, 0, 3, 2], ![7, 0, 3, 4, 11, 2, 1, 8, 6, 9, 10, 5],
  ![8, 9, 10, 11, 0, 2, 1, 3, 4, 6, 5, 7], ![8, 6, 5, 11, 1, 7, 4, 2, 10, 3, 0, 9],
  ![8, 3, 0, 11, 4, 9, 10, 7, 5, 2, 1, 6], ![8, 7, 4, 11, 5, 3, 0, 6, 1, 9, 10, 2],
  ![8, 2, 1, 11, 10, 6, 5, 9, 0, 7, 4, 3], ![9, 7, 4, 10, 2, 6, 5, 1, 11, 0, 3, 8],
  ![9, 8, 11, 10, 3, 1, 2, 0, 5, 7, 4, 6], ![9, 6, 5, 10, 4, 0, 3, 7, 2, 8, 11, 1],
  ![9, 0, 3, 10, 5, 8, 11, 6, 4, 1, 2, 7], ![9, 1, 2, 10, 11, 7, 4, 8, 3, 6, 5, 0],
  ![10, 5, 6, 9, 0, 4, 7, 3, 8, 2, 1, 11], ![10, 11, 8, 9, 1, 3, 0, 2, 7, 5, 6, 4],
  ![10, 4, 7, 9, 6, 2, 1, 5, 0, 11, 8, 3], ![10, 2, 1, 9, 7, 11, 8, 4, 6, 3, 0, 5],
  ![10, 3, 0, 9, 8, 5, 6, 11, 1, 4, 7, 2], ![11, 10, 9, 8, 2, 0, 3, 1, 6, 4, 7, 5],
  ![11, 4, 7, 8, 3, 5, 6, 0, 9, 1, 2, 10], ![11, 1, 2, 8, 6, 10, 9, 5, 7, 0, 3, 4],
  ![11, 5, 6, 8, 7, 1, 2, 4, 3, 10, 9, 0], ![11, 0, 3, 8, 9, 4, 7, 10, 2, 5, 6, 1]]

/-- `inv k`: the index of the transpose of rotation `k`. -/
def inv : Fin 60 → Fin 60 := ![
  3, 1, 4, 0, 2, 39, 59, 7, 48, 25, 21, 42, 12, 54, 33, 15, 16, 17, 18, 19, 20, 10, 50, 40, 30, 9,
  37, 47, 28, 55, 24, 43, 32, 14, 51, 56, 36, 26, 46, 5, 23, 52, 11, 31, 44, 45, 38, 27, 8, 57, 22,
  34, 41, 53, 13, 29, 35, 49, 58, 6]

/-! ### The exact checks -/

theorem vE_injective : ∀ i j : Fin 12, vE i = vE j → i = j := by
  decide +kernel

theorem vE_dot_self : ∀ i : Fin 12, (vE i).dot (vE i) = ⟨2, 1⟩ := by
  decide +kernel

theorem vE_dot_cases : ∀ i j : Fin 12, vE j = vE i ∨ (vE i).dot (vE j) = ⟨0, 1⟩ ∨
    (vE i).dot (vE j) = ⟨0, -1⟩ ∨ vE j = (vE i).neg := by
  decide +kernel

theorem vE_card_phi :
    ∀ i : Fin 12, (Finset.univ.filter fun j => (vE i).dot (vE j) = ⟨0, 1⟩).card = 5 := by
  decide +kernel

theorem vE_card_neg_phi :
    ∀ i : Fin 12, (Finset.univ.filter fun j => (vE i).dot (vE j) = ⟨0, -1⟩).card = 5 := by
  decide +kernel

theorem vE_neg : ∀ i : Fin 12, ∃ j, vE j = (vE i).neg := by
  decide +kernel

theorem gE_ortho : ∀ k : Fin 60, (gE k).Ortho4 := by
  decide +kernel

theorem gE_det : ∀ k : Fin 60, (gE k).det = ⟨8, 0⟩ := by
  decide +kernel

theorem gE_perm : ∀ k : Fin 60, ∀ i : Fin 12, (gE k).mulVec (vE i) = (vE (perm k i)).double := by
  decide +kernel

theorem gE_transpose : ∀ k : Fin 60, (gE k).transpose = gE (inv k) := by
  decide +kernel

/-- Every directed edge is the image of the base edge under one of the sixty. -/
theorem edge_cover :
    ∀ i j : Fin 12, (vE i).dot (vE j) = ⟨0, 1⟩ → ∃ k : Fin 60, perm k 0 = i ∧ perm k 4 = j := by
  decide +kernel

/-- Different rotations carry the base edge to different edges. -/
theorem edge_injective :
    ∀ k l : Fin 60, perm k 0 = perm l 0 → perm k 4 = perm l 4 → k = l := by
  decide +kernel

theorem gE_trace_cases : ∀ k : Fin 60, (gE k).trace = ⟨6, 0⟩ ∨ (gE k).trace = ⟨-2, 0⟩ ∨
    (gE k).trace = ⟨0, 0⟩ ∨ (gE k).trace = ⟨0, 2⟩ ∨ (gE k).trace = ⟨2, -2⟩ := by
  decide +kernel

theorem gE_trace_card :
    (Finset.univ.filter fun k => (gE k).trace = ⟨6, 0⟩).card = 1 ∧
    (Finset.univ.filter fun k => (gE k).trace = ⟨-2, 0⟩).card = 15 ∧
    (Finset.univ.filter fun k => (gE k).trace = ⟨0, 0⟩).card = 20 ∧
    (Finset.univ.filter fun k => (gE k).trace = ⟨0, 2⟩).card = 12 ∧
    (Finset.univ.filter fun k => (gE k).trace = ⟨2, -2⟩).card = 12 := by
  decide +kernel

/-! ### The vertices -/

/-- The vertices as real vectors. -/
noncomputable def vR (i : Fin 12) : Fin 3 → ℝ := (vE i).toReal

theorem vR_eq_vec : vR = ![![0, 1, goldenRatio], ![0, 1, -goldenRatio], ![0, -1, goldenRatio],
    ![0, -1, -goldenRatio], ![goldenRatio, 0, 1], ![goldenRatio, 0, -1], ![-goldenRatio, 0, 1],
    ![-goldenRatio, 0, -1], ![1, goldenRatio, 0], ![1, -goldenRatio, 0], ![-1, goldenRatio, 0],
    ![-1, -goldenRatio, 0]] := by
  funext i
  fin_cases i <;> funext j <;> fin_cases j <;> simp [vR, vE, v, V3.toReal, ZPhi.toReal]

theorem icoVertices_eq : icoVertices = Set.range vR := by
  rw [vR_eq_vec]
  simp only [icoVertices, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.insert_eq]

theorem vR_injective : Function.Injective vR :=
  fun i j h => vE_injective i j (V3.toReal_injective h)

theorem vR_dot (i j : Fin 12) : vR i ⬝ᵥ vR j = ((vE i).dot (vE j)).toReal :=
  V3.toReal_dot _ _

theorem toReal_phi : (⟨0, 1⟩ : ZPhi).toReal = goldenRatio := by
  simp [ZPhi.toReal]

theorem toReal_neg_phi : (⟨0, -1⟩ : ZPhi).toReal = -goldenRatio := by
  simp [ZPhi.toReal]

theorem vR_dot_eq_phi_iff (i j : Fin 12) :
    vR i ⬝ᵥ vR j = goldenRatio ↔ (vE i).dot (vE j) = ⟨0, 1⟩ := by
  rw [vR_dot, ← toReal_phi, ZPhi.toReal_inj]

theorem vR_dot_eq_neg_phi_iff (i j : Fin 12) :
    vR i ⬝ᵥ vR j = -goldenRatio ↔ (vE i).dot (vE j) = ⟨0, -1⟩ := by
  rw [vR_dot, ← toReal_neg_phi, ZPhi.toReal_inj]

theorem vR_dot_self (i : Fin 12) : vR i ⬝ᵥ vR i = goldenRatio + 2 := by
  rw [vR_dot, vE_dot_self, ZPhi.toReal_mk]
  push_cast
  ring

theorem dot_self_of_mem {w : Fin 3 → ℝ} (hw : w ∈ icoVertices) : w ⬝ᵥ w = goldenRatio + 2 := by
  rw [icoVertices_eq] at hw
  obtain ⟨i, rfl⟩ := hw
  exact vR_dot_self i

/-- The number of points of an injectively indexed finite set with a property. -/
theorem ncard_filter_range {α : Type*} {n : ℕ} {f : Fin n → α} (hf : Function.Injective f)
    (P : α → Prop) (Q : Fin n → Prop) [DecidablePred Q] (hPQ : ∀ i, P (f i) ↔ Q i) :
    {x | x ∈ Set.range f ∧ P x}.ncard = (Finset.univ.filter Q).card := by
  have h : {x | x ∈ Set.range f ∧ P x} = f '' ↑(Finset.univ.filter Q) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.mem_image, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hx⟩
      exact ⟨i, (hPQ i).1 hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, (hPQ i).2 hi⟩
  rw [h, Set.ncard_image_of_injective _ hf, Set.ncard_coe_finset]

/-! ### Rotations and frames -/

/-- A rotation commutes with the cross product. -/
theorem mulVec_cross {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) : M *ᵥ (a ⨯₃ b) = (M *ᵥ a) ⨯₃ (M *ᵥ b) := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff] at hM
  obtain ⟨hO, hdet⟩ := hM
  have hadj : M.adjugate = Mᵀ := by
    calc M.adjugate = M.adjugate * (M * Mᵀ) := by rw [hO, Matrix.mul_one]
      _ = M.adjugate * M * Mᵀ := by rw [Matrix.mul_assoc]
      _ = Mᵀ := by rw [adjugate_mul, hdet, one_smul, Matrix.one_mul]
  have key : (M *ᵥ a) ⨯₃ (M *ᵥ b) = M.adjugateᵀ *ᵥ (a ⨯₃ b) := by
    rw [adjugate_fin_three]
    ext i
    fin_cases i <;> simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  rw [key, hadj, transpose_transpose]

/-- An orthogonal matrix keeps dot products. -/
theorem dot_mulVec {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : Mᵀ * M = 1) (a b : Fin 3 → ℝ) :
    (M *ᵥ a) ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hM, one_mulVec]

/-- Two matrices that agree on `a`, `b` and `a ⨯₃ b`, with `a ⨯₃ b ≠ 0`, are equal:
the three vectors form a basis. -/
theorem eq_of_frame {M N : Matrix (Fin 3) (Fin 3) ℝ} {a b : Fin 3 → ℝ}
    (hab : (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) ≠ 0) (ha : M *ᵥ a = N *ᵥ a) (hb : M *ᵥ b = N *ᵥ b)
    (hc : M *ᵥ (a ⨯₃ b) = N *ᵥ (a ⨯₃ b)) : M = N := by
  set P : Matrix (Fin 3) (Fin 3) ℝ := (Matrix.of ![a, b, a ⨯₃ b])ᵀ with hPdef
  have hP : IsUnit P.det := by
    rw [isUnit_iff_ne_zero, hPdef, det_transpose]
    have h3 : (Matrix.of ![a, b, a ⨯₃ b]).det = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) := by
      rw [← triple_product_permutation, ← triple_product_permutation]
      exact (triple_product_eq_det a b (a ⨯₃ b)).symm
    rw [h3]
    exact hab
  have hMP : M * P = N * P := by
    ext i j
    have hcol : ∀ X : Matrix (Fin 3) (Fin 3) ℝ, (X * P) i j = (X *ᵥ ![a, b, a ⨯₃ b] j) i := by
      intro X
      simp [P, Matrix.mul_apply, mulVec, dotProduct]
    rw [hcol, hcol]
    fin_cases j
    · simp [ha]
    · simp [hb]
    · simp [hc]
  calc M = M * P * P⁻¹ := (mul_nonsing_inv_cancel_right P M hP).symm
    _ = N * P * P⁻¹ := by rw [hMP]
    _ = N := mul_nonsing_inv_cancel_right P N hP

/-- For two neighbours `a`, `b`: `(a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) = (φ + 2)² - φ² = 4 φ + 4 ≠ 0`. -/
theorem cross_dot_self_ne {a b : Fin 3 → ℝ} (ha : a ⬝ᵥ a = goldenRatio + 2)
    (hb : b ⬝ᵥ b = goldenRatio + 2) (hab : a ⬝ᵥ b = goldenRatio) :
    (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) ≠ 0 := by
  rw [cross_dot_cross, ha, hb, hab, dotProduct_comm b a, hab]
  have h : (goldenRatio + 2) * (goldenRatio + 2) - goldenRatio * goldenRatio =
      4 * goldenRatio + 4 := by ring
  rw [h]
  have := goldenRatio_pos
  positivity

/-! ### The sixty rotations -/

/-- The sixty rotations as real matrices. -/
noncomputable def R (k : Fin 60) : Matrix (Fin 3) (Fin 3) ℝ := (gE k).toRealHalf

theorem R_mulVec (k : Fin 60) (i : Fin 12) : R k *ᵥ vR i = vR (perm k i) :=
  M3.toRealHalf_mulVec (gE_perm k i)

theorem R_mem_SO (k : Fin 60) : R k ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  refine ⟨M3.toRealHalf_mul_transpose (gE_ortho k), ?_⟩
  rw [R, M3.det_toRealHalf, gE_det k, ZPhi.toReal_mk]
  norm_num

theorem R_mem (k : Fin 60) : R k ∈ icoRotations := by
  refine ⟨R_mem_SO k, ?_⟩
  rw [icoVertices_eq]
  rintro _ ⟨i, rfl⟩
  exact ⟨perm k i, (R_mulVec k i).symm⟩

theorem R_transpose (k : Fin 60) : (R k)ᵀ = R (inv k) := by
  rw [R, R, ← gE_transpose k, M3.toRealHalf_transpose]

theorem R_transpose_mul (k : Fin 60) : R (inv k) * R k = 1 := by
  rw [← R_transpose]
  exact (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp (R_mem_SO k)).1

theorem R_trace (k : Fin 60) : (R k).trace = (gE k).trace.toReal / 2 :=
  M3.trace_toRealHalf _

theorem icoRotations_mul {M N : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ icoRotations)
    (hN : N ∈ icoRotations) : M * N ∈ icoRotations :=
  ⟨Submonoid.mul_mem _ hM.1 hN.1, fun w hw => by
    rw [← mulVec_mulVec]
    exact hM.2 _ (hN.2 w hw)⟩

/-- The base edge: `(0, 1, φ)` and `(φ, 0, 1)` are neighbours. -/
theorem base_edge : (vE 0).dot (vE 4) = ⟨0, 1⟩ := by
  decide +kernel

/-- Every rotation of the icosahedron is one of the sixty. -/
theorem exists_R_of_mem {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ icoRotations) :
    ∃ k, R k = M := by
  obtain ⟨hSO, hV⟩ := hM
  rw [icoVertices_eq] at hV
  obtain ⟨i, hi⟩ := hV (vR 0) ⟨0, rfl⟩
  obtain ⟨j, hj⟩ := hV (vR 4) ⟨4, rfl⟩
  have hO : Mᵀ * M = 1 :=
    (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp hSO).1
  have hdot : (vE i).dot (vE j) = ⟨0, 1⟩ := by
    rw [← vR_dot_eq_phi_iff, hi, hj, dot_mulVec hO, vR_dot_eq_phi_iff]
    exact base_edge
  obtain ⟨k, hk0, hk4⟩ := edge_cover i j hdot
  refine ⟨k, eq_of_frame (a := vR 0) (b := vR 4) ?_ ?_ ?_ ?_⟩
  · exact cross_dot_self_ne (vR_dot_self 0) (vR_dot_self 4) ((vR_dot_eq_phi_iff 0 4).2 base_edge)
  · rw [R_mulVec, hk0, hi]
  · rw [R_mulVec, hk4, hj]
  · rw [mulVec_cross (R_mem_SO k), mulVec_cross hSO, R_mulVec, R_mulVec, hk0, hk4, hi, hj]

theorem icoRotations_eq : icoRotations = Set.range R := by
  ext M
  exact ⟨exists_R_of_mem, by rintro ⟨k, rfl⟩; exact R_mem k⟩

theorem R_injective : Function.Injective R := by
  intro k l h
  apply edge_injective
  · apply vR_injective
    rw [← R_mulVec, ← R_mulVec, h]
  · apply vR_injective
    rw [← R_mulVec, ← R_mulVec, h]

/-! ### The six claims -/

theorem ncard_icoVertices : icoVertices.ncard = 12 := by
  rw [icoVertices_eq, Set.ncard_range_of_injective vR_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem vertex_products : ∀ v ∈ icoVertices,
    v ⬝ᵥ v = goldenRatio + 2 ∧
    (∀ w ∈ icoVertices, w = v ∨ v ⬝ᵥ w = goldenRatio ∨ v ⬝ᵥ w = -goldenRatio ∨ w = -v) ∧
    {w | w ∈ icoVertices ∧ v ⬝ᵥ w = goldenRatio}.ncard = 5 ∧
    {w | w ∈ icoVertices ∧ v ⬝ᵥ w = -goldenRatio}.ncard = 5 ∧
    -v ∈ icoVertices := by
  rw [icoVertices_eq]
  rintro _ ⟨i, rfl⟩
  refine ⟨vR_dot_self i, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    rcases vE_dot_cases i j with h | h | h | h
    · exact Or.inl (by simp only [vR, h])
    · exact Or.inr (Or.inl ((vR_dot_eq_phi_iff i j).2 h))
    · exact Or.inr (Or.inr (Or.inl ((vR_dot_eq_neg_phi_iff i j).2 h)))
    · exact Or.inr (Or.inr (Or.inr (by simp only [vR, h, V3.toReal_neg])))
  · rw [ncard_filter_range vR_injective _ _ (vR_dot_eq_phi_iff i)]
    exact vE_card_phi i
  · rw [ncard_filter_range vR_injective _ _ (vR_dot_eq_neg_phi_iff i)]
    exact vE_card_neg_phi i
  · obtain ⟨j, hj⟩ := vE_neg i
    exact ⟨j, by simp only [vR, hj, V3.toReal_neg]⟩

theorem determined : ∀ v₁ ∈ icoVertices, ∀ v₂ ∈ icoVertices, v₁ ⬝ᵥ v₂ = goldenRatio →
    ∀ M ∈ icoRotations, ∀ N ∈ icoRotations,
      M.mulVec v₁ = N.mulVec v₁ → M.mulVec v₂ = N.mulVec v₂ → M = N := by
  intro v₁ hv₁ v₂ hv₂ hv M hM N hN h₁ h₂
  refine eq_of_frame (cross_dot_self_ne (dot_self_of_mem hv₁) (dot_self_of_mem hv₂) hv) h₁ h₂ ?_
  rw [mulVec_cross hM.1, mulVec_cross hN.1, h₁, h₂]

/-- The matrix carrying one frame of neighbours to another is unique among all
matrices, and it is one of the sixty: a rotation with entries in `½ℤ[φ]`. -/
theorem frame_rotation : ∀ v₁ ∈ icoVertices, ∀ v₂ ∈ icoVertices, v₁ ⬝ᵥ v₂ = goldenRatio →
    ∀ w₁ ∈ icoVertices, ∀ w₂ ∈ icoVertices, w₁ ⬝ᵥ w₂ = goldenRatio →
      (∃! M : Matrix (Fin 3) (Fin 3) ℝ,
        M.mulVec v₁ = w₁ ∧ M.mulVec v₂ = w₂ ∧ M.mulVec (v₁ ⨯₃ v₂) = w₁ ⨯₃ w₂) ∧
      ∀ M : Matrix (Fin 3) (Fin 3) ℝ,
        M.mulVec v₁ = w₁ → M.mulVec v₂ = w₂ → M.mulVec (v₁ ⨯₃ v₂) = w₁ ⨯₃ w₂ →
          M ∈ icoRotations ∧ ∀ i j, ∃ a b : ℤ, M i j = (a + b * goldenRatio) / 2 := by
  intro v₁ hv₁ v₂ hv₂ hv w₁ hw₁ w₂ hw₂ hw
  have hcross := cross_dot_self_ne (dot_self_of_mem hv₁) (dot_self_of_mem hv₂) hv
  rw [icoVertices_eq] at hv₁ hv₂ hw₁ hw₂
  obtain ⟨i₁, rfl⟩ := hv₁
  obtain ⟨j₁, rfl⟩ := hv₂
  obtain ⟨i₂, rfl⟩ := hw₁
  obtain ⟨j₂, rfl⟩ := hw₂
  rw [vR_dot_eq_phi_iff] at hv hw
  obtain ⟨k₁, rfl, rfl⟩ := edge_cover i₁ j₁ hv
  obtain ⟨k₂, rfl, rfl⟩ := edge_cover i₂ j₂ hw
  have hrot : R k₂ * R (inv k₁) ∈ icoRotations := icoRotations_mul (R_mem k₂) (R_mem (inv k₁))
  have hmap : ∀ i : Fin 12, (R k₂ * R (inv k₁)) *ᵥ vR (perm k₁ i) = vR (perm k₂ i) := by
    intro i
    rw [← R_mulVec, mulVec_mulVec, Matrix.mul_assoc, R_transpose_mul, Matrix.mul_one, R_mulVec]
  have hmap3 : (R k₂ * R (inv k₁)) *ᵥ (vR (perm k₁ 0) ⨯₃ vR (perm k₁ 4)) =
      vR (perm k₂ 0) ⨯₃ vR (perm k₂ 4) := by
    rw [mulVec_cross hrot.1, hmap, hmap]
  -- Any matrix carrying the frame is this one, since the frame is a basis.
  have huniq : ∀ N : Matrix (Fin 3) (Fin 3) ℝ, N *ᵥ vR (perm k₁ 0) = vR (perm k₂ 0) →
      N *ᵥ vR (perm k₁ 4) = vR (perm k₂ 4) →
      N *ᵥ (vR (perm k₁ 0) ⨯₃ vR (perm k₁ 4)) = vR (perm k₂ 0) ⨯₃ vR (perm k₂ 4) →
      N = R k₂ * R (inv k₁) := fun N hN₁ hN₂ hN₃ =>
    eq_of_frame hcross (hN₁.trans (hmap 0).symm) (hN₂.trans (hmap 4).symm)
      (hN₃.trans hmap3.symm)
  refine ⟨⟨R k₂ * R (inv k₁), ⟨hmap 0, hmap 4, hmap3⟩, ?_⟩, ?_⟩
  · rintro N ⟨hN₁, hN₂, hN₃⟩
    exact huniq N hN₁ hN₂ hN₃
  · intro N hN₁ hN₂ hN₃
    rw [huniq N hN₁ hN₂ hN₃]
    refine ⟨hrot, ?_⟩
    obtain ⟨k, hk⟩ := exists_R_of_mem hrot
    rw [← hk]
    exact M3.toRealHalf_entry (gE k)

theorem ncard_icoRotations : icoRotations.ncard = 60 := by
  rw [icoRotations_eq, Set.ncard_range_of_injective R_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The rotations of trace `z / 2`, for an exact `z`. -/
theorem ncard_trace_eq (t : ℝ) (z : ZPhi) (hz : z.toReal / 2 = t) :
    {M | M ∈ icoRotations ∧ M.trace = t}.ncard =
      (Finset.univ.filter fun k => (gE k).trace = z).card := by
  rw [icoRotations_eq]
  refine ncard_filter_range R_injective _ _ fun k => ?_
  rw [R_trace, ← hz, div_left_inj' two_ne_zero, ZPhi.toReal_inj]

theorem trace_counts : ∀ t : ℝ, {M | M ∈ icoRotations ∧ M.trace = t}.ncard =
    if t = 3 then 1 else if t = -1 then 15 else if t = 0 then 20
    else if t = goldenRatio then 12 else if t = 1 - goldenRatio then 12 else 0 := by
  intro t
  obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := gE_trace_card
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · rw [ncard_trace_eq t ⟨6, 0⟩ (by rw [h₁, ZPhi.toReal_mk]; norm_num), c₁]
  · rw [ncard_trace_eq t ⟨-2, 0⟩ (by rw [h₂, ZPhi.toReal_mk]; norm_num), c₂]
  · rw [ncard_trace_eq t ⟨0, 0⟩ (by rw [h₃, ZPhi.toReal_mk]; norm_num), c₃]
  · rw [ncard_trace_eq t ⟨0, 2⟩ (by rw [h₄, ZPhi.toReal_mk]; push_cast; ring), c₄]
  · rw [ncard_trace_eq t ⟨2, -2⟩ (by rw [h₅, ZPhi.toReal_mk]; push_cast; ring), c₅]
  · rw [icoRotations_eq, ncard_filter_range R_injective _ (fun _ => False) fun k => ?_]
    · simp
    · simp only [iff_false, R_trace]
      rcases gE_trace_cases k with h | h | h | h | h <;> rw [h, ZPhi.toReal_mk] <;> intro ht
      · exact h₁ (by rw [← ht]; norm_num)
      · exact h₂ (by rw [← ht]; norm_num)
      · exact h₃ (by rw [← ht]; norm_num)
      · exact h₄ (by rw [← ht]; push_cast; ring)
      · exact h₅ (by rw [← ht]; push_cast; ring)

end Icosahedron

/-- **Proposition 12.8** (The sixty rotations). The twelve vertices, their dot
products, the rotations fixed by the image of an edge, the sixty frame
rotations with entries in `½ℤ[φ]`, and the counts of their traces. -/
@[book "prop:mm-icosahedron"]
theorem sixtyRotations : Statement.sixtyRotations :=
  ⟨Icosahedron.ncard_icoVertices, Icosahedron.vertex_products, Icosahedron.determined,
    Icosahedron.frame_rotation, Icosahedron.ncard_icoRotations, Icosahedron.trace_counts⟩

/-! ## Non-vacuity -/

/-- The frame marked in the book's picture of the icosahedron
(`fig:mm-icosahedron`), `v₁ = (0, 1, φ)` and its neighbour `v₂ = (φ, 0, 1)`,
meets the hypotheses on vertices: both are vertices, and `v₁ ⬝ᵥ v₂ = φ`. -/
example : ![0, 1, goldenRatio] ∈ icoVertices ∧ ![goldenRatio, 0, 1] ∈ icoVertices ∧
    ![0, 1, goldenRatio] ⬝ᵥ ![goldenRatio, 0, 1] = goldenRatio :=
  ⟨by simp [icoVertices], by simp [icoVertices], by simp⟩

/-- The hypotheses on rotations can be met: the identity is a rotation of the
icosahedron. -/
example : (1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ icoRotations :=
  ⟨one_mem _, fun w hw => by rwa [one_mulVec]⟩

end Artform
