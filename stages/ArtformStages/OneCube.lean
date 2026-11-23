import ArtformStages.ManyCells

/-!
# One cube: its field and its modes (finding 492)

Wave N2 of campaign 15 of road DP. Findings 485 and 486 read photons on windows of squares. Here the
window of one cube is set up for the same reading: its 8 corners `(x, y, z)` in `{0, 1}³`, numbered
`4 x + 2 y + z`; its 12 lines, four along each axis, from the corner with `0` to the corner with `1`
on that axis; its 6 faces `x = 0, x = 1, y = 0, y = 1, z = 0, z = 1`, each round its four lines in
the sense that points out of the cube.

* `oneCubeGauge`, `oneCubeIncidence`, `oneCube_incidence_mul_gauge` (PC1): the two maps close,
  `C G = 0`;
* `oneCubeTouch`, `oneCube_faces_table` (PC1): the faces' table `C Cᵀ` is `4` less the table of the
  faces that touch, the octahedron's;
* `oneCubeModes`, `oneCube_levels`, `oneCube_modes_orth`, `oneCube_modes_det` (PC1): six level
  vectors, all ones, the differences of opposite faces and two combinations of the opposite pairs,
  give
  `C Cᵀ Q = Q diag(0, 4, 4, 4, 6, 6)` with `Qᵀ Q` diagonal and `det Q ≠ 0`: the levels of `C Cᵀ`
  are `0` once, `4` three times and `6` twice;
* `oneCubeTick`, `oneCubeTick_sum_sq` (PC2): R4's tick on the cube keeps the sum of the squares.

The tables are checked entry by entry by `decide`. None of this is new: the faces of a cube are
the corners of an octahedron, whose levels are `4`, `0` three times and `-2` twice.
-/

open Matrix

namespace Artform.Stages

section OneCube

/-- **The cube's gauge**: for each line, `+1` at its head and `-1` at its tail. Lines `0` to `3` run
along `x`, `4` to `7` along `y`, `8` to `11` along `z`. -/
def oneCubeGauge : Matrix (Fin 12) (Fin 8) ℤ :=
  !![-1, 0, 0, 0, 1, 0, 0, 0; 0, -1, 0, 0, 0, 1, 0, 0; 0, 0, -1, 0, 0, 0, 1, 0;
    0, 0, 0, -1, 0, 0, 0, 1; -1, 0, 1, 0, 0, 0, 0, 0; 0, -1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 1, 0; 0, 0, 0, 0, 0, -1, 0, 1; -1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 1, 0, 0; 0, 0, 0, 0, 0, 0, -1, 1]

/-- **The cube's incidence**: each face round its four lines, in the sense that points out of the
cube. Faces `0` to `5` are `x = 0, x = 1, y = 0, y = 1, z = 0, z = 1`. -/
def oneCubeIncidence : Matrix (Fin 6) (Fin 12) ℤ :=
  !![0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0; 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1;
    1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0; 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, -1;
    -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0, 0; 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0]

/-- PC1. **The cube's maps close**: no gauge change has a flux. -/
theorem oneCube_incidence_mul_gauge : oneCubeIncidence * oneCubeGauge = 0 := by decide

/-- The faces that touch: `1` for two faces that share a line, the octahedron's table. -/
def oneCubeTouch : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1; 0, 0, 1, 1, 1, 1; 1, 1, 0, 0, 1, 1; 1, 1, 0, 0, 1, 1;
    1, 1, 1, 1, 0, 0; 1, 1, 1, 1, 0, 0]

/-- PC1. **The faces' table** is `4` less the table of the faces that touch. -/
theorem oneCube_faces_table : oneCubeIncidence * oneCubeIncidenceᵀ = 4 - oneCubeTouch := by decide

/-- The six level vectors, as columns: all ones; the three differences of opposite faces; the
difference of the first two opposite pairs, and their sum less twice the third. -/
def oneCubeModes : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1; 1, -1, 0, 0, 1, 1; 1, 0, 1, 0, -1, 1; 1, 0, -1, 0, -1, 1;
    1, 0, 0, 1, 0, -2; 1, 0, 0, -1, 0, -2]

/-- PC1. **The levels of the faces' table**: `C Cᵀ Q = Q diag(0, 4, 4, 4, 6, 6)`. -/
theorem oneCube_levels :
    oneCubeIncidence * oneCubeIncidenceᵀ * oneCubeModes =
      oneCubeModes * diagonal ![0, 4, 4, 4, 6, 6] := by
  decide

/-- PC1. The level vectors are orthogonal. -/
theorem oneCube_modes_orth :
    oneCubeModesᵀ * oneCubeModes = diagonal ![6, 2, 2, 2, 4, 12] := by
  decide

/-- PC1. So the level vectors are independent: `det Q ≠ 0`, and the levels of `C Cᵀ` are `0`
once, `4` three times and `6` twice. -/
theorem oneCube_modes_det : oneCubeModes.det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det oneCube_modes_orth
  rw [det_mul, det_transpose, h, mul_zero, det_diagonal] at h2
  simp [Fin.prod_univ_succ] at h2

/-- **R4's tick on the cube**, on the dial of `n`: the drift of the weights `l` on the lines after
the kick of the weights `κ` on the faces' fluxes (finding 491). -/
noncomputable def oneCubeTick (n : ℕ) [NeZero n] (κ : Fin 6 → ℝ) (l : Fin 12 → ℝ) :
    Module.End ℂ (LightWave (Fin 12) n) :=
  energyTick (oneCubeIncidence.map (Int.cast : ℤ → ZMod n)) κ l

/-- PC2. **R4's tick on the cube keeps the sum of the squares** of every wave. -/
theorem oneCubeTick_sum_sq (n : ℕ) [NeZero n] (κ : Fin 6 → ℝ) (l : Fin 12 → ℝ)
    (ψ : LightWave (Fin 12) n) : ∑ b, ‖oneCubeTick n κ l ψ b‖ ^ 2 = ∑ b, ‖ψ b‖ ^ 2 :=
  energyTick_sum_sq _ κ l ψ

end OneCube

end Artform.Stages
