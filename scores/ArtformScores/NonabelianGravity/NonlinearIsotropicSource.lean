import ArtformScores.GravityBridge.Native.Full40.Coordinates

/-! # Exact nonlinear isotropic pullback of the pinned five-corner curvature

One middle cell and its future neighbour; the preceding incident cell has
identity links and is independent of the middle temporal coframe column.
The source holonomy is -(H-H^-1)/2, not a logarithm. Both diagonal transports
remain explicit. C and S become cosh(b), sinh(b) on real boost links.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]

def face : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def complement : Fin 6 → Fin 4 × Fin 4 × ℤ :=
  ![(2, 3, 1), (1, 3, -1), (1, 2, 1), (0, 3, 1), (0, 2, -1), (0, 1, 1)]

def frame (ell a : K) : Frame K := Matrix.diagonal ![ell, a, a, a]

def link (C S : K) (k : Fin 4) : Frame K := fun i j =>
  if k = 0 then if i = j then 1 else 0
  else if i = j then if i = 0 ∨ i = k then C else 1
  else if (i = 0 ∧ j = k) ∨ (i = k ∧ j = 0) then S else 0

def atFrame (ell a c : K) (t : ℕ) : Frame K :=
  if t = 0 then frame ell a else frame 1 c

def atLink (C S : K) (t : ℕ) (k : Fin 4) : Frame K :=
  if t = 0 then link C S k else 1

def shift (k : Fin 4) : ℕ := if k = 0 then 1 else 0

def wedgeColumns (E : Frame K) (i j : Fin 4) : Biv K :=
  ![E 0 i * E 1 j - E 1 i * E 0 j,
    E 0 i * E 2 j - E 2 i * E 0 j,
    E 0 i * E 3 j - E 3 i * E 0 j,
    E 2 i * E 3 j - E 3 i * E 2 j,
    E 3 i * E 1 j - E 1 i * E 3 j,
    E 1 i * E 2 j - E 2 i * E 1 j]

def transported (E P : Frame K) (f : Fin 6) : Biv K :=
  (complement f).2.2 • wedgeColumns (P * E) (complement f).1 (complement f).2.1

def averaged (C S ell a c : K) (f : Fin 6) : Biv K :=
  let k := (face f).1
  let l := (face f).2
  (1 / 4 : K) • transported (frame ell a) 1 f +
  (1 / 4 : K) • transported (atFrame ell a c (shift k)) (link C (-S) k) f +
  (1 / 4 : K) • transported (atFrame ell a c (shift l)) (link C (-S) l) f +
  (1 / 8 : K) • transported (atFrame ell a c (shift k + shift l))
    (link C (-S) k * atLink C (-S) (shift k) l) f +
  (1 / 8 : K) • transported (atFrame ell a c (shift k + shift l))
    (link C (-S) l * atLink C (-S) (shift l) k) f

def holonomy (C S : K) (f : Fin 6) : Frame K :=
  let k := (face f).1
  let l := (face f).2
  link C (-S) l * atLink C (-S) (shift l) k *
    atLink C S (shift k) l * link C S k

def inverseHolonomy (C S : K) (f : Fin 6) : Frame K :=
  let k := (face f).1
  let l := (face f).2
  link C (-S) k * atLink C (-S) (shift k) l *
    atLink C S (shift l) k * link C S l

def curvatureFace (C S ell a c : K) (f : Fin 6) : K :=
  bivPair (averaged C S ell a c f)
    (internalStar (lieCoordinates ((-(1 / 2) : K) •
      (holonomy C S f - inverseHolonomy C S f))))

def curvature (C S ell a c : K) : K := ∑ f, curvatureFace C S ell a c f

def rawLapse (C S : K) : K :=
  (3 / 8) * S ^ 2 * (1 - C ^ 2 + 7 * C + C ^ 3 - 3 * S ^ 2 - C * S ^ 2)

def closedLapse (C S : K) : K := (3 / 2) * S ^ 2 * (1 + 2 * C - C ^ 2)

lemma raw_closed (C S : K) (h : C ^ 2 - S ^ 2 = 1) : rawLapse C S = closedLapse C S := by
  dsimp [rawLapse, closedLapse]
  linear_combination (3 / 8) * S ^ 2 * (C + 3) * h

/-! The same cell constructor with arbitrary two-site coframes and links.
This makes the preceding incident cell and its lapse independence explicit. -/

def cellAverage (E : ℕ → Frame K) (V : ℕ → Fin 4 → Frame K) (f : Fin 6) : Biv K :=
  let k := (face f).1
  let l := (face f).2
  (1 / 4 : K) • transported (E 0) 1 f +
  (1 / 4 : K) • transported (E (shift k)) (V 0 k) f +
  (1 / 4 : K) • transported (E (shift l)) (V 0 l) f +
  (1 / 8 : K) • transported (E (shift k + shift l)) (V 0 k * V (shift k) l) f +
  (1 / 8 : K) • transported (E (shift k + shift l)) (V 0 l * V (shift l) k) f

def cellHolonomy (U V : ℕ → Fin 4 → Frame K) (f : Fin 6) : Frame K :=
  let k := (face f).1
  let l := (face f).2
  V 0 l * V (shift l) k * U (shift k) l * U 0 k

def cellInverseHolonomy (U V : ℕ → Fin 4 → Frame K) (f : Fin 6) : Frame K :=
  let k := (face f).1
  let l := (face f).2
  V 0 k * V (shift k) l * U (shift l) k * U 0 l

def cellCurvatureFace (E : ℕ → Frame K) (U V : ℕ → Fin 4 → Frame K)
    (f : Fin 6) : K :=
  bivPair (cellAverage E V f) (internalStar (lieCoordinates
    ((-(1 / 2) : K) • (cellHolonomy U V f - cellInverseHolonomy U V f))))

omit [CharZero K] in
lemma middle_constructor (C S ell a c : K) (f : Fin 6) :
    curvatureFace C S ell a c f =
      cellCurvatureFace (atFrame ell a c) (atLink C S) (atLink C (-S)) f := rfl

def incomingFrame (ell a : K) (t : ℕ) : Frame K :=
  if t = 0 then frame 1 1 else frame ell a

def incomingLink (C S : K) (t : ℕ) (k : Fin 4) : Frame K :=
  if t = 0 then 1 else link C S k

def incomingCurvature (C S ell a : K) : K :=
  ∑ f, cellCurvatureFace (incomingFrame ell a) (incomingLink C S) (incomingLink C (-S)) f

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
