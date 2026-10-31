import Mathlib
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Defs.OneFace
import ArtformTextbook.Ch06.Defs.Maxwell
/-! # Fixed-source Gauss-preserving field scores -/

set_option autoImplicit false
namespace Artform.Scores.Gauge
open Artform Finset
@[ext] structure FieldState (K : Canvas) (R : Type) where
  A : K.E → R
  E : K.E → R
  ρ : K.V → R
variable {K : Canvas} {R : Type} [CommRing R]
def faceImpulse (p : K.F) (b : R) : K.E → R := K.curlStar (Pi.single p b)
def faceKick (p : K.F) (k : R) (s : FieldState K R) : FieldState K R :=
  ⟨s.A, s.E + faceImpulse p (k * K.curl s.A p), s.ρ⟩
def edgeMove (e : K.E) (k : R) (s : FieldState K R) : FieldState K R :=
  ⟨s.A + Pi.single e (k * s.E e), s.E, s.ρ⟩
def source (J : K.E → R) (s : FieldState K R) : FieldState K R :=
  ⟨s.A, s.E - J, s.ρ - K.div J⟩
def gauge (φ : K.V → R) (s : FieldState K R) : FieldState K R :=
  ⟨s.A + K.diff φ, s.E, s.ρ⟩
def defect (s : FieldState K R) : K.V → R := K.div s.E - s.ρ
abbrev Tangent (K : Canvas) (R : Type) := (K.E → R) × (K.E → R)
def dot (a b : K.E → R) : R := ∑ e, a e * b e
def omega (u v : Tangent K R) : R := dot u.1 v.2 - dot u.2 v.1

def faceTangent (p : K.F) (k : R) (u : Tangent K R) : Tangent K R :=
  (u.1, u.2 + faceImpulse p (k * K.curl u.1 p))
def moveTangent (e : K.E) (k : R) (u : Tangent K R) : Tangent K R :=
  (u.1 + Pi.single e (k * u.2 e), u.2)

lemma faceImpulse_apply (p : K.F) (b : R) (e : K.E) :
    faceImpulse p b e = (K.inc e p : R) * b := by
  simp [faceImpulse, Canvas.curlStar, Pi.single_apply]

lemma face_defect (p : K.F) (k : R) (s : FieldState K R) :
    defect (faceKick p k s) = defect s := by
  simp [defect, faceKick, faceImpulse]
lemma move_defect (e : K.E) (k : R) (s : FieldState K R) :
    defect (edgeMove e k s) = defect s := rfl
lemma source_defect (J : K.E → R) (s : FieldState K R) :
    defect (source J s) = defect s := by
  simp only [defect, source, Canvas.div_sub]
  abel
lemma face_gauge (p : K.F) (k : R) (φ : K.V → R) (s : FieldState K R) :
    faceKick p k (gauge φ s) = gauge φ (faceKick p k s) := by
  simp [faceKick, gauge]
lemma move_gauge (e : K.E) (k : R) (φ : K.V → R) (s : FieldState K R) :
    edgeMove e k (gauge φ s) = gauge φ (edgeMove e k s) := by
  apply FieldState.ext <;> simp [edgeMove, gauge, add_right_comm]
lemma source_gauge (J : K.E → R) (φ : K.V → R) (s : FieldState K R) :
    source J (gauge φ s) = gauge φ (source J s) := rfl
lemma face_inverse (p : K.F) (k : R) (s : FieldState K R) :
    faceKick p (-k) (faceKick p k s) = s := by
  apply FieldState.ext
  · rfl
  · funext e
    simp [faceKick, faceImpulse_apply]
  · rfl
lemma move_inverse (e : K.E) (k : R) (s : FieldState K R) :
    edgeMove e (-k) (edgeMove e k s) = s := by
  apply FieldState.ext
  · funext j
    simp only [edgeMove, Pi.add_apply, Pi.single_apply, neg_mul]
    split_ifs <;> ring
  · rfl
  · rfl
lemma source_inverse (J : K.E → R) (s : FieldState K R) :
    source (-J) (source J s) = s := by
  apply FieldState.ext <;> simp [source]

lemma dot_add_right (a b c : K.E → R) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]
lemma dot_add_left (a b c : K.E → R) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]
lemma dot_comm (a b : K.E → R) : dot a b = dot b a := by
  simp [dot, mul_comm]
lemma dot_face (a : K.E → R) (p : K.F) (b : R) :
    dot a (faceImpulse p b) = K.curl a p * b := by
  rw [dot, faceImpulse, ← K.sum_curl_mul]
  simp [Pi.single_apply]
lemma dot_single (a : K.E → R) (e : K.E) (b : R) :
    dot a (Pi.single e b) = a e * b := by
  simp [dot, Pi.single_apply]
lemma face_canonical (p : K.F) (k : R) (u v : Tangent K R) :
    omega (faceTangent p k u) (faceTangent p k v) = omega u v := by
  simp only [omega, faceTangent, dot_add_right, dot_add_left]
  rw [dot_comm (faceImpulse p (k * K.curl u.1 p)) v.1, dot_face, dot_face]
  ring
lemma move_canonical (e : K.E) (k : R) (u v : Tangent K R) :
    omega (moveTangent e k u) (moveTangent e k v) = omega u v := by
  simp only [omega, moveTangent, dot_add_right, dot_add_left]
  rw [dot_comm (Pi.single e (k * u.2 e)) v.2, dot_single, dot_single]
  ring

inductive Instruction (K : Canvas) (R : Type)
  | face : K.F → R → Instruction K R
  | move : K.E → R → Instruction K R
  | current : K.E → R → Instruction K R
  | hold : Instruction K R

def execute (g : Instruction K R) (s : FieldState K R) : FieldState K R :=
  match g with
  | .face p k => faceKick p k s
  | .move e k => edgeMove e k s
  | .current e j => source (Pi.single e j) s
  | .hold => s

def linearize (g : Instruction K R) (u : Tangent K R) : Tangent K R :=
  match g with
  | .face p k => faceTangent p k u
  | .move e k => moveTangent e k u
  | .current _ _ => u
  | .hold => u

def run : List (Instruction K R) → FieldState K R → FieldState K R
  | [], s => s
  | g :: w, s => run w (execute g s)

def tangentRun : List (Instruction K R) → Tangent K R → Tangent K R
  | [], s => s
  | g :: w, s => tangentRun w (linearize g s)

lemma run_defect (w : List (Instruction K R)) (s : FieldState K R) :
    defect (run w s) = defect s := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih =>
    rw [run, ih]
    cases g with
    | face p k => exact face_defect p k s
    | move e k => rfl
    | current e j => exact source_defect _ s
    | hold => rfl
lemma run_gauge (w : List (Instruction K R)) (φ : K.V → R) (s : FieldState K R) :
    run w (gauge φ s) = gauge φ (run w s) := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih =>
    change run w (execute g (gauge φ s)) = gauge φ (run w (execute g s))
    have hg : execute g (gauge φ s) = gauge φ (execute g s) := by
      cases g with
      | face p k => exact face_gauge p k φ s
      | move e k => exact move_gauge e k φ s
      | current e j => rfl
      | hold => rfl
    rw [hg, ih]
lemma run_canonical (w : List (Instruction K R)) (u v : Tangent K R) :
    omega (tangentRun w u) (tangentRun w v) = omega u v := by
  induction w generalizing u v with
  | nil => rfl
  | cons g w ih =>
    rw [tangentRun, tangentRun, ih]
    cases g with
    | face p k => exact face_canonical p k u v
    | move e k => exact move_canonical e k u v
    | current e j => rfl
    | hold => rfl
def perturb (s : FieldState K R) (u : Tangent K R) : FieldState K R :=
  ⟨s.A + u.1, s.E + u.2, s.ρ⟩
lemma execute_perturb (g : Instruction K R) (s : FieldState K R) (u : Tangent K R) :
    execute g (perturb s u) = perturb (execute g s) (linearize g u) := by
  cases g with
  | face p k =>
    apply FieldState.ext
    · rfl
    · funext e
      simp only [execute, faceKick, perturb, linearize, faceTangent, Pi.add_apply,
        Canvas.curl_add, faceImpulse_apply]
      ring
    · rfl
  | move e k =>
    apply FieldState.ext
    · funext j
      simp only [execute, edgeMove, perturb, linearize, moveTangent, Pi.add_apply,
        Pi.single_apply]
      split_ifs <;> ring
    · rfl
    · rfl
  | current e j =>
    apply FieldState.ext <;> simp [execute, source, perturb, linearize, sub_add_eq_add_sub]
  | hold => rfl
lemma run_perturb (w : List (Instruction K R)) (s : FieldState K R) (u : Tangent K R) :
    run w (perturb s u) = perturb (run w s) (tangentRun w u) := by
  induction w generalizing s u with
  | nil => rfl
  | cons g w ih =>
    rw [run, execute_perturb, ih]
    rfl

def inverseInstruction : Instruction K R → Instruction K R
  | .face p k => .face p (-k)
  | .move e k => .move e (-k)
  | .current e j => .current e (-j)
  | .hold => .hold
lemma inverse_execute (g : Instruction K R) (s : FieldState K R) :
    execute (inverseInstruction g) (execute g s) = s := by
  cases g with
  | face p k => exact face_inverse p k s
  | move e k => exact move_inverse e k s
  | current e j =>
    have hp : Pi.single e (-j) = -(Pi.single e j : K.E → R) := by
      funext i; simp only [Pi.single_apply, Pi.neg_apply]; split_ifs <;> simp
    change source (Pi.single e (-j)) (source (Pi.single e j) s) = s
    rw [hp, source_inverse]
  | hold => rfl
lemma run_append (u v : List (Instruction K R)) (s : FieldState K R) :
    run (u ++ v) s = run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons g u ih => exact ih (execute g s)
lemma run_inverse (w : List (Instruction K R)) (s : FieldState K R) :
    run (w.reverse.map inverseInstruction) (run w s) = s := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, run_append,
      run, ih, inverse_execute]

@[simp] lemma inverseInstruction_invol (g : Instruction K R) :
    inverseInstruction (inverseInstruction g) = g := by cases g <;> simp [inverseInstruction]
lemma inverse_word_invol (w : List (Instruction K R)) :
    (w.reverse.map inverseInstruction).reverse.map inverseInstruction = w := by
  simp [List.map_reverse, List.map_map, Function.comp_def]
lemma run_inverse_other (w : List (Instruction K R)) (s : FieldState K R) :
    run w (run (w.reverse.map inverseInstruction) s) = s := by
  simpa only [inverse_word_invol] using run_inverse (w.reverse.map inverseInstruction) s
lemma tangent_gauss (w : List (Instruction K R)) (u : Tangent K R) :
    K.div (tangentRun w u).2 = K.div u.2 := by
  induction w generalizing u with
  | nil => rfl
  | cons g w ih =>
    rw [tangentRun, ih]
    cases g <;> simp [linearize, faceTangent, moveTangent, faceImpulse]

end Artform.Scores.Gauge
