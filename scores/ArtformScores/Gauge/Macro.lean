import ArtformScores.Gauge.Defs
/-! # Exact K-then-M native Maxwell compilation -/

set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Gauge
open Artform
variable {K : Canvas} {R : Type} [CommRing R]
lemma run_faces (ps : List K.F) (s : FieldState K R) :
    run (ps.map (fun p => .face p 1)) s =
      ⟨s.A, s.E + (ps.map (fun p => faceImpulse p (K.curl s.A p))).sum, s.ρ⟩ := by
  induction ps generalizing s with
  | nil => simp [run]
  | cons p ps ih =>
    simp only [List.map_cons, run, execute, ih, faceKick, one_mul, List.sum_cons]
    congr 1
    abel
lemma run_moves (es : List K.E) (s : FieldState K R) :
    run (es.map (fun e => .move e (-1))) s =
      ⟨s.A - (es.map (fun e => Pi.single e (s.E e))).sum, s.E, s.ρ⟩ := by
  induction es generalizing s with
  | nil => simp [run]
  | cons e es ih =>
    simp only [List.map_cons, run, execute, ih, edgeMove, neg_one_mul, List.sum_cons]
    apply FieldState.ext
    · have hp : Pi.single e (-s.E e) = -(Pi.single e (s.E e) : K.E → R) := by
        funext j; simp only [Pi.single_apply, Pi.neg_apply]; split_ifs <;> simp
      dsimp
      rw [hp]
      abel
    · rfl
    · rfl
lemma run_currents (es : List K.E) (J : K.E → R) (s : FieldState K R) :
    run (es.map (fun e => .current e (J e))) s =
      source ((es.map (fun e => Pi.single e (J e))).sum) s := by
  induction es generalizing s with
  | nil => simp [run, source]
  | cons e es ih =>
    simp only [List.map_cons, run, execute, ih, List.sum_cons]
    apply FieldState.ext <;> simp only [source, Canvas.div_add] <;> abel

lemma enum_single {I : Type} [Fintype I] [DecidableEq I] (f : I → R) :
    ((Finset.univ.toList).map (fun i => Pi.single i (f i))).sum = f := by
  rw [Finset.sum_map_toList]
  funext i
  simp [Pi.single_apply]

lemma enum_faces (A : K.E → R) :
    ((Finset.univ.toList).map (fun p => faceImpulse p (K.curl A p))).sum =
      K.curlStar (K.curl A) := by
  rw [Finset.sum_map_toList]
  funext e
  simp [faceImpulse_apply, Canvas.curlStar]

def maxwellWord (K : Canvas) (J : K.E → R) : List (Instruction K R) :=
  (Finset.univ.toList.map (fun p => .face p 1)) ++
  (Finset.univ.toList.map (fun e => .current e (J e))) ++
  (Finset.univ.toList.map (fun e => .move e (-1)))

def fieldTick (J : K.E → R) (s : FieldState K R) : FieldState K R :=
  let ep := s.E + K.curlStar (K.curl s.A) - J
  ⟨s.A-ep,ep,s.ρ-K.div J⟩

lemma maxwell_word (J : K.E → R) (s : FieldState K R) :
    run (maxwellWord K J) s = fieldTick J s := by
  simp only [maxwellWord, run_append, run_faces, enum_faces, run_currents, enum_single,
    run_moves, source, fieldTick]

lemma fieldTick_native (J : K.E → ZMod 8) (s : FieldState K (ZMod 8)) :
    fieldTick J s =
      let t := maxwellTick K J ⟨s.A,s.E,s.ρ⟩
      ⟨t.A,t.E,t.ρ⟩ := rfl
end Artform.Scores.Gauge
