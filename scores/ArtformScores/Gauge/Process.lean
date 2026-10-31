import ArtformScores.Gauge.Defs
import ArtformTextbook.Ch05.Defs.Steps
/-! # Owned local profiles and a total periodic realizer -/

set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Gauge
open Artform
inductive Position (K : Canvas)
  | potential : K.E → Position K
  | electric : K.E → Position K
  | charge : K.V → Position K

abbrev frame (K : Canvas) (R : Type) : Presentation := ⟨Position K, fun _ => R⟩
def encode {K : Canvas} {R : Type} (s : FieldState K R) : (frame K R).Table
  | .potential e => s.A e
  | .electric e => s.E e
  | .charge v => s.ρ v
def decode {K : Canvas} {R : Type} (x : (frame K R).Table) : FieldState K R :=
  ⟨fun e => x (.potential e), fun e => x (.electric e), fun v => x (.charge v)⟩
@[simp] lemma decode_encode {K : Canvas} {R : Type} (s : FieldState K R) :
    decode (encode s) = s := rfl
@[simp] lemma encode_decode {K : Canvas} {R : Type} (x : (frame K R).Table) :
    encode (decode x) = x := by funext p; cases p <;> rfl

variable {K : Canvas} {R : Type} [CommRing R]
def writes (g : Instruction K R) : Set (Position K) := fun q =>
  match g, q with
  | .face p _, .electric e => K.inc e p ≠ 0
  | .move e _, .potential f => f = e
  | .current e _, .electric f => f = e
  | .current e _, .charge v => K.src e = v ∨ K.tgt e = v
  | _, _ => False

def reads (g : Instruction K R) : Set (Position K) := fun q =>
  writes g q ∨ match g, q with
  | .face p _, .potential e => K.inc e p ≠ 0
  | .move e _, .electric f => f = e
  | _, _ => False

lemma curl_reads (p : K.F) (k : R) (x y : (frame K R).Table)
    (h : ∀ q ∈ reads (.face p k), x q = y q) :
    K.curl (decode x).A p = K.curl (decode y).A p := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : K.inc e p = 0
  · simp [he]
  · rw [show (decode x).A e = (decode y).A e from h (.potential e) (Or.inr he)]

lemma proposal_reads (g : Instruction K R) (x y : (frame K R).Table)
    (h : ∀ q ∈ reads g, x q = y q) (q : Position K) (hq : q ∈ writes g) :
    encode (execute g (decode x)) q = encode (execute g (decode y)) q := by
  have hq' := h q (Or.inl hq)
  cases g with
  | face p k =>
    have hc : K.curl (decode x).A p = K.curl (decode y).A p :=
      curl_reads p k x y h
    cases q with
    | potential e => exact False.elim hq
    | charge v => exact False.elim hq
    | electric e => simp only [encode, execute, faceKick, Pi.add_apply, decode,
        faceImpulse_apply] at *; rw [hq', hc]
  | move e k =>
    have he := h (.electric e) (Or.inr rfl)
    cases q with
    | electric f => exact False.elim hq
    | charge v => exact False.elim hq
    | potential f =>
      simp only [encode, execute, edgeMove, Pi.add_apply, Pi.single_apply, decode]
      change x (.potential f) = y (.potential f) at hq'
      change x (.electric e) = y (.electric e) at he
      rw [hq', he]
  | current e j =>
    cases q with
    | potential f => exact False.elim hq
    | electric f =>
      simpa only [encode, execute, source, decode, Pi.sub_apply] using
        (congrArg (fun r : R => r - (Pi.single e j : K.E → R) f) hq')
    | charge v =>
      simpa only [encode, execute, source, decode, Pi.sub_apply] using
        (congrArg (fun r : R => r - K.div (Pi.single e j) v) hq')
  | hold => exact False.elim hq

lemma proposal_frame (g : Instruction K R) (x : (frame K R).Table)
    (q : Position K) (hq : q ∉ writes g) : encode (execute g (decode x)) q = x q := by
  cases g with
  | face p k =>
    cases q with
    | potential e => rfl
    | charge v => rfl
    | electric e =>
      have he : K.inc e p = 0 := Classical.not_not.mp hq
      simp [encode, execute, faceKick, faceImpulse_apply, decode, he]
  | move e k =>
    cases q with
    | potential f => simp [encode, execute, edgeMove, decode,
        show e ≠ f from Ne.symm hq]
    | electric f => rfl
    | charge v => rfl
  | current e j =>
    cases q with
    | potential f => rfl
    | electric f => simp [encode, execute, source, decode,
        show e ≠ f from Ne.symm hq]
    | charge v =>
      have hv : ¬(K.src e = v ∨ K.tgt e = v) := hq
      have hd : K.div (Pi.single e j) v = 0 := by
        unfold Canvas.div
        apply Finset.sum_eq_zero
        intro f _
        by_cases hf : f = e
        · subst f; simp [ (not_or.mp hv).1, (not_or.mp hv).2]
        · simp [hf]
      simp [encode, execute, source, decode, hd]
  | hold => exact congrFun (encode_decode x) q

def profile (g : Instruction K R) : ProcessProfile (frame K R) where
  guard _ := True
  reads := reads g
  writes := writes g
  update x := encode (execute g (decode x))
  guard_reads _ _ _ := Iff.rfl
  update_reads := proposal_reads g

lemma profile_apply (g : Instruction K R) (x : (frame K R).Table) :
    (profile g).apply x = encode (execute g (decode x)) := by
  classical
  funext q
  change (if q ∈ writes g then encode (execute g (decode x)) q else x q) = _
  by_cases h : q ∈ writes g
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact (proposal_frame g x q h).symm

lemma execute_defect (g : Instruction K R) (s : FieldState K R) :
    defect (execute g s) = defect s := by
  cases g with
  | face p k => exact face_defect p k s
  | move e k => rfl
  | current e j => exact source_defect _ s
  | hold => rfl

def law (w : List (Instruction K R)) : LawInSteps (frame K R) where
  Step := Fin (w.length+1)
  moves i := [profile (w[i.val]?.getD .hold)]
  invariants := [⟨fun x => defect (decode x) = 0, Set.univ⟩]
  score :=
    { opens t := ⟨t % (w.length+1), Nat.mod_lt _ (by omega)⟩
      allowsEmpty _ := False
      period := w.length+1
      period_pos := by omega
      repeats t := by
        constructor
        · apply Fin.ext; simp
        · rfl }
  moves_legal t x hx u hu _ J hJ _ := by
    simp only [List.mem_singleton] at hu hJ
    subst u
    subst J
    have hd : defect (decode x) = 0 := hx _ (List.mem_singleton_self _) trivial
    simpa only [profile_apply, decode_encode, execute_defect] using hd

lemma law_legal (w : List (Instruction K R)) (t : ℕ) (x : (frame K R).Table) :
    (law w).LegalAt t x ↔ defect (decode x) = 0 := by
  simp [LawInSteps.LegalAt, law]

def singletonBatch (g : Instruction K R) (x : (frame K R).Table) : Batch (frame K R) x :=
  ⟨[⟨profile g, trivial⟩], by simp⟩
lemma singleton_apply (g : Instruction K R) (x : (frame K R).Table) :
    (singletonBatch g x).apply = encode (execute g (decode x)) := profile_apply g x

def realizer (w : List (Instruction K R)) : (law w).DetRealizer where
  select t x := singletonBatch (w[t % (w.length+1)]?.getD .hold) x
  allows t x _ a ha := by
    simp only [singletonBatch, List.mem_singleton] at ha
    subst a
    exact List.mem_singleton_self _
  keeps t x hx := by
    rw [law_legal] at hx ⊢
    simpa only [singleton_apply, decode_encode, execute_defect] using hx

lemma realizer_wellPosed (w : List (Instruction K R)) : (realizer w).WellPosed where
  total _ _ _ _ := List.cons_ne_nil _ _
  orderFree t x _ l hl := by
    have he := hl.eq_singleton
    subst l
    rfl

lemma realizer_slot (w : List (Instruction K R)) (t : ℕ) (s : FieldState K R) :
    ((realizer w).select t (encode s)).apply =
      encode (execute (w[t % (w.length+1)]?.getD .hold) s) := by
  exact singleton_apply _ _

def history (w : List (Instruction K R)) (s : FieldState K R) : ℕ → FieldState K R
  | 0 => s
  | n+1 => decode (((realizer w).select n (encode (history w s n))).apply)
lemma history_prefix (w : List (Instruction K R)) (s : FieldState K R) (n : ℕ)
    (hn : n ≤ w.length) : history w s n=run (w.take n) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < w.length := by omega
    rw [history, realizer_slot, decode_encode, ih (by omega), Nat.mod_eq_of_lt (by omega),
      List.getElem?_eq_getElem hlt, Option.getD_some,
      List.take_succ_eq_append_getElem hlt, run_append]
    rfl
lemma history_cycle (w : List (Instruction K R)) (s : FieldState K R) :
    history w s (law w).score.period = run w s := by
  change history w s (w.length+1) = _
  rw [history, realizer_slot, decode_encode, Nat.mod_eq_of_lt (by omega),
    List.getElem?_length, Option.getD_none]
  change history w s w.length=run w s
  rw [history_prefix w s w.length (le_refl _), List.take_length]

end Artform.Scores.Gauge
