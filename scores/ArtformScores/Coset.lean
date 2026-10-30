import Mathlib

/-!
# Coset tables with certificates

An upper bound for the cosets of a subgroup `H`, checked by computation. A coset
table has the rows `0, …, n - 1`, the action of each generator and of its inverse
on them, and a word `r_i` for each row, with `r_0` empty. An edge `(i, a)` leads
from row `i` along the generator `a` to a row `j`, and is good when
`H r_i a = H r_j`. The certificate makes every edge good in one of three ways.
- A tree edge: `r_j = r_i a`, or `r_i = r_j a⁻¹`.
- The subgroup edge: `i = 0`, `a ∈ H` and `j = 0`.
- A deduction at time `t` from a relator `ρ`: traced from a row `c`, `ρ` comes back
  to `c`, and every other edge on the way is justified at an earlier time. Since
  `ρ = 1`, the remaining edge is good as well.

`check` tests all of this, and `cover_of_check` concludes that right
multiplication by any word sends each coset `H r_i` to some `H r_j`. Starting from
`H r_0 = H`, every element lies in one of the `n` cosets. The deductions are those
of Todd–Coxeter coset enumeration.
-/

namespace Artform.Scores.Coset

section Words

variable {G : Type*} [Group G] {ι : Type*}

/-- A letter `(a, true)` is the generator `a`, and `(a, false)` its inverse. -/
def letter (gen : ι → G) : ι × Bool → G
  | (a, true) => gen a
  | (a, false) => (gen a)⁻¹

/-- The product of a word, letter by letter from the left. -/
def evalWord (gen : ι → G) (w : List (ι × Bool)) : G := (w.map (letter gen)).prod

@[simp] theorem evalWord_nil (gen : ι → G) : evalWord gen [] = 1 := rfl

@[simp] theorem evalWord_cons (gen : ι → G) (x : ι × Bool) (w : List (ι × Bool)) :
    evalWord gen (x :: w) = letter gen x * evalWord gen w := rfl

@[simp] theorem evalWord_append (gen : ι → G) (v w : List (ι × Bool)) :
    evalWord gen (v ++ w) = evalWord gen v * evalWord gen w := by
  simp [evalWord]

theorem map_evalWord {G' : Type*} [Group G'] (φ : G →* G') (gen : ι → G) (w : List (ι × Bool)) :
    φ (evalWord gen w) = evalWord (φ ∘ gen) w := by
  induction w with
  | nil => simp
  | cons x w ih => obtain ⟨a, _ | _⟩ := x <;> simp [letter, ih]

/-- Free reduction of a word. -/
def reduceWord [DecidableEq ι] : List (ι × Bool) → List (ι × Bool)
  | [] => []
  | x :: w =>
    match reduceWord w with
    | [] => [x]
    | y :: w' => if x.1 = y.1 ∧ x.2 = !y.2 then w' else x :: y :: w'

theorem evalWord_reduceWord [DecidableEq ι] (gen : ι → G) (w : List (ι × Bool)) :
    evalWord gen (reduceWord w) = evalWord gen w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [evalWord_cons, ← ih]
    simp only [reduceWord]
    split
    · rename_i h; simp [h]
    · rename_i y w' h
      split
      · rename_i hc
        obtain ⟨a, b⟩ := x
        obtain ⟨c, d⟩ := y
        simp only at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases d <;> simp [h, letter]
      · simp [h]

end Words

/-- How an edge of a coset table is justified. -/
inductive Just
  /-- an edge of the tree of representatives -/
  | tree
  /-- a generator of the subgroup at the row of the subgroup -/
  | subgroup
  /-- deduced at time `t` from the relator `ρ` traced from the row `c`, the edge being its
  letter `k` -/
  | deduce (t ρ c k : ℕ)

def Just.time : Just → ℕ
  | .deduce t _ _ _ => t
  | _ => 0

/-- A coset table with its certificate: rows `0, …, n - 1`, the action of each generator
and of its inverse, a representative word for each row, a justification for each edge,
and the relators the deductions use. -/
structure Cert (ι : Type*) where
  n : ℕ
  fwd : ι → ℕ → ℕ
  bwd : ι → ℕ → ℕ
  word : ℕ → List (ι × Bool)
  just : ℕ → ι → Just
  rels : List (List (ι × Bool))

section Check

variable {ι : Type*} (C : Cert ι)

/-- The row a letter leads to. -/
def step (c : ℕ) : ι × Bool → ℕ
  | (a, true) => C.fwd a c
  | (a, false) => C.bwd a c

/-- The row of the edge a letter uses: the letter `(a, false)` at `c` uses the edge
`(bwd a c, a)`. -/
def edgeRow (c : ℕ) : ι × Bool → ℕ
  | (_, true) => c
  | (a, false) => C.bwd a c

/-- The end of the trace of `w` from `c`, when every edge on it is older than `t`. -/
def traceBelow (t : ℕ) : ℕ → List (ι × Bool) → Option ℕ
  | c, [] => some c
  | c, x :: w =>
    if (C.just (edgeRow C c x) x.1).time < t then traceBelow t (step C c x) w else none

variable [DecidableEq ι]

def checkDeduce (i : ℕ) (a : ι) (t ρ c k : ℕ) : Bool :=
  match C.rels[ρ]? with
  | none => false
  | some w =>
    match w[k]? with
    | none => false
    | some x =>
      decide (0 < t) && decide (c < C.n) && decide (x.1 = a) &&
        match traceBelow C t c (w.take k) with
        | none => false
        | some c' =>
          decide (edgeRow C c' x = i) &&
            match traceBelow C t (step C c' x) (w.drop (k + 1)) with
            | none => false
            | some c'' => decide (c'' = c)

def checkEdge (sub : List ι) (i : ℕ) (a : ι) : Bool :=
  match C.just i a with
  | .tree => decide (C.word (C.fwd a i) = C.word i ++ [(a, true)]) ||
      decide (C.word i = C.word (C.fwd a i) ++ [(a, false)])
  | .subgroup => decide (a ∈ sub) && decide (C.word i = []) && decide (C.fwd a i = i)
  | .deduce t ρ c k => checkDeduce C i a t ρ c k

/-- The check of a certificate: row `0` has the empty word, every column is a permutation
of the rows, and every edge is justified. -/
def check (gens sub : List ι) : Bool :=
  decide (0 < C.n) && decide (C.word 0 = []) &&
    (List.range C.n).all fun i => gens.all fun a =>
      decide (C.fwd a i < C.n) && decide (C.bwd a i < C.n) &&
        decide (C.bwd a (C.fwd a i) = i) && decide (C.fwd a (C.bwd a i) = i) &&
          checkEdge C sub i a

end Check

theorem check_n_pos {ι : Type*} [DecidableEq ι] {C : Cert ι} {gens sub : List ι}
    (h : check C gens sub = true) : 0 < C.n := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem check_word_zero {ι : Type*} [DecidableEq ι] {C : Cert ι} {gens sub : List ι}
    (h : check C gens sub = true) : C.word 0 = [] := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

section Sound

variable {G : Type*} [Group G] {ι : Type*} (gen : ι → G) (H : Subgroup G) (C : Cert ι)

/-- The representative of a row. -/
def rep (i : ℕ) : G := evalWord gen (C.word i)

/-- The edge `(i, a)` is good when `H r_i a = H r_j`, `j` the row it leads to. -/
def Good (i : ℕ) (a : ι) : Prop := rep gen C i * gen a * (rep gen C (C.fwd a i))⁻¹ ∈ H

variable {gen H C}

theorem traceBelow_good {t : ℕ} (hrange : ∀ i < C.n, ∀ a, C.fwd a i < C.n ∧ C.bwd a i < C.n ∧
      C.bwd a (C.fwd a i) = i ∧ C.fwd a (C.bwd a i) = i)
    (hgood : ∀ i < C.n, ∀ a, (C.just i a).time < t → Good gen H C i a) :
    ∀ (w : List (ι × Bool)) (c c' : ℕ), c < C.n → traceBelow C t c w = some c' →
      c' < C.n ∧ rep gen C c * evalWord gen w * (rep gen C c')⁻¹ ∈ H := by
  intro w
  induction w with
  | nil =>
    intro c c' hc h
    simp only [traceBelow, Option.some.injEq] at h
    subst h
    simp [hc]
  | cons x w ih =>
    intro c c' hc h
    simp only [traceBelow] at h
    split at h
    · rename_i ht
      obtain ⟨hd, hw⟩ := ih _ _ (by obtain ⟨a, _ | _⟩ := x <;> simp [step, hrange c hc a]) h
      refine ⟨hd, ?_⟩
      have key : rep gen C c * letter gen x * (rep gen C (step C c x))⁻¹ ∈ H := by
        obtain ⟨a, _ | _⟩ := x
        · have hb := hrange c hc a
          have := hgood _ hb.2.1 a ht
          simp only [Good] at this
          rw [hb.2.2.2] at this
          simpa [letter, step, mul_assoc] using H.inv_mem this
        · exact hgood c hc a ht
      have := H.mul_mem key hw
      simpa [mul_assoc] using this
    · simp at h

variable [DecidableEq ι]

theorem checkDeduce_good {i : ℕ} {a : ι} {t ρ c k : ℕ}
    (hrange : ∀ i < C.n, ∀ a, C.fwd a i < C.n ∧ C.bwd a i < C.n ∧
      C.bwd a (C.fwd a i) = i ∧ C.fwd a (C.bwd a i) = i)
    (hrels : ∀ w ∈ C.rels, evalWord gen w = 1)
    (hgood : ∀ i < C.n, ∀ a, (C.just i a).time < t → Good gen H C i a)
    (h : checkDeduce C i a t ρ c k = true) : Good gen H C i a := by
  unfold checkDeduce at h
  split at h
  · simp at h
  rename_i w hw
  split at h
  · simp at h
  rename_i x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hc⟩, hxa⟩, h⟩ := h
  split at h
  · simp at h
  rename_i c' hα
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hedge, h⟩ := h
  split at h
  · simp at h
  rename_i c'' hβ
  simp only [decide_eq_true_eq] at h
  rw [h] at hβ
  have hw1 : evalWord gen w = 1 := hrels w (List.mem_of_getElem? hw)
  have hsplit : w = w.take k ++ x :: w.drop (k + 1) := by
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  obtain ⟨hc', h1⟩ := traceBelow_good hrange hgood _ _ _ hc hα
  have hd : step C c' x < C.n := by obtain ⟨b, _ | _⟩ := x <;> simp [step, hrange c' hc' b]
  obtain ⟨-, h2⟩ := traceBelow_good hrange hgood _ _ _ hd hβ
  have hrel : evalWord gen (w.take k) * letter gen x * evalWord gen (w.drop (k + 1)) = 1 := by
    have e : evalWord gen w = evalWord gen (w.take k ++ x :: w.drop (k + 1)) := congrArg _ hsplit
    rw [hw1, evalWord_append, evalWord_cons] at e
    rw [mul_assoc]
    exact e.symm
  obtain ⟨b, _ | _⟩ := x
  · simp only at hxa
    subst hxa
    simp only [edgeRow] at hedge
    subst hedge
    simp only [step] at h2
    have hb := (hrange c' hc' b).2.2.2
    rw [Good, hb]
    simp only [letter] at hrel
    have key : rep gen C (C.bwd b c') * gen b * (rep gen C c')⁻¹ =
        ((rep gen C c * evalWord gen (w.take k) * (rep gen C c')⁻¹)⁻¹ *
          (rep gen C c * (evalWord gen (w.take k) * (gen b)⁻¹ * evalWord gen (w.drop (k + 1))) *
            (rep gen C c)⁻¹) *
          (rep gen C (C.bwd b c') * evalWord gen (w.drop (k + 1)) * (rep gen C c)⁻¹)⁻¹)⁻¹ := by
      group
    rw [key, hrel, mul_one, mul_inv_cancel, mul_one]
    exact H.inv_mem (H.mul_mem (H.inv_mem h1) (H.inv_mem h2))
  · simp only at hxa
    subst hxa
    simp only [edgeRow] at hedge
    subst hedge
    simp only [step] at h2
    rw [Good]
    simp only [letter] at hrel
    have key : rep gen C c' * gen b * (rep gen C (C.fwd b c'))⁻¹ =
        (rep gen C c * evalWord gen (w.take k) * (rep gen C c')⁻¹)⁻¹ *
          (rep gen C c * (evalWord gen (w.take k) * gen b * evalWord gen (w.drop (k + 1))) *
            (rep gen C c)⁻¹) *
          (rep gen C (C.fwd b c') * evalWord gen (w.drop (k + 1)) * (rep gen C c)⁻¹)⁻¹ := by
      group
    rw [key, hrel, mul_one, mul_inv_cancel, mul_one]
    exact H.mul_mem (H.inv_mem h1) (H.inv_mem h2)

theorem range_of_check {gens sub : List ι} (hgens : ∀ a, a ∈ gens) (h : check C gens sub = true) :
    ∀ i < C.n, ∀ a, C.fwd a i < C.n ∧ C.bwd a i < C.n ∧
      C.bwd a (C.fwd a i) = i ∧ C.fwd a (C.bwd a i) = i := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  intro i hi a
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h.2 i hi a (hgens a)
  exact ⟨h1, h2, h3, h4⟩

/-- Every edge of a checked certificate is good. -/
theorem good_of_check {gens sub : List ι} (hgens : ∀ a, a ∈ gens) (hsub : ∀ a ∈ sub, gen a ∈ H)
    (hrels : ∀ w ∈ C.rels, evalWord gen w = 1) (h : check C gens sub = true) :
    ∀ i < C.n, ∀ a, Good gen H C i a := by
  have hrange := range_of_check hgens h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  have hedge : ∀ i < C.n, ∀ a, checkEdge C sub i a = true := fun i hi a =>
    (h.2 i hi a (hgens a)).2
  suffices ∀ t, ∀ i < C.n, ∀ a, (C.just i a).time = t → Good gen H C i a from
    fun i hi a => this _ i hi a rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i hi a ht
  have hgood : ∀ j < C.n, ∀ b, (C.just j b).time < t → Good gen H C j b :=
    fun j hj b hb => ih _ (ht ▸ hb) j hj b rfl
  have he := hedge i hi a
  unfold checkEdge at he
  split at he
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at he
    rcases he with he | he
    · simp [Good, rep, he, letter]
    · simp [Good, rep, he, letter]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨ha, hw⟩, hf⟩ := he
    simp [Good, rep, hw, hf, hsub a ha]
  · rename_i t' ρ c k hj
    rw [hj] at ht
    simp only [Just.time] at ht
    subst ht
    exact checkDeduce_good hrange hrels hgood he

/-- The cosets `H r_j` of a checked certificate are closed under every word. -/
theorem cover_of_check {gens sub : List ι} (hgens : ∀ a, a ∈ gens) (hsub : ∀ a ∈ sub, gen a ∈ H)
    (hrels : ∀ w ∈ C.rels, evalWord gen w = 1) (h : check C gens sub = true) (v : FreeGroup ι) :
    ∀ i < C.n, ∃ j < C.n, rep gen C i * FreeGroup.lift gen v * (rep gen C j)⁻¹ ∈ H := by
  have hgood := good_of_check hgens hsub hrels h
  have hrange := range_of_check hgens h
  induction v using FreeGroup.induction_on with
  | one => exact fun i hi => ⟨i, hi, by simp⟩
  | of x => exact fun i hi => ⟨C.fwd x i, (hrange i hi x).1, by simpa [Good] using hgood i hi x⟩
  | inv_of x _ =>
    intro i hi
    refine ⟨C.bwd x i, (hrange i hi x).2.1, ?_⟩
    have := hgood _ (hrange i hi x).2.1 x
    rw [Good, (hrange i hi x).2.2.2] at this
    simpa [mul_assoc] using H.inv_mem this
  | mul v₁ v₂ h₁ h₂ =>
    intro i hi
    obtain ⟨j, hj, hj'⟩ := h₁ i hi
    obtain ⟨k, hk, hk'⟩ := h₂ j hj
    exact ⟨k, hk, by simpa [mul_assoc] using H.mul_mem hj' hk'⟩

end Sound

end Artform.Scores.Coset
