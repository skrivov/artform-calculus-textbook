import ArtformStages.BookBoard

/-!
# D17 on the dominos

Finding 449 of the research ledger on a layered universe put the charter's one rule in Lean as one
rule for the far weights, and left on paper the step to it from D17 itself. Here the step is taken
(finding 461 of the ledger). For a kick of reach 1 the reach of a line is its *domino*: the two
squares at the line, with their sides and their corners. A *naming* of the domino is a flag
`(σ, i)` of the line with a way of reading it: along the turn of `σ` (`true`), or turned over
(`false`), from the other end of the line.

* `Board.domino_corner_injective`, `Board.domino_line_injective`, `Board.domino_square_ne`,
  `Board.domino_gauge`, `Board.domino_incidence` (DM1): on a wide board, in every naming, the
  domino has six different corners, seven different lines and two different squares, and its gauge
  and its incidence, read with the naming's signs, are two fixed tables;
* `Board.domino_reach` (DM2): every square at the line is a named square, and every side and
  every corner of a named square is named;
* `Board.d17_oneRuleFar` (DM3): a kick that meets D17 meets one rule for the far weights;
* `Board.d17_classes`, `Board.d17_one_number`, `torus_d17` (DM4): so with A10, A11 and reach 1 the
  kick is `Cᵀ diag K C` with `K` one number on each class of squares, one number where every
  corner has one paint, and one number on the torus of sides at least 3;
* `Board.kick_rowRead`, `Board.kick_meets_d17` (DM5): the row of `Cᵀ diag K C` read in a naming;
  with one number `κ` it is the same in every naming, so `Cᵀ diag κ C` meets D17.
-/

open Matrix

namespace Artform.Stages

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- The places of the six named corners when the domino is turned over: the ends of the line
change places. -/
def reflCorner : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- The places of the seven named lines when the domino is turned over. -/
def reflLine : Fin 7 → Fin 7 := ![0, 3, 2, 1, 6, 5, 4]

/-- The named corner where each named line ends, in the order of the naming. -/
def dominoHead : Fin 7 → Fin 6 := ![1, 2, 3, 0, 4, 5, 1]

/-- The named corner where each named line starts, in the order of the naming. -/
def dominoTail : Fin 7 → Fin 6 := ![0, 1, 2, 3, 0, 4, 5]

/-- The gauge table of a domino: `1` where a named line ends, `-1` where it starts. -/
def dominoGauge (r : Fin 7) (p : Fin 6) : ℝ :=
  (if dominoHead r = p then 1 else 0) - (if dominoTail r = p then 1 else 0)

/-- The incidence table of a domino: the first square has the lines `0` to `3` along its turn,
the second has the line `0` against it and the lines `4` to `6` along it. -/
def dominoIncidence : Fin 2 → Fin 7 → ℝ :=
  ![![1, 1, 1, 1, 0, 0, 0], ![-1, 0, 0, 0, 1, 1, 1]]

/-- The six named corners of the flag `(σ, i)`, read along: the corners of `σ` from `i` in its
turn, then the two far corners of the other square at the line. -/
noncomputable def alongCorner (σ : f) (i : Fin 4) : Fin 6 → v :=
  ![B.corner σ i, B.corner σ (i + 1), B.corner σ (i + 2), B.corner σ (i + 3),
    B.corner (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 2),
    B.corner (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 3)]

/-- The seven named lines of the flag `(σ, i)`, read along: the line, the other sides of `σ`,
then the other sides of the other square. -/
noncomputable def alongLine (σ : f) (i : Fin 4) : Fin 7 → e :=
  ![B.side σ i, B.side σ (i + 1), B.side σ (i + 2), B.side σ (i + 3),
    B.side (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 1),
    B.side (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 2),
    B.side (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 3)]

/-- The signs of the named lines, read along: `1` along the turn of their square, `-1`
against it. -/
noncomputable def alongSign (σ : f) (i : Fin 4) : Fin 7 → ℝ :=
  ![turnSign (B.along σ i), turnSign (B.along σ (i + 1)), turnSign (B.along σ (i + 2)),
    turnSign (B.along σ (i + 3)),
    turnSign (B.along (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 1)),
    turnSign (B.along (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 2)),
    turnSign (B.along (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 3))]

/-- The named corners of the naming of `(σ, i)` read along (`true`) or turned over (`false`). -/
noncomputable def namedCorner (σ : f) (i : Fin 4) : Bool → Fin 6 → v
  | true => B.alongCorner σ i
  | false => fun p => B.alongCorner σ i (reflCorner p)

/-- The named lines of a naming. -/
noncomputable def namedLine (σ : f) (i : Fin 4) : Bool → Fin 7 → e
  | true => B.alongLine σ i
  | false => fun r => B.alongLine σ i (reflLine r)

/-- The signs of the named lines of a naming: turned over, every sign is changed. -/
noncomputable def namedSign (σ : f) (i : Fin 4) : Bool → Fin 7 → ℝ
  | true => B.alongSign σ i
  | false => fun r => -B.alongSign σ i (reflLine r)

/-- The two named squares of the flag `(σ, i)`: `σ`, and the other square at its side `i`. -/
noncomputable def namedSquare (σ : f) (i : Fin 4) : Fin 2 → f := ![σ, (B.otherFlag σ i).1]

/-- The sign of the squares of a naming: turned over, it is changed. -/
def squareSign : Bool → ℝ
  | true => 1
  | false => -1

/-- The six paints of a naming: the paints of its six named corners. -/
noncomputable def namedPaints [Fintype f] [DecidableEq v] (σ : f) (i : Fin 4) (b : Bool) :
    Fin 6 → ℕ :=
  fun p => B.paint (B.namedCorner σ i b p)

/-- The row of a kick read in a naming: its weight from the named line `0` to each named line,
times the signs of the two lines. -/
noncomputable def rowRead (M : Matrix e e ℝ) (σ : f) (i : Fin 4) (b : Bool) (r : Fin 7) : ℝ :=
  M (B.namedLine σ i b 0) (B.namedLine σ i b r) * B.namedSign σ i b 0 * B.namedSign σ i b r

/-- **D17 for a kick.** Any two namings with the same six paints have the same row read. -/
def D17Kick [Fintype f] [DecidableEq v] (M : Matrix e e ℝ) : Prop :=
  ∀ (σ : f) (i : Fin 4) (b : Bool) (τ : f) (j : Fin 4) (c : Bool),
    B.namedPaints σ i b = B.namedPaints τ j c → B.rowRead M σ i b = B.rowRead M τ j c

/-- The other flag runs along the same line the other way, so its corners at its side are the
corners `i + 1` and `i` of `σ`. -/
theorem otherFlag_corner (σ : f) (i : Fin 4) :
    B.corner (B.otherFlag σ i).1 (B.otherFlag σ i).2 = B.corner σ (i + 1) ∧
      B.corner (B.otherFlag σ i).1 ((B.otherFlag σ i).2 + 1) = B.corner σ i := by
  have hs := B.otherFlag_side σ i
  have ha := B.otherFlag_along σ i
  have ht := congrArg B.tail hs
  have hh := congrArg B.head hs
  rw [B.tail_side, B.tail_side, ha] at ht
  rw [B.head_side, B.head_side, ha] at hh
  cases hb : B.along σ i <;>
    simp only [hb, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] at ht hh
  · exact ⟨ht, hh⟩
  · exact ⟨hh, ht⟩

/-- The other flag runs the other way. -/
theorem otherFlag_along_ne (σ : f) (i : Fin 4) :
    B.along σ i ≠ B.along (B.otherFlag σ i).1 (B.otherFlag σ i).2 := by
  rw [B.otherFlag_along]
  cases B.along σ i <;> decide

/-- **DM1.** The two named squares are different. -/
theorem domino_square_ne (σ : f) (i : Fin 4) : B.namedSquare σ i 0 ≠ B.namedSquare σ i 1 := by
  have hs := B.otherFlag_side σ i
  have hne := B.otherFlag_along_ne σ i
  simp only [namedSquare, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize B.otherFlag σ i = T at hs hne ⊢
  obtain ⟨τ, j⟩ := T
  dsimp only at hs hne ⊢
  rintro rfl
  exact hne (by rw [B.side_injective σ hs])

/-- **DM2.** Every square at the line is a named square, and every side and every corner of a named
square is a named line or a named corner. -/
theorem domino_reach (σ : f) (i : Fin 4) :
    (∀ τ a, B.side τ a = B.side σ i → τ = B.namedSquare σ i 0 ∨ τ = B.namedSquare σ i 1) ∧
      (∀ k a, ∃ r, B.side (B.namedSquare σ i k) a = B.namedLine σ i true r) ∧
      (∀ k a, ∃ p, B.corner (B.namedSquare σ i k) a = B.namedCorner σ i true p) := by
  have hs := B.otherFlag_side σ i
  have hne := B.otherFlag_along_ne σ i
  have hc := B.otherFlag_corner σ i
  simp only [namedSquare, namedLine, namedCorner, alongLine, alongCorner]
  generalize B.otherFlag σ i = T at hs hne hc ⊢
  obtain ⟨τ, j⟩ := T
  dsimp only at hs hne hc ⊢
  have split : ∀ x y : Fin 4, ∃ d : Fin 4, y = x + d := fun x y => ⟨y - x, by abel⟩
  refine ⟨fun ρ a h => ?_, fun k a => ?_, fun k a => ?_⟩
  · rcases B.flag_cover hs.symm hne h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · fin_cases k
    · obtain ⟨d, rfl⟩ := split i a
      fin_cases d
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
    · obtain ⟨d, rfl⟩ := split j a
      fin_cases d
      · exact ⟨0, by simpa using hs⟩
      · exact ⟨4, by simp⟩
      · exact ⟨5, by simp⟩
      · exact ⟨6, by simp⟩
  · fin_cases k
    · obtain ⟨d, rfl⟩ := split i a
      fin_cases d
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
    · obtain ⟨d, rfl⟩ := split j a
      fin_cases d
      · exact ⟨1, by simpa using hc.1⟩
      · exact ⟨0, by simpa using hc.2⟩
      · exact ⟨4, by simp⟩
      · exact ⟨5, by simp⟩

variable {B}

/-- On a wide board the six named corners, read along, are six different corners. -/
theorem along_corner_injective (hW : B.Wide) (σ : f) (i : Fin 4) :
    Function.Injective (B.alongCorner σ i) := by
  have hs := B.otherFlag_side σ i
  have hne := B.otherFlag_along_ne σ i
  have hc := B.otherFlag_corner σ i
  unfold alongCorner
  generalize B.otherFlag σ i = T at hs hne hc ⊢
  obtain ⟨τ, j⟩ := T
  dsimp only at hs hne hc ⊢
  have iσ := B.corner_injective σ
  have iτ := B.corner_injective τ
  have k2 : ∀ x : Fin 4, x + 2 ≠ x ∧ x + 2 ≠ x + 1 := by decide
  have k3 : ∀ x : Fin 4, x + 3 ≠ x ∧ x + 3 ≠ x + 1 := by decide
  have a01 : ∀ x : Fin 4, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x ≠ x + 3 := by decide
  have a12 : ∀ x : Fin 4, x + 1 ≠ x + 2 ∧ x + 1 ≠ x + 3 ∧ x + 2 ≠ x + 3 := by decide
  have w2 : ∀ b, B.corner σ (i + 2) ≠ B.corner τ b := hW.corner_ne hs.symm hne (k2 i)
  have w3 : ∀ b, B.corner σ (i + 3) ≠ B.corner τ b := hW.corner_ne hs.symm hne (k3 i)
  have n01 : B.corner σ i ≠ B.corner σ (i + 1) := iσ.ne (a01 i).1
  have n02 : B.corner σ i ≠ B.corner σ (i + 2) := iσ.ne (a01 i).2.1
  have n03 : B.corner σ i ≠ B.corner σ (i + 3) := iσ.ne (a01 i).2.2
  have n12 : B.corner σ (i + 1) ≠ B.corner σ (i + 2) := iσ.ne (a12 i).1
  have n13 : B.corner σ (i + 1) ≠ B.corner σ (i + 3) := iσ.ne (a12 i).2.1
  have n23 : B.corner σ (i + 2) ≠ B.corner σ (i + 3) := iσ.ne (a12 i).2.2
  have n45 : B.corner τ (j + 2) ≠ B.corner τ (j + 3) := iτ.ne (a12 j).2.2
  have n24 := w2 (j + 2)
  have n25 := w2 (j + 3)
  have n34 := w3 (j + 2)
  have n35 := w3 (j + 3)
  have n04 : B.corner σ i ≠ B.corner τ (j + 2) := hc.2 ▸ iτ.ne (a12 j).1
  have n05 : B.corner σ i ≠ B.corner τ (j + 3) := hc.2 ▸ iτ.ne (a12 j).2.1
  have n14 : B.corner σ (i + 1) ≠ B.corner τ (j + 2) := hc.1 ▸ iτ.ne (a01 j).2.1
  have n15 : B.corner σ (i + 1) ≠ B.corner τ (j + 3) := hc.1 ▸ iτ.ne (a01 j).2.2
  intro p q h
  fin_cases p <;> fin_cases q <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at h <;>
    first
    | rfl
    | exact absurd h n01 | exact absurd h.symm n01 | exact absurd h n02 | exact absurd h.symm n02
    | exact absurd h n03 | exact absurd h.symm n03 | exact absurd h n12 | exact absurd h.symm n12
    | exact absurd h n13 | exact absurd h.symm n13 | exact absurd h n23 | exact absurd h.symm n23
    | exact absurd h n45 | exact absurd h.symm n45 | exact absurd h n24 | exact absurd h.symm n24
    | exact absurd h n25 | exact absurd h.symm n25 | exact absurd h n34 | exact absurd h.symm n34
    | exact absurd h n35 | exact absurd h.symm n35 | exact absurd h n04 | exact absurd h.symm n04
    | exact absurd h n05 | exact absurd h.symm n05 | exact absurd h n14 | exact absurd h.symm n14
    | exact absurd h n15 | exact absurd h.symm n15

/-- On a wide board the seven named lines, read along, are seven different lines. -/
theorem along_line_injective (hW : B.Wide) (σ : f) (i : Fin 4) :
    Function.Injective (B.alongLine σ i) := by
  have hs := B.otherFlag_side σ i
  have hne := B.otherFlag_along_ne σ i
  unfold alongLine
  generalize B.otherFlag σ i = T at hs hne ⊢
  obtain ⟨τ, j⟩ := T
  dsimp only at hs hne ⊢
  have iσ := B.side_injective σ
  have iτ := B.side_injective τ
  have a01 : ∀ x : Fin 4, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x ≠ x + 3 := by decide
  have a12 : ∀ x : Fin 4, x + 1 ≠ x + 2 ∧ x + 1 ≠ x + 3 ∧ x + 2 ≠ x + 3 := by decide
  have b0 : ∀ x : Fin 4, x + 1 ≠ x ∧ x + 2 ≠ x ∧ x + 3 ≠ x := by decide
  have w1 : ∀ k, B.side τ k ≠ B.side σ (i + 1) := hW.side_ne hs.symm hne (b0 i).1
  have w2 : ∀ k, B.side τ k ≠ B.side σ (i + 2) := hW.side_ne hs.symm hne (b0 i).2.1
  have w3 : ∀ k, B.side τ k ≠ B.side σ (i + 3) := hW.side_ne hs.symm hne (b0 i).2.2
  have n01 : B.side σ i ≠ B.side σ (i + 1) := iσ.ne (a01 i).1
  have n02 : B.side σ i ≠ B.side σ (i + 2) := iσ.ne (a01 i).2.1
  have n03 : B.side σ i ≠ B.side σ (i + 3) := iσ.ne (a01 i).2.2
  have n12 : B.side σ (i + 1) ≠ B.side σ (i + 2) := iσ.ne (a12 i).1
  have n13 : B.side σ (i + 1) ≠ B.side σ (i + 3) := iσ.ne (a12 i).2.1
  have n23 : B.side σ (i + 2) ≠ B.side σ (i + 3) := iσ.ne (a12 i).2.2
  have n45 : B.side τ (j + 1) ≠ B.side τ (j + 2) := iτ.ne (a12 j).1
  have n46 : B.side τ (j + 1) ≠ B.side τ (j + 3) := iτ.ne (a12 j).2.1
  have n56 : B.side τ (j + 2) ≠ B.side τ (j + 3) := iτ.ne (a12 j).2.2
  have n04 : B.side σ i ≠ B.side τ (j + 1) := hs ▸ iτ.ne (a01 j).1
  have n05 : B.side σ i ≠ B.side τ (j + 2) := hs ▸ iτ.ne (a01 j).2.1
  have n06 : B.side σ i ≠ B.side τ (j + 3) := hs ▸ iτ.ne (a01 j).2.2
  have m14 := w1 (j + 1)
  have m15 := w1 (j + 2)
  have m16 := w1 (j + 3)
  have m24 := w2 (j + 1)
  have m25 := w2 (j + 2)
  have m26 := w2 (j + 3)
  have m34 := w3 (j + 1)
  have m35 := w3 (j + 2)
  have m36 := w3 (j + 3)
  intro p q h
  fin_cases p <;> fin_cases q <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at h <;>
    first
    | rfl
    | exact absurd h n01 | exact absurd h.symm n01 | exact absurd h n02 | exact absurd h.symm n02
    | exact absurd h n03 | exact absurd h.symm n03 | exact absurd h n12 | exact absurd h.symm n12
    | exact absurd h n13 | exact absurd h.symm n13 | exact absurd h n23 | exact absurd h.symm n23
    | exact absurd h n45 | exact absurd h.symm n45 | exact absurd h n46 | exact absurd h.symm n46
    | exact absurd h n56 | exact absurd h.symm n56 | exact absurd h n04 | exact absurd h.symm n04
    | exact absurd h n05 | exact absurd h.symm n05 | exact absurd h n06 | exact absurd h.symm n06
    | exact absurd h m14 | exact absurd h.symm m14 | exact absurd h m15 | exact absurd h.symm m15
    | exact absurd h m16 | exact absurd h.symm m16 | exact absurd h m24 | exact absurd h.symm m24
    | exact absurd h m25 | exact absurd h.symm m25 | exact absurd h m26 | exact absurd h.symm m26
    | exact absurd h m34 | exact absurd h.symm m34 | exact absurd h m35 | exact absurd h.symm m35
    | exact absurd h m36 | exact absurd h.symm m36

/-- **DM1.** On a wide board, in every naming, the six named corners are six different corners. -/
theorem domino_corner_injective (hW : B.Wide) (σ : f) (i : Fin 4) (b : Bool) :
    Function.Injective (B.namedCorner σ i b) := by
  cases b
  · have hr : Function.Injective reflCorner := by decide
    exact (along_corner_injective hW σ i).comp hr
  · exact along_corner_injective hW σ i

/-- **DM1.** On a wide board, in every naming, the seven named lines are seven different lines. -/
theorem domino_line_injective (hW : B.Wide) (σ : f) (i : Fin 4) (b : Bool) :
    Function.Injective (B.namedLine σ i b) := by
  cases b
  · have hr : Function.Injective reflLine := by decide
    exact (along_line_injective hW σ i).comp hr
  · exact along_line_injective hW σ i

/-- The gauge table, read along. -/
theorem along_gauge [DecidableEq v] (hW : B.Wide) (σ : f) (i : Fin 4) (r : Fin 7) (p : Fin 6) :
    B.alongSign σ i r * B.gauge (B.alongLine σ i r) (B.alongCorner σ i p) = dominoGauge r p := by
  have inj := along_corner_injective hW σ i
  have key : ∀ w, B.alongSign σ i r * B.gauge (B.alongLine σ i r) w =
      (if B.alongCorner σ i (dominoHead r) = w then 1 else 0) -
        (if B.alongCorner σ i (dominoTail r) = w then 1 else 0) := by
    intro w
    have hc := B.otherFlag_corner σ i
    have e1 : ∀ x : Fin 4, x + 1 + 1 = x + 2 := by decide
    have e2 : ∀ x : Fin 4, x + 2 + 1 = x + 3 := by decide
    have e3 : ∀ x : Fin 4, x + 3 + 1 = x := by decide
    fin_cases r <;>
      simp only [alongSign, alongLine, alongCorner, dominoHead, dominoTail, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, B.gauge_side, ← mul_assoc,
        turnSign_mul_self, one_mul, e1, e2, e3, hc.1, hc.2] <;>
      congr 1
  rw [key]
  simp only [inj.eq_iff, dominoGauge]

/-- Turning the domino over changes the sign of its gauge table. -/
theorem dominoGauge_refl (r : Fin 7) (p : Fin 6) :
    dominoGauge (reflLine r) (reflCorner p) = -dominoGauge r p := by
  have h1 : ∀ r, dominoHead (reflLine r) = reflCorner (dominoTail r) := by decide
  have h2 : ∀ r, dominoTail (reflLine r) = reflCorner (dominoHead r) := by decide
  have h3 : ∀ x y : Fin 6, reflCorner x = reflCorner y ↔ x = y := by decide
  simp only [dominoGauge, h1, h2, h3]
  ring

/-- **DM1.** On a wide board, in every naming, the gauge between a named line and a named corner,
times the line's sign, is the gauge table. -/
theorem domino_gauge [DecidableEq v] (hW : B.Wide) (σ : f) (i : Fin 4) (b : Bool) (r : Fin 7)
    (p : Fin 6) :
    B.namedSign σ i b r * B.gauge (B.namedLine σ i b r) (B.namedCorner σ i b p) =
      dominoGauge r p := by
  cases b
  · simp only [namedSign, namedLine, namedCorner]
    rw [neg_mul, along_gauge hW, dominoGauge_refl, neg_neg]
  · exact along_gauge hW σ i r p

/-- The incidence table, read along. -/
theorem along_incidence [DecidableEq e] (hW : B.Wide) (σ : f) (i : Fin 4) (k : Fin 2)
    (r : Fin 7) :
    B.incidence (B.namedSquare σ i k) (B.alongLine σ i r) * B.alongSign σ i r =
      dominoIncidence k r := by
  have hs := B.otherFlag_side σ i
  have hne := B.otherFlag_along_ne σ i
  have ha := B.otherFlag_along σ i
  unfold namedSquare alongLine alongSign
  generalize B.otherFlag σ i = T at hs hne ha ⊢
  obtain ⟨τ, j⟩ := T
  dsimp only at hs hne ha ⊢
  have hne' : B.along τ j ≠ B.along σ i := fun h => hne h.symm
  have b0 : ∀ x : Fin 4, x + 1 ≠ x ∧ x + 2 ≠ x ∧ x + 3 ≠ x := by decide
  have nτ : ∀ c, c ≠ i → B.incidence τ (B.side σ c) = 0 := fun c hc =>
    B.incidence_of_not fun a => hW.side_ne hs.symm hne hc a
  have nσ : ∀ c, c ≠ j → B.incidence σ (B.side τ c) = 0 := fun c hc =>
    B.incidence_of_not fun a => hW.side_ne hs hne' hc a
  have own : ∀ (ρ : f) (c : Fin 4),
      B.incidence ρ (B.side ρ c) * turnSign (B.along ρ c) = 1 := fun ρ c => by
    rw [B.incidence_of_side rfl, turnSign_mul_self]
  fin_cases k <;> fin_cases r <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, dominoIncidence]
  · exact own σ i
  · exact own σ (i + 1)
  · exact own σ (i + 2)
  · exact own σ (i + 3)
  · rw [nσ _ (b0 j).1, zero_mul]
  · rw [nσ _ (b0 j).2.1, zero_mul]
  · rw [nσ _ (b0 j).2.2, zero_mul]
  · rw [B.incidence_of_side hs, ha]
    cases B.along σ i <;> norm_num [turnSign]
  · rw [nτ _ (b0 i).1, zero_mul]
  · rw [nτ _ (b0 i).2.1, zero_mul]
  · rw [nτ _ (b0 i).2.2, zero_mul]
  · exact own τ (j + 1)
  · exact own τ (j + 2)
  · exact own τ (j + 3)

/-- **DM1.** On a wide board, in every naming, the incidence between a named square and a named
line, times the signs of both, is the incidence table. -/
theorem domino_incidence [DecidableEq e] (hW : B.Wide) (σ : f) (i : Fin 4) (b : Bool) (k : Fin 2)
    (r : Fin 7) :
    squareSign b * B.incidence (B.namedSquare σ i k) (B.namedLine σ i b r) * B.namedSign σ i b r =
      dominoIncidence k r := by
  cases b
  · simp only [squareSign, namedLine, namedSign]
    have h := along_incidence hW σ i k (reflLine r)
    have hr : dominoIncidence k (reflLine r) = dominoIncidence k r := by
      fin_cases k <;> fin_cases r <;> rfl
    linear_combination h + hr
  · simp only [squareSign, namedLine, namedSign, one_mul]
    exact along_incidence hW σ i k r

variable (B)

/-- Read along, the six paints of a naming are finding 449's six paints of the flag. -/
theorem namedPaints_true [Fintype f] [DecidableEq v] (σ : f) (i : Fin 4) :
    B.namedPaints σ i true = B.flagPaints σ i := by
  funext p
  fin_cases p <;> rfl

/-- Turned over, they are finding 449's six paints turned over. -/
theorem namedPaints_false [Fintype f] [DecidableEq v] (σ : f) (i : Fin 4) :
    B.namedPaints σ i false = turnOver (B.flagPaints σ i) := by
  funext p
  fin_cases p <;> rfl

/-- Read along, the entry `2` of the row is the far weight. -/
theorem rowRead_true_two (M : Matrix e e ℝ) (σ : f) (i : Fin 4) :
    B.rowRead M σ i true 2 = B.farWeightRead M σ i := rfl

/-- The row turned over is the row read along, turned over. -/
theorem rowRead_false (M : Matrix e e ℝ) (σ : f) (i : Fin 4) (r : Fin 7) :
    B.rowRead M σ i false r = B.rowRead M σ i true (reflLine r) := by
  have h0 : reflLine 0 = 0 := rfl
  simp only [rowRead, namedLine, namedSign, h0]
  ring

/-- **DM3.** A kick that meets D17 meets one rule for the far weights. -/
theorem d17_oneRuleFar [Fintype f] [DecidableEq v] (M : Matrix e e ℝ) (h : B.D17Kick M) :
    B.OneRuleFar M := by
  classical
  refine ⟨fun p => if hp : ∃ x : f × Fin 4 × Bool, B.namedPaints x.1 x.2.1 x.2.2 = p then
    B.rowRead M hp.choose.1 hp.choose.2.1 hp.choose.2.2 2 else 0, fun σ i => ⟨?_, ?_⟩⟩
  · have hp : ∃ x : f × Fin 4 × Bool, B.namedPaints x.1 x.2.1 x.2.2 = B.flagPaints σ i :=
      ⟨(σ, i, true), B.namedPaints_true σ i⟩
    dsimp only
    rw [dite_eq_left hp, ← B.rowRead_true_two]
    exact congrFun (h σ i true _ _ _ ((B.namedPaints_true σ i).trans hp.choose_spec.symm)) 2
  · have hp : ∃ x : f × Fin 4 × Bool,
        B.namedPaints x.1 x.2.1 x.2.2 = turnOver (B.flagPaints σ i) :=
      ⟨(σ, i, false), B.namedPaints_false σ i⟩
    dsimp only
    have h2 : B.farWeightRead M σ i = B.rowRead M σ i false 2 := by
      rw [rowRead_false]
      rfl
    rw [dite_eq_left hp, h2]
    exact congrFun (h σ i false _ _ _ ((B.namedPaints_false σ i).trans hp.choose_spec.symm)) 2

variable {B}

/-- **DM4.** On a wide board, a kick of reach 1 that meets A10, A11 and D17 is `Cᵀ diag K C` with
`K` one number on each class of squares. -/
theorem d17_classes [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    (hW : B.Wide) (M : Matrix e e ℝ) (hR : B.ReachOne M) (h10 : M * B.gauge = 0)
    (h11 : B.gaugeᵀ * M = 0) (h17 : B.D17Kick M) :
    ∃ K : f → ℝ, M = B.incidenceᵀ * diagonal K * B.incidence ∧
      ∀ σ τ, Relation.EqvGen (fun ρ ρ' => ∃ i j, B.flagPaints ρ i = B.flagPaints ρ' j ∨
        B.flagPaints ρ i = turnOver (B.flagPaints ρ' j)) σ τ → K σ = K τ :=
  one_rule_classes hW M hR h10 h11 (B.d17_oneRuleFar M h17)

/-- **DM4.** Where every corner has one paint, such a kick is `Cᵀ diag κ C` for one number `κ`. -/
theorem d17_one_number [Fintype f] [DecidableEq f] [Fintype e] [DecidableEq e] [DecidableEq v]
    [Nonempty f] (hW : B.Wide) (hpaint : ∀ w w' : v, B.paint w = B.paint w') (M : Matrix e e ℝ)
    (hR : B.ReachOne M) (h10 : M * B.gauge = 0) (h11 : B.gaugeᵀ * M = 0) (h17 : B.D17Kick M) :
    ∃ κ : ℝ, M = B.incidenceᵀ * diagonal (fun _ : f => κ) * B.incidence :=
  one_rule_one_number hW hpaint M hR h10 h11 (B.d17_oneRuleFar M h17)

/-- The row of `Cᵀ diag K C` read along. -/
theorem kick_rowRead_true [Fintype f] [DecidableEq f] [DecidableEq e] (hW : B.Wide) (K : f → ℝ)
    (σ : f) (i : Fin 4) (r : Fin 7) :
    B.rowRead (B.incidenceᵀ * diagonal K * B.incidence) σ i true r =
      K (B.namedSquare σ i 0) * dominoIncidence 0 r -
        K (B.namedSquare σ i 1) * dominoIncidence 1 r := by
  have hne := B.domino_square_ne σ i
  have hreach := (B.domino_reach σ i).1
  have e00 := along_incidence hW σ i 0 0
  have e0r := along_incidence hW σ i 0 r
  have e10 := along_incidence hW σ i 1 0
  have e1r := along_incidence hW σ i 1 r
  have hl0 : B.alongLine σ i 0 = B.side σ i := rfl
  have hsum : (B.incidenceᵀ * diagonal K * B.incidence) (B.alongLine σ i 0) (B.alongLine σ i r) =
      B.incidence (B.namedSquare σ i 0) (B.alongLine σ i 0) * K (B.namedSquare σ i 0) *
          B.incidence (B.namedSquare σ i 0) (B.alongLine σ i r) +
        B.incidence (B.namedSquare σ i 1) (B.alongLine σ i 0) * K (B.namedSquare σ i 1) *
          B.incidence (B.namedSquare σ i 1) (B.alongLine σ i r) := by
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, transpose_apply]
    refine Fintype.sum_eq_add _ _ hne fun ρ hρ => ?_
    have h0 : B.incidence ρ (B.alongLine σ i 0) = 0 := by
      refine B.incidence_of_not fun a ha => ?_
      rcases hreach ρ a (ha.trans hl0) with h | h
      · exact hρ.1 h
      · exact hρ.2 h
    rw [h0, zero_mul, zero_mul]
  have d00 : dominoIncidence 0 0 = 1 := rfl
  have d10 : dominoIncidence 1 0 = -1 := rfl
  rw [d00] at e00
  rw [d10] at e10
  simp only [rowRead, namedLine, namedSign]
  rw [hsum]
  linear_combination
    (K (B.namedSquare σ i 0) * B.incidence (B.namedSquare σ i 0) (B.alongLine σ i r) *
        B.alongSign σ i r) * e00 + K (B.namedSquare σ i 0) * e0r +
      (K (B.namedSquare σ i 1) * B.incidence (B.namedSquare σ i 1) (B.alongLine σ i r) *
        B.alongSign σ i r) * e10 - K (B.namedSquare σ i 1) * e1r

/-- **DM5.** On a wide board the row of `Cᵀ diag K C` read in a naming of `(σ, i)` is `K σ` times
the first row of the incidence table less `K` of the other square times the second. -/
theorem kick_rowRead [Fintype f] [DecidableEq f] [DecidableEq e] (hW : B.Wide) (K : f → ℝ)
    (σ : f) (i : Fin 4) (b : Bool) (r : Fin 7) :
    B.rowRead (B.incidenceᵀ * diagonal K * B.incidence) σ i b r =
      K (B.namedSquare σ i 0) * dominoIncidence 0 r -
        K (B.namedSquare σ i 1) * dominoIncidence 1 r := by
  cases b
  · rw [rowRead_false, kick_rowRead_true hW]
    have h0 : dominoIncidence 0 (reflLine r) = dominoIncidence 0 r := by fin_cases r <;> rfl
    have h1 : dominoIncidence 1 (reflLine r) = dominoIncidence 1 r := by fin_cases r <;> rfl
    rw [h0, h1]
  · exact kick_rowRead_true hW K σ i r

/-- **DM5.** So with one number `κ` the row read is the same in every naming, and `Cᵀ diag κ C`
meets D17. -/
theorem kick_meets_d17 [Fintype f] [DecidableEq f] [DecidableEq e] [DecidableEq v] (hW : B.Wide)
    (κ : ℝ) : B.D17Kick (B.incidenceᵀ * diagonal (fun _ : f => κ) * B.incidence) := by
  intro σ i b τ j c _
  funext r
  rw [kick_rowRead hW, kick_rowRead hW]

end Board

variable (n m : ℕ) [Fact (1 < n)] [Fact (1 < m)]

/-- **DM4.** For `n, m ≥ 3`, on the torus a kick of reach 1 that meets A10, A11 and D17 is
`Cᵀ diag κ C` with one number `κ` on every square. -/
theorem torus_d17 (hn : 2 < n) (hm : 2 < m)
    (M : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (hR : (torus n m).ReachOne M) (h10 : M * (torus n m).gauge = 0)
    (h11 : (torus n m).gaugeᵀ * M = 0) (h17 : (torus n m).D17Kick M) :
    ∃ κ : ℝ, M = (torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
      (torus n m).incidence :=
  torus_kick_forced n m hn hm M hR h10 h11 ((torus n m).d17_oneRuleFar M h17)

end Artform.Stages
