import ArtformRoles.Construction
import ArtformRoles.Histories

/-!
# The book's examples

Section 5 of the paper.

* `chess`: the five roles on one capture, after the textbook's §1.9
  (`fig:chess-frame-instance`, `fig:chess-attack-vs-eval`,
  `fig:chess-typed-arrows`). The construction is valid; letting the
  certificate read the engine's evaluation is not (`chess_readback_invalid`),
  and neither is writing the score without a gate (`chess_silent_score_invalid`).
* `realizer`: a supplied policy installed in a realizer through a gate
  (§1.9, *Four useful words that are not roles*; §5.1, `def:realizer`).
* `walker`: the walker of §5.1 (`def:law`) on the four corners of the square:
  four histories of two ticks, two ending at the start and two opposite.
-/

namespace Artform.Roles

open Grade

/-- The items of one capture, `N×e5`, in the position of the book's §1.9. -/
inductive ChessItem
  /-- the squares with their adjacency, and the step shape of each piece -/
  | board
  /-- the addressing `a1` to `h8` -/
  | addressing
  /-- the position before the capture -/
  | position
  /-- the squares White bears on, a value on every square -/
  | attackMap
  /-- the certificate that the capture is legal -/
  | certificate
  /-- the capture itself -/
  | capture
  /-- the position after the capture -/
  | next
  /-- the game score, which keeps the moves made -/
  | score
  /-- an engine's evaluation of the position -/
  | evaluation
  /-- the printed diagram -/
  | diagram
  deriving DecidableEq, Repr

instance : Fintype ChessItem :=
  Fintype.ofList
    [.board, .addressing, .position, .attackMap, .certificate, .capture, .next, .score,
      .evaluation, .diagram]
    fun i => by cases i <;> simp

open ChessItem in
/-- The role of each item. A position, before or after the move, is a state:
a legal choice of a piece or none on every square, witness data. -/
def ChessItem.role : ChessItem → Role
  | board => .form
  | addressing => .presentation
  | position => .witness
  | attackMap => .witness
  | certificate => .witness
  | capture => .script
  | next => .witness
  | score => .form
  | evaluation => .rendering
  | diagram => .rendering

open ChessItem in
/-- The direct dependencies of the capture. The score keeps the capture
through a gate; every other use is ordinary. -/
def ChessItem.edge : ChessItem → ChessItem → Grade
  | board, addressing => .free
  | board, position => .free
  | addressing, position => .free
  | board, attackMap => .free
  | position, attackMap => .free
  | position, certificate => .free
  | attackMap, certificate => .free
  | capture, certificate => .free
  | position, next => .free
  | capture, next => .free
  | certificate, next => .free
  | capture, score => .gated
  | position, evaluation => .free
  | position, diagram => .free
  | addressing, diagram => .free
  | _, _ => .absent

/-- The capture as a construction. -/
def chess : Construction ChessItem := ⟨ChessItem.role, ChessItem.edge⟩

theorem chess_valid : chess.Valid demand := by
  unfold Construction.Valid; decide

/-- The same capture with the certificate reading the engine's evaluation. -/
def chessReadback : Construction ChessItem :=
  ⟨ChessItem.role, fun u v =>
    if u = .evaluation ∧ v = .certificate then .free else ChessItem.edge u v⟩

/-- A rule that consults a reading is ill-typed. -/
theorem chess_readback_invalid : ¬ chessReadback.Valid demand := by
  unfold Construction.Valid; decide

/-- The same capture with the score written without a gate. -/
def chessSilentScore : Construction ChessItem :=
  ⟨ChessItem.role, fun u v =>
    if u = .capture ∧ v = .score then .free else ChessItem.edge u v⟩

/-- A move enters a form only on the record. -/
theorem chess_silent_score_invalid : ¬ chessSilentScore.Valid demand := by
  unfold Construction.Valid; decide

/-- The engine's evaluation reaches neither the certificate nor the position
after the move. -/
theorem chess_evaluation_terminal :
    ¬ chess.Reach .gated .evaluation .certificate ∧ ¬ chess.Reach .gated .evaluation .next :=
  ⟨Construction.no_reach_of_rendering chess_valid rfl (by decide),
    Construction.no_reach_of_rendering chess_valid rfl (by decide)⟩

/-- The items of an installation: a policy supplied to a law and the realizer
that carries it (`def:realizer`). -/
inductive RealizerItem
  /-- the law: its moves and invariants -/
  | law
  /-- the policy, while it is supplied -/
  | supplied
  /-- the realizer, which carries the installed policy -/
  | realizer
  deriving DecidableEq, Repr

instance : Fintype RealizerItem :=
  Fintype.ofList [.law, .supplied, .realizer] fun i => by cases i <;> simp

/-- One datum, two stages: the policy is a witness while it is supplied and
carried structure once installed; the installation is a gate. -/
def realizer : Construction RealizerItem where
  role
    | .law => .form
    | .supplied => .witness
    | .realizer => .presentation
  edge
    | .law, .supplied => .free
    | .law, .realizer => .free
    | .supplied, .realizer => .gated
    | _, _ => .absent

theorem realizer_valid : realizer.Valid demand := by
  unfold Construction.Valid; decide

/-- The installation crosses a gate, and the gate's record reaches the
realizer. -/
theorem realizer_installation_recorded :
    ¬ realizer.Reach .free .supplied .realizer ∧
      realizer.Reach .gated .supplied .realizer :=
  ⟨Construction.no_free_reach realizer_valid rfl,
    .tail (.refl _) (by decide)⟩

/-- The walker on the four corners of the square: from each corner the token
steps ahead or behind; each step has one certificate, that the token is at the
corner it leaves. -/
def walker : Law (Fin 4) where
  App y z := Fin ((if z = y + 1 then 1 else 0) + (if z + 1 = y then 1 else 0))
  Ev _ := Fin 1

/-- Two ticks from `v₀`: two histories end at `v₀` and two at `v₂`. -/
theorem walker_two_ticks :
    walker.histories 0 2 0 = 2 ∧ walker.histories 0 2 2 = 2 ∧
      walker.histories 0 2 1 = 0 ∧ walker.histories 0 2 3 = 0 := by
  decide

/-- On the square each step has one certificate and leads to a corner of its
own, so the three counts of §4 agree. -/
theorem walker_counts_agree (n : ℕ) (z : Fin 4) :
    walker.proofs 0 n z = walker.histories 0 n z ∧
      walker.histories 0 n z = walker.trajectories 0 n z := by
  refine ⟨walker.proofs_eq_histories
    (fun _ => Fintype.card_le_one_iff_subsingleton.mpr (inferInstanceAs (Subsingleton (Fin 1))))
    0 n z, walker.histories_eq_trajectories ?_ 0 n z⟩
  intro y z a b _ _
  have hk : (if z = y + 1 then 1 else 0) + (if z + 1 = y then 1 else 0) ≤ 1 := by
    revert y z; decide
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

end Artform.Roles
