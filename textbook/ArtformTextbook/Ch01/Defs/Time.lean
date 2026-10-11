import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import ArtformTextbook.Ch01.Defs.Rods

/-!
# Supports, tapestries and period spectra (Section 1.5)

A finite temporal support and the cycle `CycleTime(n)`; Definition 1.5
(rectangular tapestry) and its frame; and what Section 1.5 reads off a tapestry
on a cycle: the period of a row and the temporal period spectrum `TempSpec`.
Also the covering and grouping equations of "One clock on two scales", and the
temporal palette with its phases written locally, as Section 1.6 lays it.
-/

namespace Artform

/-- A finite temporal support (Section 1.5), the type `TimeForm`: finitely many
positions and a successor that is an injective function defined on some of
them. A position with no successor is terminal. -/
structure TimeForm where
  /-- The positions, `cells(T)`. -/
  cells : Type
  /-- There are finitely many positions. -/
  [fintype : Fintype cells]
  /-- The successor of each position; `none` at a terminal position. -/
  next : cells → Option cells
  /-- The successor is injective: no position follows two positions. -/
  next_injective : ∀ s t u, next s = some u → next t = some u → s = t

attribute [instance] TimeForm.fintype

/-- The cycle `CycleTime(n)`, for `n ≥ 1` (Section 1.5): the positions
`0, …, n - 1`, where `t + 1` follows `t` and `0` follows `n - 1`. -/
abbrev CycleTime (n : ℕ) [NeZero n] : TimeForm where
  cells := Fin n
  next t := some (t + 1)
  next_injective _ _ _ hs ht :=
    add_right_cancel ((Option.some.inj hs).trans (Option.some.inj ht).symm)

/-- **Definition 1.5** (rectangular tapestry). The support `T : TimeForm`
supplies the temporal positions and their successor; the cells of the ordered
form `R` name the rows, in order. Every row `r` has a type `V r` of allowed
values (the family `V` is the temporal palette), and a thread
`e r : cells(T) → V r` gives the row one allowed value at every position.
`RectTapestry(T; R, V, e)` retains `T`, `R`, `V` and `e`; its addresses are the
pairs `(r, t)`, and its entry at `(r, t)` is `e r t`. The support `T` is a
parameter here: `RectTapestry T` is the type of the rectangular tapestries on
`T`. -/
@[book "def:time-rectangular"]
structure RectTapestry (T : TimeForm) where
  /-- The rows, in order: each cell of `R` names one row. -/
  R : OrderedForm
  /-- The type of values allowed in each row. -/
  V : R.cells → Type
  /-- The thread of each row: one allowed value at every position. -/
  e : (r : R.cells) → T.cells → V r

/-- **Definition 1.5** (frame). The frame `A_rect(T; R, V)` keeps the support
`T`, the rows `R` and the value types `V`, and leaves the entries
unspecified. -/
@[book "def:time-rectangular"]
structure RectFrame (T : TimeForm) where
  /-- The rows, in order. -/
  R : OrderedForm
  /-- The type of values allowed in each row. -/
  V : R.cells → Type

/-- **Definition 1.5** (frame). The frame of a tapestry: its support, rows and
value types, without its entries. -/
@[book "def:time-rectangular"]
def RectTapestry.frame {T : TimeForm} (τ : RectTapestry T) : RectFrame T := ⟨τ.R, τ.V⟩

/-- The cells of an ordered form are finite: those of `glue(P, Q)` are those of
`P` and those of `Q`. This is a definition, not an instance; the spectrum
below uses it to range over the rows of a tapestry. -/
@[instance_reducible]
def OrderedForm.cellsFintype : (X : OrderedForm) → Fintype X.cells
  | .rod n => inferInstanceAs (Fintype (Fin n))
  | .glue P Q =>
    letI := P.cellsFintype
    letI := Q.cellsFintype
    Fintype.ofEquiv (P.cells ⊕ Q.cells)
      { toFun := Sum.elim (fun p => ⟨.L, p⟩) fun q => ⟨.R, q⟩
        invFun := fun
          | ⟨.L, p⟩ => .inl p
          | ⟨.R, q⟩ => .inr q
        left_inv := by rintro (_ | _) <;> rfl
        right_inv := by rintro ⟨_ | _, _⟩ <;> rfl }

namespace RectTapestry

variable {L : ℕ} [NeZero L] (τ : RectTapestry (CycleTime L))

/-- A row of a tapestry on `CycleTime(L)` has period `d` (Section 1.5) when `d`
is a positive divisor of `L` and `e_r(t + d) = e_r(t)` at every cyclic position
`t`; the sum `t + d` is taken modulo `L`. -/
def HasPeriod (r : τ.R.cells) (d : ℕ) : Prop :=
  0 < d ∧ d ∣ L ∧ ∀ t : Fin L, τ.e r (t + Fin.ofNat L d) = τ.e r t

/-- `L` itself is a period of every row. -/
theorem hasPeriod_self (r : τ.R.cells) : τ.HasPeriod r L :=
  ⟨Nat.pos_of_neZero L, dvd_rfl, fun t => by simp⟩

open Classical in
/-- The least period of a row (Section 1.5). -/
noncomputable def leastPeriod (r : τ.R.cells) : ℕ :=
  Nat.find ⟨L, τ.hasPeriod_self r⟩

/-- The temporal period spectrum `TempSpec` (Section 1.5): the multiset of the
least periods of the rows. -/
noncomputable def tempSpec : Multiset ℕ :=
  letI := τ.R.cellsFintype
  Finset.univ.val.map τ.leastPeriod

end RectTapestry

/-- The covering equation (Section 1.5, "One clock on two scales"). A map `c`
from the positions of `CycleTime(L)` to the phases of a row with `k` phases
satisfies `c(t + 1) = c(t) + 1 (mod k)` at every position `t`; the sum `t + 1`
is taken on the cycle. The phases are written as natural numbers here, so the
equation is a congruence modulo `k`. -/
def CoveringEq {L : ℕ} [NeZero L] (k : ℕ) (c : Fin L → ℕ) : Prop :=
  ∀ t : Fin L, c (t + 1) ≡ c t + 1 [MOD k]

/-- The grouping equation (Section 1.5, "One clock on two scales"). A map `p`
from the positions of `CycleTime(L)` to the phases of a row with `k` phases
satisfies `p(t + L/k) = p(t) + 1 (mod k)` at every position `t`; the sum
`t + L/k` is taken on the cycle. -/
def GroupingEq {L : ℕ} [NeZero L] (k : ℕ) (p : Fin L → ℕ) : Prop :=
  ∀ t : Fin L, p (t + Fin.ofNat L (L / k)) ≡ p t + 1 [MOD k]

/-- A temporal palette with its phases written locally (Sections 1.5 and 1.6).
The rows are the cells of an ordered form `R`, and row `r` has `k r` phases,
written locally `0, …, k r - 1`; these are the values `V r` allowed in that
row. The names that a drawing gives the phases are a legend and are not
kept. -/
structure TemporalPalette where
  /-- The rows, in order. -/
  R : OrderedForm
  /-- The number of phases of each row. -/
  k : R.cells → ℕ

/-- The phases of row `r` of a palette, `V r = {0, …, k r - 1}`: the values
allowed in that row. -/
abbrev TemporalPalette.V (F : TemporalPalette) (r : F.R.cells) : Type := Fin (F.k r)

end Artform
