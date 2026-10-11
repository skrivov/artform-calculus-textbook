import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Field.Rat
import ArtformTextbook.Meta.Book

/-!
# Receipts and margins (Section 3.12, "From sampled pictures to feature states")

An observation of a sampled picture fills a feature state from receipts, and every receipt of
the six of the book (elongated, round, connected, joint, angle band, proportion) is a finite family
of comparisons of rational numbers computed from the supplied pixels and the declared candidates,
read together with combinatorial data of the picture: connectivity, boundaries, ports and joint
sites, membership in the candidate inventories.

* **Comparisons.** A comparison is `L ≤ R`, or `L < R` when strict (`Receipts.Cmp`); its slack is
  `R - L`, and its recorded margin is the absolute slack `|R - L|`.
* **Receipts.** A receipt has a finite family of comparisons and a verdict decided from their
  truth values and the combinatorial data it reads (`Receipts.Receipt`). The verdict may be a
  truth value, a band value, or a refusal (`none`), as the protocol's rejection rule allows.
* **The six receipts** are written in this form (`Receipts.elongatedR`, …), each with its
  comparisons as the book states them (`Receipts.elongatedCmps`, …).
* **Observations.** An observation has finite parts and, for every atom it fills (a relation or
  channel with a tuple of parts), a receipt, the data it reads and its comparisons
  (`Receipts.Observation`); its feature state is the table of the verdicts.
-/

namespace Artform

namespace Receipts

/-- The square-step form `q(x, y) = x² + y²`, on rational vectors. -/
def q (x : ℚ × ℚ) : ℚ := x.1 ^ 2 + x.2 ^ 2

/-- The inner product `⟨(x₁, y₁), (x₂, y₂)⟩ = x₁ x₂ + y₁ y₂`. -/
def ip (x y : ℚ × ℚ) : ℚ := x.1 * y.1 + x.2 * y.2

/-- A comparison of two rational numbers: `L ≤ R`, or `L < R` when `strict`. -/
structure Cmp where
  /-- The left side. -/
  L : ℚ
  /-- The right side. -/
  R : ℚ
  /-- Whether the comparison is strict. -/
  strict : Bool

namespace Cmp

/-- The comparison holds. -/
def Holds (c : Cmp) : Prop := if c.strict then c.L < c.R else c.L ≤ c.R

instance (c : Cmp) : Decidable c.Holds := by
  unfold Holds
  split <;> infer_instance

/-- The slack `R - L`. -/
def slack (c : Cmp) : ℚ := c.R - c.L

/-- The comparison `c'` of a second picture is `c` changed by less than its recorded margin
`|R - L|`: the same kind of comparison, whose slack moves by less than that margin. -/
def WithinMargin (c c' : Cmp) : Prop :=
  c'.strict = c.strict ∧ |c'.slack - c.slack| < |c.slack|

end Cmp

/-- A receipt: a finite family of comparisons of rational numbers, indexed by `I`, and a verdict
decided from their truth values and from the combinatorial data `D` it reads. -/
structure Receipt (D V : Type) where
  /-- The index of the comparisons. -/
  I : Type
  /-- They are finitely many. -/
  [fintype : Fintype I]
  /-- The verdict, from the data and the truth values of the comparisons. -/
  verdict : D → (I → Bool) → V

/-- The verdict of a receipt on its data and its comparisons. -/
def Receipt.eval {D V : Type} (R : Receipt D V) (d : D) (c : R.I → Cmp) : V :=
  R.verdict d fun i => decide (c i).Holds

/-! ### The six receipts -/

/-- The comparisons of the elongated receipt for a declared squared aspect `m/n > 1`, given the
spreads `A_U(u)` along and `T_U(u)` across each candidate axis `u`: at each axis, `n A ≥ m T`
(`inl`) and its strict reverse `n A < m T` (`inr`). -/
def elongatedCmps {Ax : Type} (m n : ℚ) (A T : Ax → ℚ) : Ax ⊕ Ax → Cmp
  | .inl u => ⟨m * T u, n * A u, false⟩
  | .inr u => ⟨n * A u, m * T u, true⟩

/-- The elongated receipt: positive when the region is connected and some axis of the inventory
with both endpoints in the region has `n A ≥ m T`; negative when the region is disconnected or
every axis has `n A < m T`; refused otherwise. The data are the connectivity of the region and,
for each axis, whether its endpoints lie in it. -/
def elongatedR (Ax : Type) [Fintype Ax] : Receipt (Bool × (Ax → Bool)) (Option Bool) where
  I := Ax ⊕ Ax
  verdict d t :=
    if d.1 ∧ ∃ u, d.2 u ∧ t (.inl u) then some true
    else if ¬ d.1 ∨ ∀ u, t (.inr u) then some false else none

/-- The comparisons of the round receipt for a declared `m/n ≥ 1`, given the nearest and farthest
squared distances `r₋`, `r₊` of the boundary from the candidate centre: `0 < r₋` and
`n r₊ ≤ m r₋`. -/
def roundCmps (m n rMinus rPlus : ℚ) : Fin 2 → Cmp :=
  ![⟨0, rMinus, true⟩, ⟨n * rPlus, m * rMinus, false⟩]

/-- The round receipt: positive when the region is connected, its boundary is nonempty, and both
comparisons hold. The data are the connectivity and the nonemptiness of the boundary. -/
def roundR : Receipt (Bool × Bool) Bool where
  I := Fin 2
  verdict d t := d.1 && d.2 && t 0 && t 1

/-- The comparison of the connected receipt: `d_q(U, V) ≤ δ²`, for the least squared distance
`d_q` between the boundaries. -/
def connectedCmps (dq delta2 : ℚ) : Fin 1 → Cmp := ![⟨dq, delta2, false⟩]

/-- The connected receipt: positive when both boundaries are nonempty and `d_q ≤ δ²`. The data
are the nonemptiness of the two boundaries. -/
def connectedR : Receipt (Bool × Bool) Bool where
  I := Fin 1
  verdict d t := d.1 && d.2 && t 0

/-- The joint receipt: a connected receipt whose minimizing pair lies at the declared ports, with
a joint site from the inventory. The data are those of the connected receipt, and whether the
ports and the joint site are declared and the minimizing pair lies at the ports. -/
def jointR : Receipt ((Bool × Bool) × Bool) Bool where
  I := Fin 1
  verdict d t := d.1.1 && d.1.2 && d.2 && t 0

/-- The comparisons of an angle band `[a, b]`, for direction witnesses with squared lengths
`qu`, `qv` and inner product `p`: `a qu qv ≤ p²` and `p² ≤ b qu qv`. -/
def angleCmps (a b qu qv p : ℚ) : Fin 2 → Cmp :=
  ![⟨a * qu * qv, p ^ 2, false⟩, ⟨p ^ 2, b * qu * qv, false⟩]

/-- The angle-band receipt: positive when both witnesses are nonzero and both comparisons hold. -/
def angleR : Receipt Bool Bool where
  I := Fin 2
  verdict d t := d && t 0 && t 1

/-- The comparisons of a proportion band `[ℓ₋, ℓ₊]`, for segment witnesses with squared lengths
`qu`, `qv`: `ℓ₋ qv ≤ qu ≤ ℓ₊ qv`. -/
def proportionCmps (lMinus lPlus qu qv : ℚ) : Fin 2 → Cmp :=
  ![⟨lMinus * qv, qu, false⟩, ⟨qu, lPlus * qv, false⟩]

/-- The proportion receipt: positive when both comparisons hold. -/
def proportionR : Receipt Unit Bool where
  I := Fin 2
  verdict _ t := t 0 && t 1

/-! ### Observations and feature states -/

/-- The receipts an observation protocol declares: for every relation or channel `r` of the
feature profile, its arity and the receipt that decides it, with verdicts in `V` (a truth value,
a band value, or a refusal) and combinatorial data in `D`. -/
structure Protocol (D V : Type) where
  /-- The relations and channels of the profile. -/
  Sym : Type
  /-- The arity of each. -/
  arity : Sym → ℕ
  /-- The receipt that decides each. -/
  receipt : Sym → Receipt D V

variable {D V : Type}

/-- An observation of a picture under a protocol, read through its receipts: the parts and, for
every atom (a relation or channel with a tuple of parts), the combinatorial data its receipt reads
and its comparisons with this picture's numbers. -/
structure Observation (π : Protocol D V) where
  /-- The parts. -/
  Part : Type
  /-- The data each receipt reads. -/
  data : (r : π.Sym) → (Fin (π.arity r) → Part) → D
  /-- The comparisons of each receipt, with this picture's numbers. -/
  cmps : (r : π.Sym) → (Fin (π.arity r) → Part) → (π.receipt r).I → Cmp

/-- The feature state an observation produces: the table of the verdicts of its receipts. -/
def Observation.featureState {π : Protocol D V} (o : Observation π) (r : π.Sym)
    (t : Fin (π.arity r) → o.Part) : V :=
  (π.receipt r).eval (o.data r t) (o.cmps r t)

end Receipts

end Artform
