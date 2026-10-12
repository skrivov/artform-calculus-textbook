import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ArtformTextbook.Ch03.Recognition

/-!
# Degree and recurrence of positive patterns (*Groups acting on patterns*)

* Definition 3.23: two atoms of a set of atoms are adjacent when they share a
  position, and an atom-sharing component is a class of the connectedness
  relation that adjacency generates, together with the positions occurring in
  its atoms. The component inventory lists the pair `(o_C, p_C)` of each
  component `C`, its numbers of positions and of atoms; the degree is
  `Σ_C o_C p_C`. The definitions are stated for any set of atoms
  (`AtomSet.inventory`, `AtomSet.degree`), and apply to the credited atoms of a
  partial positive comparison (`PartialComparison.degree`) and to the atoms of
  a positive template, its positions being its variables
  (`PositiveTemplate.degree`).
* Definition 3.24: the atom support of a positive occurrence is its atom image,
  independent of the representative by Proposition 3.22
  (`Instantiation.atomImage_comp`). Two occurrences are atom-disjoint when their
  supports are disjoint. A template recurs internally in `G` when it has two
  atom-disjoint occurrences there, and externally when it has an occurrence in
  `G` and one in a state of a declared reference repertoire. A recurrence
  witness is a family of pairwise atom-disjoint occurrences of maximum size.
-/

namespace Artform

variable {R : RecognitionProfile}

/-! ## Definition 3.23: component inventory and degree -/

namespace AtomSet

variable {X : Type} (A : Set (Atom R X))

/-- **Definition 3.23** (adjacency): two atoms of `A` are adjacent when they
share a position. -/
@[book "def:pattern-degree-book"]
def Adjacent (α β : A) : Prop := ((α : Atom R X).vars ∩ (β : Atom R X).vars).Nonempty

/-- The graph of adjacency on the atoms of `A`. -/
def sharingGraph : SimpleGraph A := SimpleGraph.fromRel (Adjacent A)

/-- **Definition 3.23** (atom-sharing component): a class of the connectedness
relation that adjacency generates. -/
@[book "def:pattern-degree-book"]
abbrev Component : Type := (sharingGraph A).ConnectedComponent

variable {A}

/-- The atoms of a component. -/
def Component.atoms (C : Component A) : Set (Atom R X) :=
  Subtype.val '' {α | (sharingGraph A).connectedComponentMk α = C}

/-- The positions of a component: those occurring in its atoms. -/
def Component.positions (C : Component A) : Set X := ⋃ α ∈ C.atoms, α.vars

/-- **Definition 3.23** (component inventory), one entry: the pair `(o_C, p_C)`
of the numbers of positions and of atoms of the component `C`. -/
@[book "def:pattern-degree-book"]
noncomputable def Component.pair (C : Component A) : ℕ × ℕ :=
  (C.positions.ncard, C.atoms.ncard)

variable (A)

/-- **Definition 3.23** (component inventory): the list of the pairs
`(o_C, p_C)`, one per component, as a multiset. -/
@[book "def:pattern-degree-book"]
noncomputable def inventory [Finite A] : Multiset (ℕ × ℕ) :=
  letI := Fintype.ofFinite (Component A)
  (Finset.univ : Finset (Component A)).val.map Component.pair

/-- **Definition 3.23** (degree): the readout `deg = Σ_C o_C p_C`. -/
@[book "def:pattern-degree-book"]
noncomputable def degree [Finite A] : ℕ :=
  ((inventory A).map fun p => p.1 * p.2).sum

end AtomSet

/-- **Definition 3.23** (degree of a partial positive comparison): the degree of
its credited atoms. -/
@[book "def:pattern-degree-book"]
noncomputable def PartialComparison.degree {G₁ G₂ : ProfiledState R}
    (F : PartialComparison G₁ G₂) [Finite F.credited] : ℕ :=
  AtomSet.degree F.credited

/-- **Definition 3.23** (degree of a positive template): the same definitions
applied to its own atoms and variables. -/
@[book "def:pattern-degree-book"]
noncomputable def PositiveTemplate.degree (K : PositiveTemplate R) : ℕ :=
  haveI : Finite K.atoms := K.atoms_finite
  AtomSet.degree K.atoms

/-! ## Definition 3.24: atom support and recurrence -/

namespace PositiveOccurrence

variable {K : PositiveTemplate R} {G : ProfiledState R}

/-- **Definition 3.24** (atom support): the atom image of an occurrence, which
does not depend on the representative (Proposition 3.22). -/
@[book "def:atom-disjoint-recurrence-book"]
def support (P : PositiveOccurrence K G) : Set (Atom R G.Pos) :=
  Quotient.liftOn P Instantiation.atomImage fun j _ ⟨a, h⟩ =>
    h ▸ (Instantiation.atomImage_comp j a).symm

/-- **Definition 3.24** (atom-disjoint): two occurrences whose supports are
disjoint. They may share positions. -/
@[book "def:atom-disjoint-recurrence-book"]
def AtomDisjoint (P Q : PositiveOccurrence K G) : Prop := Disjoint P.support Q.support

end PositiveOccurrence

/-- **Definition 3.24** (internal recurrence): the template `K` recurs
internally in `G` when it has two atom-disjoint occurrences in `G`. -/
@[book "def:atom-disjoint-recurrence-book"]
def RecursInternally (K : PositiveTemplate R) (G : ProfiledState R) : Prop :=
  ∃ P Q : PositiveOccurrence K G, P.AtomDisjoint Q

/-- **Definition 3.24** (external recurrence): the template `K` recurs
externally in `G` when it has an occurrence in `G` and one in a state of the
declared reference repertoire. -/
@[book "def:atom-disjoint-recurrence-book"]
def RecursExternally (K : PositiveTemplate R) (G : ProfiledState R)
    (repertoire : Set (ProfiledState R)) : Prop :=
  Nonempty (PositiveOccurrence K G) ∧ ∃ H ∈ repertoire, Nonempty (PositiveOccurrence K H)

/-- **Definition 3.24** (recurrence witness): a family of pairwise
atom-disjoint occurrences of maximum size among such families. -/
@[book "def:atom-disjoint-recurrence-book"]
def IsRecurrenceWitness {K : PositiveTemplate R} {G : ProfiledState R}
    (W : Finset (PositiveOccurrence K G)) : Prop :=
  (W : Set (PositiveOccurrence K G)).Pairwise PositiveOccurrence.AtomDisjoint ∧
    ∀ W' : Finset (PositiveOccurrence K G),
      (W' : Set (PositiveOccurrence K G)).Pairwise PositiveOccurrence.AtomDisjoint →
        W'.card ≤ W.card

end Artform
