import Mathlib.MeasureTheory.MeasurableSpace.Basic
import ArtformTextbook.Meta.Book

/-!
# Events available to a finite report (*What a report can distinguish*)

Definition 4.1: for a report `f : Ω → Y` between finite sets, the report event
algebra on the source, its atoms, and the events available to the report.

* `reportEvents f`: `𝒜_f = {f⁻¹(C) : C ⊆ Y}`. It is the algebra of the events
  measurable for `MeasurableSpace.comap f ⊤` (`reportEvents_eq_comap`).
* `reportAtoms f`: its nonempty atoms, the nonempty fibres `f⁻¹({y})`.
* `Available f A`: `A` is a union of these fibres; exactly the events of `𝒜_f`
  (`available_iff`).

Nothing here needs the sets to be finite; the book's reports are.
-/

namespace Artform

variable {Ω Y : Type*}

/-- **Definition 4.1** (report event algebra): the events of the source that a
report `f : Ω → Y` determines, `𝒜_f = {f⁻¹(C) : C ⊆ Y}`. -/
@[book "def:report-events"]
def reportEvents (f : Ω → Y) : Set (Set Ω) := {A | ∃ C : Set Y, A = f ⁻¹' C}

/-- **Definition 4.1** (atoms): the nonempty atoms of `𝒜_f`, the nonempty fibres
`f⁻¹({y})`. -/
@[book "def:report-events"]
def reportAtoms (f : Ω → Y) : Set (Set Ω) := {A | ∃ y, A = f ⁻¹' {y} ∧ A.Nonempty}

/-- **Definition 4.1** (available event): an event is available to the report
when it is a union of nonempty fibres. -/
@[book "def:report-events"]
def Available (f : Ω → Y) (A : Set Ω) : Prop := ∃ S ⊆ reportAtoms f, A = ⋃₀ S

/-- An event is available to a report exactly when it is in the report event
algebra. -/
theorem available_iff (f : Ω → Y) (A : Set Ω) : Available f A ↔ A ∈ reportEvents f := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    refine ⟨{y | f ⁻¹' {y} ∈ S}, ?_⟩
    ext x
    simp only [Set.mem_sUnion, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨B, hB, hx⟩
      obtain ⟨y, rfl, -⟩ := hS hB
      have hy : f x = y := hx
      rw [hy]
      exact hB
    · intro hx
      exact ⟨_, hx, rfl⟩
  · rintro ⟨C, rfl⟩
    refine ⟨{B | ∃ y ∈ C, B = f ⁻¹' {y} ∧ B.Nonempty}, ?_, ?_⟩
    · rintro B ⟨y, -, hB⟩
      exact ⟨y, hB⟩
    · ext x
      simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_ofPred_eq]
      constructor
      · intro hx
        exact ⟨f ⁻¹' {f x}, ⟨f x, hx, rfl, x, rfl⟩, rfl⟩
      · rintro ⟨B, ⟨y, hy, rfl, -⟩, hx⟩
        have : f x = y := hx
        rw [this]
        exact hy

/-- The report event algebra is the algebra of the events measurable for the
σ-algebra that the report pulls back from all subsets of `Y`. -/
theorem reportEvents_eq_comap (f : Ω → Y) :
    reportEvents f = {A | @MeasurableSet Ω (MeasurableSpace.comap f ⊤) A} := by
  ext A
  simp only [reportEvents, Set.mem_ofPred_eq, MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C, trivial, rfl⟩
  · rintro ⟨C, -, rfl⟩
    exact ⟨C, rfl⟩

/-! ## Non-vacuity -/

/-- The parity of a die's face, read by a report: the event "the face is even"
is available to it. -/
example : Available (fun n : Fin 6 => n.val % 2) {n | n.val % 2 = 0} :=
  (available_iff _ _).mpr ⟨{0}, by ext n; simp⟩

end Artform
