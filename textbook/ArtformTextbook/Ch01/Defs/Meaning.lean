import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Defs
import ArtformTextbook.Ch01.Defs.Time

/-!
# One artform, many meanings (Section 1.6)

Definition 1.9: an interpretation profile, the interpretation witnesses of an
endpoint from an artform under a profile, the semantic fibre and the selected
layer. Then the data of Proposition 1.10: the ten-cell palette `P` (the
tetractys), the laying rules `ℓ_rec` and `ℓ_div`, the profiles `𝒞_rec` and
`𝒞_div`, and the tapestries `I_rec` and `I_div` of Figures 1.25 and 1.40.
-/

namespace Artform

universe u v w

/-- **Definition 1.9** (interpretation profile). The profile `𝒞` that
Definition 1.9 starts from, as Section 1.6 introduces it just before the
definition. An interpretation profile for raw artforms of type `Src` declares
three things: what an interpretation may produce, its endpoints; which rules
may produce a given endpoint `θ` from a given artform `F`, its realizers; and
the law a realizer must obey. The law may read the artform and the endpoint, as
the laws of the tetractys profiles read the rows of the palette and the
periods of the tapestry produced. -/
@[book "def:intwit-book"]
structure IntProfile (Src : Type u) where
  /-- The endpoints: what an interpretation may produce. -/
  Endpoint : Type v
  /-- The realizers: the rules that may produce the endpoint `θ` from the
  artform `F`. -/
  Realizer : Src → Endpoint → Type w
  /-- `Produces F θ ℓ`: the realizer `ℓ` produces `θ` from `F`. -/
  Produces : (F : Src) → (θ : Endpoint) → Realizer F θ → Prop
  /-- `Law F θ ℓ`: the realizer `ℓ`, producing `θ` from `F`, obeys the law of
  the profile. -/
  Law : (F : Src) → (θ : Endpoint) → Realizer F θ → Prop

/-- **Definition 1.9** (interpretation witness). Let `𝒞` be an interpretation
profile, `F` a raw artform and `θ` an endpoint of `𝒞`. An interpretation
witness of `θ` from `F` under `𝒞` is a pair `w = (ℓ, c)`: a realizer `ℓ` of `𝒞`
together with a certificate `c`, evidence in a form that can be checked that `ℓ`
produces `θ` from `F` and obeys the law of `𝒞`. `IntWit 𝒞 F θ` is the type of
such witnesses, as `Align P Q` is the type of perfect alignments. The
certificate is a proof, which Lean checks. -/
@[book "def:intwit-book"]
structure IntWit {Src : Type u} (C : IntProfile.{u, v, w} Src) (F : Src) (θ : C.Endpoint) where
  /-- The realizer `ℓ`. -/
  realizer : C.Realizer F θ
  /-- The certificate `c`: `ℓ` produces `θ` from `F` and obeys the law of `𝒞`. -/
  cert : C.Produces F θ realizer ∧ C.Law F θ realizer

/-- **Definition 1.9** (semantic fibre). If `Γ` lists the profiles in use, the
semantic fibre `Sem_Γ(F)` of `F` is the type of the tagged witnesses
`(𝒞, θ, w)`, with `𝒞` a profile of `Γ`, `θ` an endpoint of `𝒞` and
`w ∈ IntWit_𝒞(F, θ)`: every witness of every available profile, each carrying
the tag of its profile. A profile of `Γ` applies to `F` because it is a profile
for artforms of the type of `F`. The fibre stands beside `F` and selects
nothing; `F` itself is not changed. -/
@[book "def:intwit-book"]
def Sem {Src : Type u} (Γ : Set (IntProfile.{u, v, w} Src)) (F : Src) : Type _ :=
  Σ C : Γ, Σ θ : C.1.Endpoint, IntWit C.1 F θ

/-- **Definition 1.9** (selected layer). `PointedInt_Γ` is the type of the
pairs `(F, (𝒞, θ, w))`: an artform together with one tagged witness chosen from
its semantic fibre. -/
@[book "def:intwit-book"]
def PointedInt {Src : Type u} (Γ : Set (IntProfile.{u, v, w} Src)) : Type _ :=
  Σ F : Src, Sem Γ F

/-! ## The two layings of the tetractys (Proposition 1.10) -/

/-- A laying rule on a clock of `L` ticks (Section 1.6): it puts the phases of a
row at the ticks of the clock, giving for a row with `k` phases and a tick `t`
the local phase `ℓ(k, t)` that the row shows at `t`. -/
abbrev Laying (L : ℕ) : Type := ℕ → Fin L → ℕ

/-- The phase typing of the rows of a palette under a laying (Section 1.6): each
row shows only its own phases, `ℓ(k, t) < k` for a row with `k` phases. -/
def PhaseTyped {L : ℕ} (F : TemporalPalette) (ℓ : Laying L) : Prop :=
  ∀ (r : F.R.cells) (t : Fin L), ℓ (F.k r) t < F.k r

/-- The tapestry that a phase-typed laying lays from a palette on the cycle
`CycleTime(L)`: its rows are the rows of the palette, its values the phases of
the palette, and row `r` shows the phase `ℓ(k r, t)` at the tick `t`. -/
def TemporalPalette.lay {L : ℕ} [NeZero L] (F : TemporalPalette) (ℓ : Laying L)
    (h : PhaseTyped F ℓ) : RectTapestry (CycleTime L) where
  R := F.R
  V := F.V
  e r t := ⟨ℓ (F.k r) t, h r t⟩

/-- The ten-cell palette `P` of Sections 1.5 and 1.6, the tetractys: four rows,
in order, with `1, 2, 3, 4` phases. -/
abbrev tetractys : TemporalPalette where
  R := .rod 4
  k r := r.val + 1

/-- The recurrence laying `ℓ_rec(k, t) = t mod k` on the clock `t ∈ {0, …, 11}`
(Proposition 1.10). -/
def layRec : Laying 12 := fun k t => t.val % k

/-- The division laying `ℓ_div(k, t) = ⌊kt/12⌋` on the clock `t ∈ {0, …, 11}`
(Proposition 1.10). -/
def layDiv : Laying 12 := fun k t => k * t.val / 12

/-- A profile of layings on the twelve-tick clock, with a given law. Its
endpoints are the tapestries on `CycleTime(12)` and its realizers the laying
rules. A laying produces `θ` from the palette `F` when each row of `F` shows
only its own phases under it and `θ` is the tapestry it lays from `F`. -/
def layingProfile
    (law : TemporalPalette → RectTapestry (CycleTime 12) → Laying 12 → Prop) :
    IntProfile TemporalPalette where
  Endpoint := RectTapestry (CycleTime 12)
  Realizer _ _ := Laying 12
  Produces F θ ℓ := ∃ h : PhaseTyped F ℓ, θ = F.lay ℓ h
  Law := law

/-- The recurrence profile `𝒞_rec` (Section 1.6, Proposition 1.10). Its law is
the covering equation for the row of every size `k` of the palette, the phase
typing, and the period spectrum `{{1, 2, 3, 4}}`, read off the tapestry
produced. -/
def Crec : IntProfile TemporalPalette :=
  layingProfile fun F θ ℓ =>
    (∀ r, CoveringEq (F.k r) (ℓ (F.k r))) ∧ PhaseTyped F ℓ ∧ θ.tempSpec = {1, 2, 3, 4}

/-- The division profile `𝒞_div` (Section 1.6, Proposition 1.10). Its law is
the grouping equation for the row of every size `k` of the palette, the phase
typing, and the period spectrum `{{1, 12, 12, 12}}`, read off the tapestry
produced. -/
def Cdiv : IntProfile TemporalPalette :=
  layingProfile fun F θ ℓ =>
    (∀ r, GroupingEq (F.k r) (ℓ (F.k r))) ∧ PhaseTyped F ℓ ∧ θ.tempSpec = {1, 12, 12, 12}

/-- The rows of the recurrence tapestry of Figure 1.25, with the phases of each
row written locally: the row with `k` phases shows `0, 1, …, k - 1, 0, 1, …`. -/
def recRows : Fin 4 → Fin 12 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]]

/-- The rows of the division tapestry of Figure 1.40, with the phases of each
row written locally: the row with `k` phases holds each phase for a bar of
`12/k` ticks. -/
def divRows : Fin 4 → Fin 12 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],
    ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3]]

/-- Each row of the recurrence tapestry shows only its own phases. -/
theorem recRows_lt : ∀ (r : Fin 4) (t : Fin 12), recRows r t < r.val + 1 := by decide

/-- Each row of the division tapestry shows only its own phases. -/
theorem divRows_lt : ∀ (r : Fin 4) (t : Fin 12), divRows r t < r.val + 1 := by decide

/-- The recurrence tapestry `I_rec` (Figure 1.25) on the support `CycleTime(12)`
of the twelve-tick clock: the rows and phases of the palette `P`, each row
read as in Figure 1.25. -/
abbrev Irec : RectTapestry (CycleTime 12) where
  R := tetractys.R
  V := tetractys.V
  e r t := ⟨recRows r t, recRows_lt r t⟩

/-- The division tapestry `I_div` (Figure 1.40) on the support `CycleTime(12)`
of the twelve-tick clock: the rows and phases of the palette `P`, each row read
as in Figure 1.40. -/
abbrev Idiv : RectTapestry (CycleTime 12) where
  R := tetractys.R
  V := tetractys.V
  e r t := ⟨divRows r t, divRows_lt r t⟩

end Artform
