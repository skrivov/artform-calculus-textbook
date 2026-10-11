import ArtformTextbook.Ch06.Defs.Source

/-!
# Temporal links (Section 6.4, "Gauge changes from tick to tick")

A run of the Maxwell tick, and Definition 6.8: a temporal-link table, the
extended tick that moves the potential by the difference of the temporal links,
and the gauge change by a site function at every tick. Runs are indexed by the
ticks `0, 1, 2, …`; a run over finitely many ticks is the start of one.
-/

namespace Artform

variable (K : Canvas)

/-- A run of the Maxwell tick for the source `J`: a state at every tick, each
the macro-tick of the one before. -/
def IsMaxwellRun (J : K.E → ZMod 8) (s : ℕ → MaxwellState K) : Prop :=
  ∀ t, s (t + 1) = maxwellTick K J (s t)

/-- **Definition 6.8** (temporal links). A temporal-link table `a₀`: a site
function for each tick, its value `a₀(t)(v)` standing on the temporal link
from `(v, t)` to `(v, t + 1)`. -/
@[book "def:temporal-links"]
abbrev TemporalLinks : Type := ℕ → K.V → ZMod 8

/-- **Definition 6.8** (extended Maxwell tick), from a tick whose temporal
links are the site function `a`: it keeps the kick, `E' = E + curl*(curl A) − J`
with the charge update `ρ' = ρ − div J`, and moves the potential by
`A' = A − E' + Da`. -/
@[book "def:temporal-links"]
def extendedTick (J : K.E → ZMod 8) (a : K.V → ZMod 8) (s : MaxwellState K) :
    MaxwellState K :=
  let s' := maxwellTick K J s
  ⟨s'.A + K.diff a, s'.E, s'.ρ⟩

/-- A run of the extended tick: a state at every tick and a temporal-link
table, each state the extended tick of the one before, with the temporal links
from that tick. -/
def IsExtendedRun (J : K.E → ZMod 8) (s : ℕ → MaxwellState K) (a : TemporalLinks K) :
    Prop :=
  ∀ t, s (t + 1) = extendedTick K J (a t) (s t)

variable {K}

/-- **Definition 6.8** (a gauge change, on the states). The gauge change by
site functions `χ_t` adds `Dχ_t` to the potential at tick `t`. -/
@[book "def:temporal-links"]
def gaugeStates (χ : ℕ → K.V → ZMod 8) (s : ℕ → MaxwellState K) : ℕ → MaxwellState K :=
  fun t => (s t).gauge (χ t)

/-- **Definition 6.8** (a gauge change, on the temporal links). The gauge
change by site functions `χ_t` adds `χ_{t+1} − χ_t` to the temporal links from
tick `t`. -/
@[book "def:temporal-links"]
def gaugeLinks (χ : ℕ → K.V → ZMod 8) (a : TemporalLinks K) : TemporalLinks K :=
  fun t => a t + (χ (t + 1) - χ t)

end Artform
