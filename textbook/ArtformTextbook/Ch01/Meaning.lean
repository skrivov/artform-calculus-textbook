import Mathlib.Data.Fintype.Sigma
import ArtformTextbook.Ch01.Statements.Meaning

/-!
# The two tetractys interpretations coexist (Section 1.6)

The proof of Proposition 1.10. Every check is a finite computation on the
twelve ticks: the phase typing and the covering or grouping equation row by
row, the tapestry that each laying lays from the palette, and the least
periods of its rows. The two tagged witnesses differ because their profiles
differ: the division laying obeys the law of `𝒞_div`, but not the covering
equation of `𝒞_rec`.
-/

namespace Artform

/-! ## Least periods -/

/-- The least period of a row is `d` exactly when `d` is a period of the row
and no smaller number is. -/
theorem RectTapestry.leastPeriod_eq_iff {L : ℕ} [NeZero L] (τ : RectTapestry (CycleTime L))
    (r : τ.R.cells) (d : ℕ) :
    τ.leastPeriod r = d ↔ τ.HasPeriod r d ∧ ∀ m < d, ¬ τ.HasPeriod r m := by
  classical
  exact Nat.find_eq_iff _

/-! ## The recurrence witness -/

/-- Under `ℓ_rec` each row of the palette shows only its own phases. -/
theorem phaseTyped_layRec : PhaseTyped tetractys layRec := by
  change ∀ (r : Fin 4) (t : Fin 12), t.val % (r.val + 1) < r.val + 1
  decide

/-- `ℓ_rec` satisfies the covering equation in every row of the palette. -/
theorem covering_layRec : ∀ r, CoveringEq (tetractys.k r) (layRec (tetractys.k r)) := by
  change ∀ (r : Fin 4) (t : Fin 12),
    (t + 1).val % (r.val + 1) ≡ t.val % (r.val + 1) + 1 [MOD r.val + 1]
  decide

/-- `ℓ_rec` lays the recurrence tapestry `I_rec` from the palette. -/
theorem Irec_eq_lay : Irec = tetractys.lay layRec phaseTyped_layRec := by
  have h : ∀ (r : Fin 4) (t : Fin 12), recRows r t = t.val % (r.val + 1) := by decide
  unfold Irec TemporalPalette.lay
  congr
  funext r t
  exact Fin.ext (h r t)

/-- The periods of a row of `I_rec`, read off its entries. -/
theorem Irec_hasPeriod (r : Fin 4) (d : ℕ) :
    Irec.HasPeriod r d ↔
      0 < d ∧ d ∣ 12 ∧ ∀ t : Fin 12, recRows r (t + Fin.ofNat 12 d) = recRows r t := by
  simp only [RectTapestry.HasPeriod, Fin.ext_iff]

/-- The row of `I_rec` with `k` phases has least period `k`. -/
theorem Irec_leastPeriod (r : Fin 4) : Irec.leastPeriod r = r.val + 1 := by
  rw [RectTapestry.leastPeriod_eq_iff]
  simp only [Irec_hasPeriod]
  revert r
  decide

/-- The period spectrum of `I_rec` is `{{1, 2, 3, 4}}`. -/
theorem Irec_tempSpec : Irec.tempSpec = {1, 2, 3, 4} := by
  change (Finset.univ : Finset (Fin 4)).val.map Irec.leastPeriod = _
  rw [Fin.univ_val_map]
  simp only [List.ofFn_succ, List.ofFn_zero, Irec_leastPeriod]
  decide

/-- The witness `w_rec = (ℓ_rec, c_rec) ∈ IntWit_{𝒞_rec}(P, I_rec)`. -/
def wRec : IntWit Crec tetractys Irec where
  realizer := layRec
  cert := ⟨⟨phaseTyped_layRec, Irec_eq_lay⟩, covering_layRec, phaseTyped_layRec, Irec_tempSpec⟩

/-! ## The division witness -/

/-- Under `ℓ_div` each row of the palette shows only its own phases. -/
theorem phaseTyped_layDiv : PhaseTyped tetractys layDiv := by
  change ∀ (r : Fin 4) (t : Fin 12), (r.val + 1) * t.val / 12 < r.val + 1
  decide

/-- `ℓ_div` satisfies the grouping equation in every row of the palette. -/
theorem grouping_layDiv : ∀ r, GroupingEq (tetractys.k r) (layDiv (tetractys.k r)) := by
  change ∀ (r : Fin 4) (t : Fin 12),
    (r.val + 1) * (t + Fin.ofNat 12 (12 / (r.val + 1))).val / 12 ≡
      (r.val + 1) * t.val / 12 + 1 [MOD r.val + 1]
  decide

/-- `ℓ_div` lays the division tapestry `I_div` from the palette. -/
theorem Idiv_eq_lay : Idiv = tetractys.lay layDiv phaseTyped_layDiv := by
  have h : ∀ (r : Fin 4) (t : Fin 12), divRows r t = (r.val + 1) * t.val / 12 := by decide
  unfold Idiv TemporalPalette.lay
  congr
  funext r t
  exact Fin.ext (h r t)

/-- The periods of a row of `I_div`, read off its entries. -/
theorem Idiv_hasPeriod (r : Fin 4) (d : ℕ) :
    Idiv.HasPeriod r d ↔
      0 < d ∧ d ∣ 12 ∧ ∀ t : Fin 12, divRows r (t + Fin.ofNat 12 d) = divRows r t := by
  simp only [RectTapestry.HasPeriod, Fin.ext_iff]

/-- The constant row of `I_div` has least period `1`, and every other row
takes the whole twelve ticks to come round. -/
theorem Idiv_leastPeriod (r : Fin 4) : Idiv.leastPeriod r = if r = 0 then 1 else 12 := by
  rw [RectTapestry.leastPeriod_eq_iff]
  simp only [Idiv_hasPeriod]
  revert r
  decide

/-- The period spectrum of `I_div` is `{{1, 12, 12, 12}}`. -/
theorem Idiv_tempSpec : Idiv.tempSpec = {1, 12, 12, 12} := by
  change (Finset.univ : Finset (Fin 4)).val.map Idiv.leastPeriod = _
  rw [Fin.univ_val_map]
  simp only [List.ofFn_succ, List.ofFn_zero, Idiv_leastPeriod]
  decide

/-- The witness `w_div = (ℓ_div, c_div) ∈ IntWit_{𝒞_div}(P, I_div)`. -/
def wDiv : IntWit Cdiv tetractys Idiv where
  realizer := layDiv
  cert := ⟨⟨phaseTyped_layDiv, Idiv_eq_lay⟩, grouping_layDiv, phaseTyped_layDiv, Idiv_tempSpec⟩

/-! ## The two profiles differ -/

/-- `ℓ_div` fails the covering equation in the row with two phases: it shows
`0` at the ticks `0` and `1`. -/
theorem not_covering_layDiv : ¬ ∀ r, CoveringEq (tetractys.k r) (layDiv (tetractys.k r)) :=
  fun h => absurd (h 1 0) (by decide)

/-- The recurrence and division profiles are different: `ℓ_div` with
`I_div` obeys the law of `𝒞_div` but not that of `𝒞_rec`. -/
theorem Crec_ne_Cdiv : Crec ≠ Cdiv := by
  intro h
  have hlaw : Crec.Law = Cdiv.Law := eq_of_heq (congr_arg_heq IntProfile.Law h)
  have hdiv : Crec.Law tetractys Idiv layDiv := by
    rw [hlaw]
    exact wDiv.cert.2
  exact not_covering_layDiv hdiv.1

/-! ## Proposition 1.10 -/

/-- **Proposition 1.10** (the two tetractys interpretations coexist). `ℓ_rec`
and `ℓ_div` with their certificates are witnesses in
`IntWit_{𝒞_rec}(P, I_rec)` and `IntWit_{𝒞_div}(P, I_div)`, and tagged with their
profiles and endpoints they are two different elements of `Sem_Γ(P)` whenever
`Γ` lists the two profiles. -/
@[book "prop:tetractys-intwits"]
theorem tetractysIntwits : Statement.tetractysIntwits :=
  ⟨⟨wRec, rfl⟩, ⟨wDiv, rfl⟩, fun Γ _ _ _ _ h =>
    Crec_ne_Cdiv (congrArg (fun x : Sem Γ tetractys => x.1.1) h)⟩

/-! ## Non-vacuity -/

/-- The palette `P` has ten cells, in rows of one, two, three and four. -/
example : Fintype.card ((r : Fin 4) × tetractys.V r) = 10 := by decide

/-- The hypotheses can be met: `Γ = {𝒞_rec, 𝒞_div}` lists the two profiles,
and the two witnesses tagged with their profiles and endpoints are elements of
its fibre `Sem_Γ(P)`. -/
example : Sem ({Crec, Cdiv} : Set (IntProfile TemporalPalette)) tetractys ×
    Sem ({Crec, Cdiv} : Set (IntProfile TemporalPalette)) tetractys :=
  (⟨⟨Crec, Or.inl rfl⟩, Irec, wRec⟩, ⟨⟨Cdiv, Or.inr rfl⟩, Idiv, wDiv⟩)

/-- Selecting the first tagged witness gives an element of the selected layer
`PointedInt_Γ`. -/
example : PointedInt ({Crec, Cdiv} : Set (IntProfile TemporalPalette)) :=
  ⟨tetractys, ⟨Crec, Or.inl rfl⟩, Irec, wRec⟩

/-- The two spectra differ: `{{1, 2, 3, 4}}` against `{{1, 12, 12, 12}}`. -/
example : Irec.tempSpec ≠ Idiv.tempSpec := by
  rw [Irec_tempSpec, Idiv_tempSpec]
  decide

/-- The laws are not empty conditions: the division tapestry has no witness
under the recurrence profile. A laying that lays `I_div` from `P` shows `0` at
the ticks `0` and `1` of the row with two phases, against the covering
equation; this is the move of Section 1.7 that was not made. -/
example : IsEmpty (IntWit Crec tetractys Idiv) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨⟨h, hθ⟩, hcov, -, -⟩ := w.cert
  have he : Idiv.e = (tetractys.lay w.realizer h).e :=
    eq_of_heq (congr_arg_heq RectTapestry.e hθ)
  have h0 : 0 = w.realizer 2 0 := congrArg Fin.val (congrFun (congrFun he 1) 0)
  have h1 : 0 = w.realizer 2 1 := congrArg Fin.val (congrFun (congrFun he 1) 1)
  have c : w.realizer 2 1 ≡ w.realizer 2 0 + 1 [MOD 2] := hcov 1 0
  rw [← h0, ← h1] at c
  exact absurd c (by decide)

end Artform
