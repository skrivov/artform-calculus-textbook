import ArtformTextbook.Ch01.Defs.Meaning

/-!
# Statements of Chapter 1: one artform, many meanings

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 1.10** (the two tetractys interpretations coexist). Let `P`
be the ten-cell palette with row sizes `k = 1, 2, 3, 4`, and write the phases
in each row locally as `0, …, k - 1`. On the common clock `t ∈ {0, …, 11}` the
two laying rules are `ℓ_rec(k, t) = t mod k` and `ℓ_div(k, t) = ⌊kt/12⌋`.
There are profiles `𝒞_rec` and `𝒞_div` whose laws are respectively the
covering and the grouping equation, the phase typing, and the period spectra
`{{1, 2, 3, 4}}` and `{{1, 12, 12, 12}}`. Consequently `ℓ_rec` with a
certificate `c_rec` is a witness `w_rec ∈ IntWit_{𝒞_rec}(P, I_rec)`, `ℓ_div`
with a certificate `c_div` is a witness `w_div ∈ IntWit_{𝒞_div}(P, I_div)`,
and whenever `Γ` lists the two profiles, tagging each witness with its profile
and endpoint gives two elements of `Sem_Γ(P)`, which are different.

In Lean `P` is `tetractys`, the laying rules are `layRec` and `layDiv`, the
profiles are the definitions `Crec` and `Cdiv`, and the endpoints are the
tapestries `Irec` and `Idiv` of Figures 1.25 and 1.40. -/
@[book "prop:tetractys-intwits"]
def tetractysIntwits : Prop :=
  (∃ w : IntWit Crec tetractys Irec, w.realizer = layRec) ∧
  (∃ w : IntWit Cdiv tetractys Idiv, w.realizer = layDiv) ∧
  ∀ (Γ : Set (IntProfile TemporalPalette)) (hrec : Crec ∈ Γ) (hdiv : Cdiv ∈ Γ)
    (wrec : IntWit Crec tetractys Irec) (wdiv : IntWit Cdiv tetractys Idiv),
    (⟨⟨Crec, hrec⟩, Irec, wrec⟩ : Sem Γ tetractys) ≠ ⟨⟨Cdiv, hdiv⟩, Idiv, wdiv⟩

end Artform.Statement
