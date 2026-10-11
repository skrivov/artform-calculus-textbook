import ArtformTextbook.Ch03.Defs.Recognition

/-!
# Statements of Chapter 3: recognition

Each statement of the book is a proposition here, tagged with the book's label. Its proof, in
`Ch03/Recognition.lean`, is a theorem whose type is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 3.11** (shared positive pattern). Let `G₁` and `G₂` be states profiled by `R`.
1. If a positive template `K` has an instantiation `j₁` in `G₁` and an instantiation `j₂` in
   `G₂`, then `F = j₂ ∘ j₁⁻¹`, defined on `j₁(E_K)`, is a partial positive comparison
   `G₁ ⇀ G₂`, and every atom of `j₁*(𝒜_K)` is credited to it.
2. If a partial positive comparison `F : G₁ ⇀ G₂` credits at least one atom, then renaming its
   active positions to fresh variables and transporting its credited atoms gives a positive
   template `K_F`, with an instantiation `j₁` in `G₁` by the renaming and an instantiation
   `j₂ = F ∘ j₁` in `G₂`; and `j₂ ∘ j₁⁻¹` is `F` restricted to the active positions.

In part 2 the renaming is a bijection `ρ` from the variables of `K_F` onto the active positions
of `F`; the variables keep the sorts of their positions, and the atoms of `K_F` are those whose
renaming is a credited atom. -/
@[book "prop:shared-positive-pattern-book"]
def sharedPositivePattern : Prop :=
  ∀ (R : RecognitionProfile) (G₁ G₂ : ProfiledState R),
    (∀ (K : PositiveTemplate R) (j₁ : Instantiation K G₁) (j₂ : Instantiation K G₂),
      IsPartialComparison G₁ G₂ (Set.range j₁) (j₁.comparison j₂) ∧
      Atom.map j₁ '' K.atoms ⊆ creditedAtoms G₁ G₂ (Set.range j₁) (j₁.comparison j₂)) ∧
    (∀ F : PartialComparison G₁ G₂, F.credited.Nonempty →
      ∃ (K : PositiveTemplate R) (ρ : K.Var ≃ F.active) (j₁ : Instantiation K G₁)
        (j₂ : Instantiation K G₂),
        (∀ x, K.sort x = G₁.sort (ρ x : F.dom)) ∧
        K.atoms = {β | β.map j₁ ∈ F.credited} ∧
        (∀ x, j₁ x = ((ρ x : F.dom) : G₁.Pos)) ∧
        (∀ x, j₂ x = F.toFun (ρ x)) ∧
        ∀ p : F.active, j₂ (ρ.symm p) = F.toFun p)

/-- **Proposition 3.12** (partial profile isomorphism). Let `F : D → D'` be a sort-preserving
bijection between a set of positions of `G₁` and a set of positions of `G₂`, and let every
selected relation and channel be total on both sides, so that every well-sorted tuple of `D` and
of `D'` has a verdict or a value. If the selected tables of `G₁` on `D` and of `G₂` on `D'` agree
through `F` in both directions, then `F` is a strong occurrence of the restriction of `G₁` to `D`
in `G₂`, and `F⁻¹` is one in the other direction; both read labels rigidly, with the identity
label map. Such an `F` is a partial profile isomorphism. Equivalently, `F` and `F⁻¹` each credit
every atom of their domain. -/
@[book "prop:partial-profile-iso-book"]
def partialProfileIso : Prop :=
  ∀ (R : RecognitionProfile) (G₁ G₂ : ProfiledState R) (D : Set G₁.Pos) (D' : Set G₂.Pos)
    (F : D ≃ D'), (∀ x, G₂.sort (F x) = G₁.sort x) → G₁.TotalOn D → G₂.TotalOn D' →
    (TablesAgree G₁ G₂ D (Subtype.val ∘ F) ∧ TablesAgree G₂ G₁ D' (Subtype.val ∘ F.symm) →
      IsStrongOccurrence (G₁.restrict D) G₂ 1 (Subtype.val ∘ F) ∧
      IsStrongOccurrence (G₂.restrict D') G₁ 1 (Subtype.val ∘ F.symm)) ∧
    (TablesAgree G₁ G₂ D (Subtype.val ∘ F) ∧ TablesAgree G₂ G₁ D' (Subtype.val ∘ F.symm) ↔
      CreditsEveryAtom G₁ G₂ D (Subtype.val ∘ F) ∧
      CreditsEveryAtom G₂ G₁ D' (Subtype.val ∘ F.symm))

/-- **Proposition 3.22** (positive occurrences are atom images). The action of `Aut⁺_R(K)` on
`Instantiation_R(K, G)` is free, and two instantiations have the same atom image if and only if
they differ by an element of `Aut⁺_R(K)`, which is then unique. Hence `[j] ↦ aim_K(j)` is a
bijection from `Occurrence⁺_R(K, G)` onto the set of instantiated atom sets in `G`. -/
@[book "prop:atom-image-occurrence-book"]
def atomImageOccurrence : Prop :=
  ∀ (R : RecognitionProfile) (K : PositiveTemplate R) (G : ProfiledState R),
    (∀ (a : K.posAut) (j : Instantiation K G), j.comp a = j → a = 1) ∧
    (∀ j j' : Instantiation K G,
      (j.atomImage = j'.atomImage ↔ ∃ a : K.posAut, j' = j.comp a) ∧
      (j.atomImage = j'.atomImage → ∃! a : K.posAut, j' = j.comp a)) ∧
    ∃ e : PositiveOccurrence K G ≃ Set.range (fun j : Instantiation K G => j.atomImage),
      ∀ j : Instantiation K G, (e (PositiveOccurrence.mk j) : Set (Atom R G.Pos)) = j.atomImage

/-- **Proposition 3.45** (reference marking along a comparison). Let `j_s` and `j_v` instantiate
`K` in `G_s` and `G_v`, let `F = j_v ∘ j_s⁻¹`, and let `λ_v` be a marking of `j_v(E_K)`. Then
`λ_v ∘ F` is a marking of `j_s(E_K)`, and replacing `j_s` by `j_s ∘ a` for `a ∈ Aut⁺_R(K)`
replaces it by `λ_v ∘ j_v ∘ a⁻¹ ∘ j_s⁻¹`. The pulled-back marking is indexed by the comparison,
and it is unchanged under `a` only when `λ_v ∘ j_v` is.

Here `λ_v ∘ F` is `Marking.pullback j_s j_v λ_v`; that it is a marking of `j_s(E_K)` is the
statement that `F` carries `j_s(E_K)` into `j_v(E_K)`, the domain of `λ_v`. The replacement has
the same domain, `j_s(E_K) = (j_s ∘ a)(E_K)`, and the two markings are compared at each of its
positions. In `λ_v ∘ j_v ∘ a⁻¹ ∘ j_s⁻¹`, `j_v` is read as a map into `j_v(E_K)`. The last clause
is stated in both directions. -/
@[book "prop:reference-marking-pullback-book"]
def referenceMarkingPullback : Prop :=
  ∀ (R : RecognitionProfile) (K : PositiveTemplate R) (Gs Gv : ProfiledState R)
    (js : Instantiation K Gs) (jv : Instantiation K Gv) (N : Type)
    (lv : Marking (Set.range jv) N),
    (∀ p : Set.range js, js.comparison jv p ∈ Set.range jv) ∧
    (∀ a : K.posAut, Set.range (js.comp a) = Set.range js ∧
      ∀ (p : Gs.Pos) (h : p ∈ Set.range (js.comp a)) (h' : p ∈ Set.range js),
        Marking.pullback (js.comp a) jv lv ⟨p, h⟩ =
          (lv ∘ Set.rangeFactorization jv ∘ ⇑(a : Equiv.Perm K.Var)⁻¹ ∘
            (Equiv.ofInjective js js.injective).symm) ⟨p, h'⟩) ∧
    ∀ a : K.posAut,
      (∀ (p : Gs.Pos) (h : p ∈ Set.range (js.comp a)) (h' : p ∈ Set.range js),
        Marking.pullback (js.comp a) jv lv ⟨p, h⟩ = Marking.pullback js jv lv ⟨p, h'⟩) ↔
      lv ∘ Set.rangeFactorization jv ∘ ⇑(a : Equiv.Perm K.Var) = lv ∘ Set.rangeFactorization jv

end Artform.Statement
