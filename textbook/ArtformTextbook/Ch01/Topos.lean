import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import ArtformTextbook.Ch01.Statements

/-!
# Sets form a topos (Section 1.10, the Category Café)

The proof of Proposition 1.29, in the order of the book's proof.

* A singleton is terminal, and the pullbacks of `Set` and `FinSet` are Mathlib's
  (those of `FinSet` are computed in `Set`, and are finite when the inputs are).
* Function sets are exponentials: `B^A = A → B` with evaluation, a finite set when `A`
  and `B` are. An element of a product `Z ⨯ A` is given by its two components
  (`SetTopos.pair`, `SetTopos.finPair`).
* A monomorphism of sets is an injective function `m : S ⟶ X`, and a square over
  `true : 1 ⟶ {0,1}` with `m` on top is a pullback exactly when `χ` takes the value `1`
  on the image of `m` and nowhere else (`SetTopos.isPullback_true_iff`). The
  characteristic function of the image is such a `χ`, and it is the only one. In `FinSet`
  the same square is read in `Set` through the inclusion, which preserves pullbacks
  and monomorphisms and reflects pullbacks.
-/

namespace Artform

open CategoryTheory CategoryTheory.Limits

namespace SetTopos

/-! ### The classifier of `Set` -/

/-- In `Set`, for an injective `m : S ⟶ X`, the square `m ≫ χ = u ≫ true` over
`true(*) = 1` is a pullback exactly when `χ` takes the value `1` on the image of `m`
and nowhere else. -/
theorem isPullback_true_iff {S X : Type} (m : S ⟶ X) (hm : Function.Injective m)
    (u : S ⟶ PUnit.{1}) (χ : X ⟶ Fin 2) :
    IsPullback m u χ (TypeCat.ofHom fun _ => (1 : Fin 2)) ↔
      ∀ x, χ x = 1 ↔ x ∈ Set.range m := by
  rw [Types.isPullback_iff]
  constructor
  · rintro ⟨w, -, h⟩ x
    constructor
    · intro hx
      obtain ⟨s, hs, -⟩ := h x PUnit.unit hx
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      exact ConcreteCategory.congr_hom w s
  · intro h
    refine ⟨?_, fun x y hxy => hm hxy.1, fun x t hx => ?_⟩
    · exact ConcreteCategory.hom_ext _ _ fun s => (h (m s)).2 ⟨s, rfl⟩
    · obtain ⟨s, hs⟩ := (h x).1 hx
      exact ⟨s, hs, Subsingleton.elim _ _⟩

open scoped Classical in
/-- The characteristic function of the image of `m`: `1` on the image, `0` elsewhere. -/
noncomputable def charFun {S X : Type} (m : S ⟶ X) (x : X) : Fin 2 :=
  if x ∈ Set.range m then 1 else 0

theorem charFun_eq_one_iff {S X : Type} (m : S ⟶ X) (x : X) :
    charFun m x = 1 ↔ x ∈ Set.range m := by
  unfold charFun
  split_ifs with h <;> simp [h]

/-- An element of `{0,1}` is determined by whether it is `1`. -/
theorem fin_two_eq_of_iff : ∀ a b : Fin 2, (a = 1 ↔ b = 1) → a = b := by
  decide

/-- `true : 1 ⟶ {0,1}`, `true(*) = 1`, is a subobject classifier of `Set`. -/
theorem set_classifier (hone : IsTerminal (PUnit.{1} : Type)) :
    IsSubobjectClassifier hone (Fin 2) (TypeCat.ofHom fun _ => (1 : Fin 2)) := by
  intro S X m hm
  have hinj : Function.Injective m := (mono_iff_injective m).1 hm
  refine ⟨TypeCat.ofHom (charFun m), (isPullback_true_iff m hinj _ _).2 (charFun_eq_one_iff m),
    fun χ hχ => ?_⟩
  have h := (isPullback_true_iff m hinj _ _).1 hχ
  exact ConcreteCategory.hom_ext _ _ fun x =>
    fin_two_eq_of_iff _ _ ((h x).trans (charFun_eq_one_iff m x).symm)

/-! ### The exponentials of `Set` -/

/-- The point `x` of a set `X`, as an arrow from the one-point set. -/
def point {X : Type} (x : X) : PUnit.{1} ⟶ X :=
  TypeCat.ofHom fun _ => x

section Pair

variable {Z A : Type}

/-- The element of the product `Z ⨯ A` with components `z` and `a`. -/
noncomputable def pair (z : Z) (a : A) : (Z ⨯ A : Type) :=
  prod.lift (point z) (point a) PUnit.unit

theorem pair_fst (z : Z) (a : A) : (prod.fst : Z ⨯ A ⟶ Z) (pair z a) = z :=
  ConcreteCategory.congr_hom (prod.lift_fst (point z) (point a)) PUnit.unit

theorem pair_snd (z : Z) (a : A) : (prod.snd : Z ⨯ A ⟶ A) (pair z a) = a :=
  ConcreteCategory.congr_hom (prod.lift_snd (point z) (point a)) PUnit.unit

/-- An element of `Z ⨯ A` is the pair of its components. -/
theorem pair_eta (x : (Z ⨯ A : Type)) :
    pair ((prod.fst : Z ⨯ A ⟶ Z) x) ((prod.snd : Z ⨯ A ⟶ A) x) = x := by
  have : point (pair ((prod.fst : Z ⨯ A ⟶ Z) x) ((prod.snd : Z ⨯ A ⟶ A) x)) = point x :=
    prod.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => pair_fst _ _)
      (ConcreteCategory.hom_ext _ _ fun _ => pair_snd _ _)
  exact ConcreteCategory.congr_hom this PUnit.unit

end Pair

/-- Function sets are exponentials in `Set`: `B^A = A → B`, with evaluation. -/
theorem set_hasExponentials : HasExponentials Type := by
  intro A B
  refine ⟨A → B, TypeCat.ofHom fun x => (prod.fst : (A → B) ⨯ A ⟶ (A → B)) x
    ((prod.snd : (A → B) ⨯ A ⟶ A) x), fun Z h => ?_⟩
  refine ⟨TypeCat.ofHom fun z a => h (pair z a), ?_, fun g hg => ?_⟩
  · refine ConcreteCategory.hom_ext _ _ fun x => ?_
    have h1 := ConcreteCategory.congr_hom
      (prod.map_fst (TypeCat.ofHom fun z a => h (pair z a)) (𝟙 A)) x
    have h2 := ConcreteCategory.congr_hom
      (prod.map_snd (TypeCat.ofHom fun z a => h (pair z a)) (𝟙 A)) x
    simp only [types_comp_apply, types_id_apply] at h1 h2
    simp only [types_comp_apply, TypeCat.ofHom_apply, h1, h2, pair_eta]
  · refine ConcreteCategory.hom_ext _ _ fun z => funext fun a => ?_
    have h1 := ConcreteCategory.congr_hom (prod.map_fst g (𝟙 A)) (pair z a)
    have h2 := ConcreteCategory.congr_hom (prod.map_snd g (𝟙 A)) (pair z a)
    have h3 := ConcreteCategory.congr_hom hg (pair z a)
    simp only [types_comp_apply, types_id_apply, pair_fst, pair_snd] at h1 h2
    simp only [types_comp_apply, TypeCat.ofHom_apply, h1, h2] at h3
    simp only [TypeCat.ofHom_apply, ← h3]

/-- `Set` is a topos. -/
theorem set_isTopos : IsTopos Type :=
  ⟨inferInstance, inferInstance, ⟨inferInstance, set_hasExponentials⟩,
    ⟨PUnit, Types.isTerminalPUnit, Fin 2, _, set_classifier Types.isTerminalPUnit⟩⟩

/-! ### `FinSet` -/

/-- The one-point finite set is terminal. -/
def finTerminal : IsTerminal (FintypeCat.of PUnit.{1}) :=
  IsTerminal.ofUniqueHom (fun _ => FintypeCat.homMk fun _ => PUnit.unit)
    fun _ _ => FintypeCat.hom_ext _ _ fun _ => Subsingleton.elim _ _

/-- `true : 1 ⟶ {0,1}`, `true(*) = 1`, is a subobject classifier of `FinSet`: the
square is read in `Set` through the inclusion. -/
theorem finSet_classifier (hone : IsTerminal (FintypeCat.of PUnit.{1})) :
    IsSubobjectClassifier hone (FintypeCat.of (Fin 2))
      (FintypeCat.homMk fun _ => (1 : Fin 2)) := by
  intro S X m hm
  have hinj : Function.Injective (FintypeCat.incl.map m) :=
    (mono_iff_injective _).1 (FintypeCat.incl.map_mono m)
  refine ⟨FintypeCat.homMk (charFun (FintypeCat.incl.map m)), ?_, fun χ hχ => ?_⟩
  · apply IsPullback.of_map_of_faithful FintypeCat.incl
    exact (isPullback_true_iff _ hinj _ _).2 (charFun_eq_one_iff _)
  · have h := (isPullback_true_iff _ hinj _ _).1 (hχ.map FintypeCat.incl)
    exact FintypeCat.hom_ext _ _ fun x =>
      fin_two_eq_of_iff _ _ ((h x).trans (charFun_eq_one_iff _ x).symm)

/-- The point `x` of a finite set `X`, as an arrow from the one-point set. -/
def finPoint {X : FintypeCat.{0}} (x : X) : FintypeCat.of PUnit.{1} ⟶ X :=
  FintypeCat.homMk fun _ => x

section FinPair

variable {Z A : FintypeCat.{0}}

/-- The element of the product `Z ⨯ A` of finite sets with components `z` and `a`. -/
noncomputable def finPair (z : Z) (a : A) : (Z ⨯ A : FintypeCat.{0}) :=
  prod.lift (finPoint z) (finPoint a) PUnit.unit

theorem finPair_fst (z : Z) (a : A) : (prod.fst : Z ⨯ A ⟶ Z) (finPair z a) = z :=
  ConcreteCategory.congr_hom (prod.lift_fst (finPoint z) (finPoint a)) PUnit.unit

theorem finPair_snd (z : Z) (a : A) : (prod.snd : Z ⨯ A ⟶ A) (finPair z a) = a :=
  ConcreteCategory.congr_hom (prod.lift_snd (finPoint z) (finPoint a)) PUnit.unit

/-- An element of `Z ⨯ A` is the pair of its components. -/
theorem finPair_eta (x : (Z ⨯ A : FintypeCat.{0})) :
    finPair ((prod.fst : Z ⨯ A ⟶ Z) x) ((prod.snd : Z ⨯ A ⟶ A) x) = x := by
  have : finPoint (finPair ((prod.fst : Z ⨯ A ⟶ Z) x) ((prod.snd : Z ⨯ A ⟶ A) x)) =
      finPoint x :=
    prod.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => finPair_fst _ _)
      (ConcreteCategory.hom_ext _ _ fun _ => finPair_snd _ _)
  exact ConcreteCategory.congr_hom this PUnit.unit

end FinPair

/-- Function sets of finite sets are finite, and they are the exponentials of `FinSet`:
`B^A = A → B`, with evaluation. -/
theorem finSet_hasExponentials : HasExponentials FintypeCat.{0} := by
  intro A B
  refine ⟨FintypeCat.of (A → B), FintypeCat.homMk fun x =>
    (prod.fst : FintypeCat.of (A → B) ⨯ A ⟶ FintypeCat.of (A → B)) x
    ((prod.snd : FintypeCat.of (A → B) ⨯ A ⟶ A) x), fun Z h => ?_⟩
  refine ⟨FintypeCat.homMk fun z a => h (finPair z a), ?_, fun g hg => ?_⟩
  · refine ConcreteCategory.hom_ext _ _ fun x => ?_
    have h1 := ConcreteCategory.congr_hom
      (prod.map_fst (FintypeCat.homMk (Y := FintypeCat.of (A → B)) fun z a => h (finPair z a))
        (𝟙 A)) x
    have h2 := ConcreteCategory.congr_hom
      (prod.map_snd (FintypeCat.homMk (Y := FintypeCat.of (A → B)) fun z a => h (finPair z a))
        (𝟙 A)) x
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h1 h2
    simp only [ConcreteCategory.comp_apply, FintypeCat.homMk_apply, h1, h2]
    exact congrArg (ConcreteCategory.hom h) (finPair_eta x)
  · refine ConcreteCategory.hom_ext _ _ fun z => funext fun a => ?_
    have h1 := ConcreteCategory.congr_hom (prod.map_fst g (𝟙 A)) (finPair z a)
    have h2 := ConcreteCategory.congr_hom (prod.map_snd g (𝟙 A)) (finPair z a)
    have h3 := ConcreteCategory.congr_hom hg (finPair z a)
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, finPair_fst,
      finPair_snd] at h1 h2
    simp only [ConcreteCategory.comp_apply, FintypeCat.homMk_apply, h1, h2] at h3
    exact h3

/-- `FinSet` is a topos. -/
theorem finSet_isTopos : IsTopos FintypeCat.{0} :=
  ⟨inferInstance, inferInstance, ⟨inferInstance, finSet_hasExponentials⟩,
    ⟨_, finTerminal, _, _, finSet_classifier finTerminal⟩⟩

end SetTopos

/-- **Proposition 1.29** (Sets form a topos). `FinSet` and `Set` are topoi, with
`Ω = {0,1}` and `true(*) = 1`. -/
@[book "prop:finset-topos-book"]
theorem finsetTopos : Statement.finsetTopos :=
  ⟨SetTopos.set_isTopos, SetTopos.finSet_isTopos,
    ⟨Types.isTerminalPUnit, SetTopos.set_classifier _⟩,
    ⟨SetTopos.finTerminal, SetTopos.finSet_classifier _⟩⟩

end Artform
