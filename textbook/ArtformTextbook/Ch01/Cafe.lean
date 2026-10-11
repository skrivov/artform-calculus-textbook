import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import ArtformTextbook.Ch01.Statements.Cafe

/-!
# The Category Café: the Artform category, its quotients, adjoints and topoi (Section 1.10)

The proofs of Propositions 1.16, 1.19, 1.27 and 1.30, each in the order of the book's proof.

* **1.16.** Concatenation of lists is associative and has the empty lists as units (Mathlib's
  `Quiver.Path.comp_assoc`, `nil_comp` and `comp_nil`). An equivalence relation preserved by
  composition is a congruence, so `[g] ∘ [f] = [g ∘ f]` does not depend on the representatives:
  Mathlib's quotient category `CategoryTheory.Quotient r` is the quotient, and two lists have the
  same class exactly when they are related.
* **1.19.** `S(g ∘ f) = S(g) ∘ S(f)` shows that state-equivalence is preserved by composition, and
  Proposition 1.16 gives the quotient category. The state interpretation descends to it
  (`Quotient.lift`), and two classes with the same state function have state-equivalent
  representatives, so they are equal: the quotient's state interpretation is faithful.
* **1.27.** An arrow `Σ_f E ⟶ B` is, by the case rule, one function `E(j) → B(f(j))` for each `j`,
  that is, an arrow `E ⟶ f^* B`; an arrow `B ⟶ Π_f E` is, by currying, one function
  `B(f(j)) → E(j)` for each `j`, that is, an arrow `f^* B ⟶ E`. Both bijections commute with
  composition on either side (`Adjunction.mkOfHomEquiv`).
* **1.30.** In a topos the pairing `⟨1_X, 1_X⟩` has `p₁ ∘ ⟨1_X, 1_X⟩ = 1_X = p₂ ∘ ⟨1_X, 1_X⟩`; a
  concatenation is empty only when both lists are, so `p₁` and `p₂` are both the empty list and
  `f = p₁ ∘ ⟨f, g⟩ = p₂ ∘ ⟨f, g⟩ = g`: between two frames there is at most one script. Every script
  is then a monomorphism; the script `X ⟶ 1` is classified, and its pullback square gives a script
  `1 ⟶ X`, so `X ⟶ 1` is invertible. In a free category an invertible script is empty, so every
  frame is `1`, and the only script `1 ⟶ 1` is the empty one: there is no operation.
-/

namespace Artform

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

/-! ## Proposition 1.16: the Artform category and its quotients -/

namespace Cafe

section Quotients

variable {C : Type u} [Category.{v} C]

/-- An equivalence relation on parallel arrows that is preserved by composition is a
congruence. -/
theorem congruence_of {r : HomRel C} (hr : ∀ A B : C, Equivalence (@r A B))
    (hc : ∀ ⦃A B D : C⦄ (f f' : A ⟶ B) (g g' : B ⟶ D),
      r f f' → r g g' → r (f ≫ g) (f' ≫ g')) :
    Congruence r where
  equivalence := hr _ _
  comp_left f _ _ h := hc _ _ _ _ ((hr _ _).refl f) h
  comp_right g h := hc _ _ _ _ h ((hr _ _).refl g)

/-- Mathlib's quotient category by a congruence is the quotient: its functor is a bijection
on objects, every arrow is a class, and two arrows have the same class exactly when they are
related. -/
theorem isQuotientBy_functor (r : HomRel C) [Congruence r] :
    IsQuotientBy r (CategoryTheory.Quotient.functor r) :=
  ⟨(CategoryTheory.Quotient.equiv r).symm.bijective, inferInstance,
    fun _ _ f g => CategoryTheory.Quotient.functor_map_eq_iff r f g⟩

end Quotients

end Cafe

/-- **Proposition 1.16** (the Artform category). -/
@[book "prop:artform-category-book"]
theorem artformCategory : Statement.artformCategory.{v, u} := by
  intro F _
  refine ⟨fun _ _ _ _ f g h => Quiver.Path.comp_assoc f g h,
    fun _ _ f => ⟨Quiver.Path.nil_comp f, Quiver.Path.comp_nil f⟩,
    fun _ => rfl, fun _ _ _ _ _ => rfl, fun r hr hc => ?_⟩
  have := Cafe.congruence_of hr hc
  exact ⟨_, inferInstance, CategoryTheory.Quotient.functor r, Cafe.isQuotientBy_functor r⟩

/-! ## Proposition 1.19: the semantic quotient -/

namespace StateInterpretation

variable {F : Type u} [Quiver.{v} F] (S : StateInterpretation.{w} F)

/-- Two scripts are state-equivalent exactly when they have the same state function. -/
theorem stateEquivalent_iff {A B : ArtSyn F} (f g : A ⟶ B) :
    S.StateEquivalent f g ↔ S.functor.map f = S.functor.map g :=
  ⟨fun h => ConcreteCategory.hom_ext _ _ fun x => h x,
    fun h x => ConcreteCategory.congr_hom h x⟩

/-- Equality of functions is an equivalence relation. -/
theorem stateEquivalent_equivalence (A B : ArtSyn F) :
    Equivalence (fun f g : A ⟶ B => S.StateEquivalent f g) where
  refl _ _ := rfl
  symm h x := (h x).symm
  trans h h' x := (h x).trans (h' x)

/-- State-equivalence is preserved by composition: `S(g ∘ f) = S(g) ∘ S(f)`. -/
theorem stateEquivalent_comp ⦃A B C : ArtSyn F⦄ (f f' : A ⟶ B) (g g' : B ⟶ C)
    (hf : S.StateEquivalent f f') (hg : S.StateEquivalent g g') :
    S.StateEquivalent (f ≫ g) (f' ≫ g') := by
  rw [stateEquivalent_iff] at *
  rw [Functor.map_comp, Functor.map_comp, hf, hg]

end StateInterpretation

/-- **Proposition 1.19** (the semantic quotient). -/
@[book "prop:semantic-quotient-book"]
theorem semanticQuotient : Statement.semanticQuotient.{w, v, u} := by
  intro F _ S
  refine ⟨S.stateEquivalent_comp, ?_⟩
  have := Cafe.congruence_of S.stateEquivalent_equivalence S.stateEquivalent_comp
  have H : ∀ (A B : ArtSyn F) (f g : A ⟶ B), S.StateEquivalent f g →
      S.functor.map f = S.functor.map g :=
    fun _ _ f g h => (S.stateEquivalent_iff f g).1 h
  refine ⟨_, inferInstance, CategoryTheory.Quotient.functor S.StateEquivalent,
    CategoryTheory.Quotient.lift S.StateEquivalent S.functor H, Cafe.isQuotientBy_functor _,
    CategoryTheory.Quotient.lift_spec _ _ _, ⟨fun {X Y} a b hab => ?_⟩⟩
  -- two classes with the same state function were identified by the definition
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor S.StateEquivalent).map_surjective a
  obtain ⟨g, rfl⟩ := (CategoryTheory.Quotient.functor S.StateEquivalent).map_surjective b
  exact CategoryTheory.Quotient.sound _ ((S.stateEquivalent_iff f g).2 hab)

/-! ## Proposition 1.27: adjoints of reindexing -/

namespace Fam

variable {I J : Type u} (f : J → I)

/-- The case rule over the fibres of `f`: an arrow `Σ_f E ⟶ B` is one function
`E(j) → B(f(j))` for each `j`, that is, an arrow `E ⟶ f^* B`. The way back sends the entry
`e` at `j` in the fibre over `i` to the value at `e`, carried along `f(j) = i`. -/
def sigmaHomEquiv (E : Fam J) (B : Fam I) :
    ((sigma f).obj E ⟶ B) ≃ (E ⟶ (reindex f).obj B) where
  toFun φ j := TypeCat.ofHom fun e => φ (f j) ⟨⟨j, rfl⟩, e⟩
  invFun ψ _ := TypeCat.ofHom fun x => cast (congrArg B x.1.2) (ψ x.1.1 x.2)
  left_inv φ := by
    ext i ⟨⟨j, hj⟩, e⟩
    subst hj
    rfl
  right_inv _ := rfl

/-- `Σ_f ⊣ f^*`: the case rule commutes with composition before and after. -/
def sigmaAdjunction : sigma f ⊣ reindex f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sigmaHomEquiv f
      homEquiv_naturality_left_symm := by
        intro _ _ _ _ _
        ext i ⟨⟨j, hj⟩, e⟩
        subst hj
        rfl
      homEquiv_naturality_right := by
        intro _ _ _ _ _
        rfl }

/-- Currying over the fibres of `f`: an arrow `B ⟶ Π_f E` is one function `B(f(j)) → E(j)`
for each `j`, that is, an arrow `f^* B ⟶ E`. The way there sends `b` in `B(i)` to the
assignment whose entry at `j` in the fibre over `i` is the value at `b`, carried along
`i = f(j)`. -/
def piHomEquiv (B : Fam I) (E : Fam J) :
    ((reindex f).obj B ⟶ E) ≃ (B ⟶ (pi f).obj E) where
  toFun φ _ := TypeCat.ofHom fun b j => φ j.1 (cast (congrArg B j.2).symm b)
  invFun ψ j := TypeCat.ofHom fun b => ψ (f j) b ⟨j, rfl⟩
  left_inv _ := rfl
  right_inv ψ := by
    ext i b
    funext ⟨j, hj⟩
    subst hj
    rfl

/-- `f^* ⊣ Π_f`: currying commutes with composition before and after. -/
def piAdjunction : reindex f ⊣ pi f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := piHomEquiv f
      homEquiv_naturality_left_symm := by
        intro _ _ _ _ _
        ext j b
        rfl
      homEquiv_naturality_right := by
        intro _ _ _ _ _
        ext i b
        funext ⟨j, hj⟩
        subst hj
        rfl }

end Fam

/-- **Proposition 1.27** (adjoints of reindexing). -/
@[book "prop:adjoints-book"]
theorem adjoints : Statement.adjoints.{u} :=
  fun _ _ f => ⟨⟨Fam.sigmaAdjunction f⟩, ⟨Fam.piAdjunction f⟩⟩

/-! ## Proposition 1.30: the Artform category is not a topos -/

namespace ArtSyn

variable {F : Type u} [Quiver.{v} F]

/-- The length of a script: the number of operations in its list. -/
def length {A B : ArtSyn F} (f : A ⟶ B) : ℕ :=
  Quiver.Path.length (V := F) f

theorem length_comp {A B C : ArtSyn F} (f : A ⟶ B) (g : B ⟶ C) :
    length (f ≫ g) = length f + length g :=
  Quiver.Path.length_comp (V := F) f g

theorem length_id (A : ArtSyn F) : length (𝟙 A) = 0 :=
  rfl

/-- A script of length zero has the same source and target. -/
theorem eq_of_length_eq_zero {A B : ArtSyn F} (f : A ⟶ B) (hf : length f = 0) : A = B :=
  Quiver.Path.eq_of_length_zero (V := F) f hf

/-- Two scripts of length zero with the same endpoints are equal: both are the empty list. -/
theorem eq_of_length_eq_zero_of_length_eq_zero {A B : ArtSyn F} (f g : A ⟶ B)
    (hf : length f = 0) (hg : length g = 0) : f = g := by
  obtain rfl := eq_of_length_eq_zero f hf
  exact (Quiver.Path.eq_nil_of_length_zero (V := F) f hf).trans
    (Quiver.Path.eq_nil_of_length_zero (V := F) g hg).symm

/-- A concatenation of two lists is the empty list only when both are empty; so if
`g ∘ f = 1_A` for `f : A ⟶ B`, then `A = B`: in a free category the only isomorphisms are
identities. -/
theorem eq_of_comp_eq_id {A B : ArtSyn F} (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) :
    A = B := by
  have hl := congrArg length h
  rw [length_comp, length_id] at hl
  exact eq_of_length_eq_zero f (by omega)

/-- With binary products, between two frames there is at most one script: the projections
`p₁, p₂ : X × X ⟶ X` are both the empty list, so `f = p₁ ∘ ⟨f, g⟩ = p₂ ∘ ⟨f, g⟩ = g`. -/
theorem subsingleton_hom [HasBinaryProducts (ArtSyn F)] (Z X : ArtSyn F) :
    Subsingleton (Z ⟶ X) := by
  have h1 := congrArg length (prod.lift_fst (𝟙 X) (𝟙 X))
  have h2 := congrArg length (prod.lift_snd (𝟙 X) (𝟙 X))
  rw [length_comp, length_id] at h1 h2
  have hfs : (prod.fst : X ⨯ X ⟶ X) = prod.snd :=
    eq_of_length_eq_zero_of_length_eq_zero _ _ (by omega) (by omega)
  refine ⟨fun f g => ?_⟩
  calc f = prod.lift f g ≫ prod.fst := (prod.lift_fst f g).symm
    _ = prod.lift f g ≫ prod.snd := by rw [hfs]
    _ = g := prod.lift_snd f g

/-- If there is at most one script from a frame to itself, the frame has no operation to
itself: the list of that one operation would be the empty list. -/
theorem isEmpty_of_subsingleton (A : ArtSyn F) (h : Subsingleton (A ⟶ A)) :
    IsEmpty (Quiver.Hom (V := F) A A) :=
  ⟨fun o => Nat.one_ne_zero (congrArg length (h.elim (show A ⟶ A from o.toPath) (𝟙 A)))⟩

end ArtSyn

/-- **Proposition 1.30** (the Artform category is not a topos). -/
@[book "prop:artform-not-topos-book"]
theorem artformNotTopos : Statement.artformNotTopos.{v, u} := by
  intro F _ ⟨_, _, ⟨_, _⟩, one, hone, Ω, tru, hcl⟩
  -- binary products: between two frames there is at most one script
  have hsub := ArtSyn.subsingleton_hom (F := F)
  -- every script is a monomorphism, and the classifier makes `X ⟶ 1` invertible
  have heq : ∀ X : ArtSyn F, X = one := by
    intro X
    have hm : Mono (hone.from X) := ⟨fun _ _ _ => Subsingleton.elim _ _⟩
    obtain ⟨χ, hχ, -⟩ := hcl (hone.from X) hm
    let l : one ⟶ X := hχ.lift (𝟙 one) (𝟙 one) (Subsingleton.elim _ _)
    exact (ArtSyn.eq_of_comp_eq_id l (hone.from X) (Subsingleton.elim _ _)).symm
  refine ⟨⟨one, heq⟩, fun A B => ?_⟩
  -- the only script `1 ⟶ 1` is the empty one
  obtain rfl : A = B := (heq A).trans (heq B).symm
  exact ArtSyn.isEmpty_of_subsingleton A (hsub A A)

/-! ## Non-vacuity -/

namespace Cafe

/-! ### The binary lamp (Propositions 1.16 and 1.19) -/

/-- The binary lamp has one frame. -/
inductive LampFrame : Type
  | lamp

/-- The lamp's one declared operation, the toggle. -/
inductive LampOp : LampFrame → LampFrame → Type
  | toggle : LampOp .lamp .lamp

instance : Quiver.{0} LampFrame :=
  ⟨LampOp⟩

/-- The lamp, as an object of the Artform category. -/
def lamp : ArtSyn LampFrame :=
  LampFrame.lamp

/-- The script that toggles the lamp once. -/
def toggle : lamp ⟶ lamp :=
  (Paths.of LampFrame).map LampOp.toggle

/-- The lamp's legal states are off and on, and the toggle switches them. -/
def lampStates : StateInterpretation LampFrame where
  State _ := Bool
  act _ := not

/-- The lamp with a toggle counter: the state also records how often the lamp was toggled. -/
def countedLamp : StateInterpretation LampFrame where
  State _ := Bool × ℕ
  act _ s := (!s.1, s.2 + 1)

/-- Two toggles and the empty script are different scripts. -/
example : toggle ≫ toggle ≠ 𝟙 lamp :=
  fun h => nomatch congrArg ArtSyn.length h

/-- Two toggles and the empty script have the same state function on the lamp. -/
example : lampStates.StateEquivalent (toggle ≫ toggle) (𝟙 lamp) := by
  intro x
  cases x <;> rfl

/-- If the state also records a toggle counter, their state functions differ. -/
example : ¬ countedLamp.StateEquivalent (toggle ≫ toggle) (𝟙 lamp) :=
  fun h => nomatch congrArg Prod.snd (h (true, 0))

/-- Proposition 1.16: state-equivalence on the lamp is an equivalence relation on parallel
lists that is preserved by composition, so it gives a quotient category. -/
example : ∃ (Q : Type) (_ : Category.{0} Q) (π : ArtSyn LampFrame ⥤ Q),
    IsQuotientBy lampStates.StateEquivalent π :=
  (artformCategory LampFrame).2.2.2.2 _ lampStates.stateEquivalent_equivalence
    lampStates.stateEquivalent_comp

/-- Proposition 1.19 on the lamp: the semantic quotient identifies two toggles with the empty
script. -/
example : ∃ (Q : Type) (_ : Category.{0} Q) (π : ArtSyn LampFrame ⥤ Q),
    IsQuotientBy lampStates.StateEquivalent π ∧ π.map (toggle ≫ toggle) = π.map (𝟙 lamp) := by
  obtain ⟨Q, _, π, -, hπ, -, -⟩ := (semanticQuotient LampFrame lampStates).2
  exact ⟨Q, _, π, hπ, (hπ.2.2 _ _).2 fun x => by cases x <;> rfl⟩

/-! ### The two-rod family (Proposition 1.27) -/

/-- The two tags `L` and `R`. -/
inductive Side : Type
  | L
  | R

/-- The two-rod family over `{L, R}`: the cells of `R₂` over `L` and the cells of `R₃`
over `R`. -/
def twoRods : Fam Side
  | .L => Fin 2
  | .R => Fin 3

/-- The map `f : {0, 1, 2} → {L, R}` with `f(0) = f(1) = L` and `f(2) = R`. -/
def side : Fin 3 → Side :=
  ![.L, .L, .R]

/-- Reindexing the two-rod family along `f` gives fibres of sizes `2, 2, 3`. -/
example : (Fam.reindex side).obj twoRods = ![Fin 2, Fin 2, Fin 3] := by
  funext j
  fin_cases j <;> rfl

/-- Proposition 1.27 for this `f`: `Σ_f ⊣ f^* ⊣ Π_f`. -/
example : Nonempty (Fam.sigma side ⊣ Fam.reindex side) ∧
    Nonempty (Fam.reindex side ⊣ Fam.pi side) :=
  adjoints Side (Fin 3) side

/-! ### One frame and no operation (Proposition 1.30) -/

section OneArrow

variable {C : Type u} [Category.{v} C] [∀ X Y : C, Unique (X ⟶ Y)]

/-- In a category with exactly one arrow between any two objects, every cone is a limit. -/
def isLimitOfUnique {J : Type u'} [Category.{v'} J] {K : J ⥤ C} (c : Cone K) : IsLimit c where
  lift _ := default
  fac _ _ := Subsingleton.elim _ _
  uniq _ _ _ := Subsingleton.elim _ _

/-- A category with an object and exactly one arrow between any two objects has the limits of
every shape. -/
theorem hasLimitsOfShape_of_unique (X₀ : C) (J : Type u') [Category.{v'} J] :
    HasLimitsOfShape J C :=
  ⟨fun _ => HasLimit.mk
    ⟨{ pt := X₀
       π := { app := fun _ => default, naturality := fun _ _ _ => Subsingleton.elim _ _ } },
      isLimitOfUnique _⟩⟩

/-- A category with an object and exactly one arrow between any two objects is a topos. -/
theorem isTopos_of_unique (X₀ : C) : IsTopos C := by
  have hp : HasBinaryProducts C := hasLimitsOfShape_of_unique X₀ _
  refine ⟨hasLimitsOfShape_of_unique X₀ _, hasLimitsOfShape_of_unique X₀ _,
    ⟨hp, fun A _ => ⟨A, default, fun _ _ => ⟨default, Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩⟩⟩,
    X₀, IsTerminal.ofUnique X₀, X₀, 𝟙 X₀, fun S X m _ => ⟨default, ?_,
      fun _ _ => Subsingleton.elim _ _⟩⟩
  exact IsPullback.of_isLimit (c := PullbackCone.mk m ((IsTerminal.ofUnique X₀).from S)
    (Subsingleton.elim _ _)) (isLimitOfUnique _)

end OneArrow

/-- Declared data with one frame and no operation. -/
inductive OneFrame : Type
  | frame

instance : Quiver.{0} OneFrame :=
  ⟨fun _ _ => Empty⟩

/-- With one frame and no operation, the only script is the empty one. -/
instance (X Y : ArtSyn OneFrame) : Unique (X ⟶ Y) where
  default := by
    cases X
    cases Y
    exact Quiver.Path.nil
  uniq p := by
    cases X
    cases Y
    match p with
    | .nil => rfl
    | .cons _ e => exact e.elim

/-- The hypothesis of Proposition 1.30 can be met: with one frame and no operation, the Artform
category is a topos. -/
example : IsTopos (ArtSyn OneFrame) :=
  isTopos_of_unique OneFrame.frame

/-- Proposition 1.30 on the lamp: with its toggle, the lamp's Artform category is not a topos. -/
example : ¬ IsTopos (ArtSyn LampFrame) :=
  fun h => ((artformNotTopos LampFrame h).2 .lamp .lamp).false LampOp.toggle

end Cafe

end Artform
