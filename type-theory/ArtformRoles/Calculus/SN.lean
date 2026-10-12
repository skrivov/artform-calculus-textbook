import ArtformRoles.Calculus.Principal

/-!
# Strong normalization: reducibility

§8.4 of the paper. `SN t`: no infinite reduction starts at `t`. The
reducibility sets `Red τ` are defined by recursion on simple skeletons:

* `R_ι = SN`;
* `R_{Sτ}`: strongly normalizing terms whose stamp reducts have a reducible
  payload and strongly normalizing event and origin;
* `R_{τ⇒υ}`: strongly normalizing terms whose applications to reducible
  arguments are reducible;
* `R_{τ×υ}`: strongly normalizing terms whose projections are reducible.

Lemma 8.7 (reducibility closure): (i) `red_sn`; (ii) `red_step`; (iii)
`red_of_notIntro`, for every term that is not a lambda, a pair or a stamp, in
particular every neutral term; (iv) head expansion for beta, projections and
the record step (`red_beta`, `red_fst`, `red_snd`, `red_gate`); (v) `red_stamp`.
Lemma 8.8 (gate and node reducibility): `red_node`, `red_gate`.
-/

namespace Artform.Roles.Calculus

open Exp Relation

/-- Strong normalization: every reduction sequence from `t` is finite. -/
def SN (t : Exp) : Prop := Acc (fun a b => Step b a) t

namespace SN

theorem intro {t : Exp} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

theorem step {t t' : Exp} (h : SN t) (hs : Step t t') : SN t' := Acc.inv h hs

theorem steps {t t' : Exp} (h : SN t) (hs : Steps t t') : SN t' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem of_normal {t : Exp} (h : ∀ t', ¬Step t t') : SN t :=
  intro fun t' hs => absurd hs (h t')

theorem var (i : ℕ) : SN (.var i) := of_normal fun _ h => by cases h
theorem const (i k : ℕ) : SN (.const i k) := of_normal fun _ h => by cases h
theorem event : SN .event := of_normal fun _ h => by cases h
theorem nil : SN .nil := of_normal fun _ h => by cases h

/-- A term is strongly normalizing when an instance of it is. -/
theorem of_subst {t : Exp} {σ : ℕ → Exp} (h : SN (t.subst σ)) : SN t := by
  generalize hs : t.subst σ = s at h
  induction h generalizing t with
  | intro s _ ih =>
    subst hs
    exact intro fun t' ht => ih _ (ht.subst σ) rfl

theorem fam {a : ℕ} {args : Exp} (h : SN args) : SN (.fam a args) := by
  induction h with
  | intro args _ ih =>
    exact intro fun t' hs => by cases hs with | fam h => exact ih _ h

theorem stamped {σ : Role} {A : Exp} (h : SN A) : SN (.stamped σ A) := by
  induction h with
  | intro A _ ih =>
    exact intro fun t' hs => by cases hs with | stamped h => exact ih _ h

/-- A former that reduces only in its two components. -/
theorem two {f : Exp → Exp → Exp}
    (hf : ∀ {a b t'}, Step (f a b) t' →
      (∃ a', Step a a' ∧ t' = f a' b) ∨ (∃ b', Step b b' ∧ t' = f a b'))
    {a b : Exp} (ha : SN a) (hb : SN b) : SN (f a b) := by
  induction ha generalizing b with
  | intro a ha' iha =>
    induction hb with
    | intro b hb' ihb =>
      refine intro fun t' hs => ?_
      rcases hf hs with ⟨a', h, rfl⟩ | ⟨b', h, rfl⟩
      · exact iha _ h (Acc.intro b hb')
      · exact ihb _ h

/-- A former that reduces only in its three components. -/
theorem three {f : Exp → Exp → Exp → Exp}
    (hf : ∀ {a b c t'}, Step (f a b c) t' →
      (∃ a', Step a a' ∧ t' = f a' b c) ∨ (∃ b', Step b b' ∧ t' = f a b' c) ∨
        (∃ c', Step c c' ∧ t' = f a b c'))
    {a b c : Exp} (ha : SN a) (hb : SN b) (hc : SN c) : SN (f a b c) := by
  induction ha generalizing b c with
  | intro a ha' iha =>
    induction hb generalizing c with
    | intro b hb' ihb =>
      induction hc with
      | intro c hc' ihc =>
        refine intro fun t' hs => ?_
        rcases hf hs with ⟨a', h, rfl⟩ | ⟨b', h, rfl⟩ | ⟨c', h, rfl⟩
        · exact iha _ h (Acc.intro b hb') (Acc.intro c hc')
        · exact ihb _ h (Acc.intro c hc')
        · exact ihc _ h

theorem pi {q : Grade} {σ : Role} {A B : Exp} (hA : SN A) (hB : SN B) : SN (.pi q σ A B) :=
  two (f := Exp.pi q σ) (fun hs => by
    cases hs with
    | pi₁ h => exact .inl ⟨_, h, rfl⟩
    | pi₂ h => exact .inr ⟨_, h, rfl⟩) hA hB

theorem sigma {ρ : Role} {A B : Exp} (hA : SN A) (hB : SN B) : SN (.sigma ρ A B) :=
  two (f := Exp.sigma ρ) (fun hs => by
    cases hs with
    | sigma₁ h => exact .inl ⟨_, h, rfl⟩
    | sigma₂ h => exact .inr ⟨_, h, rfl⟩) hA hB

theorem lam {q : Grade} {σ : Role} {A b : Exp} (hA : SN A) (hb : SN b) : SN (.lam q σ A b) :=
  two (f := Exp.lam q σ) (fun hs => by
    cases hs with
    | lam₁ h => exact .inl ⟨_, h, rfl⟩
    | lam₂ h => exact .inr ⟨_, h, rfl⟩) hA hb

theorem pair {t u : Exp} (ht : SN t) (hu : SN u) : SN (.pair t u) :=
  two (f := Exp.pair) (fun hs => by
    cases hs with
    | pair₁ h => exact .inl ⟨_, h, rfl⟩
    | pair₂ h => exact .inr ⟨_, h, rfl⟩) ht hu

theorem cons {t ts : Exp} (ht : SN t) (hts : SN ts) : SN (.cons t ts) :=
  two (f := Exp.cons) (fun hs => by
    cases hs with
    | cons₁ h => exact .inl ⟨_, h, rfl⟩
    | cons₂ h => exact .inr ⟨_, h, rfl⟩) ht hts

theorem origin {A e t : Exp} (hA : SN A) (he : SN e) (ht : SN t) : SN (.origin A e t) :=
  three (f := Exp.origin) (fun hs => by
    cases hs with
    | origin₁ h => exact .inl ⟨_, h, rfl⟩
    | origin₂ h => exact .inr (.inl ⟨_, h, rfl⟩)
    | origin₃ h => exact .inr (.inr ⟨_, h, rfl⟩)) hA he ht

theorem stamp {t e o : Exp} (ht : SN t) (he : SN e) (ho : SN o) : SN (.stamp t e o) :=
  three (f := Exp.stamp) (fun hs => by
    cases hs with
    | stamp₁ h => exact .inl ⟨_, h, rfl⟩
    | stamp₂ h => exact .inr (.inl ⟨_, h, rfl⟩)
    | stamp₃ h => exact .inr (.inr ⟨_, h, rfl⟩)) ht he ho

theorem node {g ℓ : ℕ} {ds t e : Exp} (hd : SN ds) (ht : SN t) (he : SN e) :
    SN (.node g ℓ ds t e) :=
  three (f := Exp.node g ℓ) (fun hs => by
    cases hs with
    | node₁ h => exact .inl ⟨_, h, rfl⟩
    | node₂ h => exact .inr (.inl ⟨_, h, rfl⟩)
    | node₃ h => exact .inr (.inr ⟨_, h, rfl⟩)) hd ht he

/-- Components of a strongly normalizing application are strongly normalizing. -/
theorem app_left {t u : Exp} (h : SN (.app t u)) : SN t := by
  generalize hs : Exp.app t u = s at h
  induction h generalizing t with
  | intro s _ ih =>
    subst hs
    exact intro fun t' ht => ih _ (.app₁ ht) rfl

end SN

/-! ## Reducibility -/

/-- The reducibility sets of §8.4, by recursion on simple skeletons. -/
def Red : Skel → Exp → Prop
  | .stmp τ, t => SN t ∧ ∀ u e o, Steps t (.stamp u e o) → Red τ u ∧ SN e ∧ SN o
  | .arr τ υ, t => SN t ∧ ∀ u, Red τ u → Red υ (.app t u)
  | .prod τ υ, t => SN t ∧ Red τ (.fst t) ∧ Red υ (.snd t)
  | _, t => SN t

/-- Not an introduction form: not a lambda, a pair or a stamp. -/
def NotIntro : Exp → Prop
  | .lam .. | .pair .. | .stamp .. => False
  | _ => True

/-- Lemma 8.7 (i): reducible terms are strongly normalizing. -/
theorem red_sn {τ : Skel} {t : Exp} (h : Red τ t) : SN t := by
  cases τ <;> first | exact h | exact h.1

/-- Lemma 8.7 (ii): reducibility is closed under reduction. -/
theorem red_step {τ : Skel} {t t' : Exp} (h : Red τ t) (hs : Step t t') : Red τ t' := by
  induction τ generalizing t t' with
  | stmp τ _ =>
    exact ⟨h.1.step hs, fun u e o hu => h.2 u e o ((Steps.single hs).trans hu)⟩
  | arr τ υ _ ihυ =>
    exact ⟨h.1.step hs, fun u hu => ihυ (h.2 u hu) (.app₁ hs)⟩
  | prod τ υ ihτ ihυ =>
    exact ⟨h.1.step hs, ihτ h.2.1 (.fst hs), ihυ h.2.2 (.snd hs)⟩
  | _ => exact SN.step h hs

theorem red_steps {τ : Skel} {t t' : Exp} (h : Red τ t) (hs : Steps t t') : Red τ t' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact red_step ih hs

/-- Lemma 8.7 (iii): a term that is not an introduction form is reducible when
all its one-step reducts are. -/
theorem red_of_notIntro {τ : Skel} {r : Exp} (hr : NotIntro r) (h : ∀ r', Step r r' → Red τ r') :
    Red τ r := by
  induction τ generalizing r with
  | stmp τ _ =>
    refine ⟨SN.intro fun r' hs => red_sn (h r' hs), fun u e o hu => ?_⟩
    rcases ReflTransGen.cases_head hu with heq | ⟨r₁, hs, hrest⟩
    · subst heq; exact absurd hr id
    · exact (h r₁ hs).2 u e o hrest
  | arr τ υ _ ihυ =>
    refine ⟨SN.intro fun r' hs => red_sn (h r' hs), fun u hu => ?_⟩
    have hsn : SN u := red_sn hu
    induction hsn with
    | intro u _ ihu =>
      refine ihυ trivial fun x hs => ?_
      cases hs with
      | beta => exact absurd hr id
      | app₁ h' => exact (h _ h').2 u hu
      | app₂ h' => exact ihu _ h' (red_step hu h')
  | prod τ υ ihτ ihυ =>
    refine ⟨SN.intro fun r' hs => red_sn (h r' hs), ?_, ?_⟩
    · refine ihτ trivial fun x hs => ?_
      cases hs with
      | fstPair => exact absurd hr id
      | fst h' => exact (h _ h').2.1
    · refine ihυ trivial fun x hs => ?_
      cases hs with
      | sndPair => exact absurd hr id
      | snd h' => exact (h _ h').2.2
  | _ => exact SN.intro fun r' hs => red_sn (h r' hs)

/-- Variables are reducible at every skeleton. -/
theorem red_var (τ : Skel) (i : ℕ) : Red τ (.var i) :=
  red_of_notIntro trivial fun _ hs => by cases hs

/-- Public constants are reducible at every skeleton. -/
theorem red_const (τ : Skel) (i k : ℕ) : Red τ (.const i k) :=
  red_of_notIntro trivial fun _ hs => by cases hs

/-- Lemma 8.7 (v): a stamp with a reducible payload and strongly normalizing
event and origin is reducible. -/
theorem red_stamp {τ : Skel} {t e o : Exp} (ht : Red τ t) (he : SN e) (ho : SN o) :
    Red (.stmp τ) (.stamp t e o) := by
  refine ⟨SN.stamp (red_sn ht) he ho, fun u e' o' hs => ?_⟩
  obtain ⟨t', e'', o'', heq, h₁, h₂, h₃⟩ := Steps.stamp_inv hs
  cases heq
  exact ⟨red_steps ht h₁, he.steps h₂, ho.steps h₃⟩

/-- Lemma 8.8 (i): a node with strongly normalizing fields is reducible at every
skeleton. -/
theorem red_node (τ : Skel) {g ℓ : ℕ} {ds t e : Exp} (hd : SN ds) (ht : SN t) (he : SN e) :
    Red τ (.node g ℓ ds t e) := by
  induction hd generalizing t e with
  | intro ds _ ihd =>
    induction ht generalizing e with
    | intro t ht' iht =>
      induction he with
      | intro e he' ihe =>
        refine red_of_notIntro trivial fun x hs => ?_
        cases hs with
        | node₁ h => exact ihd _ h (Acc.intro t ht') (Acc.intro e he')
        | node₂ h => exact iht _ h (Acc.intro e he')
        | node₃ h => exact ihe _ h

/-- Lemma 8.8 (ii) and record head expansion: a gate with strongly normalizing
parameters and a reducible credential is reducible at every skeleton. -/
theorem red_gate (τ υ : Skel) {g : ℕ} {ds s : Exp} (hd : SN ds) (hs : Red (.stmp υ) s) :
    Red τ (.gate g ds s) := by
  have hsn : SN s := hs.1
  induction hd generalizing s with
  | intro ds hd' ihd =>
    induction hsn with
    | intro s _ ihs =>
      refine red_of_notIntro trivial fun x hx => ?_
      cases hx with
      | @record _ _ t e o =>
        obtain ⟨ht, he, -⟩ := hs.2 t e o .refl
        exact red_node τ (Acc.intro ds hd') (red_sn ht) he
      | gate₁ h => exact ihd _ h hs hs.1
      | gate₂ h => exact ihs _ h (red_step hs h)

/-- Lemma 8.7 (iv), beta head expansion. -/
theorem red_beta {υ : Skel} {q : Grade} {σ : Role} {A b u : Exp} (hA : SN A) (hb : SN b)
    (hu : SN u) (h : Red υ (b.inst u)) : Red υ (.app (.lam q σ A b) u) := by
  induction hA generalizing b u with
  | intro A hA' ihA =>
    induction hb generalizing u with
    | intro b hb' ihb =>
      induction hu with
      | intro u hu' ihu =>
        refine red_of_notIntro trivial fun x hx => ?_
        cases hx with
        | beta => exact h
        | app₁ h' =>
          cases h' with
          | lam₁ hA₁ => exact ihA _ hA₁ (Acc.intro b hb') (Acc.intro u hu') h
          | lam₂ hb₁ => exact ihb _ hb₁ (Acc.intro u hu') (red_step h (hb₁.subst _))
        | app₂ h' => exact ihu _ h' (red_steps h (Steps.inst_arg (.single h') b))

/-- Lemma 8.7 (iv), first projection head expansion. -/
theorem red_fst {τ : Skel} {t u : Exp} (ht : Red τ t) (hu : SN u) : Red τ (.fst (.pair t u)) := by
  have htsn : SN t := red_sn ht
  induction htsn generalizing u with
  | intro t ht' iht =>
    induction hu with
    | intro u hu' ihu =>
      refine red_of_notIntro trivial fun x hx => ?_
      cases hx with
      | fstPair => exact ht
      | fst h' =>
        cases h' with
        | pair₁ h₁ => exact iht _ h₁ (red_step ht h₁) (Acc.intro u hu')
        | pair₂ h₂ => exact ihu _ h₂

/-- Lemma 8.7 (iv), second projection head expansion. -/
theorem red_snd {υ : Skel} {t u : Exp} (ht : SN t) (hu : Red υ u) : Red υ (.snd (.pair t u)) := by
  have husn : SN u := red_sn hu
  induction ht generalizing u with
  | intro t ht' iht =>
    induction husn with
    | intro u _ ihu =>
      refine red_of_notIntro trivial fun x hx => ?_
      cases hx with
      | sndPair => exact hu
      | snd h' =>
        cases h' with
        | pair₁ h₁ => exact iht _ h₁ hu (red_sn hu)
        | pair₂ h₂ => exact ihu _ h₂ (red_step hu h₂)

end Artform.Roles.Calculus

/-! ## The fundamental lemma -/

namespace Artform.Roles.Calculus

open Exp

/-- Renaming keeps the graded skeleton of any expression. -/
theorem gskel_ren (A : Exp) (ξ : ℕ → ℕ) : gskel (A.ren ξ) = gskel A := by
  induction A generalizing ξ with
  | stamped σ A ih => simp only [Exp.ren, gskel, ih]
  | pi q σ A B ihA ihB => simp only [Exp.ren, gskel, ihA, ihB]
  | sigma ρ A B ihA ihB => simp only [Exp.ren, gskel, ihA, ihB]
  | _ => rfl

theorem skel_ren (A : Exp) (ξ : ℕ → ℕ) : skel (A.ren ξ) = skel A := by
  simp [skel, gskel_ren]

/-- A substitution reducible for `Γ`: it maps each variable to a term reducible
at the skeleton of its type. -/
def RedSubst (Γ : Ctx) (γ : ℕ → Exp) : Prop :=
  ∀ i ρ A, Γ[i]? = some (ρ, A) → Red (skel A) (γ i)

/-- Extend a substitution by a term for a new nearest variable. -/
def consSub (u : Exp) (γ : ℕ → Exp) : ℕ → Exp
  | 0 => u
  | i + 1 => γ i

theorem subst_up_inst (t u : Exp) (γ : ℕ → Exp) :
    (t.subst (up γ)).inst u = t.subst (consSub u γ) := by
  simp only [inst, subst_subst]
  refine subst_ext (fun i => ?_) t
  cases i with
  | zero => rfl
  | succ i => simp [subst_ren, inst1_comp_succ, consSub]

theorem RedSubst.cons {Γ : Ctx} {γ : ℕ → Exp} (h : RedSubst Γ γ) {σ : Role} {A u : Exp}
    (hu : Red (skel A) u) : RedSubst ((σ, A) :: Γ) (consSub u γ) := by
  intro i ρ B hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨-, rfl⟩ := hi
    exact hu
  | succ i => exact h i ρ B (by simpa using hi)

theorem RedSubst.var (Γ : Ctx) : RedSubst Γ Exp.var := fun i _ _ _ => red_var _ i

/-- Strong normalization under a binder, from an instance by a variable. -/
theorem sn_up {Γ : Ctx} {γ : ℕ → Exp} (h : RedSubst Γ γ) {σ : Role} {A t : Exp}
    (ih : ∀ γ', RedSubst ((σ, A) :: Γ) γ' → SN (t.subst γ')) : SN (t.subst (up γ)) := by
  have h' := ih _ (h.cons (σ := σ) (red_var (skel A) 0))
  rw [← subst_up_inst] at h'
  exact SN.of_subst h'

/-- Lemma 8.9 (fundamental lemma): under a reducible substitution, a well-formed
type is strongly normalizing, a well-typed term is reducible at the skeleton of
its type, and a checked argument list is strongly normalizing. -/
theorem Deriv.fundamental {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    match j with
    | .ty Γ _ A _ => ∀ γ, RedSubst Γ γ → SN (A.subst γ)
    | .tm Γ _ t A _ => ∀ γ, RedSubst Γ γ → Red (skel A) (t.subst γ)
    | .spine Γ ts _ _ => ∀ γ, RedSubst Γ γ → SN (ts.subst γ)
    | .tel _ _ _ => True := by
  induction d with
  | tyFam _ _ _ _ ih => exact fun γ hγ => SN.fam (ih γ hγ)
  | tyEvent => exact fun _ _ => SN.event
  | tyOrigin _ _ _ _ _ ihA ihe iht =>
    exact fun γ hγ => SN.origin (ihA γ hγ) (red_sn (ihe γ hγ)) (red_sn (iht γ hγ))
  | tyStamped _ _ _ _ ih => exact fun γ hγ => SN.stamped (ih γ hγ)
  | tyPi _ _ _ _ _ ihA ihB => exact fun γ hγ => SN.pi (ihA γ hγ) (sn_up hγ ihB)
  | tySigma _ _ _ _ ihA ihB => exact fun γ hγ => SN.sigma (ihA γ hγ) (sn_up hγ ihB)
  | var hΓ hC _ _ _ _ =>
    intro γ hγ
    subst hC
    rw [skel_ren]
    exact hγ _ _ _ hΓ
  | const => exact fun _ _ => red_const _ _ _
  | @lam Γ q σ ρ A B t α θ γ₀ ε dA dt hq dC hε hv ihA iht ihC =>
    intro γ hγ
    have hsnt : SN (t.subst (up γ)) := sn_up hγ fun γ' h' => red_sn (iht γ' h')
    refine ⟨SN.lam (ihA γ hγ) hsnt, fun u hu => ?_⟩
    refine red_beta (ihA γ hγ) hsnt (red_sn hu) ?_
    rw [subst_up_inst]
    exact iht _ (hγ.cons hu)
  | @app Γ q σ ρ A B f u C φ η γ₀ ε df du hC dC hε hv ihf ihu ihC =>
    intro γ hγ
    subst hC
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    have hB := dpi.tyShape_ty.2
    rw [skel_subst hB]
    exact (ihf γ hγ).2 _ (ihu γ hγ)
  | @pair Γ ρ A B t u θ η γ₀ ε dt du dC hε hv iht ihu ihC =>
    intro γ hγ
    have hB := dC.tyShape_ty.2
    have hu := ihu γ hγ
    rw [skel_subst hB] at hu
    exact ⟨SN.pair (red_sn (iht γ hγ)) (red_sn hu), red_fst (iht γ hγ) (red_sn hu),
      red_snd (red_sn (iht γ hγ)) hu⟩
  | fst _ _ _ ihp _ => exact fun γ hγ => (ihp γ hγ).2.1
  | @snd Γ ρ A B C p π γ₀ dp hC dC hv ihp ihC =>
    intro γ hγ
    subst hC
    obtain ⟨γs, ⟨ds⟩⟩ := dp.tm_ty
    rw [skel_subst ds.tyShape_ty.2]
    exact (ihp γ hγ).2.2
  | stamp _ _ _ _ _ _ iht ihe iho _ =>
    exact fun γ hγ => red_stamp (iht γ hγ) (red_sn (ihe γ hγ)) (red_sn (iho γ hγ))
  | gate _ _ _ _ _ _ _ ihds ihs _ =>
    exact fun γ hγ => red_gate _ _ (ihds γ hγ) (ihs γ hγ)
  | node _ _ _ _ _ _ _ _ ihds iht ihe _ =>
    exact fun γ hγ => red_node _ (ihds γ hγ) (red_sn (iht γ hγ)) (red_sn (ihe γ hγ))
  | @conv Γ ρ t A B θ γ₀ dt hAB dB iht ihB =>
    intro γ hγ
    obtain ⟨γA, ⟨dA⟩⟩ := dt.tm_ty
    rw [← skel_conv hAB dA.tyShape_ty dB.tyShape_ty]
    exact iht γ hγ
  | spineNil => exact fun _ _ => SN.nil
  | spineCons _ _ _ iht ihts => exact fun γ hγ => SN.cons (red_sn (iht γ hγ)) (ihts γ hγ)
  | telNil => trivial
  | telCons => trivial

/-- Theorem 8.10 (strong normalization): every well-typed term is strongly
normalizing. -/
theorem Deriv.sn_tm {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t A : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ t A ε)) : SN t := by
  have h := d.fundamental Exp.var (RedSubst.var Γ)
  rw [subst_var] at h
  exact red_sn h

/-- Theorem 8.10 (strong normalization): every well-formed type is strongly
normalizing. -/
theorem Deriv.sn_ty {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp} {α : Eff}
    (d : Deriv S acc (.ty Γ ρ A α)) : SN A := by
  have h := d.fundamental Exp.var (RedSubst.var Γ)
  rw [subst_var] at h
  exact h

/-- A checked argument list is strongly normalizing. -/
theorem Deriv.sn_spine {S : Sig} {acc : Bool} {Γ : Ctx} {ts : Exp} {Δ : Tel} {ε : Eff}
    (d : Deriv S acc (.spine Γ ts Δ ε)) : SN ts := by
  have h := d.fundamental Exp.var (RedSubst.var Γ)
  rw [subst_var] at h
  exact h

end Artform.Roles.Calculus
