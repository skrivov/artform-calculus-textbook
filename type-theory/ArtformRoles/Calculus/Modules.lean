import ArtformRoles.Calculus.Justified

/-!
# Modules and extension theorems

§10 of the paper. A module `M` extends a well-formed signature `S`; the
extended signature is `S ++ M`, and the base has `N = S.length` entries.

* `Exp.Old N`: an expression is old when its declarations all lie in the base;
  `OldConv N C`: `C` reduces to an old expression.
* Module classes: `RenderingOnly`, `FreshWitnessFamily`, `EvidenceInhabitant`;
  `ModuleEvent`, the qualified event constants `Event_E` of a module.
* `Deriv.region_old`: the grade-free region lemma behind Lemma 10.2 (i)–(ii).
  In a normal term at a non-rendering role whose type is grade-free and old,
  in a context of such variables, no new constant can occur when every new
  constant has the rendering role or a new result family; every gate's
  interface is grade-free (Sig-Gate), so the region includes gates and nodes.

The gate interface. Sig-Gate requires the parameter and payload types of a gate
to be grade-free, as well as its result. Without the requirement on parameters
the extension theorems fail: a parameter of type `Π^0(h :_F Π^∞(y :_R G). X). X`
lets `gate_g(λh. h r; c)` carry a new rendering constant `r` into the node of an
old grade-free type.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Old expressions -/

/-- `t` mentions only the declarations `0, …, N-1`: it is old over a base
signature of length `N`. -/
def Exp.Old (N : ℕ) : Exp → Prop
  | var _ => True
  | const i _ => i < N
  | fam a args => a < N ∧ args.Old N
  | event => True
  | origin A e t => A.Old N ∧ e.Old N ∧ t.Old N
  | stamped _ A => A.Old N
  | pi _ _ A B => A.Old N ∧ B.Old N
  | sigma _ A B => A.Old N ∧ B.Old N
  | lam _ _ A t => A.Old N ∧ t.Old N
  | app t u => t.Old N ∧ u.Old N
  | pair t u => t.Old N ∧ u.Old N
  | fst t => t.Old N
  | snd t => t.Old N
  | stamp t e o => t.Old N ∧ e.Old N ∧ o.Old N
  | gate g ds s => g < N ∧ ds.Old N ∧ s.Old N
  | node g _ ds t e => g < N ∧ ds.Old N ∧ t.Old N ∧ e.Old N
  | nil => True
  | cons t ts => t.Old N ∧ ts.Old N

theorem Exp.Old.mono {N N' : ℕ} (h : N ≤ N') {t : Exp} (ht : t.Old N) : t.Old N' := by
  induction t <;> simp_all [Exp.Old] <;> omega

theorem Exp.Old.ren {N : ℕ} {t : Exp} (ht : t.Old N) (ξ : ℕ → ℕ) : (t.ren ξ).Old N := by
  induction t generalizing ξ <;> simp_all [Exp.Old, Exp.ren]

theorem Exp.Old.subst {N : ℕ} {t : Exp} (ht : t.Old N) {σ : ℕ → Exp}
    (hσ : ∀ i, (σ i).Old N) : (t.subst σ).Old N := by
  induction t generalizing σ with
  | var i => exact hσ i
  | pi q ρ A B ihA ihB =>
    refine ⟨ihA ht.1 hσ, ihB ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren _
  | sigma ρ A B ihA ihB =>
    refine ⟨ihA ht.1 hσ, ihB ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren _
  | lam q ρ A t ihA iht =>
    refine ⟨ihA ht.1 hσ, iht ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren _
  | _ => simp_all [Exp.Old, Exp.subst]

theorem Exp.Old.inst {N : ℕ} {t u : Exp} (ht : t.Old N) (hu : u.Old N) : (t.inst u).Old N :=
  ht.subst fun i => by cases i with | zero => exact hu | succ => trivial

theorem Exp.Old.upN {N : ℕ} {σ : ℕ → Exp} (hσ : ∀ i, (σ i).Old N) :
    ∀ k i, (upN k σ i).Old N := by
  intro k
  induction k with
  | zero => exact hσ
  | succ k ih =>
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (ih i).ren _

theorem Exp.Old.instType {N : ℕ} {ds : Exp} (hds : ds.Old N) :
    ∀ {Δ : Tel} {C : Exp}, C.Old N → (instType ds Δ C).Old N := by
  induction ds with
  | cons t ts _ ihts =>
    intro Δ C hC
    cases Δ with
    | nil => exact hC
    | cons p Δ =>
      exact ihts hds.2 (hC.subst (Exp.Old.upN (fun i => by
        cases i with | zero => exact hds.1 | succ => trivial) _))
  | _ => intro Δ C hC; cases Δ <;> exact hC

/-- A step keeps an expression old: reduction introduces no declaration. -/
theorem Step.old {N : ℕ} {t t' : Exp} (h : Step t t') (ht : t.Old N) : t'.Old N := by
  induction h with
  | beta => exact ht.1.2.inst ht.2
  | fstPair => exact ht.1
  | sndPair => exact ht.2
  | record => exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
  | _ => simp_all [Exp.Old]

theorem Steps.old {N : ℕ} {t t' : Exp} (h : Steps t t') (ht : t.Old N) : t'.Old N := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact hs.old ih

/-- `C` reduces to an old expression. -/
def OldConv (N : ℕ) (C : Exp) : Prop := ∃ w, Steps C w ∧ w.Old N

theorem OldConv.of_old {N : ℕ} {C : Exp} (h : C.Old N) : OldConv N C := ⟨C, .refl, h⟩

/-- Reducing to an old expression is invariant under conversion. -/
theorem OldConv.of_conv {N : ℕ} {C C' : Exp} (hc : Conv C C') (h : OldConv N C') :
    OldConv N C := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨v, h₁, h₂⟩ := hc.joinable
  obtain ⟨x, h₃, h₄⟩ := Steps.confluent h₂ hw
  exact ⟨x, h₁.trans h₃, h₄.old hold⟩

theorem OldConv.steps {N : ℕ} {C C' : Exp} (h : Steps C C') (hC : OldConv N C) :
    OldConv N C' :=
  OldConv.of_conv (Conv.of_steps h).symm hC

/-- A normal expression that reduces to an old one is old. -/
theorem Normal.old {N : ℕ} {C : Exp} (hn : Normal C) (h : OldConv N C) : C.Old N := by
  obtain ⟨w, hw, hold⟩ := h
  rwa [hn.eq_of_steps hw]

theorem OldConv.pi {N : ℕ} {q : Grade} {σ : Role} {A B : Exp} (h : OldConv N (.pi q σ A B)) :
    OldConv N A ∧ OldConv N B := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨A', B', rfl, h₁, h₂⟩ := Steps.pi_inv hw
  exact ⟨⟨A', h₁, hold.1⟩, ⟨B', h₂, hold.2⟩⟩

theorem OldConv.sigma {N : ℕ} {ρ : Role} {A B : Exp} (h : OldConv N (.sigma ρ A B)) :
    OldConv N A ∧ OldConv N B := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨A', B', rfl, h₁, h₂⟩ := Steps.sigma_inv hw
  exact ⟨⟨A', h₁, hold.1⟩, ⟨B', h₂, hold.2⟩⟩

theorem OldConv.stamped {N : ℕ} {σ : Role} {A : Exp} (h : OldConv N (.stamped σ A)) :
    OldConv N A := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨A', rfl, h₁⟩ := Steps.stamped_inv hw
  exact ⟨A', h₁, hold⟩

theorem OldConv.subst {N : ℕ} {B : Exp} (h : OldConv N B) {σ : ℕ → Exp}
    (hσ : ∀ i, (σ i).Old N) : OldConv N (B.subst σ) := by
  obtain ⟨w, hw, hold⟩ := h
  exact ⟨w.subst σ, hw.subst σ, hold.subst hσ⟩

theorem OldConv.inst {N : ℕ} {B u : Exp} (h : OldConv N B) (hu : u.Old N) :
    OldConv N (B.inst u) :=
  h.subst fun i => by cases i with | zero => exact hu | succ => trivial

theorem OldConv.origin {N : ℕ} {A e t : Exp} (hA : OldConv N A) (he : e.Old N) (ht : t.Old N) :
    OldConv N (.origin A e t) := by
  obtain ⟨w, hw, hold⟩ := hA
  exact ⟨.origin w e t, Steps.lift (fun X => Exp.origin X e t) Step.origin₁ hw, hold, he, ht⟩

/-! ## Typed subjects are old over their signature -/

/-- Every declaration of a typed subject exists: the subject is old over the
signature. -/
theorem Deriv.subject_old {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    match j with
    | .ty _ _ A _ => A.Old S.length
    | .tm _ _ t _ _ => t.Old S.length
    | .spine _ ts _ _ => ts.Old S.length
    | .tel _ Δ _ => ∀ p ∈ Δ, p.2.Old S.length := by
  induction d with
  | tyFam hS' _ _ _ ih => exact ⟨Sig.lt_of_family hS', ih⟩
  | tyEvent => trivial
  | tyOrigin _ _ _ _ _ ihA ihe iht => exact ⟨ihA, ihe, iht⟩
  | tyStamped _ _ _ _ ih => exact ih
  | tyPi _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | tySigma _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | var => trivial
  | const hc _ _ _ _ => exact Sig.lt_of_const hc
  | lam _ _ _ _ _ _ ihA iht _ => exact ⟨ihA, iht⟩
  | app _ _ _ _ _ _ ihf ihu _ => exact ⟨ihf, ihu⟩
  | pair _ _ _ _ _ iht ihu _ => exact ⟨iht, ihu⟩
  | fst _ _ _ ihp _ => exact ihp
  | snd _ _ _ _ ihp _ => exact ihp
  | stamp _ _ _ _ _ _ iht ihe iho _ => exact ⟨iht, ihe, iho⟩
  | gate hg _ _ _ _ _ _ ihds ihs _ => exact ⟨Sig.lt_of_gate hg, ihds, ihs⟩
  | node hg _ _ _ _ _ _ _ ihds iht ihe _ => exact ⟨Sig.lt_of_gate hg, ihds, iht, ihe⟩
  | conv _ _ _ iht _ => exact iht
  | spineNil => trivial
  | spineCons _ _ _ iht ihts => exact ⟨iht, ihts⟩
  | telNil => intro p hp; cases hp
  | telCons _ _ _ ihA ihΔ =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ihA
    · exact ihΔ p hp

/-- Every entry type of a formed telescope has the shape of a type. -/
theorem Deriv.tel_tyShape {S : Sig} {acc : Bool} {Γ : Ctx} {Δ : Tel} {δ : Eff}
    (d : Deriv S acc (.tel Γ Δ δ)) : ∀ p ∈ Δ, p.2.TyShape := by
  generalize hj : Judg.tel Γ Δ δ = j at d
  induction d generalizing Γ Δ δ with
  | telNil => cases hj; intro p hp; cases hp
  | telCons dA _ _ _ ihΔ =>
    cases hj
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact dA.tyShape_ty
    · exact ihΔ rfl p hp
  | _ => cases hj

/-- The interface of a declared gate is old below the gate's position. -/
theorem SigWF.gate_old {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) :
    (∀ p ∈ Δ, p.2.Old g) ∧ A.Old g ∧ B.Old g := by
  induction hS with
  | nil => simp [Sig.gate?] at h
  | @gate S' Δ' σ' A' ρ' B' δ' α' β' _ hΔ' hA' hB' _ _ _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨hi, _, _, _, _, _, he, hp⟩
    · exact ih h
    · cases he; cases hp; subst hi
      obtain ⟨dΔ⟩ := hΔ'
      obtain ⟨dA⟩ := hA'
      obtain ⟨dB⟩ := hB'
      exact ⟨dΔ.subject_old, dA.subject_old, dB.subject_old⟩
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
    · exact ih h
    · cases he


/-- The type of a constant is old below the next entry. -/
theorem SigWF.const_old {S : Sig} (hS : SigWF S) {i k : ℕ} {ρ : Role} {T : Exp}
    (h : S.const? i k = some (ρ, T)) : T.Old (i + 1) := by
  induction hS with
  | nil => simp [Sig.const?] at h
  | family _ _ ih | gate _ _ _ _ _ _ _ _ _ _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨_, h'⟩
    · exact ih h'
    · rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ <;> cases he
  | @prim S' ρ' A' α _ hA _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · exact ih h'
    · rcases h' with ⟨_, _, he, -, hp⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩
      · cases he; cases hp; subst hi
        obtain ⟨dA⟩ := hA
        exact (dA.subject_old).mono (Nat.le_succ _)
      · cases he
      · cases he
  | @cert S' σ' A' α _ hA _ _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · exact ih h'
    · subst hi
      obtain ⟨dA⟩ := hA
      have hA' : A'.Old (S'.length + 1) := (dA.subject_old).mono (Nat.le_succ _)
      rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩ | ⟨_, _, he, _⟩
      · cases he
      · cases he
        rcases hk with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> cases hp
        · exact hA'
        · trivial
        · exact ⟨hA', Nat.lt_succ_self _, Nat.lt_succ_self _⟩
      · cases he
  | @attest S' A' t' θ _ ht _ _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · exact ih h'
    · subst hi
      obtain ⟨dt⟩ := ht
      obtain ⟨γ, ⟨dA⟩⟩ := dt.tm_ty
      have hA' : A'.Old (S'.length + 1) := (dA.subject_old).mono (Nat.le_succ _)
      have ht' : t'.Old (S'.length + 1) := (dt.subject_old).mono (Nat.le_succ _)
      rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩
      · cases he
      · cases he
      · cases he
        rcases hk with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> cases hp
        · trivial
        · exact ⟨hA', Nat.lt_succ_self _, ht'⟩

/-- An attested term and its type are old below their entry. -/
theorem SigWF.attest_old {S : Sig} (hS : SigWF S) {i : ℕ} {A t : Exp}
    (h : S[i]? = some (.attest A t)) : A.Old i ∧ t.Old i := by
  induction hS with
  | nil => simp at h
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | gate _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [getElem?_append_singleton] at h
    split_ifs at h with h₁ h₂
    · exact ih h
    · cases h
  | @attest S' A' t' θ _ ht _ _ _ ih =>
    rw [getElem?_append_singleton] at h
    split_ifs at h with h₁ h₂
    · exact ih h
    · cases h; subst h₂
      obtain ⟨dt⟩ := ht
      obtain ⟨γ, ⟨dA⟩⟩ := dt.tm_ty
      exact ⟨dA.subject_old, dt.subject_old⟩

/-! ## Module classes -/

/-- A rendering-only module: every new family and primitive has the rendering
role; it adds no certificate, attestation or gate. -/
def RenderingOnly (M : Sig) : Prop :=
  ∀ e ∈ M, (∃ Δ, e = .family Δ .rendering) ∨ (∃ A, e = .prim .rendering A)

/-- A fresh-witness-family module over a base of `N` entries: every new family
has the witness role, and every new primitive is a constructor whose result is
headed by a new family; it adds no certificate, attestation or gate. -/
def FreshWitnessFamily (N : ℕ) (M : Sig) : Prop :=
  ∀ e ∈ M, (∃ Δ, e = .family Δ .witness) ∨
    (∃ ρ A a args, e = .prim ρ A ∧ A.resultHead = .fam a args ∧ N ≤ a)

/-- An evidence-inhabitant module over a base of `N` entries: a nonempty mixture
of certificate bundles for old types at the witness role and exact attestations
of old terms at old types; it adds no family, primitive or gate. -/
def EvidenceInhabitant (N : ℕ) (M : Sig) : Prop :=
  M ≠ [] ∧ ∀ e ∈ M, (∃ A, e = .cert .witness A ∧ A.Old N) ∨
    (∃ A t, e = .attest A t ∧ A.Old N ∧ t.Old N)

/-- The qualified event constants `Event_E` of the module `M` over the base `S`:
the event of each of its evidence entries. -/
def ModuleEvent (S M : Sig) (e : Exp) : Prop :=
  ∃ i, S.length ≤ i ∧
    ((∃ σ A, (S ++ M)[i]? = some (.cert σ A) ∧ e = .const i 1) ∨
     (∃ A t, (S ++ M)[i]? = some (.attest A t) ∧ e = .const i 0))

theorem entry_of_new {S M : Sig} {i : ℕ} (hi : S.length ≤ i) {e : Entry}
    (h : (S ++ M)[i]? = some e) : e ∈ M := by
  rw [List.getElem?_append_right hi] at h
  exact List.mem_of_getElem? h

/-- The new constants cannot head a term of an old type at a non-rendering role:
each has the rendering role or a type whose result family is new. -/
def NewConstsExcluded (S : Sig) (N : ℕ) : Prop :=
  ∀ i k ρ T, N ≤ i → S.const? i k = some (ρ, T) →
    ρ = .rendering ∨ ∃ a args, T.resultHead = .fam a args ∧ N ≤ a

theorem const_entry {S : Sig} {i k : ℕ} {ρ : Role} {T : Exp} (h : S.const? i k = some (ρ, T)) :
    ∃ e, S[i]? = some e ∧ ((∃ A, e = .prim ρ A ∧ k = 0 ∧ T = A) ∨ (∃ σ A, e = .cert σ A) ∨
      (∃ A t, e = .attest A t)) := by
  unfold Sig.const? at h
  cases hS : S[i]? with
  | none => simp [hS] at h
  | some e =>
    refine ⟨e, rfl, ?_⟩
    rw [hS] at h
    rcases e with ⟨Δ, ρ'⟩ | ⟨ρ', A⟩ | ⟨σ, A⟩ | ⟨A, t⟩ | ⟨Δ, σ, A, ρ', B⟩
    · simp at h
    · rcases k with _ | k <;> simp_all
    · exact .inr (.inl ⟨σ, A, rfl⟩)
    · exact .inr (.inr ⟨A, t, rfl⟩)
    · simp at h

theorem RenderingOnly.excluded {S M : Sig} (hM : RenderingOnly M) :
    NewConstsExcluded (S ++ M) S.length := by
  intro i k ρ T hi hc
  obtain ⟨e, he, hk⟩ := const_entry hc
  rcases hM e (entry_of_new hi he) with ⟨Δ, rfl⟩ | ⟨A, rfl⟩
  · rcases hk with ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · rcases hk with ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    exact .inl rfl

theorem FreshWitnessFamily.excluded {S M : Sig} (hM : FreshWitnessFamily S.length M) :
    NewConstsExcluded (S ++ M) S.length := by
  intro i k ρ T hi hc
  obtain ⟨e, he, hk⟩ := const_entry hc
  rcases hM e (entry_of_new hi he) with ⟨Δ, rfl⟩ | ⟨ρ', A, a, args, rfl, hres, ha⟩
  · rcases hk with ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · rcases hk with ⟨_, h, _, rfl⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    exact .inr ⟨a, args, hres, ha⟩

/-- A module adding no gate keeps every gate in the base. -/
theorem gate_old_of_no_gate {S M : Sig} (hM : ∀ e ∈ M, ∀ Δ σ A ρ B, e ≠ .gate Δ σ A ρ B)
    {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp} (h : (S ++ M).gate? g = some (Δ, σ, A, ρ, B)) :
    g < S.length := by
  by_contra hg
  unfold Sig.gate? at h
  cases he : (S ++ M)[g]? with
  | none => simp [he] at h
  | some e =>
    rw [he] at h
    have := hM e (entry_of_new (by omega) he)
    rcases e with _ | _ | _ | _ | ⟨Δ', σ', A', ρ', B'⟩ <;> simp at h
    exact this _ _ _ _ _ rfl

theorem RenderingOnly.no_gate {M : Sig} (hM : RenderingOnly M) :
    ∀ e ∈ M, ∀ Δ σ A ρ B, e ≠ .gate Δ σ A ρ B := by
  intro e he Δ σ A ρ B h
  subst h
  rcases hM _ he with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem FreshWitnessFamily.no_gate {N : ℕ} {M : Sig} (hM : FreshWitnessFamily N M) :
    ∀ e ∈ M, ∀ Δ σ A ρ B, e ≠ .gate Δ σ A ρ B := by
  intro e he Δ σ A ρ B h
  subst h
  rcases hM _ he with ⟨_, h⟩ | ⟨_, _, _, _, h, _⟩ <;> cases h

theorem EvidenceInhabitant.no_gate {N : ℕ} {M : Sig} (hM : EvidenceInhabitant N M) :
    ∀ e ∈ M, ∀ Δ σ A ρ B, e ≠ .gate Δ σ A ρ B := by
  intro e he Δ σ A ρ B h
  subst h
  rcases hM.2 _ he with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ <;> cases h

/-! ## Skeletons ending in a new family -/

/-- After its codomains, the skeleton ends in a new family. -/
def GSkel.UltNew (N : ℕ) : GSkel → Prop
  | .base a => N ≤ a
  | .arr _ _ _ υ => υ.UltNew N
  | _ => False

theorem gskel_ultNew {N : ℕ} {T : Exp} {a : ℕ} {args : Exp} (h : T.resultHead = .fam a args)
    (ha : N ≤ a) : (gskel T).UltNew N := by
  induction T with
  | pi q σ A B _ ihB => exact ihB h
  | fam a' args' => cases h; exact ha
  | _ => cases h

theorem not_ultNew_of_old {N : ℕ} {w : Exp} (h : w.Old N) : ¬(gskel w).UltNew N := by
  induction w with
  | pi q σ A B _ ihB => exact ihB h.2
  | fam a args => exact fun h' => absurd h.1 (Nat.not_lt.mpr h')
  | _ => exact id

theorem OldConv.not_ultNew {N : ℕ} {C : Exp} (hC : C.TyShape) (h : OldConv N C) :
    ¬(gskel C).UltNew N := by
  obtain ⟨w, hw, hold⟩ := h
  rw [← (gskel_steps hw hC).1]
  exact not_ultNew_of_old hold

/-! ## The grade-free region -/

/-- A context of variables at non-rendering roles with grade-free old types. -/
def CtxReg (N : ℕ) (Γ : Ctx) : Prop :=
  ∀ p ∈ Γ, p.1 ≠ .rendering ∧ (gskel p.2).GF ∧ p.2.Old N

theorem CtxReg.nil {N : ℕ} : CtxReg N [] := fun _ h => by cases h

theorem nonrendering_of_demand {σ ρ : Role} (h : demand σ ρ ≤ .free) (hρ : ρ ≠ .rendering) :
    σ ≠ .rendering := by
  rintro rfl
  cases ρ <;> first | exact hρ rfl | exact absurd h (by decide)

theorem Tel.mem_subst {σ : ℕ → Exp} {Δ : Tel} {p : Role × Exp} (h : p ∈ Tel.subst σ Δ) :
    ∃ q ∈ Δ, ∃ k, p = (q.1, q.2.subst (upN k σ)) := by
  induction Δ generalizing σ with
  | nil => cases h
  | cons q Δ ih =>
    obtain ⟨ρ, A⟩ := q
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(ρ, A), List.mem_cons_self .., 0, rfl⟩
    · obtain ⟨q', hq', k, rfl⟩ := ih h
      exact ⟨q', List.mem_cons_of_mem _ hq', k + 1, by rw [upN_succ']⟩

/-- The region lemma behind Lemma 10.2 (i)–(ii). Let every new constant have
the rendering role or a new result family, and every gate be old. A normal term
at a non-rendering role, in a context of non-rendering variables with grade-free
old types, whose type is grade-free and reduces to an old type (or which is
neutral), is old with such a type; or it is a neutral whose type ends in a new
family. Argument lists against such telescopes are old. -/
theorem Deriv.region_old {S : Sig} (hS : SigWF S) {N : ℕ} (hexcl : NewConstsExcluded S N)
    (hgate : ∀ g Δ σ A ρ B, S.gate? g = some (Δ, σ, A, ρ, B) → g < N) {acc : Bool} {j : Judg}
    (d : Deriv S acc j) :
    match j with
    | .tm Γ ρ n C _ => Normal n → ρ ≠ .rendering → CtxReg N Γ →
        (((gskel C).GF ∧ OldConv N C) ∨ NotIntro n) →
        ((gskel C).GF ∧ OldConv N C ∧ n.Old N) ∨ (NotIntro n ∧ (gskel C).UltNew N)
    | .spine Γ ts Δ _ => Normal ts → CtxReg N Γ →
        (∀ p ∈ Δ, p.1 ≠ .rendering ∧ p.2.TyShape ∧ (gskel p.2).GF ∧ OldConv N p.2) →
        ts.Old N
    | _ => True := by
  induction d with
  | tyFam | tyEvent | tyOrigin | tyStamped | tyPi | tySigma | telNil | telCons => trivial
  | @var Γ i ρ A C γ ε hΓi hC _ _ _ _ =>
    intro _ _ hctx _
    obtain ⟨-, hgf, hold⟩ := hctx _ (List.mem_of_getElem? hΓi)
    refine .inl ⟨?_, ?_, trivial⟩
    · rw [hC, gskel_ren]; exact hgf
    · rw [hC]; exact .of_old (hold.ren _)
  | @const Γ i k ρ A γ ε hc _ _ _ _ =>
    intro _ hρ _ _
    by_cases hi : i < N
    · exact .inl ⟨hS.const_gf hc, .of_old ((hS.const_old hc).mono (by omega)), hi⟩
    · rcases hexcl i k ρ A (by omega) hc with h | ⟨a, args, hres, ha⟩
      · exact absurd h hρ
      · exact .inr ⟨trivial, gskel_ultNew hres ha⟩
  | @lam Γ q σ ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro hn hρ hctx hCh
    obtain ⟨⟨hq0, hAgf, hBgf⟩, hold⟩ := hCh.resolve_right id
    have hσ : σ ≠ .rendering := nonrendering_of_demand (hq0 ▸ dC.tyPi_demand) hρ
    have hAold : A.Old N := (Normal.lam hn).1.old hold.pi.1
    have hctx' : CtxReg N ((σ, A) :: Γ) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hσ, hAgf, hAold⟩
      · exact hctx p hp
    rcases iht (Normal.lam hn).2 hρ hctx' (.inl ⟨hBgf, hold.pi.2⟩) with ⟨-, -, hbold⟩ | ⟨-, hult⟩
    · exact .inl ⟨⟨hq0, hAgf, hBgf⟩, hold, hAold, hbold⟩
    · exact absurd hult (hold.pi.2.not_ultNew dC.tyShape_ty.2)
  | @app Γ q σ ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro hn hρ hctx _
    obtain ⟨hnf, hnu, hnl⟩ := hn.app
    have hfi : NotIntro f := by
      cases f with
      | lam q' σ' A' b => exact hnl _ _ _ _ rfl
      | pair => exact df.not_pair_of_pi
      | stamp => exact df.not_stamp_of_pi
      | _ => trivial
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    have hCB : gskel C = gskel B := by rw [hC, (gskel_subst dpi.tyShape_ty.2 _).1]
    rcases ihf hnf hρ hctx (.inr hfi) with ⟨⟨hq0, hAgf, hBgf⟩, hold, hfold⟩ | ⟨-, hult⟩
    · have hσ : σ ≠ .rendering := nonrendering_of_demand (hq0 ▸ dpi.tyPi_demand) hρ
      rcases ihu hnu hσ hctx (.inl ⟨hAgf, hold.pi.1⟩) with ⟨-, -, huold⟩ | ⟨-, hult⟩
      · exact .inl ⟨hCB ▸ hBgf, hC ▸ hold.pi.2.inst huold, hfold, huold⟩
      · exact absurd hult (hold.pi.1.not_ultNew dpi.tyShape_ty.1)
    · exact .inr ⟨trivial, hCB ▸ hult⟩
  | @pair Γ ρ A B t u θ η γ ε dt du dC hε hv iht ihu ihC =>
    intro hn hρ hctx hCh
    obtain ⟨⟨hAgf, hBgf⟩, hold⟩ := hCh.resolve_right id
    obtain ⟨hnt, hnu⟩ := hn.pair
    obtain ⟨-, -, β, ⟨dB⟩⟩ := dC.inv_tySigma
    rcases iht hnt hρ hctx (.inl ⟨hAgf, hold.sigma.1⟩) with ⟨-, -, htold⟩ | ⟨-, hult⟩
    · have hBt : (gskel (B.inst t)).GF := by rw [(gskel_subst dB.tyShape_ty _).1]; exact hBgf
      rcases ihu hnu hρ hctx (.inl ⟨hBt, hold.sigma.2.inst htold⟩) with ⟨-, -, huold⟩ |
          ⟨-, hult⟩
      · exact .inl ⟨⟨hAgf, hBgf⟩, hold, htold, huold⟩
      · exact absurd hult ((hold.sigma.2.inst htold).not_ultNew (gskel_subst dB.tyShape_ty _).2)
    · obtain ⟨-, ⟨αA, ⟨dA⟩⟩, -⟩ := dC.inv_tySigma
      exact absurd hult (hold.sigma.1.not_ultNew dA.tyShape_ty)
  | @fst Γ ρ A B p π γ dp dA hv ihp ihA =>
    intro hn hρ hctx _
    obtain ⟨hnp, hnpair⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    rcases ihp hnp hρ hctx (.inr hpi) with ⟨⟨hAgf, -⟩, hold, hpold⟩ | ⟨-, hult⟩
    · exact .inl ⟨hAgf, hold.sigma.1, hpold⟩
    · exact hult.elim
  | @snd Γ ρ A B C p π γ dp hC dC hv ihp ihC =>
    intro hn hρ hctx _
    obtain ⟨hnp, hnpair⟩ := hn.snd
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨γp, ⟨ds⟩⟩ := dp.tm_ty
    rcases ihp hnp hρ hctx (.inr hpi) with ⟨⟨-, hBgf⟩, hold, hpold⟩ | ⟨-, hult⟩
    · refine .inl ⟨?_, hC ▸ hold.sigma.2.inst hpold, hpold⟩
      rw [hC, (gskel_subst ds.tyShape_ty.2 _).1]; exact hBgf
    · exact hult.elim
  | @stamp Γ σ A t e o θ η ω γ ε dt de dorg dC hε hv iht ihe iho ihC =>
    intro hn hρ hctx hCh
    obtain ⟨hAgf, hold⟩ := hCh.resolve_right id
    obtain ⟨-, hσ, αA, ⟨dA⟩⟩ := dC.inv_tyStamped
    obtain ⟨hnt, hne, hno⟩ := hn.stamp
    rcases iht hnt hσ hctx (.inl ⟨hAgf, hold.stamped⟩) with ⟨-, -, htold⟩ | ⟨-, hult⟩
    · rcases ihe hne (by decide) hctx (.inl ⟨trivial, .of_old trivial⟩) with ⟨-, -, heold⟩ |
          ⟨-, hult⟩
      · rcases iho hno (by decide) hctx (.inl ⟨trivial, .origin hold.stamped heold htold⟩) with
          ⟨-, -, hoold⟩ | ⟨-, hult⟩
        · exact .inl ⟨hAgf, hold, htold, heold, hoold⟩
        · exact hult.elim
      · exact hult.elim
    · exact absurd hult (hold.stamped.not_ultNew dA.tyShape_ty)
  | @gate Γ g ds s Δ σ A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro hn hρ hctx _
    obtain ⟨hσg, hρg, hΔ, -, hBg⟩ := hS.gate_cond hg
    obtain ⟨hΔgf, hAgf⟩ := hS.gate_gradefree hg
    obtain ⟨hΔold, hAold, hBold⟩ := hS.gate_old hg
    have hgN := hgate _ _ _ _ _ _ hg
    obtain ⟨⟨hAf, ⟨dAf⟩⟩, ⟨hBf, ⟨dBf⟩⟩⟩ := hS.gate_formed hg
    obtain ⟨⟨δt, ⟨dtel⟩⟩, -, -⟩ := hS.gate_tel hg []
    obtain ⟨hnds, hns, -⟩ := hn.gate
    have hdsold : ds.Old N := ihds hnds hctx fun p hp =>
      ⟨by rcases protected_of_demand (le_of_eq (hΔ p hp)) hρg with h | h <;> rw [h] <;> decide,
        dtel.tel_tyShape p hp, gskel_gf (hΔgf p hp), .of_old ((hΔold p hp).mono hgN.le)⟩
    have hXold : (instType ds Δ A).Old N := Exp.Old.instType hdsold (hAold.mono hgN.le)
    have hXgf : (gskel (instType ds Δ A)).GF := by
      rw [(gskel_instType dAf.tyShape_ty ds Δ).1]; exact gskel_gf hAgf
    rcases ihst hns (by decide) hctx (.inl ⟨hXgf, .of_old hXold⟩) with ⟨-, -, hsold⟩ |
        ⟨-, hult⟩
    · refine .inl ⟨?_, ?_, hgN, hdsold, hsold⟩
      · rw [hC, (gskel_instType dBf.tyShape_ty ds Δ).1]; exact gskel_gf hBg
      · rw [hC]; exact .of_old (Exp.Old.instType hdsold (hBold.mono hgN.le))
    · exact hult.elim
  | @node Γ g ℓ ds t e Δ σ A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro hn hρ hctx _
    obtain ⟨hσg, hρg, hΔ, -, hBg⟩ := hS.gate_cond hg
    obtain ⟨hΔgf, hAgf⟩ := hS.gate_gradefree hg
    obtain ⟨hΔold, hAold, hBold⟩ := hS.gate_old hg
    have hgN := hgate _ _ _ _ _ _ hg
    obtain ⟨⟨hAf, ⟨dAf⟩⟩, ⟨hBf, ⟨dBf⟩⟩⟩ := hS.gate_formed hg
    obtain ⟨⟨δt, ⟨dtel⟩⟩, -, -⟩ := hS.gate_tel hg []
    obtain ⟨hnds, hnt, hne⟩ := hn.node
    have hdsold : ds.Old N := ihds hnds hctx fun p hp =>
      ⟨by rcases protected_of_demand (le_of_eq (hΔ p hp)) hρg with h | h <;> rw [h] <;> decide,
        dtel.tel_tyShape p hp, gskel_gf (hΔgf p hp), .of_old ((hΔold p hp).mono hgN.le)⟩
    have hXold : (instType ds Δ A).Old N := Exp.Old.instType hdsold (hAold.mono hgN.le)
    have hXgf : (gskel (instType ds Δ A)).GF := by
      rw [(gskel_instType dAf.tyShape_ty ds Δ).1]; exact gskel_gf hAgf
    rcases iht hnt hσg hctx (.inl ⟨hXgf, .of_old hXold⟩) with ⟨-, -, htold⟩ | ⟨-, hult⟩
    · rcases ihe hne (by decide) hctx (.inl ⟨trivial, .of_old trivial⟩) with ⟨-, -, heold⟩ |
          ⟨-, hult⟩
      · refine .inl ⟨?_, ?_, hgN, hdsold, htold, heold⟩
        · rw [hC, (gskel_instType dBf.tyShape_ty ds Δ).1]; exact gskel_gf hBg
        · rw [hC]; exact .of_old (Exp.Old.instType hdsold (hBold.mono hgN.le))
      · exact hult.elim
    · exact absurd hult ((OldConv.of_old hXold).not_ultNew
        (gskel_instType dAf.tyShape_ty ds Δ).2)
  | @conv Γ ρ t A B θ γ dt hAB dB iht ihB =>
    intro hn hρ hctx hCh
    obtain ⟨γ', hA⟩ := dt.tm_ty
    have hsk : gskel A = gskel B := gskel_conv hAB (TyShape.of_ty hA) dB.tyShape_ty
    rcases iht hn hρ hctx (hCh.imp (fun h => ⟨hsk ▸ h.1, OldConv.of_conv hAB h.2⟩) id) with
      ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
    · exact .inl ⟨hsk ▸ h₁, OldConv.of_conv hAB.symm h₂, h₃⟩
    · exact .inr ⟨h₁, hsk ▸ h₂⟩
  | spineNil => intro _ _ _; trivial
  | @spineCons Γ ρ t ts A Δ ε₁ ε₂ ε dt dts hε iht ihts =>
    intro hn hctx hent
    obtain ⟨hnt, hnts⟩ := hn.cons
    obtain ⟨hρt, hTyA, hGFA, hOldA⟩ := hent (ρ, A) (List.mem_cons_self ..)
    rcases iht hnt hρt hctx (.inl ⟨hGFA, hOldA⟩) with ⟨-, -, htold⟩ | ⟨-, hult⟩
    · refine ⟨htold, ihts hnts hctx fun p hp => ?_⟩
      obtain ⟨q, hq, k, rfl⟩ := Tel.mem_subst hp
      obtain ⟨hρq, hTyq, hGFq, hOldq⟩ := hent q (List.mem_cons_of_mem _ hq)
      have hτ : ∀ i, (upN k (inst1 t) i).Old N :=
        Exp.Old.upN (fun i => by cases i with | zero => exact htold | succ => trivial) k
      exact ⟨hρq, (gskel_subst hTyq _).2, (gskel_subst hTyq _).1 ▸ hGFq, hOldq.subst hτ⟩
    · exact absurd hult (hOldA.not_ultNew hTyA)


/-! ## Normal forms -/

/-- A strongly normalizing expression has a normal form. -/
theorem SN.exists_normal {t : Exp} (h : SN t) : ∃ n, Steps t n ∧ Normal n := by
  induction h with
  | intro t _ ih =>
    by_cases hn : Normal t
    · exact ⟨t, .refl, hn⟩
    · simp only [Normal, not_forall, not_not] at hn
      obtain ⟨t', hs⟩ := hn
      obtain ⟨n, h₁, h₂⟩ := ih t' hs
      exact ⟨n, Relation.ReflTransGen.head hs h₁, h₂⟩

/-- A closed well-typed term has a normal form of the same type. -/
theorem Deriv.normalize {S : Sig} (hS : SigWF S) {ρ : Role} {t A : Exp} {ε : Eff}
    (d : Deriv S true (.tm [] ρ t A ε)) :
    ∃ n ε', Steps t n ∧ Normal n ∧ ε ≤ ε' ∧ Derivable S true (.tm [] ρ n A ε') := by
  obtain ⟨n, hs, hn⟩ := d.sn_tm.exists_normal
  obtain ⟨ε', hle, hd⟩ := d.subject_reduction_steps hS (.nil hS) hs
  exact ⟨n, ε', hs, hn, hle, hd⟩

/-- Equality reflection: an old expression is joined to every expression
convertible to it through an old expression, by reductions available over the
base signature. -/
theorem Conv.old_join {N : ℕ} {t u : Exp} (ht : t.Old N) (h : Conv t u) :
    ∃ w, w.Old N ∧ Steps t w ∧ Steps u w := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  exact ⟨w, h₁.old ht, h₁, h₂⟩

/-! ## Theorems 10.4 and 10.5: conservative modules -/

theorem region_closed {S : Sig} (hS : SigWF S) {N : ℕ} (hexcl : NewConstsExcluded S N)
    (hgate : ∀ g Δ σ A ρ B, S.gate? g = some (Δ, σ, A, ρ, B) → g < N) {ρ : Role}
    (hρ : ρ ≠ .rendering) {A : Exp} (hA : A.Old N) (hgf : A.gradefree) {n : Exp} {ε : Eff}
    (d : Deriv S true (.tm [] ρ n A ε)) (hn : Normal n) : n.Old N := by
  rcases (d.region_old hS hexcl hgate) hn hρ CtxReg.nil (.inl ⟨gskel_gf hgf, .of_old hA⟩) with
    ⟨-, -, h⟩ | ⟨-, hult⟩
  · exact h
  · exact absurd hult ((OldConv.of_old hA).not_ultNew d.tm_ty.choose_spec.some.tyShape_ty)

/-- **Lemma 10.2** (i)–(ii) (grade-free extension support). Let `M` be
rendering-only, or fresh-witness-family, over `S`. A closed normal term at a
non-rendering role whose type is old and grade-free is old. -/
theorem extension_support_conservative {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : RenderingOnly M ∨ FreshWitnessFamily S.length M) {ρ : Role} (hρ : ρ ≠ .rendering)
    {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree) {n : Exp} {ε : Eff}
    (d : Deriv (S ++ M) true (.tm [] ρ n A ε)) (hn : Normal n) : n.Old S.length := by
  rcases hM with hM | hM
  · exact region_closed hSM hM.excluded (fun _ _ _ _ _ _ h => gate_old_of_no_gate hM.no_gate h)
      hρ hA hgf d hn
  · exact region_closed hSM hM.excluded (fun _ _ _ _ _ _ h => gate_old_of_no_gate hM.no_gate h)
      hρ hA hgf d hn

/-- **Theorem 10.4** (rendering noninterference). Let `M` be rendering-only over `S`.
At every old grade-free type of a non-rendering role, every closed term of the
extension reduces to an old normal term (term conservativity), and convertible
old terms are joined through old terms (equality reflection). -/
theorem rendering_noninterference {S M : Sig} (hSM : SigWF (S ++ M)) (hM : RenderingOnly M)
    {ρ : Role} (hρ : ρ ≠ .rendering) {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree)
    {t : Exp} {ε : Eff} (dt : Deriv (S ++ M) true (.tm [] ρ t A ε)) :
    (∃ n ε', Steps t n ∧ Normal n ∧ n.Old S.length ∧
      Derivable (S ++ M) true (.tm [] ρ n A ε')) ∧
    ∀ u v, u.Old S.length → v.Old S.length → Conv u v →
      ∃ w, w.Old S.length ∧ Steps u w ∧ Steps v w := by
  obtain ⟨n, ε', hs, hn, -, ⟨dn⟩⟩ := dt.normalize hSM
  exact ⟨⟨n, ε', hs, hn, extension_support_conservative hSM (.inl hM) hρ hA hgf dn hn, ⟨dn⟩⟩,
    fun _ _ hu _ h => h.old_join hu⟩

/-- **Theorem 10.5** (fresh-family conservativity). Let `M` be a fresh-witness-family
module over `S`. At every old grade-free type of a non-rendering role (the paper
states the protected roles), every closed term of the extension reduces to an
old normal term, and convertible old terms are joined through old terms. -/
theorem fresh_family_conservative {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : FreshWitnessFamily S.length M) {ρ : Role} (hρ : ρ ≠ .rendering) {A : Exp}
    (hA : A.Old S.length) (hgf : A.gradefree) {t : Exp} {ε : Eff}
    (dt : Deriv (S ++ M) true (.tm [] ρ t A ε)) :
    (∃ n ε', Steps t n ∧ Normal n ∧ n.Old S.length ∧
      Derivable (S ++ M) true (.tm [] ρ n A ε')) ∧
    ∀ u v, u.Old S.length → v.Old S.length → Conv u v →
      ∃ w, w.Old S.length ∧ Steps u w ∧ Steps v w := by
  obtain ⟨n, ε', hs, hn, -, ⟨dn⟩⟩ := dt.normalize hSM
  exact ⟨⟨n, ε', hs, hn, extension_support_conservative hSM (.inr hM) hρ hA hgf dn hn, ⟨dn⟩⟩,
    fun _ _ hu _ h => h.old_join hu⟩

/-! ## Lemma 10.1: evidence-entry inversion -/

/-- **Lemma 10.1** (ii)–(iii) (evidence-entry inversion). A closed normal stamp
comes from one evidence entry `i`: a certificate's three constants, or the
normal form of an attested term with the attestation's event and origin. When
the entry is in the base, the stamp is old; so a module that adds no
certificate or attestation adds no new closed normal stamp. -/
theorem stamp_entry {S : Sig} (hS : SigWF S) {N : ℕ} {ρ σ : Role} {t A : Exp} {ε : Eff}
    (d : Deriv S true (.tm [] ρ t (.stamped σ A) ε)) (hn : Normal t) :
    ∃ i, (i < N → t.Old N) ∧
      ((∃ σ' A', S[i]? = some (.cert σ' A') ∧
          t = .stamp (.const i 0) (.const i 1) (.const i 2)) ∨
       (∃ A' t₀ u, S[i]? = some (.attest A' t₀) ∧ t = .stamp u (.const i 0) (.const i 1) ∧
          Steps t₀ u)) := by
  rcases canonical_credential hS d hn with ⟨i, ⟨σ', A', hi, rfl⟩ | ⟨A', t₀, u, hi, rfl, hc⟩⟩
  · exact ⟨i, fun h => ⟨h, h, h⟩, .inl ⟨σ', A', hi, rfl⟩⟩
  · have hnu := hn.stamp.1
    obtain ⟨w, h₁, h₂⟩ := hc.joinable
    rw [← hnu.eq_of_steps h₁] at h₂
    refine ⟨i, fun h => ⟨?_, h, h⟩, .inr ⟨A', t₀, u, hi, rfl, h₂⟩⟩
    exact h₂.old (((hS.attest_old hi).2).mono h.le)


/-! ## Origins in a protected context -/

/-- A context whose variables all have protected roles. -/
def ProtectedCtx (Γ : Ctx) : Prop := ∀ p ∈ Γ, p.1 = .form ∨ p.1 = .presentation

/-- A normal neutral term at the witness role, in a context of protected
variables, is headed by a witness constant, and its type is reached from the
constant's type; an event or origin constant heads only itself. -/
theorem witness_neutral {S : Sig} (hS : SigWF S) {acc : Bool} :
    ∀ (t : Exp) {Γ : Ctx} {C : Exp} {ε : Eff}, ProtectedCtx Γ →
      Deriv S acc (.tm Γ .witness t C ε) → Normal t → NotIntro t →
      ∃ i k T, t.head = .const i k ∧ S.const? i k = some (.witness, T) ∧
        GSkel.Desc (gskel T) (gskel C) ∧
        (t ≠ t.head → T ≠ .event ∧ ∀ A e u, T ≠ .origin A e u) := by
  intro t
  induction t with
  | var i =>
    intro Γ C ε hΓ d _ _
    obtain ⟨A₀, hi, -⟩ := d.inv_var
    rcases hΓ _ (List.mem_of_getElem? hi) with h | h <;> cases h
  | const i k =>
    intro Γ C ε _ d _ _
    obtain ⟨A₀, hc, hconv, -, hf⟩ := d.inv_const
    obtain ⟨γ, hC⟩ := d.tm_ty
    refine ⟨i, k, A₀, rfl, hc, ?_, fun h => absurd rfl h⟩
    rw [gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)]
    exact .refl _
  | app f u ihf _ =>
    intro Γ C ε hΓ d hn _
    obtain ⟨q, σ, A, B, φ, η, hconv, -, ⟨df⟩, -, hf⟩ := d.inv_app
    obtain ⟨hnf, -, hnl⟩ := hn.app
    have hfi : NotIntro f := by
      cases f with
      | lam q' σ' A' b => exact hnl _ _ _ _ rfl
      | pair => exact df.not_pair_of_pi
      | stamp => exact df.not_stamp_of_pi
      | _ => trivial
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    have hCB : gskel C = gskel B := by
      rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
        (gskel_subst dpi.tyShape_ty.2 _).1]
    rw [hCB]
    obtain ⟨i, k, T, hh, hc, hdesc, -⟩ := ihf hΓ df hnf hfi
    refine ⟨i, k, T, hh, hc, hdesc.trans (.arr (.refl _)), fun _ => ⟨?_, ?_⟩⟩
    · rintro rfl; cases hdesc.of_ev
    · rintro A e u rfl; cases hdesc.of_org
  | fst p ihp =>
    intro Γ C ε hΓ d hn _
    obtain ⟨A, B, hconv, ⟨dp⟩, hf⟩ := d.inv_fst
    obtain ⟨hnp, hnpair⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨γ, hC⟩ := d.tm_ty
    rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)]
    obtain ⟨i, k, T, hh, hc, hdesc, -⟩ := ihp hΓ dp hnp hpi
    refine ⟨i, k, T, hh, hc, hdesc.trans (.fst (.refl _)), fun _ => ⟨?_, ?_⟩⟩
    · rintro rfl; cases hdesc.of_ev
    · rintro A e u rfl; cases hdesc.of_org
  | snd p ihp =>
    intro Γ C ε hΓ d hn _
    obtain ⟨A, B, hconv, ⟨dp⟩, hf⟩ := d.inv_snd
    obtain ⟨hnp, hnpair⟩ := hn.snd
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨γp, ⟨ds⟩⟩ := dp.tm_ty
    have hCB : gskel C = gskel B := by
      rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
        (gskel_subst ds.tyShape_ty.2 _).1]
    rw [hCB]
    obtain ⟨i, k, T, hh, hc, hdesc, -⟩ := ihp hΓ dp hnp hpi
    refine ⟨i, k, T, hh, hc, hdesc.trans (.snd (.refl _)), fun _ => ⟨?_, ?_⟩⟩
    · rintro rfl; cases hdesc.of_ev
    · rintro A e u rfl; cases hdesc.of_org
  | gate g ds s _ _ =>
    intro Γ C ε _ d _ _
    obtain ⟨Δ, σ, A, B, δ, η, hg, -⟩ := d.inv_gate
    rcases (hS.gate_cond hg).2.1 with h | h <;> cases h
  | node g ℓ ds a e _ _ _ =>
    intro Γ C ε _ d _ _
    obtain ⟨Δ, σ, A, B, δ, θ, η, hg, -⟩ := d.inv_node
    rcases (hS.gate_cond hg).2.1 with h | h <;> cases h
  | lam | pair | stamp => intro Γ C ε _ _ _ hi; exact absurd hi id
  | fam | event | origin | stamped | pi | sigma | nil | cons =>
    intro Γ C ε _ d; exact d.isTermHead.elim

/-- **Lemma 10.1** (iv), the origin part: a normal origin at the witness role in
a context of protected variables is the origin constant of one evidence entry,
whose declared type is convertible to it. -/
theorem origin_protected {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {t A e u : Exp}
    {ε : Eff} (hΓ : ProtectedCtx Γ) (d : Deriv S acc (.tm Γ .witness t (.origin A e u) ε))
    (hn : Normal t) :
    ∃ i k A' e' u', t = .const i k ∧ S.const? i k = some (.witness, .origin A' e' u') ∧
      Conv (.origin A' e' u') (.origin A e u) := by
  have hi : NotIntro t := not_notIntro_of_tags d (by trivial) (by simp [Conv.headTag])
    (by simp [Conv.headTag]) (by simp [Conv.headTag])
  obtain ⟨i, k, T, hh, hc, hdesc, hne⟩ := witness_neutral hS t hΓ d hn hi
  rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨⟨A', e', u', hT⟩, -⟩
  · simp [gskel, GSkel.Ord] at h
  · simp [gskel] at h
  · subst hT
    by_cases htt : t = t.head
    · rw [hh] at htt
      subst htt
      obtain ⟨A₀, hc', hconv, -, -⟩ := d.inv_const
      rw [hc] at hc'
      cases hc'
      exact ⟨i, k, A', e', u', rfl, hc, hconv⟩
    · exact absurd rfl ((hne htt).2 A' e' u')

/-! ## Evidence: old up to pinned records -/

/-- The payload `p` and event `e` of a node come from one evidence entry: a
certificate's payload and event constants, or an exact attestation's event
constant and a reduct of its attested term. -/
def Pinned (S : Sig) (p e : Exp) : Prop :=
  ∃ i, (∃ σ A, S[i]? = some (.cert σ A) ∧ p = .const i 0 ∧ e = .const i 1) ∨
    (∃ A t, S[i]? = some (.attest A t) ∧ e = .const i 0 ∧ Steps t p)

/-- `t` is old, except inside the payload and event of nodes pinned to an
evidence entry. -/
def Exp.OldEv (S : Sig) (N : ℕ) : Exp → Prop
  | var _ => True
  | const i _ => i < N
  | fam a args => a < N ∧ args.OldEv S N
  | event => True
  | origin A e t => A.OldEv S N ∧ e.OldEv S N ∧ t.OldEv S N
  | stamped _ A => A.OldEv S N
  | pi _ _ A B => A.OldEv S N ∧ B.OldEv S N
  | sigma _ A B => A.OldEv S N ∧ B.OldEv S N
  | lam _ _ A t => A.OldEv S N ∧ t.OldEv S N
  | app t u => t.OldEv S N ∧ u.OldEv S N
  | pair t u => t.OldEv S N ∧ u.OldEv S N
  | fst t => t.OldEv S N
  | snd t => t.OldEv S N
  | stamp t e o => t.OldEv S N ∧ e.OldEv S N ∧ o.OldEv S N
  | gate g ds s => g < N ∧ ds.OldEv S N ∧ s.OldEv S N
  | node g _ ds p e => g < N ∧ ds.OldEv S N ∧ ((p.OldEv S N ∧ e.OldEv S N) ∨ Pinned S p e)
  | nil => True
  | cons t ts => t.OldEv S N ∧ ts.OldEv S N

theorem Exp.Old.oldEv {S : Sig} {N : ℕ} {t : Exp} (h : t.Old N) : t.OldEv S N := by
  induction t <;> simp_all [Exp.Old, Exp.OldEv]

theorem SigWF.attest_closed {S : Sig} (hS : SigWF S) {i : ℕ} {A t : Exp}
    (h : S[i]? = some (.attest A t)) : t.Closed := by
  induction hS with
  | nil => simp at h
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | gate _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [getElem?_append_singleton] at h
    split_ifs at h with h₁ h₂
    · exact ih h
    · cases h
  | @attest S' A' t' θ _ ht _ _ _ ih =>
    rw [getElem?_append_singleton] at h
    split_ifs at h with h₁ h₂
    · exact ih h
    · cases h
      obtain ⟨dt⟩ := ht
      exact dt.scoped.1

theorem Pinned.subst {S : Sig} (hS : SigWF S) {p e : Exp} (h : Pinned S p e) (σ : ℕ → Exp) :
    Pinned S (p.subst σ) (e.subst σ) := by
  obtain ⟨i, ⟨σ', A, hi, rfl, rfl⟩ | ⟨A, t, hi, rfl, hs⟩⟩ := h
  · exact ⟨i, .inl ⟨σ', A, hi, rfl, rfl⟩⟩
  · refine ⟨i, .inr ⟨A, t, hi, rfl, ?_⟩⟩
    have := hs.subst σ
    rwa [Exp.subst_closed (hS.attest_closed hi)] at this

theorem Exp.OldEv.ren {S : Sig} (hS : SigWF S) {N : ℕ} {t : Exp} (ht : t.OldEv S N)
    (ξ : ℕ → ℕ) : (t.ren ξ).OldEv S N := by
  induction t generalizing ξ with
  | node g ℓ ds p e ihds ihp ihe =>
    refine ⟨ht.1, ihds ht.2.1 ξ, ?_⟩
    rcases ht.2.2 with ⟨hp, he⟩ | hpin
    · exact .inl ⟨ihp hp ξ, ihe he ξ⟩
    · have := hpin.subst hS (var ∘ ξ)
      rw [← Exp.ren_eq_subst, ← Exp.ren_eq_subst] at this
      exact .inr this
  | _ => simp_all [Exp.OldEv, Exp.ren]

theorem Exp.OldEv.subst {S : Sig} (hS : SigWF S) {N : ℕ} {t : Exp} (ht : t.OldEv S N)
    {σ : ℕ → Exp} (hσ : ∀ i, (σ i).OldEv S N) : (t.subst σ).OldEv S N := by
  induction t generalizing σ with
  | var i => exact hσ i
  | pi q ρ A B ihA ihB =>
    refine ⟨ihA ht.1 hσ, ihB ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren hS _
  | sigma ρ A B ihA ihB =>
    refine ⟨ihA ht.1 hσ, ihB ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren hS _
  | lam q ρ A t ihA iht =>
    refine ⟨ihA ht.1 hσ, iht ht.2 fun i => ?_⟩
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).ren hS _
  | node g ℓ ds p e ihds ihp ihe =>
    refine ⟨ht.1, ihds ht.2.1 hσ, ?_⟩
    rcases ht.2.2 with ⟨hp, he⟩ | hpin
    · exact .inl ⟨ihp hp hσ, ihe he hσ⟩
    · exact .inr (hpin.subst hS σ)
  | _ => simp_all [Exp.OldEv, Exp.subst]

theorem Exp.OldEv.inst {S : Sig} (hS : SigWF S) {N : ℕ} {t u : Exp} (ht : t.OldEv S N)
    (hu : u.OldEv S N) : (t.inst u).OldEv S N :=
  ht.subst hS fun i => by cases i with | zero => exact hu | succ => trivial

/-- Reduction keeps an expression old up to pinned records. -/
theorem Step.oldEv {S : Sig} (hS : SigWF S) {N : ℕ} {t t' : Exp} (h : Step t t')
    (ht : t.OldEv S N) : t'.OldEv S N := by
  induction h with
  | beta => exact ht.1.2.inst hS ht.2
  | fstPair => exact ht.1
  | sndPair => exact ht.2
  | record => exact ⟨ht.1, ht.2.1, .inl ⟨ht.2.2.1, ht.2.2.2.1⟩⟩
  | node₂ hs ih =>
    refine ⟨ht.1, ht.2.1, ?_⟩
    rcases ht.2.2 with ⟨hp, he⟩ | ⟨i, ⟨σ, A, hi, rfl, rfl⟩ | ⟨A, t, hi, rfl, hst⟩⟩
    · exact .inl ⟨ih hp, he⟩
    · cases hs
    · exact .inr ⟨i, .inr ⟨A, t, hi, rfl, hst.tail hs⟩⟩
  | node₃ hs ih =>
    refine ⟨ht.1, ht.2.1, ?_⟩
    rcases ht.2.2 with ⟨hp, he⟩ | ⟨i, ⟨σ, A, hi, rfl, rfl⟩ | ⟨A, t, hi, rfl, hst⟩⟩
    · exact .inl ⟨hp, ih he⟩
    · cases hs
    · cases hs
  | node₁ _ ih => exact ⟨ht.1, ih ht.2.1, ht.2.2⟩
  | _ => simp_all [Exp.OldEv]

theorem Steps.oldEv {S : Sig} (hS : SigWF S) {N : ℕ} {t t' : Exp} (h : Steps t t')
    (ht : t.OldEv S N) : t'.OldEv S N := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact hs.oldEv hS ih

/-- `C` reduces to an expression old up to pinned records. -/
def OldEvConv (S : Sig) (N : ℕ) (C : Exp) : Prop := ∃ w, Steps C w ∧ w.OldEv S N

theorem OldEvConv.of_oldEv {S : Sig} {N : ℕ} {C : Exp} (h : C.OldEv S N) : OldEvConv S N C :=
  ⟨C, .refl, h⟩

theorem OldEvConv.of_conv {S : Sig} (hS : SigWF S) {N : ℕ} {C C' : Exp} (hc : Conv C C')
    (h : OldEvConv S N C') : OldEvConv S N C := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨v, h₁, h₂⟩ := hc.joinable
  obtain ⟨x, h₃, h₄⟩ := Steps.confluent h₂ hw
  exact ⟨x, h₁.trans h₃, h₄.oldEv hS hold⟩

theorem Normal.oldEv {S : Sig} {N : ℕ} {C : Exp} (hn : Normal C) (h : OldEvConv S N C) :
    C.OldEv S N := by
  obtain ⟨w, hw, hold⟩ := h
  rwa [hn.eq_of_steps hw]

theorem OldEvConv.pi {S : Sig} {N : ℕ} {q : Grade} {σ : Role} {A B : Exp}
    (h : OldEvConv S N (.pi q σ A B)) : OldEvConv S N A ∧ OldEvConv S N B := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨A', B', rfl, h₁, h₂⟩ := Steps.pi_inv hw
  exact ⟨⟨A', h₁, hold.1⟩, ⟨B', h₂, hold.2⟩⟩

theorem OldEvConv.sigma {S : Sig} {N : ℕ} {ρ : Role} {A B : Exp}
    (h : OldEvConv S N (.sigma ρ A B)) : OldEvConv S N A ∧ OldEvConv S N B := by
  obtain ⟨w, hw, hold⟩ := h
  obtain ⟨A', B', rfl, h₁, h₂⟩ := Steps.sigma_inv hw
  exact ⟨⟨A', h₁, hold.1⟩, ⟨B', h₂, hold.2⟩⟩

theorem OldEvConv.subst {S : Sig} (hS : SigWF S) {N : ℕ} {B : Exp} (h : OldEvConv S N B)
    {σ : ℕ → Exp} (hσ : ∀ i, (σ i).OldEv S N) : OldEvConv S N (B.subst σ) := by
  obtain ⟨w, hw, hold⟩ := h
  exact ⟨w.subst σ, hw.subst σ, hold.subst hS hσ⟩

theorem OldEvConv.inst {S : Sig} (hS : SigWF S) {N : ℕ} {B u : Exp} (h : OldEvConv S N B)
    (hu : u.OldEv S N) : OldEvConv S N (B.inst u) :=
  h.subst hS fun i => by cases i with | zero => exact hu | succ => trivial

theorem Exp.OldEv.upN {S : Sig} (hS : SigWF S) {N : ℕ} {σ : ℕ → Exp}
    (hσ : ∀ i, (σ i).OldEv S N) : ∀ k i, (upN k σ i).OldEv S N := by
  intro k
  induction k with
  | zero => exact hσ
  | succ k ih =>
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (ih i).ren hS _

theorem Exp.OldEv.instType {S : Sig} (hS : SigWF S) {N : ℕ} {ds : Exp} (hds : ds.OldEv S N) :
    ∀ {Δ : Tel} {C : Exp}, C.OldEv S N → (instType ds Δ C).OldEv S N := by
  induction ds with
  | cons t ts _ ihts =>
    intro Δ C hC
    cases Δ with
    | nil => exact hC
    | cons p Δ =>
      exact ihts hds.2 (hC.subst hS (Exp.OldEv.upN hS (fun i => by
        cases i with | zero => exact hds.1 | succ => trivial) _))
  | _ => intro Δ C hC; cases Δ <;> exact hC

/-- An expression old up to pinned records, whose pinned records all have old
payloads and events, is old. -/
theorem Exp.OldEv.old {S : Sig} {N : ℕ} {t : Exp} (ht : t.OldEv S N)
    (h : ∀ g ℓ ds p e, Occurs (.node g ℓ ds p e) t → Pinned S p e → p.Old N ∧ e.Old N) :
    t.Old N := by
  induction t with
  | node g ℓ ds p e ihds ihp ihe =>
    refine ⟨ht.1, ihds ht.2.1 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
      (.child (by simp [Exp.children]) ho), ?_⟩
    rcases ht.2.2 with ⟨hp, he⟩ | hpin
    · exact ⟨ihp hp fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
          (.child (by simp [Exp.children]) ho),
        ihe he fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho)⟩
    · exact h g ℓ ds p e .refl hpin
  | var | const | event | nil => exact ht
  | fam a args ih =>
    exact ⟨ht.1, ih ht.2 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
      (.child (by simp [Exp.children]) ho)⟩
  | stamped _ A ih | fst A ih | snd A ih =>
    exact ih ht fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho)
  | origin A e t ihA ihe iht | stamp A e t ihA ihe iht =>
    exact ⟨ihA ht.1 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
        (.child (by simp [Exp.children]) ho),
      ihe ht.2.1 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho),
      iht ht.2.2 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho)⟩
  | pi _ _ A B ihA ihB | sigma _ A B ihA ihB | lam _ _ A B ihA ihB | app A B ihA ihB
    | pair A B ihA ihB | cons A B ihA ihB =>
    exact ⟨ihA ht.1 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
        (.child (by simp [Exp.children]) ho),
      ihB ht.2 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho)⟩
  | gate g ds s ihds ihs =>
    exact ⟨ht.1, ihds ht.2.1 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e'
        (.child (by simp [Exp.children]) ho),
      ihs ht.2.2 fun g' ℓ' ds' p' e' ho => h g' ℓ' ds' p' e' (.child (by simp [Exp.children]) ho)⟩


/-! ## Lemma 10.2 (iii) and Theorem 10.6: evidence modules -/

/-- A context of protected variables with grade-free types old up to pinned
records. -/
def CtxFP (S : Sig) (N : ℕ) (Γ : Ctx) : Prop :=
  ∀ p ∈ Γ, (p.1 = .form ∨ p.1 = .presentation) ∧ (gskel p.2).GF ∧ p.2.OldEv S N

theorem CtxFP.nil {S : Sig} {N : ℕ} : CtxFP S N [] := fun _ h => by cases h

theorem CtxFP.prot {S : Sig} {N : ℕ} {Γ : Ctx} (h : CtxFP S N Γ) : ProtectedCtx Γ :=
  fun p hp => (h p hp).1

/-- The region lemma behind Lemma 10.2 (iii). Let every new constant have the
witness role and every gate be old. A normal, justified term at a protected
role, in a context of protected variables, whose type is grade-free and reduces
to an expression old up to pinned records (or which is neutral), is old up to
pinned records: every new constant lies in the payload or event of a node
pinned to one evidence entry. -/
theorem Deriv.region_evidence {S : Sig} (hS : SigWF S) {N : ℕ}
    (hnew : ∀ i k ρ T, N ≤ i → S.const? i k = some (ρ, T) → ρ = .witness)
    (hgate : ∀ g Δ σ A ρ B, S.gate? g = some (Δ, σ, A, ρ, B) → g < N) {j : Judg}
    (d : Deriv S true j) :
    match j with
    | .tm Γ ρ n C _ => Normal n → (ρ = .form ∨ ρ = .presentation) → CtxWF S Γ → CtxFP S N Γ →
        Justified S Γ n → (((gskel C).GF ∧ OldEvConv S N C) ∨ NotIntro n) →
        (gskel C).GF ∧ OldEvConv S N C ∧ n.OldEv S N
    | .spine Γ ts Δ _ => Normal ts → CtxWF S Γ → CtxFP S N Γ → Justified S Γ ts →
        (∀ p ∈ Δ, (p.1 = .form ∨ p.1 = .presentation) ∧ p.2.TyShape ∧ (gskel p.2).GF ∧
          OldEvConv S N p.2) →
        ts.OldEv S N
    | _ => True := by
  induction d with
  | tyFam | tyEvent | tyOrigin | tyStamped | tyPi | tySigma | telNil | telCons => trivial
  | @var Γ i ρ A C γ ε hΓi hC _ _ _ _ =>
    intro _ _ _ hctx _ _
    obtain ⟨-, hgf, hold⟩ := hctx _ (List.mem_of_getElem? hΓi)
    refine ⟨?_, ?_, trivial⟩
    · rw [hC, gskel_ren]; exact hgf
    · rw [hC]; exact .of_oldEv (hold.ren hS _)
  | @const Γ i k ρ A γ ε hc _ _ _ _ =>
    intro _ hρ _ _ _ _
    have hi : i < N := by
      by_contra h
      rcases hρ with rfl | rfl <;> cases hnew i k _ A (by omega) hc
    exact ⟨hS.const_gf hc, .of_oldEv ((hS.const_old hc).mono (by omega)).oldEv, hi⟩
  | @lam Γ q σ ρ A B t α θ γ ε dA dt hq dC hε hv ihA iht ihC =>
    intro hn hρ hΓ hctx hJ hCh
    obtain ⟨⟨hq0, hAgf, hBgf⟩, hold⟩ := hCh.resolve_right id
    have hσ := protected_of_demand (hq0 ▸ dC.tyPi_demand) hρ
    have hAold : A.OldEv S N := (Normal.lam hn).1.oldEv hold.pi.1
    have hctx' : CtxFP S N ((σ, A) :: Γ) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hσ, hAgf, hAold⟩
      · exact hctx p hp
    obtain ⟨-, -, hbold⟩ := iht (Normal.lam hn).2 hρ (.cons hΓ ⟨dA⟩) hctx' hJ.2.2
      (.inl ⟨hBgf, hold.pi.2⟩)
    exact ⟨⟨hq0, hAgf, hBgf⟩, hold, hAold, hbold⟩
  | @app Γ q σ ρ A B f u C φ η γ ε df du hC dC hε hv ihf ihu ihC =>
    intro hn hρ hΓ hctx hJ _
    obtain ⟨hnf, hnu, hnl⟩ := hn.app
    have hfi : NotIntro f := by
      cases f with
      | lam q' σ' A' b => exact hnl _ _ _ _ rfl
      | pair => exact df.not_pair_of_pi
      | stamp => exact df.not_stamp_of_pi
      | _ => trivial
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    obtain ⟨⟨hq0, hAgf, hBgf⟩, hold, hfold⟩ := ihf hnf hρ hΓ hctx hJ.1 (.inr hfi)
    have hσ := protected_of_demand (hq0 ▸ dpi.tyPi_demand) hρ
    obtain ⟨-, -, huold⟩ := ihu hnu hσ hΓ hctx hJ.2 (.inl ⟨hAgf, hold.pi.1⟩)
    refine ⟨?_, hC ▸ hold.pi.2.inst hS huold, hfold, huold⟩
    rw [hC, (gskel_subst dpi.tyShape_ty.2 _).1]; exact hBgf
  | @pair Γ ρ A B t u θ η γ ε dt du dC hε hv iht ihu ihC =>
    intro hn hρ hΓ hctx hJ hCh
    obtain ⟨⟨hAgf, hBgf⟩, hold⟩ := hCh.resolve_right id
    obtain ⟨hnt, hnu⟩ := hn.pair
    obtain ⟨-, -, β, ⟨dB⟩⟩ := dC.inv_tySigma
    obtain ⟨-, -, htold⟩ := iht hnt hρ hΓ hctx hJ.1 (.inl ⟨hAgf, hold.sigma.1⟩)
    have hBt : (gskel (B.inst t)).GF := by rw [(gskel_subst dB.tyShape_ty _).1]; exact hBgf
    obtain ⟨-, -, huold⟩ := ihu hnu hρ hΓ hctx hJ.2 (.inl ⟨hBt, hold.sigma.2.inst hS htold⟩)
    exact ⟨⟨hAgf, hBgf⟩, hold, htold, huold⟩
  | @fst Γ ρ A B p π γ dp dA hv ihp ihA =>
    intro hn hρ hΓ hctx hJ _
    obtain ⟨hnp, hnpair⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨⟨hAgf, -⟩, hold, hpold⟩ := ihp hnp hρ hΓ hctx hJ (.inr hpi)
    exact ⟨hAgf, hold.sigma.1, hpold⟩
  | @snd Γ ρ A B C p π γ dp hC dC hv ihp ihC =>
    intro hn hρ hΓ hctx hJ _
    obtain ⟨hnp, hnpair⟩ := hn.snd
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨γp, ⟨ds⟩⟩ := dp.tm_ty
    obtain ⟨⟨-, hBgf⟩, hold, hpold⟩ := ihp hnp hρ hΓ hctx hJ (.inr hpi)
    refine ⟨?_, hC ▸ hold.sigma.2.inst hS hpold, hpold⟩
    rw [hC, (gskel_subst ds.tyShape_ty.2 _).1]; exact hBgf
  | stamp =>
    intro _ hρ _ _ _ _
    rcases hρ with h | h <;> cases h
  | @gate Γ g ds s Δ σ A ρ B C δ η γ ε hg dds dst hC dC hε hv ihds ihst ihC =>
    intro hn hρ hΓ hctx _ _
    exfalso
    obtain ⟨-, hns, hnst⟩ := hn.gate
    have hsi : NotIntro s := by
      cases s with
      | lam => exact dst.not_lam_of_stamped
      | pair => exact dst.not_pair_of_stamped
      | stamp a e o => exact hnst a e o rfl
      | _ => trivial
    obtain ⟨i, k, T, -, hc, hdesc, -⟩ := witness_neutral hS s hctx.prot dst hns hsi
    rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · cases h
    · cases h
  | @node Γ g ℓ ds t e Δ σ A ρ B C δ θ η γ ε hg dds dt de hC dC hε hv ihds iht ihe ihC =>
    intro hn hρ hΓ hctx hJ _
    obtain ⟨hσg, hρg, hΔ, -, hBg⟩ := hS.gate_cond hg
    obtain ⟨hΔgf, -⟩ := hS.gate_gradefree hg
    obtain ⟨hΔold, -, hBold⟩ := hS.gate_old hg
    have hgN := hgate _ _ _ _ _ _ hg
    obtain ⟨-, ⟨hBf, ⟨dBf⟩⟩⟩ := hS.gate_formed hg
    obtain ⟨⟨δt, ⟨dtel⟩⟩, -, -⟩ := hS.gate_tel hg []
    obtain ⟨hnds, hnt, hne⟩ := hn.node
    obtain ⟨⟨Δ', σ', A', ρ', B', hg', hl, o, ω, ⟨dO⟩⟩, hJds, -, -⟩ := hJ
    rw [hg] at hg'
    cases hg'
    have hdsold : ds.OldEv S N := ihds hnds hΓ hctx hJds fun p hp =>
      ⟨protected_of_demand (le_of_eq (hΔ p hp)) hρg, dtel.tel_tyShape p hp,
        gskel_gf (hΔgf p hp), .of_oldEv ((hΔold p hp).mono hgN.le).oldEv⟩
    -- the dropped origin, normalized, is an evidence origin constant
    obtain ⟨o', ho', hno'⟩ := dO.sn_tm.exists_normal
    obtain ⟨ω', -, ⟨dO'⟩⟩ := dO.subject_reduction_steps hS hΓ ho'
    obtain ⟨i, k, A₀, e₀, u₀, rfl, hc, hconv⟩ := origin_protected hS hctx.prot dO' hno'
    obtain ⟨-, hee, huu⟩ := Conv.origin_inj hconv
    have hnc : ∀ a b, Normal (.const a b) := fun a b _ h => by cases h
    have hpin : Pinned S t e := by
      rcases hS.const_cases hc with ⟨-, ho⟩ | ⟨-, hT, -⟩ | ⟨-, hent⟩
      · obtain ⟨a, args, he, -⟩ := ho; cases he
      · cases hT
      · rcases hent with ⟨σc, Ac, hi, rfl, hT⟩ | ⟨Aa, ta, hi, rfl, hT⟩ <;>
          obtain ⟨-, rfl, rfl⟩ := Exp.origin.inj hT
        · refine ⟨i, .inl ⟨σc, Ac, hi, ?_, ?_⟩⟩
          · exact (Normal.eq_of_conv (hnc _ _) hnt huu).symm
          · exact (Normal.eq_of_conv (hnc _ _) hne hee).symm
        · refine ⟨i, .inr ⟨Aa, _, hi, (Normal.eq_of_conv (hnc _ _) hne hee).symm, ?_⟩⟩
          obtain ⟨w, h₁, h₂⟩ := huu.joinable
          rwa [← hnt.eq_of_steps h₂] at h₁
    refine ⟨?_, ?_, hgN, hdsold, .inr hpin⟩
    · rw [hC, (gskel_instType dBf.tyShape_ty ds Δ).1]; exact gskel_gf hBg
    · rw [hC]; exact .of_oldEv (hdsold.instType hS ((hBold.mono hgN.le).oldEv))
  | @conv Γ ρ t A B θ γ dt hAB dB iht ihB =>
    intro hn hρ hΓ hctx hJ hCh
    obtain ⟨γ', hA⟩ := dt.tm_ty
    have hsk : gskel A = gskel B := gskel_conv hAB (TyShape.of_ty hA) dB.tyShape_ty
    obtain ⟨h₁, h₂, h₃⟩ := iht hn hρ hΓ hctx hJ
      (hCh.imp (fun h => ⟨hsk ▸ h.1, OldEvConv.of_conv hS hAB h.2⟩) id)
    exact ⟨hsk ▸ h₁, OldEvConv.of_conv hS hAB.symm h₂, h₃⟩
  | spineNil => intro _ _ _ _ _; trivial
  | @spineCons Γ ρ t ts A Δ ε₁ ε₂ ε dt dts hε iht ihts =>
    intro hn hΓ hctx hJ hent
    obtain ⟨hnt, hnts⟩ := hn.cons
    obtain ⟨hρt, hTyA, hGFA, hOldA⟩ := hent (ρ, A) (List.mem_cons_self ..)
    obtain ⟨-, -, htold⟩ := iht hnt hρt hΓ hctx hJ.1 (.inl ⟨hGFA, hOldA⟩)
    refine ⟨htold, ihts hnts hΓ hctx hJ.2 fun p hp => ?_⟩
    obtain ⟨q, hq, k, rfl⟩ := Tel.mem_subst hp
    obtain ⟨hρq, hTyq, hGFq, hOldq⟩ := hent q (List.mem_cons_of_mem _ hq)
    have hτ : ∀ i, (upN k (inst1 t) i).OldEv S N :=
      Exp.OldEv.upN hS (fun i => by cases i with | zero => exact htold | succ => trivial) k
    exact ⟨hρq, (gskel_subst hTyq _).2, (gskel_subst hTyq _).1 ▸ hGFq, hOldq.subst hS hτ⟩

theorem EvidenceInhabitant.witness {S M : Sig} (hM : EvidenceInhabitant S.length M) :
    ∀ i k ρ T, S.length ≤ i → (S ++ M).const? i k = some (ρ, T) → ρ = .witness := by
  intro i k ρ T hi hc
  unfold Sig.const? at hc
  cases he : (S ++ M)[i]? with
  | none => simp [he] at hc
  | some e =>
    rw [he] at hc
    rcases hM.2 e (entry_of_new hi he) with ⟨A, rfl, -⟩ | ⟨A, t, rfl, -⟩
    · rcases k with _ | _ | _ | k <;> simp_all
    · rcases k with _ | _ | k <;> simp_all

/-- **Lemma 10.2** (iii) (grade-free extension support, evidence case). Let `M`
be an evidence-inhabitant module over `S`, and let `n` be the normal form of a
closed public term at a protected role whose type is old and grade-free. Then
`n` is old up to pinned records: every new atom of `n` lies in the payload or
event of a node pinned to one evidence entry. -/
theorem extension_support_evidence {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : EvidenceInhabitant S.length M) {ρ : Role} (hρ : ρ = .form ∨ ρ = .presentation)
    {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree) {t : Exp} {ε : Eff}
    (dt : Deriv (S ++ M) true (.tm [] ρ t A ε)) (hpub : t.IsPublic) {n : Exp}
    (hs : Steps t n) (hn : Normal n) : n.OldEv (S ++ M) S.length := by
  obtain ⟨ε', -, ⟨dn⟩⟩ := dt.subject_reduction_steps hSM (.nil hSM) hs
  have hJ := dt.justified_of_reduct hSM (.nil hSM) hpub hs
  exact ((dn.region_evidence hSM hM.witness
    (fun _ _ _ _ _ _ h => gate_old_of_no_gate hM.no_gate h)) hn hρ (.nil hSM) CtxFP.nil hJ
    (.inl ⟨gskel_gf hgf, .of_oldEv hA.oldEv⟩)).2.2

/-- **Theorem 10.6** (no silent enabling). Let `M` be an evidence-inhabitant
module over `S`, and let `t` be a closed public term at a protected role whose
type is old and grade-free. If its normal form `n` is not old, then
`events(n) ∩ Event_M ≠ ∅`: the enabled result names the responsible module in
its normal provenance. Equality of old terms is reflected as for every module. -/
theorem no_silent_enabling {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : EvidenceInhabitant S.length M) {ρ : Role} (hρ : ρ = .form ∨ ρ = .presentation)
    {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree) {t : Exp} {ε : Eff}
    (dt : Deriv (S ++ M) true (.tm [] ρ t A ε)) (hpub : t.IsPublic) {n : Exp}
    (hs : Steps t n) (hn : Normal n) (hnew : ¬n.Old S.length) :
    ∃ e ∈ n.events, ModuleEvent S M e := by
  have hold := extension_support_evidence hSM hM hρ hA hgf dt hpub hs hn
  by_contra hno
  apply hnew
  refine hold.old fun g ℓ ds p e ho hpin => ?_
  obtain ⟨i, ⟨σ, Ac, hi, rfl, rfl⟩ | ⟨Aa, ta, hi, rfl, hst⟩⟩ := hpin
  · by_cases hlt : i < S.length
    · exact ⟨hlt, hlt⟩
    · exact absurd ⟨.const i 1, HasNode.mem_events n ⟨ds, _, ho⟩,
        i, by omega, .inl ⟨σ, Ac, hi, rfl⟩⟩ hno
  · by_cases hlt : i < S.length
    · exact ⟨hst.old ((hSM.attest_old hi).2.mono hlt.le), hlt⟩
    · exact absurd ⟨.const i 0, HasNode.mem_events n ⟨ds, _, ho⟩,
        i, by omega, .inr ⟨Aa, ta, hi, rfl⟩⟩ hno


/-- **Lemma 10.1** (i) (old-head inversion), corrected. A new constant of a
rendering-only or fresh-witness-family module cannot head a closed normal term
at a non-rendering role whose type is old and grade-free: a rendering primitive
has the rendering role, and a fresh constructor has a new result family. (The
paper's form, "a new rendering primitive has ultimate head a new rendering
family", is false: a rendering primitive may construct an old rendering family;
only its role matters.) -/
theorem old_head {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : RenderingOnly M ∨ FreshWitnessFamily S.length M) {ρ : Role} (hρ : ρ ≠ .rendering)
    {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree) {n : Exp} {ε : Eff}
    (d : Deriv (S ++ M) true (.tm [] ρ n A ε)) (hn : Normal n) {i k : ℕ}
    (hh : n.head = .const i k) : i < S.length := by
  have hold := extension_support_conservative hSM hM hρ hA hgf d hn
  have : ∀ t : Exp, t.Old S.length → t.head.Old S.length := by
    intro t ht
    induction t with
    | app f u ihf _ => exact ihf ht.1
    | fst p ih => exact ih ht
    | snd p ih => exact ih ht
    | _ => exact ht
  have h := this n hold
  rw [hh] at h
  exact h

/-! ## Theorem 10.7: composition -/

/-- **Theorem 10.7** (module composition). A module `M'` well formed over `S ++ M`
composes with `M` into the module `M ++ M'` well formed over `S`, and
concatenation is associative. Principal effects, normalization, mediation and
record adequacy are theorems about every well-formed signature, so they hold for
the composite. -/
theorem module_composition {S M M' : Sig} (h : SigWF ((S ++ M) ++ M')) :
    SigWF (S ++ (M ++ M')) ∧ (S ++ M) ++ M' = S ++ (M ++ M') := by
  rw [List.append_assoc] at h
  exact ⟨h, List.append_assoc _ _ _⟩

/-- The rendering-only class is closed under composition. -/
theorem RenderingOnly.append {M M' : Sig} (h₁ : RenderingOnly M) (h₂ : RenderingOnly M') :
    RenderingOnly (M ++ M') := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact h₁ e he
  · exact h₂ e he

/-- The fresh-witness-family class is closed under composition: a constructor of
the second module may build a family of the first, which is new over the base. -/
theorem FreshWitnessFamily.append {N : ℕ} {M M' : Sig} (h₁ : FreshWitnessFamily N M)
    (h₂ : FreshWitnessFamily N M') : FreshWitnessFamily N (M ++ M') := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact h₁ e he
  · exact h₂ e he

theorem FreshWitnessFamily.mono {N N' : ℕ} {M : Sig} (h : N ≤ N') (hM : FreshWitnessFamily N' M) :
    FreshWitnessFamily N M := by
  intro e he
  rcases hM e he with h' | ⟨ρ, A, a, args, rfl, hres, ha⟩
  · exact .inl h'
  · exact .inr ⟨ρ, A, a, args, rfl, hres, h.trans ha⟩

end Artform.Roles.Calculus
