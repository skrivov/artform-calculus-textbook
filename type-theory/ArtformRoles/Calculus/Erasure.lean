import ArtformRoles.Calculus.Modules

/-!
# Erasure and provenance

§11 of the paper.

* `KExp`: the role-free dependent `Π Σ`-calculus `K_S` with a unit type. Its
  constants are the families, the ordinary primitives and the certificate
  payload constants of `S`, and each gate `g` gives an ordinary constructor
  `ḡ : |Δ| → |A| → |B|` (the former `KExp.gate`). Its reduction has beta and the
  two projections, and no record rule.
* `Exp.erase S`: erasure. It removes roles and grades and is homomorphic on
  ordinary syntax; `|Event| = |Origin_A(e, t)| = 1`, `|Stamped_σ(A)| = |A|`,
  `|stamp(t, e, o)| = |t|`, `|gate_g(d⃗; s)| = ḡ(|d⃗|; |s|)`,
  `|node_g(d⃗; t, e)| = ḡ(|d⃗|; |t|)`, and event and origin constants erase to
  the unit term.
* Theorem 11.1 (erasure simulation): `Deriv.erase` (typing is preserved),
  `Step.erase` (a step erases to a step or to equality), `Conv.erase`.
* Proposition 11.2 (provenance stability): `provenance_stable`.
-/

namespace Artform.Roles.Calculus

/-- The expressions of the role-free target calculus `K_S`. -/
inductive KExp : Type
  | var (i : ℕ)
  | const (i k : ℕ)
  | fam (a : ℕ) (args : KExp)
  | unit
  | tt
  | pi (A B : KExp)
  | sigma (A B : KExp)
  | lam (A t : KExp)
  | app (t u : KExp)
  | pair (t u : KExp)
  | fst (t : KExp)
  | snd (t : KExp)
  | gate (g : ℕ) (ds t : KExp)
  | nil
  | cons (t ts : KExp)
  deriving DecidableEq, Repr

namespace KExp

/-- Rename the free variables. -/
def ren (ξ : ℕ → ℕ) : KExp → KExp
  | var i => var (ξ i)
  | const i k => const i k
  | fam a args => fam a (ren ξ args)
  | unit => unit
  | tt => tt
  | pi A B => pi (ren ξ A) (ren (Exp.upRen ξ) B)
  | sigma A B => sigma (ren ξ A) (ren (Exp.upRen ξ) B)
  | lam A t => lam (ren ξ A) (ren (Exp.upRen ξ) t)
  | app t u => app (ren ξ t) (ren ξ u)
  | pair t u => pair (ren ξ t) (ren ξ u)
  | fst t => fst (ren ξ t)
  | snd t => snd (ren ξ t)
  | gate g ds t => gate g (ren ξ ds) (ren ξ t)
  | nil => nil
  | cons t ts => cons (ren ξ t) (ren ξ ts)

/-- A substitution moved under a binder. -/
def up (σ : ℕ → KExp) : ℕ → KExp
  | 0 => var 0
  | i + 1 => ren Nat.succ (σ i)

/-- Substitute for the free variables. -/
def subst (σ : ℕ → KExp) : KExp → KExp
  | var i => σ i
  | const i k => const i k
  | fam a args => fam a (subst σ args)
  | unit => unit
  | tt => tt
  | pi A B => pi (subst σ A) (subst (up σ) B)
  | sigma A B => sigma (subst σ A) (subst (up σ) B)
  | lam A t => lam (subst σ A) (subst (up σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | pair t u => pair (subst σ t) (subst σ u)
  | fst t => fst (subst σ t)
  | snd t => snd (subst σ t)
  | gate g ds t => gate g (subst σ ds) (subst σ t)
  | nil => nil
  | cons t ts => cons (subst σ t) (subst σ ts)

/-- The substitution that puts `u` for `var 0`. -/
def inst1 (u : KExp) : ℕ → KExp
  | 0 => u
  | i + 1 => var i

/-- `t[u/x]`. -/
abbrev inst (t u : KExp) : KExp := subst (inst1 u) t

/-- Substitutions moved under `k` binders. -/
def upN : ℕ → (ℕ → KExp) → ℕ → KExp
  | 0, σ => σ
  | k + 1, σ => up (upN k σ)

end KExp

/-- A telescope of the target calculus. -/
abbrev KTel := List KExp

/-- Substitute in a telescope: each later entry lies under one more binder. -/
def KTel.subst : (ℕ → KExp) → KTel → KTel
  | _, [] => []
  | σ, A :: Δ => A.subst σ :: KTel.subst (KExp.up σ) Δ

/-- Instantiate a type under a whole telescope by an argument list. -/
def kinstType : KExp → KTel → KExp → KExp
  | .cons t ts, _ :: Δ, C =>
    kinstType ts (KTel.subst (KExp.inst1 t) Δ) (C.subst (KExp.upN Δ.length (KExp.inst1 t)))
  | _, _, C => C

/-- One step of the target calculus: beta, the projections, and their
compatible closure. There is no record rule. -/
inductive KStep : KExp → KExp → Prop
  | beta {A t u} : KStep (.app (.lam A t) u) (t.inst u)
  | fstPair {t u} : KStep (.fst (.pair t u)) t
  | sndPair {t u} : KStep (.snd (.pair t u)) u
  | fam {a args args'} : KStep args args' → KStep (.fam a args) (.fam a args')
  | pi₁ {A A' B} : KStep A A' → KStep (.pi A B) (.pi A' B)
  | pi₂ {A B B'} : KStep B B' → KStep (.pi A B) (.pi A B')
  | sigma₁ {A A' B} : KStep A A' → KStep (.sigma A B) (.sigma A' B)
  | sigma₂ {A B B'} : KStep B B' → KStep (.sigma A B) (.sigma A B')
  | lam₁ {A A' t} : KStep A A' → KStep (.lam A t) (.lam A' t)
  | lam₂ {A t t'} : KStep t t' → KStep (.lam A t) (.lam A t')
  | app₁ {t t' u} : KStep t t' → KStep (.app t u) (.app t' u)
  | app₂ {t u u'} : KStep u u' → KStep (.app t u) (.app t u')
  | pair₁ {t t' u} : KStep t t' → KStep (.pair t u) (.pair t' u)
  | pair₂ {t u u'} : KStep u u' → KStep (.pair t u) (.pair t u')
  | fst {t t'} : KStep t t' → KStep (.fst t) (.fst t')
  | snd {t t'} : KStep t t' → KStep (.snd t) (.snd t')
  | gate₁ {g ds ds' t} : KStep ds ds' → KStep (.gate g ds t) (.gate g ds' t)
  | gate₂ {g ds t t'} : KStep t t' → KStep (.gate g ds t) (.gate g ds t')
  | cons₁ {t t' ts} : KStep t t' → KStep (.cons t ts) (.cons t' ts)
  | cons₂ {t ts ts'} : KStep ts ts' → KStep (.cons t ts) (.cons t ts')

/-- Conversion in the target calculus. -/
abbrev KConv : KExp → KExp → Prop := Relation.EqvGen KStep

/-! ## Erasure -/

/-- The event and origin constants of the evidence entries. -/
def Sig.evidence (S : Sig) (i k : ℕ) : Bool :=
  match S[i]?, k with
  | some (.cert _ _), 1 | some (.cert _ _), 2 => true
  | some (.attest _ _), 0 | some (.attest _ _), 1 => true
  | _, _ => false

/-- Erasure into the target calculus (§11.1). -/
def Exp.erase (S : Sig) : Exp → KExp
  | .var i => .var i
  | .const i k => if S.evidence i k then .tt else .const i k
  | .fam a args => .fam a (args.erase S)
  | .event => .unit
  | .origin _ _ _ => .unit
  | .stamped _ A => A.erase S
  | .pi _ _ A B => .pi (A.erase S) (B.erase S)
  | .sigma _ A B => .sigma (A.erase S) (B.erase S)
  | .lam _ _ A t => .lam (A.erase S) (t.erase S)
  | .app t u => .app (t.erase S) (u.erase S)
  | .pair t u => .pair (t.erase S) (u.erase S)
  | .fst t => .fst (t.erase S)
  | .snd t => .snd (t.erase S)
  | .stamp t _ _ => t.erase S
  | .gate g ds s => .gate g (ds.erase S) (s.erase S)
  | .node g _ ds t _ => .gate g (ds.erase S) (t.erase S)
  | .nil => .nil
  | .cons t ts => .cons (t.erase S) (ts.erase S)

/-- Erase a telescope or a context. -/
def eraseTel (S : Sig) (Δ : List (Role × Exp)) : KTel := Δ.map fun p => p.2.erase S

theorem Exp.erase_ren (S : Sig) (ξ : ℕ → ℕ) (t : Exp) :
    (t.ren ξ).erase S = (t.erase S).ren ξ := by
  induction t generalizing ξ with
  | const i k => simp only [Exp.ren, Exp.erase]; split <;> rfl
  | _ => simp_all [Exp.ren, Exp.erase, KExp.ren]

theorem Exp.erase_up (S : Sig) (σ : ℕ → Exp) :
    Exp.erase S ∘ Exp.up σ = KExp.up (Exp.erase S ∘ σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [Exp.up, KExp.up, Exp.erase_ren]

theorem Exp.erase_subst (S : Sig) (σ : ℕ → Exp) (t : Exp) :
    (t.subst σ).erase S = (t.erase S).subst (Exp.erase S ∘ σ) := by
  induction t generalizing σ with
  | const i k => simp only [Exp.subst, Exp.erase]; split <;> rfl
  | _ => simp_all [Exp.subst, Exp.erase, KExp.subst, Exp.erase_up]

theorem Exp.erase_inst1 (S : Sig) (t : Exp) :
    Exp.erase S ∘ Exp.inst1 t = KExp.inst1 (t.erase S) := by
  funext i
  cases i <;> rfl

theorem Exp.erase_inst (S : Sig) (t u : Exp) :
    (t.inst u).erase S = (t.erase S).inst (u.erase S) := by
  rw [Exp.erase_subst]
  congr 1
  funext i
  cases i <;> rfl

theorem Exp.erase_upN (S : Sig) (σ : ℕ → Exp) :
    ∀ k, Exp.erase S ∘ Exp.upN k σ = KExp.upN k (Exp.erase S ∘ σ) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change Exp.erase S ∘ Exp.up (Exp.upN k σ) = KExp.up (KExp.upN k (Exp.erase S ∘ σ))
    rw [Exp.erase_up, ih]

theorem eraseTel_subst (S : Sig) (σ : ℕ → Exp) (Δ : Tel) :
    eraseTel S (Tel.subst σ Δ) = KTel.subst (Exp.erase S ∘ σ) (eraseTel S Δ) := by
  induction Δ generalizing σ with
  | nil => rfl
  | cons p Δ ih =>
    simp only [Tel.subst, eraseTel, List.map_cons, KTel.subst]
    rw [Exp.erase_subst]
    congr 1
    rw [← Exp.erase_up]
    exact ih _

theorem erase_instType (S : Sig) {ds : Exp} {Δ : Tel} (h : ds.IsList Δ.length) (C : Exp) :
    (instType ds Δ C).erase S = kinstType (ds.erase S) (eraseTel S Δ) (C.erase S) := by
  induction ds generalizing Δ C with
  | nil => cases Δ <;> rfl
  | cons t ts _ ihts =>
    cases Δ with
    | nil => simp [Exp.IsList] at h
    | cons p Δ =>
      simp only [Exp.IsList, List.length_cons] at h
      simp only [instType, Exp.erase, eraseTel, List.map_cons, kinstType]
      rw [ihts (by rwa [Tel.length_inst])]
      simp only [Tel.inst, eraseTel_subst, instAt, Exp.erase_subst, Exp.erase_upN,
        List.length_map, Exp.erase_inst1]
      rfl
  | _ => cases Δ <;> simp [Exp.IsList] at h


/-! ## Theorem 11.1: erasure simulation -/

/-- Theorem 11.1, reduction: a step erases to a step of the target calculus, or
to equality (the record step and steps inside dropped provenance). -/
theorem Step.erase (S : Sig) {t t' : Exp} (h : Step t t') :
    KStep (t.erase S) (t'.erase S) ∨ t.erase S = t'.erase S := by
  induction h with
  | beta => left; rw [Exp.erase_inst]; exact .beta
  | fstPair => exact .inl .fstPair
  | sndPair => exact .inl .sndPair
  | record => exact .inr rfl
  | fam _ ih => rcases ih with h | h
                · exact .inl (.fam h)
                · exact .inr (by simp [Exp.erase, h])
  | origin₁ | origin₂ | origin₃ => exact .inr rfl
  | stamped _ ih => exact ih
  | pi₁ _ ih => rcases ih with h | h
                · exact .inl (.pi₁ h)
                · exact .inr (by simp [Exp.erase, h])
  | pi₂ _ ih => rcases ih with h | h
                · exact .inl (.pi₂ h)
                · exact .inr (by simp [Exp.erase, h])
  | sigma₁ _ ih => rcases ih with h | h
                   · exact .inl (.sigma₁ h)
                   · exact .inr (by simp [Exp.erase, h])
  | sigma₂ _ ih => rcases ih with h | h
                   · exact .inl (.sigma₂ h)
                   · exact .inr (by simp [Exp.erase, h])
  | lam₁ _ ih => rcases ih with h | h
                 · exact .inl (.lam₁ h)
                 · exact .inr (by simp [Exp.erase, h])
  | lam₂ _ ih => rcases ih with h | h
                 · exact .inl (.lam₂ h)
                 · exact .inr (by simp [Exp.erase, h])
  | app₁ _ ih => rcases ih with h | h
                 · exact .inl (.app₁ h)
                 · exact .inr (by simp [Exp.erase, h])
  | app₂ _ ih => rcases ih with h | h
                 · exact .inl (.app₂ h)
                 · exact .inr (by simp [Exp.erase, h])
  | pair₁ _ ih => rcases ih with h | h
                  · exact .inl (.pair₁ h)
                  · exact .inr (by simp [Exp.erase, h])
  | pair₂ _ ih => rcases ih with h | h
                  · exact .inl (.pair₂ h)
                  · exact .inr (by simp [Exp.erase, h])
  | fst _ ih => rcases ih with h | h
                · exact .inl (.fst h)
                · exact .inr (by simp [Exp.erase, h])
  | snd _ ih => rcases ih with h | h
                · exact .inl (.snd h)
                · exact .inr (by simp [Exp.erase, h])
  | stamp₁ _ ih => exact ih
  | stamp₂ | stamp₃ => exact .inr rfl
  | gate₁ _ ih => rcases ih with h | h
                  · exact .inl (.gate₁ h)
                  · exact .inr (by simp [Exp.erase, h])
  | gate₂ _ ih => rcases ih with h | h
                  · exact .inl (.gate₂ h)
                  · exact .inr (by simp [Exp.erase, h])
  | node₁ _ ih => rcases ih with h | h
                  · exact .inl (.gate₁ h)
                  · exact .inr (by simp [Exp.erase, h])
  | node₂ _ ih => rcases ih with h | h
                  · exact .inl (.gate₂ h)
                  · exact .inr (by simp [Exp.erase, h])
  | node₃ => exact .inr rfl
  | cons₁ _ ih => rcases ih with h | h
                  · exact .inl (.cons₁ h)
                  · exact .inr (by simp [Exp.erase, h])
  | cons₂ _ ih => rcases ih with h | h
                  · exact .inl (.cons₂ h)
                  · exact .inr (by simp [Exp.erase, h])

/-- Theorem 11.1: definitional equality is preserved by erasure. -/
theorem Conv.erase (S : Sig) {t t' : Exp} (h : Conv t t') : KConv (t.erase S) (t'.erase S) := by
  induction h with
  | rel _ _ h =>
    rcases h.erase S with h | h
    · exact .rel _ _ h
    · rw [h]; exact .refl _
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- The judgments of the target calculus. -/
inductive KJudg
  | ty (Γ : KTel) (A : KExp)
  | tm (Γ : KTel) (t A : KExp)
  | spine (Γ : KTel) (ts : KExp) (Δ : KTel)

/-- Typing in the target calculus `K_S`: the role-free dependent calculus with a
unit type over the erased families, primitives, certificate payloads and gate
constructors of `S`. -/
inductive KDeriv (S : Sig) : KJudg → Prop
  | tyFam {Γ a args Δ ρ} : S.family? a = some (Δ, ρ) →
      KDeriv S (.spine Γ args (eraseTel S Δ)) → KDeriv S (.ty Γ (.fam a args))
  | tyUnit {Γ} : KDeriv S (.ty Γ .unit)
  | tyPi {Γ A B} : KDeriv S (.ty Γ A) → KDeriv S (.ty (A :: Γ) B) → KDeriv S (.ty Γ (.pi A B))
  | tySigma {Γ A B} : KDeriv S (.ty Γ A) → KDeriv S (.ty (A :: Γ) B) →
      KDeriv S (.ty Γ (.sigma A B))
  | var {Γ i A C} : Γ[i]? = some A → C = A.ren (· + (i + 1)) → KDeriv S (.ty Γ C) →
      KDeriv S (.tm Γ (.var i) C)
  | const {Γ i k ρ A} : S.const? i k = some (ρ, A) → S.evidence i k = false →
      KDeriv S (.ty Γ (A.erase S)) → KDeriv S (.tm Γ (.const i k) (A.erase S))
  | tt {Γ} : KDeriv S (.tm Γ .tt .unit)
  | lam {Γ A B t} : KDeriv S (.ty Γ A) → KDeriv S (.tm (A :: Γ) t B) →
      KDeriv S (.ty Γ (.pi A B)) → KDeriv S (.tm Γ (.lam A t) (.pi A B))
  | app {Γ A B f u C} : KDeriv S (.tm Γ f (.pi A B)) → KDeriv S (.tm Γ u A) → C = B.inst u →
      KDeriv S (.ty Γ C) → KDeriv S (.tm Γ (.app f u) C)
  | pair {Γ A B t u} : KDeriv S (.tm Γ t A) → KDeriv S (.tm Γ u (B.inst t)) →
      KDeriv S (.ty Γ (.sigma A B)) → KDeriv S (.tm Γ (.pair t u) (.sigma A B))
  | fst {Γ A B p} : KDeriv S (.tm Γ p (.sigma A B)) → KDeriv S (.ty Γ A) →
      KDeriv S (.tm Γ (.fst p) A)
  | snd {Γ A B C p} : KDeriv S (.tm Γ p (.sigma A B)) → C = B.inst (.fst p) →
      KDeriv S (.ty Γ C) → KDeriv S (.tm Γ (.snd p) C)
  | gate {Γ g ds t Δ σ A ρ B C} : S.gate? g = some (Δ, σ, A, ρ, B) →
      KDeriv S (.spine Γ ds (eraseTel S Δ)) →
      KDeriv S (.tm Γ t (kinstType ds (eraseTel S Δ) (A.erase S))) →
      C = kinstType ds (eraseTel S Δ) (B.erase S) → KDeriv S (.ty Γ C) →
      KDeriv S (.tm Γ (.gate g ds t) C)
  | conv {Γ t A B} : KDeriv S (.tm Γ t A) → KConv A B → KDeriv S (.ty Γ B) →
      KDeriv S (.tm Γ t B)
  | spineNil {Γ} : KDeriv S (.spine Γ .nil [])
  | spineCons {Γ t ts A Δ} : KDeriv S (.tm Γ t A) →
      KDeriv S (.spine Γ ts (KTel.subst (KExp.inst1 t) Δ)) →
      KDeriv S (.spine Γ (.cons t ts) (A :: Δ))

theorem Sig.evidence_type {S : Sig} {i k : ℕ} {ρ : Role} {A : Exp} (he : S.evidence i k = true)
    (h : S.const? i k = some (ρ, A)) : A.erase S = .unit := by
  unfold Sig.evidence at he
  unfold Sig.const? at h
  split at he
  · next σ A' hS => rw [hS] at h; obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · next σ A' hS => rw [hS] at h; obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · next A' t hS => rw [hS] at h; obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · next A' t hS => rw [hS] at h; obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · cases he

theorem eraseTel_getElem? {S : Sig} {Γ : Ctx} {i : ℕ} {ρ : Role} {A : Exp}
    (h : Γ[i]? = some (ρ, A)) : (eraseTel S Γ)[i]? = some (A.erase S) := by
  simp [eraseTel, h]

/-- **Theorem 11.1** (erasure simulation), typing: erasure maps every derivation
of the calculus to a derivation of the role-free target calculus. -/
theorem Deriv.erase {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    match j with
    | .ty Γ _ A _ => KDeriv S (.ty (eraseTel S Γ) (A.erase S))
    | .tm Γ _ t A _ => KDeriv S (.tm (eraseTel S Γ) (t.erase S) (A.erase S))
    | .spine Γ ts Δ _ => KDeriv S (.spine (eraseTel S Γ) (ts.erase S) (eraseTel S Δ))
    | .tel _ _ _ => True := by
  induction d with
  | tyFam hS' _ _ _ ih => exact .tyFam hS' ih
  | tyEvent => exact .tyUnit
  | tyOrigin => exact .tyUnit
  | tyStamped _ _ _ _ ih => exact ih
  | tyPi _ _ _ _ _ ihA ihB => exact .tyPi ihA ihB
  | tySigma _ _ _ _ ihA ihB => exact .tySigma ihA ihB
  | var hΓ hC _ _ _ ihC =>
    subst hC
    exact .var (eraseTel_getElem? hΓ) (Exp.erase_ren _ _ _) ihC
  | @const Γ i k ρ A γ ε hc _ _ _ ihA =>
    change KDeriv S (.tm (eraseTel S Γ) (if S.evidence i k then .tt else .const i k) (A.erase S))
    cases he : S.evidence i k with
    | true => simp only [ite_true, Sig.evidence_type he hc]; exact .tt
    | false => simp only [Bool.false_eq_true, ite_false]; exact .const hc he ihA
  | lam _ _ _ _ _ _ ihA iht ihC => exact .lam ihA iht ihC
  | app _ _ hC _ _ _ ihf ihu ihC =>
    subst hC
    exact .app ihf ihu (Exp.erase_inst _ _ _) ihC
  | @pair Γ ρ A B t u θ η γ ε _ _ _ _ _ iht ihu ihC =>
    refine .pair iht ?_ ihC
    rw [← Exp.erase_inst]; exact ihu
  | fst _ _ _ ihp ihA => exact .fst ihp ihA
  | @snd Γ ρ A B C p π γ _ hC _ _ ihp ihC =>
    subst hC
    refine .snd ihp ?_ ihC
    rw [Exp.erase_inst]; rfl
  | stamp _ _ _ _ _ _ iht _ _ _ => exact iht
  | @gate Γ g ds s Δ σ A ρ B C δ η γ ε hg dds _ hC _ _ _ ihds ihst ihC =>
    subst hC
    have hl := dds.isList
    refine .gate hg ihds ?_ (erase_instType S hl B) ihC
    rw [← erase_instType S hl A]; exact ihst
  | @node Γ g ℓ ds t e Δ σ A ρ B C δ θ η γ ε hg dds _ _ hC _ _ _ ihds iht _ ihC =>
    subst hC
    have hl := dds.isList
    refine .gate hg ihds ?_ (erase_instType S hl B) ihC
    rw [← erase_instType S hl A]; exact iht
  | conv _ hAB _ iht ihB => exact .conv iht (hAB.erase S) ihB
  | spineNil => exact .spineNil
  | @spineCons Γ ρ t ts A Δ ε₁ ε₂ ε _ _ _ iht ihts =>
    refine .spineCons iht ?_
    have := ihts
    simp only [Tel.inst, eraseTel_subst, Exp.erase_inst1] at this
    exact this
  | telNil => trivial
  | telCons => trivial

/-! ## Proposition 11.2: provenance stability -/

/-- **Proposition 11.2** (provenance stability). Convertible closed typed terms
have one provenance normal form `pnf = nf`, and hence one support
`events(nf)`: they reach a common normal form, and any two normal forms of them
are equal. -/
theorem provenance_stable {S : Sig} {acc : Bool} {ρ ρ' : Role} {t u A A' : Exp} {ε ε' : Eff}
    (dt : Deriv S acc (.tm [] ρ t A ε)) (_du : Deriv S acc (.tm [] ρ' u A' ε'))
    (h : Conv t u) :
    (∃ n, Steps t n ∧ Steps u n ∧ Normal n) ∧
    ∀ n₁ n₂, Steps t n₁ → Normal n₁ → Steps u n₂ → Normal n₂ → n₁ = n₂ ∧ n₁.events = n₂.events := by
  have huniq : ∀ n₁ n₂, Steps t n₁ → Normal n₁ → Steps u n₂ → Normal n₂ → n₁ = n₂ := by
    intro n₁ n₂ h₁ hn₁ h₂ hn₂
    exact Normal.eq_of_conv hn₁ hn₂ (((Conv.of_steps h₁).symm.trans h).trans (Conv.of_steps h₂))
  obtain ⟨n, hs, hn⟩ := dt.sn_tm.exists_normal
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  obtain ⟨x, h₃, h₄⟩ := Steps.confluent hs h₁
  have hx : n = x := hn.eq_of_steps h₃
  subst hx
  refine ⟨⟨n, hs, h₂.trans h₄, hn⟩, fun n₁ n₂ h₁ hn₁ h₂ hn₂ => ?_⟩
  obtain rfl := huniq n₁ n₂ h₁ hn₁ h₂ hn₂
  exact ⟨rfl, rfl⟩

/-- Proposition 11.2, last part: erasure forgets provenance. Two nodes that differ
only in their event fields, or terms that differ only in role or grade
annotations, have the same erasure. -/
theorem erase_forgets_events (S : Sig) (g ℓ ℓ' : ℕ) (ds t e e' : Exp) :
    (Exp.node g ℓ ds t e).erase S = (Exp.node g ℓ' ds t e').erase S := rfl

end Artform.Roles.Calculus
