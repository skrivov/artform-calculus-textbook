import ArtformRoles.Calculus.SN
import ArtformRoles.Calculus.Canonical

/-!
# Normalization and decidable conversion

The conversion part of the decidability theorem (`thm:decidability`) and step
(6) of the reference procedure of Appendix C (`app:checker`).

* `Exp.step?` contracts one redex: the head redex if there is one, otherwise a
  redex in the leftmost child that has one. It is sound (`Exp.step?_sound`) and
  returns `none` exactly on normal forms (`Exp.step?_none`).
* `Exp.nfFuel n` iterates it at most `n` times. On a strongly normalizing
  expression some fuel suffices (`Exp.nfFuel_terminates`), so `Exp.nf` is a
  computable normal form, found by unbounded search whose termination is
  strong normalization.
* `conv_iff_nf_eq`: two strongly normalizing expressions are convertible
  exactly when their normal forms are equal; `decConv` decides it.
* `Deriv.decConvTy`, `Deriv.decConvTm`: conversion of well-formed types and of
  well-typed terms is decidable, by strong normalization (`Deriv.sn_ty`,
  `Deriv.sn_tm`) and confluence.
-/

namespace Artform.Roles.Calculus

namespace Exp

/-- One reduction step: the head redex if there is one, otherwise a step in the
leftmost child that has one. -/
def step? : Exp → Option Exp
  | var _ => none
  | const _ _ => none
  | fam a args => (step? args).map (fam a)
  | event => none
  | origin A e t =>
    match step? A, step? e, step? t with
    | some A', _, _ => some (origin A' e t)
    | none, some e', _ => some (origin A e' t)
    | none, none, some t' => some (origin A e t')
    | none, none, none => none
  | stamped σ A => (step? A).map (stamped σ)
  | pi q σ A B =>
    match step? A, step? B with
    | some A', _ => some (pi q σ A' B)
    | none, some B' => some (pi q σ A B')
    | none, none => none
  | sigma ρ A B =>
    match step? A, step? B with
    | some A', _ => some (sigma ρ A' B)
    | none, some B' => some (sigma ρ A B')
    | none, none => none
  | lam q σ A t =>
    match step? A, step? t with
    | some A', _ => some (lam q σ A' t)
    | none, some t' => some (lam q σ A t')
    | none, none => none
  | app f u =>
    match f, step? f, step? u with
    | lam _ _ _ t, _, _ => some (t.inst u)
    | _, some f', _ => some (app f' u)
    | _, none, some u' => some (app f u')
    | _, none, none => none
  | pair t u =>
    match step? t, step? u with
    | some t', _ => some (pair t' u)
    | none, some u' => some (pair t u')
    | none, none => none
  | fst p =>
    match p, step? p with
    | pair t _, _ => some t
    | _, some p' => some (fst p')
    | _, none => none
  | snd p =>
    match p, step? p with
    | pair _ u, _ => some u
    | _, some p' => some (snd p')
    | _, none => none
  | stamp t e o =>
    match step? t, step? e, step? o with
    | some t', _, _ => some (stamp t' e o)
    | none, some e', _ => some (stamp t e' o)
    | none, none, some o' => some (stamp t e o')
    | none, none, none => none
  | gate g ds s =>
    match s, step? ds, step? s with
    | stamp t e _, _, _ => some (node g 0 ds t e)
    | _, some ds', _ => some (gate g ds' s)
    | _, none, some s' => some (gate g ds s')
    | _, none, none => none
  | node g ℓ ds t e =>
    match step? ds, step? t, step? e with
    | some ds', _, _ => some (node g ℓ ds' t e)
    | none, some t', _ => some (node g ℓ ds t' e)
    | none, none, some e' => some (node g ℓ ds t e')
    | none, none, none => none
  | nil => none
  | cons t ts =>
    match step? t, step? ts with
    | some t', _ => some (cons t' ts)
    | none, some ts' => some (cons t ts')
    | none, none => none

/-- `step?` contracts a redex. -/
theorem step?_sound : ∀ (t : Exp) {t' : Exp}, step? t = some t' → Step t t' := by
  intro t
  induction t with
  | var | const | event | nil => intro t' h; simp [step?] at h
  | fam a args ih =>
    intro t' h
    simp only [step?, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    exact .fam (ih ha)
  | stamped σ A ih =>
    intro t' h
    simp only [step?, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    exact .stamped (ih ha)
  | origin A e t ihA ihe iht =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .origin₁ (ihA (by assumption))
    · exact .origin₂ (ihe (by assumption))
    · exact .origin₃ (iht (by assumption))
  | pi q σ A B ihA ihB =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .pi₁ (ihA (by assumption))
    · exact .pi₂ (ihB (by assumption))
  | sigma ρ A B ihA ihB =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .sigma₁ (ihA (by assumption))
    · exact .sigma₂ (ihB (by assumption))
  | lam q σ A t ihA iht =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .lam₁ (ihA (by assumption))
    · exact .lam₂ (iht (by assumption))
  | app f u ihf ihu =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .beta
    · exact .app₁ (ihf (by assumption))
    · exact .app₂ (ihu (by assumption))
  | pair t u iht ihu =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .pair₁ (iht (by assumption))
    · exact .pair₂ (ihu (by assumption))
  | fst p ih =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .fstPair
    · exact .fst (ih (by assumption))
  | snd p ih =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .sndPair
    · exact .snd (ih (by assumption))
  | stamp t e o iht ihe iho =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .stamp₁ (iht (by assumption))
    · exact .stamp₂ (ihe (by assumption))
    · exact .stamp₃ (iho (by assumption))
  | gate g ds s ihds ihs =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .record
    · exact .gate₁ (ihds (by assumption))
    · exact .gate₂ (ihs (by assumption))
  | node g ℓ ds t e ihds iht ihe =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .node₁ (ihds (by assumption))
    · exact .node₂ (iht (by assumption))
    · exact .node₃ (ihe (by assumption))
  | cons t ts iht ihts =>
    intro t' h
    simp only [step?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact .cons₁ (iht (by assumption))
    · exact .cons₂ (ihts (by assumption))

/-- `step?` finds a redex whenever there is one. -/
theorem step?_none {t : Exp} (h : step? t = none) : Normal t := by
  intro t' hs
  induction hs with
  | beta | fstPair | sndPair | record => simp [step?] at h
  | fam _ ih | stamped _ ih =>
    simp only [step?, Option.map_eq_none_iff] at h
    exact ih h
  | origin₁ _ ih | origin₂ _ ih | origin₃ _ ih | pi₁ _ ih | pi₂ _ ih | sigma₁ _ ih
  | sigma₂ _ ih | lam₁ _ ih | lam₂ _ ih | pair₁ _ ih | pair₂ _ ih | stamp₁ _ ih
  | stamp₂ _ ih | stamp₃ _ ih | node₁ _ ih | node₂ _ ih | node₃ _ ih | cons₁ _ ih
  | cons₂ _ ih =>
    simp only [step?] at h
    split at h <;> first | (apply ih; assumption) | simp at h
  | app₁ _ ih | app₂ _ ih | fst _ ih | snd _ ih | gate₁ _ ih | gate₂ _ ih =>
    simp only [step?] at h
    split at h <;> first | (apply ih; assumption) | simp at h

/-- `step?` returns `none` exactly on normal forms. -/
theorem step?_eq_none_iff {t : Exp} : step? t = none ↔ Normal t := by
  refine ⟨step?_none, fun hn => ?_⟩
  cases h : step? t with
  | none => rfl
  | some t' => exact absurd (step?_sound t h) (hn t')

/-- At most `n` steps of `step?`, stopping at a normal form. -/
def nfFuel : ℕ → Exp → Option Exp
  | 0, _ => none
  | n + 1, t =>
    match step? t with
    | none => some t
    | some t' => nfFuel n t'

/-- What `nfFuel` returns is a normal form of its argument. -/
theorem nfFuel_spec : ∀ (n : ℕ) {t w : Exp}, nfFuel n t = some w → Steps t w ∧ Normal w := by
  intro n
  induction n with
  | zero => intro t w h; simp [nfFuel] at h
  | succ n ih =>
    intro t w h
    simp only [nfFuel] at h
    split at h
    · cases h
      exact ⟨.refl, step?_none (by assumption)⟩
    · obtain ⟨h₁, h₂⟩ := ih h
      exact ⟨Relation.ReflTransGen.head (step?_sound t (by assumption)) h₁, h₂⟩

/-- On a strongly normalizing expression the iteration terminates. -/
theorem nfFuel_terminates {t : Exp} (h : SN t) : ∃ n, (nfFuel n t).isSome := by
  induction h with
  | intro t _ ih =>
    cases hs : step? t with
    | none => exact ⟨1, by simp [nfFuel, hs]⟩
    | some t' =>
      obtain ⟨n, hn⟩ := ih t' (step?_sound t hs)
      exact ⟨n + 1, by simpa [nfFuel, hs] using hn⟩

/-- The normal form of a strongly normalizing expression, by unbounded search
for enough fuel. -/
def nf (t : Exp) (h : SN t) : Exp :=
  (nfFuel (Nat.find (nfFuel_terminates h)) t).get (Nat.find_spec (nfFuel_terminates h))

theorem nf_spec {t : Exp} (h : SN t) : Steps t (nf t h) ∧ Normal (nf t h) :=
  nfFuel_spec _ (Option.some_get _).symm

end Exp

/-- Two strongly normalizing expressions are convertible exactly when their
normal forms are equal. -/
theorem conv_iff_nf_eq {t u : Exp} (ht : SN t) (hu : SN u) : Conv t u ↔ t.nf ht = u.nf hu := by
  obtain ⟨st, nt⟩ := Exp.nf_spec ht
  obtain ⟨su, nu⟩ := Exp.nf_spec hu
  constructor
  · intro h
    exact Normal.eq_of_conv nt nu (((Conv.of_steps st).symm.trans h).trans (Conv.of_steps su))
  · intro h
    exact (Conv.of_steps st).trans (h ▸ (Conv.of_steps su).symm)

/-- Conversion of strongly normalizing expressions is decidable. -/
def decConv {t u : Exp} (ht : SN t) (hu : SN u) : Decidable (Conv t u) :=
  decidable_of_iff _ (conv_iff_nf_eq ht hu).symm

/-- `thm:decidability`, conversion of types: whether two well-formed types are
definitionally equal is decidable. -/
def Deriv.decConvTy {S S' : Sig} {acc acc' : Bool} {Γ Γ' : Ctx} {ρ ρ' : Role} {A B : Exp}
    {α β : Eff} (dA : Deriv S acc (.ty Γ ρ A α)) (dB : Deriv S' acc' (.ty Γ' ρ' B β)) :
    Decidable (Conv A B) :=
  decConv dA.sn_ty dB.sn_ty

/-- `thm:decidability`, conversion of terms: whether two well-typed terms are
definitionally equal is decidable. -/
def Deriv.decConvTm {S S' : Sig} {acc acc' : Bool} {Γ Γ' : Ctx} {ρ ρ' : Role} {t u A B : Exp}
    {ε η : Eff} (dt : Deriv S acc (.tm Γ ρ t A ε)) (du : Deriv S' acc' (.tm Γ' ρ' u B η)) :
    Decidable (Conv t u) :=
  decConv dt.sn_tm du.sn_tm

end Artform.Roles.Calculus
