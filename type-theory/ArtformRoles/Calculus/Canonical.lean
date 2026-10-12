import ArtformRoles.Calculus.SN

/-!
# Normal forms and canonical forms

Theorem 8.14 (canonical forms) and Corollary 8.15 (canonical credentials) of
the paper.

* `Ne`, `Nf`: the neutral and normal grammar
  `h ::= x | c | node_g(n⃗; n, e) | gate_g(n⃗; r)`,
  `r ::= h | r n | fst(r) | snd(r)`,
  `n ::= r | λ^q(x :_σ A). n | (n, n) | stamp(n, e, o)`;
  every well-typed normal term is in it (`Deriv.nf_of_normal`).
* For closed normal terms (`canonical_stamped`, `canonical_event`,
  `canonical_origin`, `canonical_lam`, `canonical_protected_neutral`):
  (i) a term of `Stamped_σ(A)` is a stamp; (ii) a term of `Event` is an event
  constant of a certificate or attestation entry, and a term of `Origin_A(e, t)`
  is an origin constant whose event matches; (iii) a term of `Π^q(x :_σ A). B`
  with `q ∈ {1, ∞}` is a lambda; (iv) a closed neutral at a protected type is
  headed by an ordinary public constant or a private node, never by a public
  gate.
* `canonical_credential`: a closed normal credential is a stamp whose event and
  origin come from one evidence entry; for a certificate its payload is the
  payload constant, for an attestation it is convertible to the attested term.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Normal terms -/

theorem Normal.of_step_lift {f : Exp → Exp} (hf : ∀ {a b}, Step a b → Step (f a) (f b))
    {a : Exp} (h : Normal (f a)) : Normal a := fun _ hs => h _ (hf hs)

theorem Normal.app {t u : Exp} (h : Normal (.app t u)) :
    Normal t ∧ Normal u ∧ ∀ q σ A b, t ≠ .lam q σ A b :=
  ⟨fun _ hs => h _ (.app₁ hs), fun _ hs => h _ (.app₂ hs),
    fun q σ A b he => by subst he; exact h _ .beta⟩

theorem Normal.fst {p : Exp} (h : Normal (.fst p)) : Normal p ∧ ∀ t u, p ≠ .pair t u :=
  ⟨fun _ hs => h _ (.fst hs), fun t u he => by subst he; exact h _ .fstPair⟩

theorem Normal.snd {p : Exp} (h : Normal (.snd p)) : Normal p ∧ ∀ t u, p ≠ .pair t u :=
  ⟨fun _ hs => h _ (.snd hs), fun t u he => by subst he; exact h _ .sndPair⟩

theorem Normal.gate {g : ℕ} {ds s : Exp} (h : Normal (.gate g ds s)) :
    Normal ds ∧ Normal s ∧ ∀ t e o, s ≠ .stamp t e o :=
  ⟨fun _ hs => h _ (.gate₁ hs), fun _ hs => h _ (.gate₂ hs),
    fun t e o he => by subst he; exact h _ .record⟩

theorem Normal.stamp {t e o : Exp} (h : Normal (.stamp t e o)) :
    Normal t ∧ Normal e ∧ Normal o :=
  ⟨fun _ hs => h _ (.stamp₁ hs), fun _ hs => h _ (.stamp₂ hs), fun _ hs => h _ (.stamp₃ hs)⟩

theorem Normal.lam {q : Grade} {σ : Role} {A b : Exp} (h : Normal (.lam q σ A b)) :
    Normal A ∧ Normal b :=
  ⟨fun _ hs => h _ (.lam₁ hs), fun _ hs => h _ (.lam₂ hs)⟩

theorem Normal.pair {t u : Exp} (h : Normal (.pair t u)) : Normal t ∧ Normal u :=
  ⟨fun _ hs => h _ (.pair₁ hs), fun _ hs => h _ (.pair₂ hs)⟩

theorem Normal.node {g ℓ : ℕ} {ds t e : Exp} (h : Normal (.node g ℓ ds t e)) :
    Normal ds ∧ Normal t ∧ Normal e :=
  ⟨fun _ hs => h _ (.node₁ hs), fun _ hs => h _ (.node₂ hs), fun _ hs => h _ (.node₃ hs)⟩

theorem Normal.cons {t ts : Exp} (h : Normal (.cons t ts)) : Normal t ∧ Normal ts :=
  ⟨fun _ hs => h _ (.cons₁ hs), fun _ hs => h _ (.cons₂ hs)⟩

/-- Convertible normal expressions are equal. -/
theorem Normal.eq_of_conv {t u : Exp} (ht : Normal t) (hu : Normal u) (h : Conv t u) : t = u := by
  obtain ⟨w, h₁, h₂⟩ := h.joinable
  have e₁ : t = w := by
    rcases Relation.ReflTransGen.cases_head h₁ with h | ⟨_, hs, _⟩
    · exact h
    · exact absurd hs (ht _)
  have e₂ : u = w := by
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨_, hs, _⟩
    · exact h
    · exact absurd hs (hu _)
  rw [e₁, e₂]

/-! ## The normal and neutral grammar -/

mutual
/-- Neutral normal terms (the paper's `r`, with heads `h`). -/
inductive Ne : Exp → Prop
  | var (i : ℕ) : Ne (.var i)
  | const (i k : ℕ) : Ne (.const i k)
  | node {g ℓ ds t e} : NfArgs ds → Nf t → Nf e → Ne (.node g ℓ ds t e)
  | gate {g ds s} : NfArgs ds → Ne s → Ne (.gate g ds s)
  | app {r n} : Ne r → Nf n → Ne (.app r n)
  | fst {r} : Ne r → Ne (.fst r)
  | snd {r} : Ne r → Ne (.snd r)

/-- Normal terms (the paper's `n`): neutral terms and introductions with normal
parts. Lambda annotations are normal expressions. -/
inductive Nf : Exp → Prop
  | ne {r} : Ne r → Nf r
  | lam {q σ A n} : Normal A → Nf n → Nf (.lam q σ A n)
  | pair {n m} : Nf n → Nf m → Nf (.pair n m)
  | stamp {n e o} : Nf n → Nf e → Nf o → Nf (.stamp n e o)

/-- Normal argument lists. -/
inductive NfArgs : Exp → Prop
  | nil : NfArgs .nil
  | cons {n ns} : Nf n → NfArgs ns → NfArgs (.cons n ns)
end

theorem Deriv.not_pair_of_pi {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {q : Grade}
    {A B a b : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.pair a b) (.pi q σ A B) ε)) : False := by
  obtain ⟨_, _, _, _, hc, -⟩ := d.inv_pair
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

theorem Deriv.not_stamp_of_pi {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {q : Grade}
    {A B a e o : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.stamp a e o) (.pi q σ A B) ε)) :
    False := by
  obtain ⟨_, _, _, _, _, -, hc, -⟩ := d.inv_stamp
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

theorem Deriv.not_lam_of_sigma {S : Sig} {acc : Bool} {Γ : Ctx} {ρ ρ' σ : Role} {q : Grade}
    {A B C b : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.lam q σ C b) (.sigma ρ' A B) ε)) :
    False := by
  obtain ⟨_, _, hc, -⟩ := d.inv_lam
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

theorem Deriv.not_stamp_of_sigma {S : Sig} {acc : Bool} {Γ : Ctx} {ρ ρ' : Role}
    {A B a e o : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.stamp a e o) (.sigma ρ' A B) ε)) :
    False := by
  obtain ⟨_, _, _, _, _, -, hc, -⟩ := d.inv_stamp
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

theorem Deriv.not_lam_of_stamped {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ σ' : Role} {q : Grade}
    {A C b : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.lam q σ C b) (.stamped σ' A) ε)) :
    False := by
  obtain ⟨_, _, hc, -⟩ := d.inv_lam
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

theorem Deriv.not_pair_of_stamped {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role}
    {A a b : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ (.pair a b) (.stamped σ A) ε)) : False := by
  obtain ⟨_, _, _, _, hc, -⟩ := d.inv_pair
  exact absurd (Conv.headTag_eq (by trivial) (by trivial) hc) (by simp [Conv.headTag])

/-- Theorem 8.14, first part: every well-typed normal term has one of the normal
forms of the grammar. -/
theorem Deriv.nf_of_normal {S : Sig} {acc : Bool} :
    ∀ (t : Exp),
      (∀ {Γ : Ctx} {ρ : Role} {A : Exp} {ε : Eff}, Deriv S acc (.tm Γ ρ t A ε) → Normal t →
        Nf t ∧ (NotIntro t → Ne t)) ∧
      (∀ {Γ : Ctx} {Δ : Tel} {δ : Eff}, Deriv S acc (.spine Γ t Δ δ) → Normal t → NfArgs t) := by
  intro t
  induction t with
  | var i => exact ⟨fun _ _ => ⟨.ne (.var i), fun _ => .var i⟩, fun d => by cases d⟩
  | const i k => exact ⟨fun _ _ => ⟨.ne (.const i k), fun _ => .const i k⟩, fun d => by cases d⟩
  | lam q σ A b _ ihb =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨B, θ, -, -, -, -, ⟨db⟩, -⟩ := d.inv_lam
    exact ⟨.lam hn.lam.1 (ihb.1 db hn.lam.2).1, fun h => absurd h id⟩
  | app f u ihf ihu =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨q, σ, A, B, φ, η, -, -, ⟨df⟩, ⟨du⟩, -⟩ := d.inv_app
    obtain ⟨hf, hu, hnl⟩ := hn.app
    have hfi : NotIntro f := by
      cases f with
      | lam q' σ' A' b => exact hnl _ _ _ _ rfl
      | pair => exact df.not_pair_of_pi
      | stamp => exact df.not_stamp_of_pi
      | _ => trivial
    have hne := (ihf.1 df hf).2 hfi
    exact ⟨.ne (.app hne (ihu.1 du hu).1), fun _ => .app hne (ihu.1 du hu).1⟩
  | pair a b iha ihb =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨A, B, θ, η, -, -, ⟨da⟩, ⟨db⟩, -⟩ := d.inv_pair
    exact ⟨.pair (iha.1 da hn.pair.1).1 (ihb.1 db hn.pair.2).1, fun h => absurd h id⟩
  | fst p ihp =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨A, B, -, ⟨dp⟩, -⟩ := d.inv_fst
    obtain ⟨hp, hnp⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnp a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    have hne := (ihp.1 dp hp).2 hpi
    exact ⟨.ne (.fst hne), fun _ => .fst hne⟩
  | snd p ihp =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨A, B, -, ⟨dp⟩, -⟩ := d.inv_snd
    obtain ⟨hp, hnp⟩ := hn.snd
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnp a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    have hne := (ihp.1 dp hp).2 hpi
    exact ⟨.ne (.snd hne), fun _ => .snd hne⟩
  | stamp a e o iha ihe iho =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨σ, A, θ, η, ω, -, -, -, ⟨da⟩, ⟨de⟩, ⟨dorg⟩, -⟩ := d.inv_stamp
    obtain ⟨h₁, h₂, h₃⟩ := hn.stamp
    exact ⟨.stamp (iha.1 da h₁).1 (ihe.1 de h₂).1 (iho.1 dorg h₃).1, fun h => absurd h id⟩
  | gate g ds s ihds ihs =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨Δ, σ, A, B, δ, η, -, -, -, ⟨dds⟩, ⟨dst⟩, -⟩ := d.inv_gate
    obtain ⟨h₁, h₂, hns⟩ := hn.gate
    have hsi : NotIntro s := by
      cases s with
      | lam => exact dst.not_lam_of_stamped
      | pair => exact dst.not_pair_of_stamped
      | stamp a e o => exact hns a e o rfl
      | _ => trivial
    have hne := (ihs.1 dst h₂).2 hsi
    exact ⟨.ne (.gate (ihds.2 dds h₁) hne), fun _ => .gate (ihds.2 dds h₁) hne⟩
  | node g ℓ ds a e ihds iha ihe =>
    refine ⟨fun d hn => ?_, fun d => by cases d⟩
    obtain ⟨Δ, σ, A, B, δ, θ, η, -, -, -, ⟨dds⟩, ⟨da⟩, ⟨de⟩, -⟩ := d.inv_node
    obtain ⟨h₁, h₂, h₃⟩ := hn.node
    have hne : Ne (.node g ℓ ds a e) := .node (ihds.2 dds h₁) (iha.1 da h₂).1 (ihe.1 de h₃).1
    exact ⟨.ne hne, fun _ => hne⟩
  | nil => exact ⟨fun d => d.isTermHead.elim, fun _ _ => .nil⟩
  | cons a b iha ihb =>
    refine ⟨fun d => d.isTermHead.elim, fun d hn => ?_⟩
    cases d with
    | spineCons da db => exact .cons (iha.1 da hn.cons.1).1 (ihb.2 db hn.cons.2)
  | fam | event | origin | stamped | pi | sigma =>
    exact ⟨fun d => d.isTermHead.elim, fun d => by cases d⟩

/-! ## Constants and gates of a well-formed signature -/

theorem OrdinaryHead.append {S M : Sig} {A : Exp} (h : OrdinaryHead S A) :
    OrdinaryHead (S ++ M) A := by
  obtain ⟨a, args, h₁, h₂⟩ := h
  refine ⟨a, args, h₁, ?_⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h₂
  rw [Sig.family?_append hp]; rfl

/-- The constants of a well-formed signature: ordinary constants (primitives and
certificate payloads) with grade-free, family-headed types, event constants and
origin constants. -/
theorem SigWF.const_cases {S : Sig} (hS : SigWF S) {i k : ℕ} {ρ : Role} {T : Exp}
    (h : S.const? i k = some (ρ, T)) :
    (T.gradefree ∧ OrdinaryHead S T) ∨
    (ρ = .witness ∧ T = .event ∧ ((∃ σ A, S[i]? = some (.cert σ A) ∧ k = 1) ∨
      (∃ A t, S[i]? = some (.attest A t) ∧ k = 0))) ∨
    (ρ = .witness ∧ ((∃ σ A, S[i]? = some (.cert σ A) ∧ k = 2 ∧
        T = .origin A (.const i 1) (.const i 0)) ∨
      (∃ A t, S[i]? = some (.attest A t) ∧ k = 1 ∧ T = .origin A (.const i 0) t))) := by
  induction hS with
  | nil => simp [Sig.const?] at h
  | @family S' Δ ρ' δ _ _ ih | @gate S' Δ σ' A' ρ' B' δ α β _ _ _ _ _ _ _ _ _ _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨_, h'⟩
    · have hi := Sig.lt_of_const h'
      rcases ih h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨h₁, h₂.append⟩
      · refine .inr (.inl ⟨h₁, h₂, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₃
      · refine .inr (.inr ⟨h₁, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₂
    · rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ <;> cases he
  | @prim S' ρ' A' α _ _ hg ho ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · have hi := Sig.lt_of_const h'
      rcases ih h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨h₁, h₂.append⟩
      · refine .inr (.inl ⟨h₁, h₂, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₃
      · refine .inr (.inr ⟨h₁, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₂
    · rcases h' with ⟨_, _, he, -, hp⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩
      · cases he; cases hp; exact .inl ⟨hg, ho.append⟩
      · cases he
      · cases he
  | @cert S' σ' A' α _ _ _ hg ho ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · have hi := Sig.lt_of_const h'
      rcases ih h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨h₁, h₂.append⟩
      · refine .inr (.inl ⟨h₁, h₂, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₃
      · refine .inr (.inr ⟨h₁, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₂
    · subst hi
      rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩ | ⟨_, _, he, _⟩
      · cases he
      · cases he
        rcases hk with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> cases hp
        · exact .inl ⟨hg, ho.append⟩
        · exact .inr (.inl ⟨rfl, rfl, .inl ⟨σ', A', by simp, rfl⟩⟩)
        · exact .inr (.inr ⟨rfl, .inl ⟨σ', A', by simp, rfl, rfl⟩⟩)
      · cases he
  | @attest S' A' t' θ _ _ _ _ _ ih =>
    rcases Sig.const?_snoc h with h' | ⟨hi, h'⟩
    · have hi := Sig.lt_of_const h'
      rcases ih h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨h₁, h₂.append⟩
      · refine .inr (.inl ⟨h₁, h₂, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₃
      · refine .inr (.inr ⟨h₁, ?_⟩)
        simpa [List.getElem?_append_left hi] using h₂
    · subst hi
      rcases h' with ⟨_, _, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, _, he, hk⟩
      · cases he
      · cases he
      · cases he
        rcases hk with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> cases hp
        · exact .inr (.inl ⟨rfl, rfl, .inr ⟨A', t', by simp, rfl⟩⟩)
        · exact .inr (.inr ⟨rfl, .inr ⟨A', t', by simp, rfl, rfl⟩⟩)

/-- The payload and result types of a declared gate are formed under its
telescope. -/
theorem SigWF.gate_formed {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : S.gate? g = some (Δ, σ, A, ρ, B)) :
    (∃ α, Derivable S true (.ty Δ.reverse σ A α)) ∧
      (∃ β, Derivable S true (.ty Δ.reverse ρ B β)) := by
  induction hS with
  | nil => simp [Sig.gate?] at h
  | @gate S' Δ' σ' A' ρ' B' δ' α' β' _ _ hA' hB' _ _ _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, hp⟩
    · obtain ⟨⟨α, ha⟩, ⟨β, hb⟩⟩ := ih h
      exact ⟨⟨α, ha.weakenSig _⟩, ⟨β, hb.weakenSig _⟩⟩
    · cases he; cases hp
      exact ⟨⟨α', hA'.weakenSig _⟩, ⟨β', hB'.weakenSig _⟩⟩
  | family _ _ ih | prim _ _ _ _ ih | cert _ _ _ _ _ ih | attest _ _ _ _ _ ih =>
    rcases Sig.gate?_snoc h with h | ⟨_, _, _, _, _, _, he, _⟩
    · obtain ⟨⟨α, ha⟩, ⟨β, hb⟩⟩ := ih h
      exact ⟨⟨α, ha.weakenSig _⟩, ⟨β, hb.weakenSig _⟩⟩
    · cases he

/-! ## Descendants of skeletons -/

/-- `Desc τ ω`: `ω` is reached from `τ` through codomains and the components of
products, as the type of a spine is reached from the type of its head. -/
inductive GSkel.Desc : GSkel → GSkel → Prop
  | refl (τ : GSkel) : Desc τ τ
  | arr {q σ τ υ ω} : Desc υ ω → Desc (.arr q σ τ υ) ω
  | fst {ρ τ υ ω} : Desc τ ω → Desc (.prod ρ τ υ) ω
  | snd {ρ τ υ ω} : Desc υ ω → Desc (.prod ρ τ υ) ω

theorem GSkel.Desc.trans {τ υ ω : GSkel} (h₁ : Desc τ υ) (h₂ : Desc υ ω) : Desc τ ω := by
  induction h₁ with
  | refl => exact h₂
  | arr _ ih => exact .arr (ih h₂)
  | fst _ ih => exact .fst (ih h₂)
  | snd _ ih => exact .snd (ih h₂)

theorem GSkel.Desc.of_base {a : ℕ} {ω : GSkel} (h : Desc (.base a) ω) : ω = .base a := by
  cases h; rfl

theorem GSkel.Desc.of_ev {ω : GSkel} (h : Desc .ev ω) : ω = .ev := by
  cases h; rfl

theorem GSkel.Desc.of_org {ω : GSkel} (h : Desc .org ω) : ω = .org := by
  cases h; rfl

/-- The skeletons reached from the type of an ordinary constant: families and
grade-free functions. -/
def GSkel.Ord : GSkel → Prop
  | .base _ => True
  | .arr q _ _ _ => q = .free
  | _ => False

/-- The skeletons reached from a protected grade-free type. -/
def GSkel.Prot : GSkel → Prop
  | .base _ => True
  | .arr q _ _ _ => q = .free
  | .prod _ _ _ => True
  | _ => False

theorem ordinary_desc {S : Sig} {T : Exp} (hg : T.gradefree) (ho : OrdinaryHead S T)
    {ω : GSkel} (h : GSkel.Desc (gskel T) ω) : ω.Ord := by
  induction T with
  | fam a args => rw [GSkel.Desc.of_base h]; trivial
  | pi q σ A B _ ihB =>
    obtain ⟨hq, -, hB⟩ := hg
    have ho' : OrdinaryHead S B := ho
    cases h with
    | refl => exact hq
    | arr h' => exact ihB hB ho' h'
  | _ =>
    obtain ⟨a, args, he, -⟩ := ho
    cases he

theorem protected_desc {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {B : Exp} {β : Eff}
    (d : Deriv S acc (.ty Γ ρ B β)) (hρ : ρ = .form ∨ ρ = .presentation) (hg : B.gradefree)
    {ω : GSkel} (h : GSkel.Desc (gskel B) ω) : ω.Prot := by
  induction B generalizing Γ β with
  | fam a args => rw [GSkel.Desc.of_base h]; trivial
  | event => cases d; rcases hρ with h | h <;> cases h
  | origin => cases d; rcases hρ with h | h <;> cases h
  | stamped => cases d; rcases hρ with h | h <;> cases h
  | pi q σ A B' _ ihB =>
    obtain ⟨hq, -, hB⟩ := hg
    cases d with
    | tyPi _ dB =>
      cases h with
      | refl => exact hq
      | arr h' => exact ihB dB hB h'
  | sigma ρ' A' B' ihA ihB =>
    obtain ⟨hA, hB⟩ := hg
    cases d with
    | tySigma dA dB =>
      cases h with
      | refl => trivial
      | fst h' => exact ihA dA hA h'
      | snd h' => exact ihB dB hB h'
  | _ => cases d

/-! ## Closed neutral terms -/

/-- The head of a spine of applications and projections. -/
def Exp.head : Exp → Exp
  | .app f _ => head f
  | .fst p => head p
  | .snd p => head p
  | t => t

theorem Normal.head {t : Exp} (h : Normal t) : Normal t.head := by
  induction t with
  | app f u ihf _ => exact ihf h.app.1
  | fst p ihp => exact ihp h.fst.1
  | snd p ihp => exact ihp h.snd.1
  | _ => exact h

theorem not_notIntro_lam {q : Grade} {σ : Role} {A b : Exp} : ¬NotIntro (.lam q σ A b) := id

/-- A closed normal neutral term is a spine whose head is a constant or a gate or
node, and its type is reached from the head's type through codomains and
projections. -/
theorem closed_neutral {S : Sig} (hS : SigWF S) {acc : Bool} :
    ∀ (t : Exp) {ρ : Role} {C : Exp} {ε : Eff}, Deriv S acc (.tm [] ρ t C ε) → Normal t →
      NotIntro t →
      (∃ i k T, t.head = .const i k ∧ S.const? i k = some (ρ, T) ∧
        GSkel.Desc (gskel T) (gskel C) ∧
        (t ≠ t.head → T ≠ .event ∧ ∀ A e u, T ≠ .origin A e u)) ∨
      (∃ g Δ σ A B, S.gate? g = some (Δ, σ, A, ρ, B) ∧ GSkel.Desc (gskel B) (gskel C) ∧
        ((∃ ℓ ds a e, t.head = .node g ℓ ds a e) ∨
          (∃ ds s, t.head = .gate g ds s ∧
            ∃ X η, Derivable S acc (.tm [] .witness s (.stamped σ X) η)))) := by
  intro t
  induction t with
  | var i =>
    intro ρ C ε d _ _
    obtain ⟨_, h, -⟩ := d.inv_var
    simp at h
  | const i k =>
    intro ρ C ε d _ _
    obtain ⟨A₀, hc, hconv, -, hf⟩ := d.inv_const
    obtain ⟨γ, hC⟩ := d.tm_ty
    refine .inl ⟨i, k, A₀, rfl, hc, ?_, fun h => absurd rfl h⟩
    rw [gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)]
    exact .refl _
  | app f u ihf _ =>
    intro ρ C ε d hn _
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
    have hB := dpi.tyShape_ty.2
    have hCB : gskel C = gskel B := by
      rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC), (gskel_subst hB _).1]
    rw [hCB]
    rcases ihf df hnf hfi with ⟨i, k, T, hh, hc, hdesc, -⟩ | ⟨g, Δ, σg, Ag, Bg, hg, hdesc, hhead⟩
    · refine .inl ⟨i, k, T, hh, hc, hdesc.trans (.arr (.refl _)), fun _ => ⟨?_, ?_⟩⟩
      · rintro rfl; cases hdesc.of_ev
      · rintro A e u rfl; cases hdesc.of_org
    · exact .inr ⟨g, Δ, σg, Ag, Bg, hg, hdesc.trans (.arr (.refl _)), hhead⟩
  | fst p ihp =>
    intro ρ C ε d hn _
    obtain ⟨A, B, hconv, ⟨dp⟩, hf⟩ := d.inv_fst
    obtain ⟨hnp, hnpair⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨γ, hC⟩ := d.tm_ty
    have hCA : gskel C = gskel A := (gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)).symm
    rw [hCA]
    rcases ihp dp hnp hpi with ⟨i, k, T, hh, hc, hdesc, -⟩ | ⟨g, Δ, σg, Ag, Bg, hg, hdesc, hhead⟩
    · refine .inl ⟨i, k, T, hh, hc, hdesc.trans (.fst (.refl _)), fun _ => ⟨?_, ?_⟩⟩
      · rintro rfl; cases hdesc.of_ev
      · rintro A e u rfl; cases hdesc.of_org
    · exact .inr ⟨g, Δ, σg, Ag, Bg, hg, hdesc.trans (.fst (.refl _)), hhead⟩
  | snd p ihp =>
    intro ρ C ε d hn _
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
    rcases ihp dp hnp hpi with ⟨i, k, T, hh, hc, hdesc, -⟩ | ⟨g, Δ, σg, Ag, Bg, hg, hdesc, hhead⟩
    · refine .inl ⟨i, k, T, hh, hc, hdesc.trans (.snd (.refl _)), fun _ => ⟨?_, ?_⟩⟩
      · rintro rfl; cases hdesc.of_ev
      · rintro A e u rfl; cases hdesc.of_org
    · exact .inr ⟨g, Δ, σg, Ag, Bg, hg, hdesc.trans (.snd (.refl _)), hhead⟩
  | gate g ds s _ _ =>
    intro ρ C ε d _ _
    obtain ⟨Δ, σ, A, B, δ, η, hg, hconv, -, -, ⟨dst⟩, hf⟩ := d.inv_gate
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
    refine .inr ⟨g, Δ, σ, A, B, hg, ?_, .inr ⟨ds, s, rfl, _, _, ⟨dst⟩⟩⟩
    rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
      (gskel_instType dB.tyShape_ty ds Δ).1]
    exact .refl _
  | node g ℓ ds a e _ _ _ =>
    intro ρ C ε d _ _
    obtain ⟨Δ, σ, A, B, δ, θ, η, hg, hconv, -, -, -, -, hf⟩ := d.inv_node
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
    refine .inr ⟨g, Δ, σ, A, B, hg, ?_, .inl ⟨ℓ, ds, a, e, rfl⟩⟩
    rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
      (gskel_instType dB.tyShape_ty ds Δ).1]
    exact .refl _
  | lam | pair | stamp => intro ρ C ε _ _ hi; exact absurd hi id
  | fam | event | origin | stamped | pi | sigma | nil | cons =>
    intro ρ C ε d; exact d.isTermHead.elim

/-- The skeleton reached from a gate result is protected. -/
theorem gate_desc {S : Sig} (hS : SigWF S) {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (hg : S.gate? g = some (Δ, σ, A, ρ, B)) {ω : GSkel} (h : GSkel.Desc (gskel B) ω) :
    ω.Prot := by
  obtain ⟨-, hρ, -, -, hgf⟩ := hS.gate_cond hg
  obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
  exact protected_desc dB hρ hgf h

/-- The skeleton reached from a constant's type. -/
theorem const_desc {S : Sig} (hS : SigWF S) {i k : ℕ} {ρ : Role} {T : Exp}
    (hc : S.const? i k = some (ρ, T)) {ω : GSkel} (h : GSkel.Desc (gskel T) ω) :
    ω.Ord ∨ (T = .event ∧ ω = .ev) ∨ ((∃ A e u, T = .origin A e u) ∧ ω = .org) := by
  rcases hS.const_cases hc with ⟨hg, ho⟩ | ⟨-, hT, -⟩ | ⟨-, hT⟩
  · exact .inl (ordinary_desc hg ho h)
  · subst hT; exact .inr (.inl ⟨rfl, h.of_ev⟩)
  · refine .inr (.inr ⟨?_, ?_⟩)
    · rcases hT with ⟨_, A, _, _, _, rfl⟩ | ⟨A, t, _, _, rfl⟩ <;> exact ⟨_, _, _, rfl⟩
    · rcases hT with ⟨_, A, _, _, _, rfl⟩ | ⟨A, t, _, _, rfl⟩ <;> exact h.of_org

/-! ## Canonical forms of closed normal terms -/

/-- The head tag of the type of an introduction form. -/
theorem Deriv.intro_tags {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t C : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ t C ε)) (hC : Conv.Rigid C) :
    (∀ q σ A b, t = .lam q σ A b → Conv.headTag C = 4) ∧
      (∀ a b, t = .pair a b → Conv.headTag C = 5) ∧
      (∀ a e o, t = .stamp a e o → Conv.headTag C = 3) := by
  refine ⟨fun q σ A b ht => ?_, fun a b ht => ?_, fun a e o ht => ?_⟩
  · subst ht
    obtain ⟨_, _, hc, -⟩ := d.inv_lam
    exact (Conv.headTag_eq (by trivial) hC hc).symm
  · subst ht
    obtain ⟨_, _, _, _, hc, -⟩ := d.inv_pair
    exact (Conv.headTag_eq (by trivial) hC hc).symm
  · subst ht
    obtain ⟨_, _, _, _, _, -, hc, -⟩ := d.inv_stamp
    exact (Conv.headTag_eq (by trivial) hC hc).symm

/-- Theorem 8.14 (i): a closed normal term of a stamped type is a stamp. -/
theorem canonical_stamped {S : Sig} (hS : SigWF S) {acc : Bool} {ρ σ : Role} {t A : Exp}
    {ε : Eff} (d : Deriv S acc (.tm [] ρ t (.stamped σ A) ε)) (hn : Normal t) :
    ∃ u e o, t = .stamp u e o := by
  obtain ⟨hl, hp, -⟩ := d.intro_tags (by trivial)
  cases t with
  | stamp u e o => exact ⟨u, e, o, rfl⟩
  | lam q σ' A' b => cases hl q σ' A' b rfl
  | pair a b => cases hp a b rfl
  | _ =>
    rcases closed_neutral hS _ d hn trivial with ⟨i, k, T, -, hc, hdesc, -⟩ |
      ⟨g, Δ, σg, Ag, Bg, hg, hdesc, -⟩
    · rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨-, h⟩ <;>
        simp [gskel, GSkel.Ord] at h
    · have h := gate_desc hS hg hdesc
      simp [gskel, GSkel.Prot] at h

theorem not_notIntro_of_tags {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t C : Exp} {ε : Eff}
    (d : Deriv S acc (.tm Γ ρ t C ε)) (hC : Conv.Rigid C) (h₁ : Conv.headTag C ≠ 4)
    (h₂ : Conv.headTag C ≠ 5) (h₃ : Conv.headTag C ≠ 3) : NotIntro t := by
  obtain ⟨hl, hp, hs⟩ := d.intro_tags hC
  cases t with
  | lam q σ A b => exact h₁ (hl q σ A b rfl)
  | pair a b => exact h₂ (hp a b rfl)
  | stamp a e o => exact h₃ (hs a e o rfl)
  | _ => trivial

/-- Theorem 8.14 (ii): a closed normal term of `Event` is an event constant, of a
certificate or attestation entry. -/
theorem canonical_event {S : Sig} (hS : SigWF S) {acc : Bool} {ρ : Role} {t : Exp} {ε : Eff}
    (d : Deriv S acc (.tm [] ρ t .event ε)) (hn : Normal t) :
    ∃ i k, t = .const i k ∧ S.const? i k = some (.witness, .event) := by
  have hi : NotIntro t := not_notIntro_of_tags d (by trivial) (by decide) (by decide) (by decide)
  obtain ⟨γ, ⟨dE⟩⟩ := d.tm_ty
  have hρ : ρ = .witness := by cases dE; rfl
  subst hρ
  rcases closed_neutral hS t d hn hi with ⟨i, k, T, hh, hc, hdesc, hne⟩ |
    ⟨g, Δ, σg, Ag, Bg, hg, hdesc, -⟩
  · rcases const_desc hS hc hdesc with h | ⟨hT, -⟩ | ⟨-, h⟩
    · simp [gskel, GSkel.Ord] at h
    · subst hT
      by_cases htt : t = t.head
      · rw [hh] at htt
        exact ⟨i, k, htt, hc⟩
      · exact absurd rfl (hne htt).1
    · simp [gskel] at h
  · have h := gate_desc hS hg hdesc
    simp [gskel, GSkel.Prot] at h

/-- Theorem 8.14 (ii): a closed normal term of `Origin_A(e, t)` is an origin
constant whose declared type is convertible to it. -/
theorem canonical_origin {S : Sig} (hS : SigWF S) {acc : Bool} {ρ : Role} {t A e u : Exp}
    {ε : Eff} (d : Deriv S acc (.tm [] ρ t (.origin A e u) ε)) (hn : Normal t) :
    ∃ i k A' e' u', t = .const i k ∧ S.const? i k = some (.witness, .origin A' e' u') ∧
      Conv (.origin A' e' u') (.origin A e u) := by
  have hi : NotIntro t := not_notIntro_of_tags d (by trivial) (by simp [Conv.headTag])
    (by simp [Conv.headTag]) (by simp [Conv.headTag])
  obtain ⟨γ, ⟨dO⟩⟩ := d.tm_ty
  have hρ : ρ = .witness := by cases dO; rfl
  subst hρ
  rcases closed_neutral hS t d hn hi with ⟨i, k, T, hh, hc, hdesc, hne⟩ |
    ⟨g, Δ, σg, Ag, Bg, hg, hdesc, -⟩
  · rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨⟨A', e', u', hT⟩, -⟩
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
  · have h := gate_desc hS hg hdesc
    simp [gskel, GSkel.Prot] at h

/-- Theorem 8.14 (iii): a closed normal function of grade `1` or `∞` is a lambda. -/
theorem canonical_lam {S : Sig} (hS : SigWF S) {acc : Bool} {ρ σ : Role} {q : Grade}
    {t A B : Exp} {ε : Eff} (d : Deriv S acc (.tm [] ρ t (.pi q σ A B) ε)) (hn : Normal t)
    (hq : q ≠ .free) : ∃ A' b, t = .lam q σ A' b := by
  cases t with
  | lam q' σ' A' b =>
    obtain ⟨B', θ, hc, -⟩ := d.inv_lam
    obtain ⟨rfl, rfl, -⟩ := Conv.pi_inj hc
    exact ⟨A', b, rfl⟩
  | pair => exact d.not_pair_of_pi.elim
  | stamp => exact d.not_stamp_of_pi.elim
  | _ =>
    rcases closed_neutral hS _ d hn trivial with ⟨i, k, T, -, hc, hdesc, -⟩ |
      ⟨g, Δ, σg, Ag, Bg, hg, hdesc, -⟩
    · rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hq
      · simp [gskel] at h
      · simp [gskel] at h
    · exact absurd (gate_desc hS hg hdesc) hq

/-- Theorem 8.14 (iv): a closed normal neutral term at a protected role is headed by
an ordinary public constant or by a private node, and never by a public gate. -/
theorem canonical_protected_neutral {S : Sig} (hS : SigWF S) {acc : Bool} {ρ : Role}
    {t C : Exp} {ε : Eff} (d : Deriv S acc (.tm [] ρ t C ε)) (hn : Normal t) (hi : NotIntro t)
    (hρ : ρ = .form ∨ ρ = .presentation) :
    ((∃ i k T, t.head = .const i k ∧ S.const? i k = some (ρ, T) ∧ T.gradefree ∧
        OrdinaryHead S T) ∨ (∃ g ℓ ds a e, t.head = .node g ℓ ds a e)) ∧
      ∀ g ds s, t.head ≠ .gate g ds s := by
  rcases closed_neutral hS t d hn hi with ⟨i, k, T, hh, hc, -, -⟩ |
    ⟨g, Δ, σg, Ag, Bg, hg, -, hhead⟩
  · refine ⟨.inl ⟨i, k, T, hh, hc, ?_⟩, fun g ds s h => by rw [hh] at h; cases h⟩
    rcases hS.const_cases hc with ⟨h₁, h₂⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact ⟨h₁, h₂⟩
    · subst h₁; rcases hρ with h | h <;> cases h
    · subst h₁; rcases hρ with h | h <;> cases h
  · rcases hhead with ⟨ℓ, ds, a, e, hh⟩ | ⟨ds, s, hh, X, η, ⟨dst⟩⟩
    · exact ⟨.inr ⟨g, ℓ, ds, a, e, hh⟩, fun g' ds' s' h => by rw [hh] at h; cases h⟩
    · exfalso
      have hng : Normal (.gate g ds s) := hh ▸ hn.head
      obtain ⟨-, hns, hnot⟩ := hng.gate
      obtain ⟨u, e, o, rfl⟩ := canonical_stamped hS dst hns
      exact hnot u e o rfl

/-- Corollary 8.15 (canonical credentials): a closed normal term of a stamped type
is a stamp whose event and origin are the constants of one evidence entry; for a
certificate its payload is the payload constant, and for an exact attestation its
payload is convertible to the attested term. -/
theorem canonical_credential {S : Sig} (hS : SigWF S) {acc : Bool} {ρ σ : Role} {t A : Exp}
    {ε : Eff} (d : Deriv S acc (.tm [] ρ t (.stamped σ A) ε)) (hn : Normal t) :
    ∃ i, (∃ σ' A', S[i]? = some (.cert σ' A') ∧
          t = .stamp (.const i 0) (.const i 1) (.const i 2)) ∨
      (∃ A' t₀ u, S[i]? = some (.attest A' t₀) ∧ t = .stamp u (.const i 0) (.const i 1) ∧
          Conv u t₀) := by
  obtain ⟨u, e, o, rfl⟩ := canonical_stamped hS d hn
  obtain ⟨σ', A', θ, η, ω, -, -, -, ⟨du⟩, ⟨de⟩, ⟨dorg⟩, -⟩ := d.inv_stamp
  obtain ⟨hnu, hne, hno⟩ := hn.stamp
  obtain ⟨i, k, rfl, hci⟩ := canonical_event hS de hne
  obtain ⟨j, k', Aj, ej, uj, rfl, hcj, hconv⟩ := canonical_origin hS dorg hno
  obtain ⟨-, hee, huu⟩ := Conv.origin_inj hconv
  have hnormal_const : ∀ a b, Normal (.const a b) := fun a b _ h => by cases h
  rcases hS.const_cases hci with ⟨-, ho⟩ | ⟨-, -, hent⟩ | ⟨-, hent⟩
  · obtain ⟨a, args, he, -⟩ := ho; cases he
  · rcases hS.const_cases hcj with ⟨-, ho⟩ | ⟨-, hT, -⟩ | ⟨-, hent'⟩
    · obtain ⟨a, args, he, -⟩ := ho; cases he
    · cases hT
    · have hji : ∀ {a b c e : ℕ}, Conv (.const a b) (.const c e) → Exp.const a b = .const c e :=
        fun h => Normal.eq_of_conv (hnormal_const _ _) (hnormal_const _ _) h
      rcases hent with ⟨σ₁, A₁, hS₁, rfl⟩ | ⟨A₁, t₁, hS₁, rfl⟩ <;>
        rcases hent' with ⟨σ₂, A₂, hS₂, rfl, hT⟩ | ⟨A₂, t₂, hS₂, rfl, hT⟩ <;>
        obtain ⟨-, rfl, rfl⟩ := Exp.origin.inj hT
      · obtain ⟨rfl, -⟩ := Exp.const.inj (hji hee)
        have hu := Normal.eq_of_conv (hnormal_const _ _) hnu huu
        subst hu
        exact ⟨j, .inl ⟨σ₂, A₂, hS₂, rfl⟩⟩
      · have := (Exp.const.inj (hji hee)).2; omega
      · have := (Exp.const.inj (hji hee)).2; omega
      · obtain ⟨rfl, -⟩ := Exp.const.inj (hji hee)
        exact ⟨j, .inr ⟨A₂, _, u, hS₂, rfl, huu.symm⟩⟩
  · rcases hent with ⟨_, _, _, _, hT⟩ | ⟨_, _, _, _, hT⟩ <;> cases hT

end Artform.Roles.Calculus
