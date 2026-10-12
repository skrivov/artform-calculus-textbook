import ArtformRoles.Calculus.Accept

/-!
# The book in the calculus

§12 of the paper: the book's frames declared in the calculus, with finite
admitted modules worked out against the rules.

* `Exp.redexFree`: a computable check for normal forms (`Exp.redexFree_normal`).
* The octagonal-rosette module (§12.2, `Rosette`): the admitted signature, the
  suspended authorization `W₈ : Π^1(s :_W Stamped_W(RosetteSpec₈(X₈))). Form`,
  the trace `T₈ ⟶β gate ⟶record N₈`, the effects before and after the record
  step, the residual record trace and event support, the failure of term
  conservativity at `Form` with no silent enabling, the rendering-only
  observation layer, and the erasure `|T₈| ⟶β |N₈|`.
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## A computable test for normal forms -/

/-- No redex occurs in the expression. -/
def Exp.redexFree : Exp → Bool
  | var _ | const _ _ | event | nil => true
  | fam _ args => args.redexFree
  | origin A e t => A.redexFree && e.redexFree && t.redexFree
  | stamped _ A => A.redexFree
  | pi _ _ A B => A.redexFree && B.redexFree
  | sigma _ A B => A.redexFree && B.redexFree
  | lam _ _ A t => A.redexFree && t.redexFree
  | app t u =>
    (match t with
      | lam .. => false
      | _ => true) && t.redexFree && u.redexFree
  | pair t u => t.redexFree && u.redexFree
  | fst t =>
    (match t with
      | pair .. => false
      | _ => true) && t.redexFree
  | snd t =>
    (match t with
      | pair .. => false
      | _ => true) && t.redexFree
  | stamp t e o => t.redexFree && e.redexFree && o.redexFree
  | gate _ ds s =>
    (match s with
      | stamp .. => false
      | _ => true) && ds.redexFree && s.redexFree
  | node _ _ ds t e => ds.redexFree && t.redexFree && e.redexFree
  | cons t ts => t.redexFree && ts.redexFree

/-- An expression without a redex is normal. -/
theorem Exp.redexFree_normal {t : Exp} (h : t.redexFree = true) : Normal t := by
  intro t' hs
  induction hs with
  | beta => simp [Exp.redexFree] at h
  | fstPair => simp [Exp.redexFree] at h
  | sndPair => simp [Exp.redexFree] at h
  | record => simp [Exp.redexFree] at h
  | fam _ ih => exact ih h
  | origin₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | origin₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | origin₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | stamped _ ih => exact ih h
  | pi₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | pi₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | sigma₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | sigma₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | lam₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | lam₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | app₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | app₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | pair₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | pair₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | fst _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | snd _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | stamp₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | stamp₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | stamp₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | gate₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | gate₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | node₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.1
  | node₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1.2
  | node₃ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2
  | cons₁ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.1
  | cons₂ _ ih => simp only [Exp.redexFree, Bool.and_eq_true] at h; exact ih h.2


/-! ## Forms and construction history -/

namespace Book

/-- `FinCode`, at declaration `0`. -/
abbrev finCode : Exp := .fam 0 .nil
/-- `Hist(A)`, at declaration `1`. -/
abbrev hist (A : Exp) : Exp := .fam 1 (.cons A .nil)
/-- `Form = Σ(A :_F FinCode). Hist(A)`: a carrier with its construction history. -/
abbrev form : Exp := .sigma .form finCode (hist (.var 0))

/-- The two families of the Artforms signature: `FinCode` and `Hist`. -/
def artforms : Sig := [.family [] .form, .family [(.form, finCode)] .form]

/-- `⊢_F FinCode type`. -/
def dFinCode {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form)) {Γ : Ctx} :
    Deriv S true (.ty Γ .form finCode (Eff.unit (.decl 0 0) ⊓ ⊤)) :=
  .mkTyFam hS h0 .mkSpineNil

/-- `⊢_F Hist(A) type`, for a term `A` of `FinCode`. -/
def dHist {S : Sig} (hS : SigWF S) (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    {Γ : Ctx} {A : Exp} {α : Eff} (dA : Deriv S true (.tm Γ .form A finCode α)) :
    Deriv S true (.ty Γ .form (hist A) (Eff.unit (.decl 1 0) ⊓ (α ⊓ ⊤))) :=
  .mkTyFam hS h1 (.mkSpineCons dA .mkSpineNil)

/-- `⊢_F Form type`. -/
def dForm {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form)) {Γ : Ctx} :
    Deriv S true (.ty Γ .form form ((Eff.unit (.decl 0 0) ⊓ ⊤) ⊓
      (Eff.unit (.decl 1 0) ⊓ (Eff.unit (.var 0) ⊓ ⊤)).unbind)) :=
  .mkTySigma (dFinCode hS h0) (dHist hS h1 (.mkVar (A := finCode) rfl (dFinCode hS h0)))

theorem artforms_wf : SigWF artforms := by
  have h₀ : SigWF [.family [] .form] := .family (S := []) .nil ⟨.mkTelNil⟩ (fun _ h => by cases h)
  refine .family (S := [.family [] .form]) h₀ ⟨.mkTelCons (dFinCode h₀ rfl) .mkTelNil⟩ ?_
  intro p hp
  rw [List.mem_singleton.mp hp]
  rfl


/-! ## §12.2: the octagonal-rosette module -/

namespace Rosette

/-- `c₈ : FinCode`, at declaration `2`. -/
abbrev c8 : Exp := .const 2 0
/-- `h₈ : Hist(c₈)`, at declaration `3`. -/
abbrev h8 : Exp := .const 3 0
/-- `X₈ = (c₈, h₈) : Form`. -/
abbrev X8 : Exp := .pair c8 h8
/-- `RosetteSpec₈(X)`, at declaration `4`. -/
abbrev spec8 (X : Exp) : Exp := .fam 4 (.cons X .nil)
/-- The certificate bundle `d₈ = (a₈, e₈, o₈)`, at declaration `6`. -/
abbrev a8 : Exp := .const 6 0
abbrev e8 : Exp := .const 6 1
abbrev o8 : Exp := .const 6 2

/-- The base signature: the Artforms families, `c₈`, `h₈`, the witness family
`RosetteSpec₈ : (X :_F Form) ⇒_W Type`, and the registered gate
`inlay₈ : (X :_F Form); Stamped_W(RosetteSpec₈(X)) ⇒_F Form`. -/
def base : Sig :=
  artforms ++ [.prim .form finCode, .prim .form (hist c8), .family [(.form, form)] .witness,
    .gate [(.form, form)] .witness (spec8 (.var 0)) .form form]

/-- The evidence-inhabitant extension `ℰ₈`: the certificate bundle
`d₈ : RosetteSpec₈(X₈)`. -/
def E8 : Sig := [.cert .witness (spec8 X8)]

/-- The rendering-only observation layer `𝒱₈`: `Canvas₈` and
`draw₈ :_R Π^0(X :_F Form). Canvas₈`. -/
def V8 : Sig := [.family [] .rendering, .prim .rendering (.pi .free .form form (.fam 7 .nil))]

/-- The declarations of the rosette module that a signature provides. -/
structure Decls (S : Sig) : Prop where
  hFin : S.family? 0 = some ([], .form)
  hHist : S.family? 1 = some ([(.form, finCode)], .form)
  hc8 : S.const? 2 0 = some (.form, finCode)
  hh8 : S.const? 3 0 = some (.form, hist c8)
  hSpec : S.family? 4 = some ([(.form, form)], .witness)
  hInlay : S.gate? 5 = some ([(.form, form)], .witness, spec8 (.var 0), .form, form)

/-- The certificate's constants in a signature. -/
structure CertDecls (S : Sig) : Prop where
  ha8 : S.const? 6 0 = some (.witness, spec8 X8)
  he8 : S.const? 6 1 = some (.witness, .event)
  ho8 : S.const? 6 2 = some (.witness, .origin (spec8 X8) e8 a8)

theorem decls_base : Decls base := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem decls_cert : Decls (base ++ E8) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem certDecls : CertDecls (base ++ E8) := ⟨rfl, rfl, rfl⟩
theorem decls_view : Decls ((base ++ E8) ++ V8) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem certDecls_view : CertDecls ((base ++ E8) ++ V8) := ⟨rfl, rfl, rfl⟩

section Derivations

variable {S : Sig}

/-- `⊢_F Form type`. -/
def dForm (hS : SigWF S) (h : Decls S) {Γ : Ctx} := Book.dForm hS h.hFin h.hHist (Γ := Γ)

/-- `⊢_F c₈ : FinCode`. -/
def dc8 (hS : SigWF S) (h : Decls S) {Γ : Ctx} := Deriv.mkConst h.hc8 (dFinCode hS h.hFin (Γ := Γ))

/-- `⊢_F h₈ : Hist(c₈)`. -/
def dh8 (hS : SigWF S) (h : Decls S) {Γ : Ctx} :=
  Deriv.mkConst h.hh8 (dHist hS h.hHist (dc8 hS h (Γ := Γ)))

/-- `⊢_F X₈ : Form`. -/
def dX8 (hS : SigWF S) (h : Decls S) {Γ : Ctx} :=
  Deriv.mkPair (B := hist (.var 0)) (dc8 hS h (Γ := Γ)) (dh8 hS h) (dForm hS h)

/-- `⊢_W RosetteSpec₈(X₈) type`. -/
def dSpecX8 (hS : SigWF S) (h : Decls S) {Γ : Ctx} :=
  Deriv.mkTyFam hS h.hSpec (Deriv.mkSpineCons (Δ := []) (dX8 hS h (Γ := Γ)) .mkSpineNil)

/-- `⊢_W Stamped_W(RosetteSpec₈(X₈)) type`. -/
def dStampedSpec (hS : SigWF S) (h : Decls S) {Γ : Ctx} :=
  Deriv.mkTyStamped (dSpecX8 hS h (Γ := Γ)) (by decide)

/-- The certificate's payload `⊢_W a₈ : RosetteSpec₈(X₈)`. -/
def da8 (hS : SigWF S) (h : Decls S) (hc : CertDecls S) {Γ : Ctx} :=
  Deriv.mkConst hc.ha8 (dSpecX8 hS h (Γ := Γ))

/-- The certificate's event `⊢_W e₈ : Event`. -/
def de8 (hc : CertDecls S) {Γ : Ctx} := Deriv.mkConst hc.he8 (Deriv.mkTyEvent (Γ := Γ))

/-- The certificate's origin `⊢_W o₈ : Origin(e₈, a₈)`. -/
def do8 (hS : SigWF S) (h : Decls S) (hc : CertDecls S) {Γ : Ctx} :=
  Deriv.mkConst hc.ho8 (Deriv.mkTyOrigin (by decide) (dSpecX8 hS h (Γ := Γ)) (de8 hc)
    (da8 hS h hc))

/-- The credential `stamp(a₈, e₈, o₈) : Stamped_W(RosetteSpec₈(X₈))`. -/
def dStamp8 (hS : SigWF S) (h : Decls S) (hc : CertDecls S) {Γ : Ctx} :=
  Deriv.mkStamp (da8 hS h hc (Γ := Γ)) (de8 hc) (do8 hS h hc) (dStampedSpec hS h)

end Derivations


/-! ### Admission (Table: admission certificate for the rosette module) -/

/-- The base signature is admitted: `c₈, h₈` by Sig-Primitive, `RosetteSpec₈` by
Sig-Family (its form dependency is ordinary into witnesses), and `inlay₈` by
Sig-Gate (form parameter demand `0`, witness credential demand `1`, protected
grade-free result and grade-free interface). -/
theorem base_wf : SigWF base := by
  have h2 : SigWF (artforms ++ [.prim .form finCode]) :=
    .prim artforms_wf ⟨dFinCode artforms_wf rfl⟩ trivial ⟨0, .nil, rfl, rfl⟩
  have h3 : SigWF ((artforms ++ [.prim .form finCode]) ++ [.prim .form (hist c8)]) :=
    .prim h2 ⟨dHist h2 rfl (Deriv.mkConst rfl (dFinCode h2 rfl))⟩ ⟨trivial, trivial⟩
      ⟨1, _, rfl, rfl⟩
  have h4 : SigWF (((artforms ++ [.prim .form finCode]) ++ [.prim .form (hist c8)]) ++
      [.family [(.form, form)] .witness]) :=
    .family h3 ⟨Deriv.mkTelCons (Book.dForm h3 rfl rfl) .mkTelNil⟩ (by simp [demand])
  have h5 := SigWF.gate (Δ := [(.form, form)]) (σ := .witness) (A := spec8 (.var 0))
    (ρ := .form) (B := form) h4 ⟨Deriv.mkTelCons (Book.dForm h4 rfl rfl) .mkTelNil⟩
    ⟨Deriv.mkTyFam h4 rfl (Deriv.mkSpineCons (Δ := [])
      (Deriv.mkVar (A := form) rfl (Book.dForm h4 rfl rfl)) .mkSpineNil)⟩
    ⟨Book.dForm h4 rfl rfl⟩ (.inl rfl) (by decide) (by simp [demand]) (by decide)
    (by simp [Exp.gradefree]) (by simp [Exp.gradefree]) (by simp [Exp.gradefree])
  exact h5

/-- `ℰ₈` is admitted by Sig-Certificate: a closed non-rendering family-headed
grade-free payload type. -/
theorem cert_wf : SigWF (base ++ E8) :=
  .cert base_wf ⟨dSpecX8 base_wf decls_base⟩ (by decide) ⟨⟨trivial, trivial⟩, trivial⟩
    ⟨4, _, rfl, rfl⟩

/-- `𝒱₈` is admitted over the extended signature. -/
theorem view_wf : SigWF ((base ++ E8) ++ V8) := by
  have h7 : SigWF ((base ++ E8) ++ [.family [] .rendering]) :=
    .family cert_wf ⟨.mkTelNil⟩ (fun _ h => by cases h)
  exact .prim h7 ⟨Deriv.mkTyPi (Book.dForm h7 rfl rfl) (Deriv.mkTyFam h7 rfl .mkSpineNil)
    (by decide)⟩ (by simp [Exp.gradefree]) ⟨7, _, rfl, rfl⟩

/-! ### The suspended authorization and its record -/

/-- The postponed gate `W₈ = λ^1(s :_W Stamped_W(RosetteSpec₈(X₈))). gate_inlay₈(X₈; s)`. -/
abbrev W8 : Exp :=
  .lam .gated .witness (.stamped .witness (spec8 X8)) (.gate 5 (.cons X8 .nil) (.var 0))
/-- `T₈ = W₈ stamp(a₈, e₈, o₈)`. -/
abbrev T8 : Exp := .app W8 (.stamp a8 e8 o8)
/-- `gate_inlay₈(X₈; stamp(a₈, e₈, o₈))`. -/
abbrev G8 : Exp := .gate 5 (.cons X8 .nil) (.stamp a8 e8 o8)
/-- `N₈ = node_inlay₈(X₈; a₈, e₈)`, with label `ℓ`. -/
abbrev N8 (ℓ : ℕ := 0) : Exp := .node 5 ℓ (.cons X8 .nil) a8 e8

/-- The extended signature `base + ℰ₈`. -/
abbrev SE : Sig := base ++ E8

/-- The body of `W₈` in the context `s :_W Stamped_W(RosetteSpec₈(X₈))`. -/
def dBody :=
  Deriv.mkGate cert_wf decls_cert.hInlay
    (Deriv.mkSpineCons (Δ := [])
      (dX8 cert_wf decls_cert (Γ := [(.witness, .stamped .witness (spec8 X8))])) .mkSpineNil)
    (Deriv.mkVar (i := 0) (A := .stamped .witness (spec8 X8)) rfl
      (dStampedSpec cert_wf decls_cert))
    (dForm cert_wf decls_cert)


/-- `⊢_F W₈ : Π^1(s :_W Stamped_W(RosetteSpec₈(X₈))). Form`. -/
def dW8 :=
  Deriv.mkLam (q := .gated) (dStampedSpec cert_wf decls_cert (Γ := [])) dBody (by decide)
    (Deriv.mkTyPi (dStampedSpec cert_wf decls_cert) (dForm cert_wf decls_cert) (by decide))

/-- `⊢_F T₈ : Form`. -/
def dT8 :=
  Deriv.mkApp dW8 (dStamp8 cert_wf decls_cert certDecls) (dForm cert_wf decls_cert)

/-- `⊢_F gate_inlay₈(X₈; stamp(a₈, e₈, o₈)) : Form`. -/
def dG8 :=
  Deriv.mkGate cert_wf decls_cert.hInlay
    (Deriv.mkSpineCons (Δ := []) (dX8 cert_wf decls_cert (Γ := [])) .mkSpineNil)
    (dStamp8 cert_wf decls_cert certDecls) (dForm cert_wf decls_cert)

/-- `⊢_F N₈ : Form`, for every label. -/
def dN8 (ℓ : ℕ) :=
  Deriv.mkNode (ℓ := ℓ) cert_wf decls_cert.hInlay
    (Deriv.mkSpineCons (Δ := []) (dX8 cert_wf decls_cert (Γ := [])) .mkSpineNil)
    (da8 cert_wf decls_cert certDecls) (de8 certDecls) (dForm cert_wf decls_cert)

/-- `W₈` is typed at the positive grade demanded by the binder policy, and its
body uses the credential at grade exactly `1`: maximal elaboration derives
`Π^1`. The function type is not grade-free: `W₈` is a suspended authorization. -/
theorem W8_typed :
    (∃ ε, Derivable SE true
      (.tm [] .form W8 (.pi .gated .witness (.stamped .witness (spec8 X8)) form) ε)) ∧
    (∀ θ, Derivable SE true (.tm [(.witness, .stamped .witness (spec8 X8))] .form
        (.gate 5 (.cons X8 .nil) (.var 0)) form θ) → θ (.var 0) = .gated) ∧
    ¬(Exp.pi .gated .witness (.stamped .witness (spec8 X8)) form).gradefree := by
  refine ⟨⟨_, ⟨dW8⟩⟩, fun θ ⟨d⟩ => ?_, fun h => by cases h.1⟩
  rw [Deriv.effect_unique d dBody]
  decide


/-- The reduction trace `T₈ ⟶β gate_inlay₈(X₈; stamp(a₈, e₈, o₈)) ⟶record N₈`, and
`N₈ = nf(T₈)`. -/
theorem trace : Step T8 G8 ∧ Step G8 (N8 0) ∧ Normal (N8 0) :=
  ⟨.beta, .record, Exp.redexFree_normal rfl⟩

/-- The principal effect before the record step:
`𝟙_inlay₈ ⊕ ξ₈ ⊕ 1 ⊗ (𝟙_a₈ ⊕ 𝟙_e₈ ⊕ 𝟙_o₈)`, with `ξ₈ = 𝟙_c₈ ⊕ 𝟙_h₈`. -/
def effBefore : Eff :=
  Eff.unit (.decl 5 0) ⊓ (Eff.unit (.decl 2 0) ⊓ Eff.unit (.decl 3 0)) ⊓
    Eff.scale .gated (Eff.unit (.decl 6 0) ⊓ Eff.unit (.decl 6 1) ⊓ Eff.unit (.decl 6 2))

/-- The principal effect after the record step: the `o₈` component is discarded. -/
def effAfter : Eff :=
  Eff.unit (.decl 5 0) ⊓ (Eff.unit (.decl 2 0) ⊓ Eff.unit (.decl 3 0)) ⊓
    Eff.scale .gated (Eff.unit (.decl 6 0) ⊓ Eff.unit (.decl 6 1))

theorem eff_eq_of_atoms {ε η : Eff} (hv : ∀ i, ε (.var i) = η (.var i))
    (hd : ∀ i k, ε (.decl i k) = η (.decl i k)) : ε = η := by
  funext z
  cases z with
  | var i => exact hv i
  | decl i k => exact hd i k

/-- Subject reduction with effect improvement on the rosette: `T₈` and the gate
term have the effect `effBefore`, and `N₈` has `effAfter`, in every derivation. -/
theorem effects :
    (∀ ρ A ε, Derivable SE true (.tm [] ρ T8 A ε) → ε = effBefore) ∧
    (∀ ρ A ε, Derivable SE true (.tm [] ρ G8 A ε) → ε = effBefore) ∧
    (∀ ℓ ρ A ε, Derivable SE true (.tm [] ρ (N8 ℓ) A ε) → ε = effAfter) := by
  refine ⟨fun ρ A ε ⟨d⟩ => ?_, fun ρ A ε ⟨d⟩ => ?_, fun ℓ ρ A ε ⟨d⟩ => ?_⟩
  · rw [Deriv.effect_unique d dT8]
    refine eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
    · simp [effBefore, Eff.unit, Eff.scale, Eff.unbind]
    · simp only [effBefore, Eff.unit, Eff.scale, Eff.unbind, Pi.inf_apply, Atom.decl.injEq]
      split_ifs <;> simp_all
  · rw [Deriv.effect_unique d dG8]
    refine eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
    · simp [effBefore, Eff.unit, Eff.scale]
    · simp only [effBefore, Eff.unit, Eff.scale, Pi.inf_apply, Atom.decl.injEq]
      split_ifs <;> simp_all
  · rw [Deriv.effect_unique d (dN8 ℓ)]
    refine eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
    · simp [effAfter, Eff.unit, Eff.scale]
    · simp only [effAfter, Eff.unit, Eff.scale, Pi.inf_apply, Atom.decl.injEq]
      split_ifs <;> simp_all

/-- The residual record trace and support: with the record step labelled `ℓ`,
`(ℓ, e₈, e₈) ∈ cross↓(T₈ ⟶* N₈, N₈)` and `e₈ ∈ events(N₈)`. -/
theorem record_trace (ℓ : ℕ) :
    LSteps [.plain, .record ℓ e8] T8 (N8 ℓ) ∧ Cross [.plain, .record ℓ e8] (N8 ℓ) ℓ e8 e8 ∧
      e8 ∈ (N8 ℓ).events :=
  ⟨(LSteps.refl.tail (.contr .beta)).tail (.contr .record),
    ⟨by simp, 5, .cons X8 .nil, a8, .refl⟩, by simp [Exp.events]⟩

/-- `ℰ₈` is an evidence-inhabitant module. -/
theorem E8_evidence : EvidenceInhabitant base.length E8 :=
  ⟨by simp [E8], fun e he => .inl ⟨spec8 X8, by simpa [E8] using he,
    by simp [Exp.Old, base, artforms]⟩⟩

/-- `ℰ₈` is not term-conservative at `Form`: no old term is convertible to `T₈`,
since its normal form `N₈` is not old. It satisfies no silent enabling exactly:
the module's qualified event `e₈` occurs in that normal form. -/
theorem enabling :
    ¬(N8 0).Old base.length ∧ (¬∃ w, w.Old base.length ∧ Conv T8 w) ∧
      ∃ e ∈ (N8 0).events, ModuleEvent base E8 e := by
  have hN : ¬(N8 0).Old base.length := by simp [Exp.Old, base, artforms]
  refine ⟨hN, ?_, e8, by simp [Exp.events], 6, by simp [base, artforms], .inl ⟨.witness,
    spec8 X8, rfl, rfl⟩⟩
  rintro ⟨w, hw, hc⟩
  have hTN : Steps T8 (N8 0) := (Relation.ReflTransGen.single trace.1).tail trace.2.1
  obtain ⟨v, h₁, h₂⟩ := ((Conv.of_steps hTN).symm.trans hc).joinable
  rw [← trace.2.2.eq_of_steps h₁] at h₂
  exact hN (h₂.old hw)

theorem base_const_type {i k : ℕ} {ρ : Role} {T : Exp} (h : base.const? i k = some (ρ, T)) :
    T = finCode ∨ T = hist c8 := by
  have hi : i < 6 := Sig.lt_of_const h
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | (rcases k with _ | k <;> simp_all [base, artforms, Sig.const?])

theorem base_gate_result {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}
    (h : base.gate? g = some (Δ, σ, A, ρ, B)) : B = form := by
  have hg : g < 6 := Sig.lt_of_gate h
  rcases g with _ | _ | _ | _ | _ | _ | g
  all_goals first
    | omega
    | simp_all [base, artforms, Sig.gate?]

/-- Before `ℰ₈`, `RosetteSpec₈(X₈)` has no closed inhabitant: the canonical-forms
theorem leaves only a constant or a gate or node at its head, and no constant or
gate result of the base reaches `RosetteSpec₈`. -/
theorem no_inhabitant_before {ρ : Role} {t : Exp} {ε : Eff} :
    ¬Derivable base true (.tm [] ρ t (spec8 X8) ε) := by
  rintro ⟨d⟩
  obtain ⟨n, ε', hs, hn, -, ⟨dn⟩⟩ := d.normalize base_wf
  have hi : NotIntro n := not_notIntro_of_tags dn (by trivial) (by simp [Conv.headTag])
    (by simp [Conv.headTag]) (by simp [Conv.headTag])
  rcases closed_neutral base_wf n dn hn hi with ⟨i, k, T, -, hc, hdesc, -⟩ |
    ⟨g, Δ, σg, Ag, Bg, hg, hdesc, -⟩
  · rcases base_const_type hc with rfl | rfl <;> cases hdesc.of_base
  · obtain rfl := base_gate_result hg
    cases hdesc with
    | fst h => cases h.of_base
    | snd h => cases h.of_base

/-- The observation layer `𝒱₈` is rendering-only over `base + ℰ₈`; by
Theorems 10.4 and 10.7 it creates no new normal form at an old grade-free type
of a non-rendering role, and reflects equality. -/
theorem view :
    RenderingOnly V8 ∧
    ∀ {ρ : Role}, ρ ≠ .rendering → ∀ {A : Exp}, A.Old SE.length → A.gradefree →
      ∀ {t : Exp} {ε : Eff}, Deriv (SE ++ V8) true (.tm [] ρ t A ε) →
        ∃ n ε', Steps t n ∧ Normal n ∧ n.Old SE.length ∧
          Derivable (SE ++ V8) true (.tm [] ρ n A ε') := by
  have hR : RenderingOnly V8 := by
    intro e he
    simp only [V8, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact .inl ⟨[], rfl⟩
    · exact .inr ⟨_, rfl⟩
  exact ⟨hR, fun hρ _ hA hgf _ _ dt => (rendering_noninterference view_wf hR hρ hA hgf dt).1⟩

/-- Erasure makes the operational loss of the certificate explicit:
`|T₈| ⟶β |N₈|`, the record step erases to an equality, and `e₈`, `o₈` are absent
from `|N₈| = inlay₈(|X₈|; |a₈|)`. -/
theorem erasure :
    KStep (T8.erase SE) ((N8 0).erase SE) ∧ G8.erase SE = (N8 0).erase SE ∧
      (N8 0).erase SE = .gate 5 (.cons (X8.erase SE) .nil) (.const 6 0) :=
  ⟨.beta, rfl, rfl⟩

/-! ### A finite structural interpretation -/

/-- A finite structure on `Fin n` with two binary relations, `Rim` and `Spoke`. -/
structure FinStr (n : ℕ) where
  rim : Fin n → Fin n → Bool
  spoke : Fin n → Fin n → Bool

/-- `⟦|N₈|⟧₈ = (fin 9, {(i, 1 + (i mod 8)) | 1 ≤ i ≤ 8}, {(0, i) | 1 ≤ i ≤ 8})`. -/
def wheel8 : FinStr 9 where
  rim i j := 1 ≤ i.val && i.val ≤ 8 && j.val == 1 + i.val % 8
  spoke i j := i.val == 0 && 1 ≤ j.val

/-- The interpretation is the directed rim and eight spokes of a wheel: every
rim vertex has exactly one successor on the rim, going round all eight, and the
centre has a spoke to each of them. -/
theorem wheel8_is_wheel :
    (∀ i : Fin 9, 1 ≤ i.val → (∃ j, wheel8.rim i j = true) ∧
      ∀ j j', wheel8.rim i j = true → wheel8.rim i j' = true → j = j') ∧
    (∀ i j : Fin 9, wheel8.rim i j = true → 1 ≤ i.val ∧ 1 ≤ j.val) ∧
    (∀ j : Fin 9, wheel8.spoke 0 j = true ↔ 1 ≤ j.val) ∧
    (∀ i j : Fin 9, wheel8.spoke i j = true → i.val = 0) := by
  decide

end Rosette

end Book

end Artform.Roles.Calculus
