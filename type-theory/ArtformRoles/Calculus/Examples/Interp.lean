import ArtformRoles.Calculus.Examples.Rosette

/-!
# Interpretation witnesses

`sec:interpretation` of the paper: interpretation profiles are
fresh-witness-family modules (`prop:profile-conservative`), an exact attestation
installs a reading traceably (`prop:attested-installation`), and the worked
interpretation profile with its admission certificate
(`tab:interpretation-certificate`), two installed readings and their records.
-/

namespace Artform.Roles.Calculus

open Exp

namespace Book

/-! ## Interpretation witnesses -/

/-- **Interpretation profiles are conservative** (`prop:profile-conservative`). A module
that adds witness families and ordinary constructors headed by new families is a
fresh-witness-family module, so it is term-conservative and equality-reflecting
at every old closed grade-free type of a non-rendering role: a new way of
reading an artform creates no raw artform, identifies none, and installs no
presentation. -/
theorem profile_conservative {S M : Sig} (hSM : SigWF (S ++ M))
    (hM : ∀ e ∈ M, (∃ Δ, e = .family Δ .witness) ∨
      (∃ ρ A a args, e = .prim ρ A ∧ A.resultHead = .fam a args ∧ S.length ≤ a))
    {ρ : Role} (hρ : ρ ≠ .rendering) {A : Exp} (hA : A.Old S.length) (hgf : A.gradefree)
    {t : Exp} {ε : Eff} (dt : Deriv (S ++ M) true (.tm [] ρ t A ε)) :
    (∃ n ε', Steps t n ∧ Normal n ∧ n.Old S.length ∧
      Derivable (S ++ M) true (.tm [] ρ n A ε')) ∧
    ∀ u v, u.Old S.length → v.Old S.length → Conv u v →
      ∃ w, w.Old S.length ∧ Steps u w ∧ Steps v w :=
  fresh_family_conservative hSM hM hρ hA hgf dt

/-- **Attested installation is traceable** (`prop:attested-installation`). An exact
attestation `q@I = (e_q, o_q)` of an old term at an old type is an
evidence-inhabitant module; the public gate term with the credential
`stamp(I, e_q, o_q)` contracts to the node that retains the exact pair `I` and
the event `e_q`; and `e_q` is in its event support and is owned by the module, as
`thm:no-silent` requires of every enabled normal form. -/
theorem attested_installation {S : Sig} {A I : Exp} (hA : A.Old S.length)
    (hI : I.Old S.length) (g ℓ : ℕ) (ds : Exp) :
    EvidenceInhabitant S.length [.attest A I] ∧
    Step (.gate g ds (.stamp I (.const S.length 0) (.const S.length 1)))
      (.node g 0 ds I (.const S.length 0)) ∧
    Exp.const S.length 0 ∈ (Exp.node g ℓ ds I (.const S.length 0)).events ∧
    ModuleEvent S [.attest A I] (.const S.length 0) :=
  ⟨⟨by simp, fun e he => .inr ⟨A, I, by simpa using he, hA, hI⟩⟩, .record,
    by simp [Exp.events], S.length, le_rfl, .inr ⟨A, I, by simp, rfl⟩⟩

/-- An endpoint cannot be a rendering: Sig-Family admits a witness family only
when every telescope edge into the witness role has demand `0`, and a
rendering-role index has demand `∞`. -/
theorem endpoint_not_rendering {S : Sig} {Δ : Tel} (h : SigWF (S ++ [.family Δ .witness])) :
    ∀ p ∈ Δ, p.1 ≠ .rendering := by
  intro p hp hR
  have := (h.family_demand (a := S.length) (Δ := Δ) (ρ := .witness)
    (by simp [Sig.family?])) p hp
  rw [hR] at this
  cases this

/-- A certificate bundle cannot deliver an interpretation witness: Sig-Certificate
requires a family-headed payload type, and an interpretation witness type is a
dependent sum. -/
theorem certificate_not_sum {S : Sig} {σ ρ : Role} {A B C : Exp}
    (h : SigWF (S ++ [Entry.cert σ A])) : A ≠ .sigma ρ B C := by
  rintro rfl
  have hc : (S ++ [Entry.cert σ (.sigma ρ B C)]).const? S.length 0 =
      some (σ, .sigma ρ B C) := by
    simp [Sig.const?]
  rcases h.const_cases hc with ⟨-, a, args, he, -⟩ | ⟨-, hT, -⟩ | ⟨-, hk⟩
  · simp [Exp.resultHead] at he
  · cases hT
  · rcases hk with ⟨_, _, _, hk, _⟩ | ⟨_, _, _, hk, _⟩ <;> cases hk

namespace Interp

/-- `Tap(F)`, at declaration `2`: the tapestries laid from a palette `F`. -/
abbrev tap (F : Exp) : Exp := .fam 2 (.cons F .nil)
/-- The palette `Q = (c_Q, h_Q)`, from declarations `3` and `4`. -/
abbrev Q : Exp := .pair (.const 3 0) (.const 4 0)
/-- The endpoints `θ_rec`, `θ_div : Tap(Q)`, at declarations `5` and `6`. -/
abbrev θrec : Exp := .const 5 0
abbrev θdiv : Exp := .const 6 0

/-- The laying witness `Lay_k(F, θ)` and the law certificate `Obeys_k(F, θ, ℓ)` of
a profile whose families sit at `lay` and `lay + 1`. -/
abbrev layF (lay : ℕ) (F θ : Exp) : Exp := .fam lay (.cons F (.cons θ .nil))
abbrev obeysF (lay : ℕ) (F θ ℓ : Exp) : Exp := .fam (lay + 1) (.cons F (.cons θ (.cons ℓ .nil)))

/-- The interpretation witness type `IntWit(F, θ) = Σ(ℓ :_W Lay(F, θ)). Obeys(F, θ, ℓ)`. -/
abbrev intWit (lay : ℕ) (F θ : Exp) : Exp :=
  .sigma .witness (layF lay F θ) (obeysF lay (F.ren .succ) (θ.ren .succ) (.var 0))

/-- The base: the Artforms families, `Tap`, the palette and the two endpoints. -/
def base : Sig :=
  artforms ++ [.family [(.form, form)] .form, .prim .form finCode,
    .prim .form (hist (.const 3 0)), .prim .form (tap Q), .prim .form (tap Q)]

/-- A profile module: `Lay`, `Obeys`, and a realizer `ℓ` with its law certificate
`c`, for the endpoint `θ`. Its declarations start at `lay`. -/
def profile (lay : ℕ) (θ : Exp) : Sig :=
  [.family [(.form, form), (.form, tap (.var 0))] .witness,
   .family [(.form, form), (.form, tap (.var 0)), (.witness, layF lay (.var 1) (.var 0))]
     .witness,
   .prim .witness (layF lay Q θ),
   .prim .witness (obeysF lay Q θ (.const (lay + 2) 0))]

/-- The recurrence and division profiles, `ℳ_rec` at `7` and `ℳ_div` at `11`. -/
def Mrec : Sig := profile 7 θrec
def Mdiv : Sig := profile 11 θdiv

/-- `I_rec = (ℓ_rec, c_rec)`, `I_div = (ℓ_div, c_div)`. -/
abbrev Irec : Exp := .pair (.const 9 0) (.const 10 0)
abbrev Idiv : Exp := .pair (.const 13 0) (.const 14 0)

/-- `Laid_rec(F, θ)`, at declaration `15`. -/
abbrev laid (F θ : Exp) : Exp := .fam 15 (.cons F (.cons θ .nil))

/-- The installation module: `Laid_rec`, a presentation family, and the gate
`installLaying_rec : (F :_F Form, θ :_F Tap(F)); Stamped_W(IntWit_rec(F, θ)) ⇒_P
Laid_rec(F, θ)`, at declaration `16`. -/
def Grec : Sig :=
  [.family [(.form, form), (.form, tap (.var 0))] .presentation,
   .gate [(.form, form), (.form, tap (.var 0))] .witness (intWit 7 (.var 1) (.var 0))
     .presentation (laid (.var 1) (.var 0))]

/-- The exact attestation `ℰ_rec = {q@I_rec = (e_rec, o_rec)}`, at declaration `17`. -/
def Erec : Sig := [.attest (intWit 7 Q θrec) Irec]

/-- A second attestation `q'@I_rec = (e'_rec, o'_rec)`, at declaration `18`. -/
def Erec' : Sig := [.attest (intWit 7 Q θrec) Irec]

/-- The whole signature. -/
abbrev Sfull : Sig := (((((base ++ Mrec) ++ Mdiv) ++ Grec) ++ Erec) ++ Erec')


section Derivations

variable {S : Sig}

/-- `⊢_F Q : Form`. -/
def dQ (hS : SigWF S) (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    (hc : S.const? 3 0 = some (.form, finCode))
    (hh : S.const? 4 0 = some (.form, hist (.const 3 0))) {Γ : Ctx} :=
  Deriv.mkPair (B := hist (.var 0)) (Deriv.mkConst hc (dFinCode hS h0 (Γ := Γ)))
    (Deriv.mkConst hh (dHist hS h1 (Deriv.mkConst hc (dFinCode hS h0))))
    (Book.dForm hS h0 h1)

/-- `⊢_F Tap(F) type`, for a term `F` of `Form`. -/
def dTap (hS : SigWF S) (h2 : S.family? 2 = some ([(.form, form)], .form)) {Γ : Ctx} {F : Exp}
    {φ : Eff} (dF : Deriv S true (.tm Γ .form F form φ)) :=
  Deriv.mkTyFam hS h2 (Deriv.mkSpineCons (Δ := []) dF .mkSpineNil)

/-- `⊢_W Lay(F, θ) type`. -/
def dLay (hS : SigWF S) {lay : ℕ}
    (hl : S.family? lay = some ([(.form, form), (.form, tap (.var 0))], .witness)) {Γ : Ctx}
    {F θ : Exp} {φ τ : Eff} (dF : Deriv S true (.tm Γ .form F form φ))
    (dθ : Deriv S true (.tm Γ .form θ (tap F) τ)) :=
  Deriv.mkTyFam hS hl (Deriv.mkSpineCons dF (Deriv.mkSpineCons (Δ := []) dθ .mkSpineNil))

/-- `⊢_W Obeys(F, θ, ℓ) type`. -/
def dObeys (hS : SigWF S) {lay : ℕ}
    (ho : S.family? (lay + 1) = some ([(.form, form), (.form, tap (.var 0)),
      (.witness, layF lay (.var 1) (.var 0))], .witness)) {Γ : Ctx}
    {F θ ℓ : Exp} {φ τ κ : Eff} (dF : Deriv S true (.tm Γ .form F form φ))
    (dθ : Deriv S true (.tm Γ .form θ (tap F) τ))
    (dℓ : Deriv S true (.tm Γ .witness ℓ (layF lay ((F.ren Nat.succ).inst θ) θ) κ)) :=
  Deriv.mkTyFam hS ho (Deriv.mkSpineCons dF (Deriv.mkSpineCons dθ
    (Deriv.mkSpineCons (Δ := []) dℓ .mkSpineNil)))

end Derivations


/-! ### Admission (`tab:interpretation-certificate`) -/

theorem base_wf : SigWF base := by
  have h2 : SigWF (artforms ++ [.family [(.form, form)] .form]) :=
    .family artforms_wf ⟨Deriv.mkTelCons (Book.dForm artforms_wf rfl rfl) .mkTelNil⟩
      (by simp [demand])
  have h3 : SigWF ((artforms ++ [.family [(.form, form)] .form]) ++ [.prim .form finCode]) :=
    .prim h2 ⟨dFinCode h2 rfl⟩ trivial ⟨0, .nil, rfl, rfl⟩
  have h4 := SigWF.prim (A := hist (.const 3 0)) (ρ := .form) h3
    ⟨dHist h3 rfl (Deriv.mkConst rfl (dFinCode h3 rfl))⟩ ⟨trivial, trivial⟩ ⟨1, _, rfl, rfl⟩
  have h5 := SigWF.prim (A := tap Q) (ρ := .form) h4
    ⟨dTap h4 rfl (dQ h4 rfl rfl rfl rfl)⟩ (by simp [Exp.gradefree]) ⟨2, _, rfl, rfl⟩
  exact SigWF.prim (A := tap Q) (ρ := .form) h5
    ⟨dTap h5 rfl (dQ h5 rfl rfl rfl rfl)⟩ (by simp [Exp.gradefree]) ⟨2, _, rfl, rfl⟩

/-- The telescope `(F :_F Form, θ :_F Tap(F))` is formed. -/
def dTelFT {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    (h2 : S.family? 2 = some ([(.form, form)], .form)) :=
  Deriv.mkTelCons (Book.dForm hS h0 h1 (Γ := []))
    (Deriv.mkTelCons (dTap hS h2 (Deriv.mkVar (i := 0) (A := form) rfl (Book.dForm hS h0 h1)))
      .mkTelNil)

/-- `F :_F Form, θ :_F Tap(F) ⊢_W Lay(F, θ) type`. -/
def dLayVars {S : Sig} (hS : SigWF S) (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    (h2 : S.family? 2 = some ([(.form, form)], .form)) {lay : ℕ}
    (hl : S.family? lay = some ([(.form, form), (.form, tap (.var 0))], .witness)) :=
  dLay hS hl (Γ := [(.form, tap (.var 0)), (.form, form)])
    (Deriv.mkVar (i := 1) (A := form) rfl (Book.dForm hS h0 h1))
    (Deriv.mkVar (i := 0) (A := tap (.var 0)) rfl
      (dTap hS h2 (Deriv.mkVar (i := 1) (A := form) rfl (Book.dForm hS h0 h1))))

/-- The whole interpretation signature is admitted: the two profile modules, the
installation gate and the two attestations (Sig-Family, Sig-Primitive,
Sig-Gate, Sig-Attest). -/
theorem full_wf : SigWF Sfull := by
  -- the recurrence profile
  have m1 := SigWF.family (Δ := [(.form, form), (.form, tap (.var 0))]) (ρ := .witness) base_wf
    ⟨dTelFT base_wf rfl rfl rfl⟩ (by simp [demand])
  have m2 := SigWF.family (Δ := [(.form, form), (.form, tap (.var 0)),
      (.witness, layF 7 (.var 1) (.var 0))]) (ρ := .witness) m1
    ⟨Deriv.mkTelCons (Book.dForm m1 rfl rfl (Γ := []))
      (Deriv.mkTelCons (dTap m1 rfl (Deriv.mkVar (i := 0) (A := form) rfl (Book.dForm m1 rfl rfl)))
        (Deriv.mkTelCons (dLayVars m1 rfl rfl rfl rfl) .mkTelNil))⟩ (by simp [demand])
  have m3 := SigWF.prim (A := layF 7 Q θrec) (ρ := .witness) m2
    ⟨dLay m2 rfl (dQ m2 rfl rfl rfl rfl) (Deriv.mkConst rfl (dTap m2 rfl (dQ m2 rfl rfl rfl rfl)))⟩
    (by simp [Exp.gradefree]) ⟨7, _, rfl, rfl⟩
  have m4 := SigWF.prim (A := obeysF 7 Q θrec (.const 9 0)) (ρ := .witness) m3
    ⟨dObeys m3 rfl (dQ m3 rfl rfl rfl rfl) (Deriv.mkConst rfl (dTap m3 rfl (dQ m3 rfl rfl rfl rfl)))
      (Deriv.mkConst rfl (dLay m3 rfl (dQ m3 rfl rfl rfl rfl)
        (Deriv.mkConst rfl (dTap m3 rfl (dQ m3 rfl rfl rfl rfl)))))⟩
    (by simp [Exp.gradefree]) ⟨8, _, rfl, rfl⟩
  -- the division profile
  have d1 := SigWF.family (Δ := [(.form, form), (.form, tap (.var 0))]) (ρ := .witness) m4
    ⟨dTelFT m4 rfl rfl rfl⟩ (by simp [demand])
  have d2 := SigWF.family (Δ := [(.form, form), (.form, tap (.var 0)),
      (.witness, layF 11 (.var 1) (.var 0))]) (ρ := .witness) d1
    ⟨Deriv.mkTelCons (Book.dForm d1 rfl rfl (Γ := []))
      (Deriv.mkTelCons (dTap d1 rfl (Deriv.mkVar (i := 0) (A := form) rfl (Book.dForm d1 rfl rfl)))
        (Deriv.mkTelCons (dLayVars d1 rfl rfl rfl rfl) .mkTelNil))⟩ (by simp [demand])
  have d3 := SigWF.prim (A := layF 11 Q θdiv) (ρ := .witness) d2
    ⟨dLay d2 rfl (dQ d2 rfl rfl rfl rfl) (Deriv.mkConst rfl (dTap d2 rfl (dQ d2 rfl rfl rfl rfl)))⟩
    (by simp [Exp.gradefree]) ⟨11, _, rfl, rfl⟩
  have d4 := SigWF.prim (A := obeysF 11 Q θdiv (.const 13 0)) (ρ := .witness) d3
    ⟨dObeys d3 rfl (dQ d3 rfl rfl rfl rfl) (Deriv.mkConst rfl (dTap d3 rfl (dQ d3 rfl rfl rfl rfl)))
      (Deriv.mkConst rfl (dLay d3 rfl (dQ d3 rfl rfl rfl rfl)
        (Deriv.mkConst rfl (dTap d3 rfl (dQ d3 rfl rfl rfl rfl)))))⟩
    (by simp [Exp.gradefree]) ⟨12, _, rfl, rfl⟩
  -- the installation gate
  have g1 := SigWF.family (Δ := [(.form, form), (.form, tap (.var 0))]) (ρ := .presentation) d4
    ⟨dTelFT d4 rfl rfl rfl⟩ (by simp [demand])
  have g2 := SigWF.gate (Δ := [(.form, form), (.form, tap (.var 0))]) (σ := .witness)
    (A := intWit 7 (.var 1) (.var 0)) (ρ := .presentation) (B := laid (.var 1) (.var 0)) g1
    ⟨dTelFT g1 rfl rfl rfl⟩
    ⟨Deriv.mkTySigma (dLayVars g1 rfl rfl rfl rfl)
      (dObeys g1 rfl (Deriv.mkVar (i := 2) (A := form) rfl (Book.dForm g1 rfl rfl))
        (Deriv.mkVar (i := 1) (A := tap (.var 0)) rfl
          (dTap g1 rfl (Deriv.mkVar (i := 2) (A := form) rfl (Book.dForm g1 rfl rfl))))
        (Deriv.mkVar (i := 0) (A := layF 7 (.var 1) (.var 0)) rfl
          (dLay g1 rfl (Deriv.mkVar (i := 2) (A := form) rfl (Book.dForm g1 rfl rfl))
            (Deriv.mkVar (i := 1) (A := tap (.var 0)) rfl
              (dTap g1 rfl (Deriv.mkVar (i := 2) (A := form) rfl (Book.dForm g1 rfl rfl)))))))⟩
    ⟨Deriv.mkTyFam g1 rfl (Deriv.mkSpineCons
      (Deriv.mkVar (i := 1) (A := form) rfl (Book.dForm g1 rfl rfl))
      (Deriv.mkSpineCons (Δ := []) (Deriv.mkVar (i := 0) (A := tap (.var 0)) rfl
        (dTap g1 rfl (Deriv.mkVar (i := 1) (A := form) rfl (Book.dForm g1 rfl rfl))))
        .mkSpineNil))⟩
    (.inr rfl) (by decide) (by simp [demand]) (by decide) (by simp [Exp.gradefree])
    (by simp [Exp.gradefree]) (by simp [Exp.gradefree, Exp.ren])
  -- the two attestations of `I_rec`
  have hI : ∀ {S : Sig}, SigWF S → S.family? 0 = some ([], .form) →
      S.family? 1 = some ([(.form, finCode)], .form) →
      S.family? 2 = some ([(.form, form)], .form) →
      S.const? 3 0 = some (.form, finCode) → S.const? 4 0 = some (.form, hist (.const 3 0)) →
      S.const? 5 0 = some (.form, tap Q) →
      S.family? 7 = some ([(.form, form), (.form, tap (.var 0))], .witness) →
      S.family? 8 = some ([(.form, form), (.form, tap (.var 0)),
        (.witness, layF 7 (.var 1) (.var 0))], .witness) →
      S.const? 9 0 = some (.witness, layF 7 Q θrec) →
      S.const? 10 0 = some (.witness, obeysF 7 Q θrec (.const 9 0)) →
      ∃ ι, Derivable S true (.tm [] .witness Irec (intWit 7 Q θrec) ι) := by
    intro S hS h0 h1 h2 hc hh hθ h7 h8 h9 h10
    have dθ := Deriv.mkConst hθ (dTap hS h2 (dQ hS h0 h1 hc hh (Γ := [])))
    have dℓ := Deriv.mkConst h9 (dLay hS h7 (dQ hS h0 h1 hc hh (Γ := [])) dθ)
    exact ⟨_, ⟨Deriv.mkPair dℓ (Deriv.mkConst h10 (dObeys hS h8 (dQ hS h0 h1 hc hh) dθ dℓ))
      (Deriv.mkTySigma (dLay hS h7 (dQ hS h0 h1 hc hh) dθ)
        (dObeys hS h8 (dQ hS h0 h1 hc hh) (Deriv.mkConst hθ (dTap hS h2 (dQ hS h0 h1 hc hh)))
          (Deriv.mkVar (i := 0) (A := layF 7 Q θrec) rfl
            (dLay hS h7 (dQ hS h0 h1 hc hh)
              (Deriv.mkConst hθ (dTap hS h2 (dQ hS h0 h1 hc hh)))))))⟩⟩
  obtain ⟨ι₁, dI₁⟩ := hI g2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have e1 := SigWF.attest (A := intWit 7 Q θrec) (t := Irec) g2 dI₁ ⟨trivial, trivial⟩
    (by simp [Exp.gradefree, Exp.ren]) (.sigma (.fam rfl) (.fam rfl))
  obtain ⟨ι₂, dI₂⟩ := hI e1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact SigWF.attest (A := intWit 7 Q θrec) (t := Irec) e1 dI₂ ⟨trivial, trivial⟩
    (by simp [Exp.gradefree, Exp.ren]) (.sigma (.fam rfl) (.fam rfl))


/-! ### Installing the recurrence reading -/

/-- The declarations of the interpretation signature used by the installation. -/
structure Decls (S : Sig) : Prop where
  h0 : S.family? 0 = some ([], .form)
  h1 : S.family? 1 = some ([(.form, finCode)], .form)
  h2 : S.family? 2 = some ([(.form, form)], .form)
  hc : S.const? 3 0 = some (.form, finCode)
  hh : S.const? 4 0 = some (.form, hist (.const 3 0))
  hθ : S.const? 5 0 = some (.form, tap Q)
  h7 : S.family? 7 = some ([(.form, form), (.form, tap (.var 0))], .witness)
  h8 : S.family? 8 = some ([(.form, form), (.form, tap (.var 0)),
    (.witness, layF 7 (.var 1) (.var 0))], .witness)
  h9 : S.const? 9 0 = some (.witness, layF 7 Q θrec)
  h10 : S.const? 10 0 = some (.witness, obeysF 7 Q θrec (.const 9 0))
  h15 : S.family? 15 = some ([(.form, form), (.form, tap (.var 0))], .presentation)
  h16 : S.gate? 16 = some ([(.form, form), (.form, tap (.var 0))], .witness,
    intWit 7 (.var 1) (.var 0), .presentation, laid (.var 1) (.var 0))
  he : S.const? 17 0 = some (.witness, .event)
  ho : S.const? 17 1 = some (.witness, .origin (intWit 7 Q θrec) (.const 17 0) Irec)

theorem decls_full : Decls Sfull :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Install

variable {S : Sig} (hS : SigWF S) (h : Decls S)

/-- `⊢_F θ_rec : Tap(Q)`. -/
def dθrec {Γ : Ctx} := Deriv.mkConst h.hθ (dTap hS h.h2 (dQ hS h.h0 h.h1 h.hc h.hh (Γ := Γ)))

/-- `⊢_W ℓ_rec : Lay_rec(Q, θ_rec)`. -/
def dℓrec {Γ : Ctx} :=
  Deriv.mkConst h.h9 (dLay hS h.h7 (dQ hS h.h0 h.h1 h.hc h.hh (Γ := Γ)) (dθrec hS h))

/-- `⊢_W IntWit_rec(Q, θ_rec) type`. -/
def dIntWit {Γ : Ctx} :=
  Deriv.mkTySigma (dLay hS h.h7 (dQ hS h.h0 h.h1 h.hc h.hh (Γ := Γ)) (dθrec hS h))
    (dObeys hS h.h8 (dQ hS h.h0 h.h1 h.hc h.hh) (dθrec hS h)
      (Deriv.mkVar (i := 0) (A := layF 7 Q θrec) rfl
        (dLay hS h.h7 (dQ hS h.h0 h.h1 h.hc h.hh) (dθrec hS h))))

/-- `⊢_W I_rec : IntWit_rec(Q, θ_rec)`. -/
def dIrec {Γ : Ctx} :=
  Deriv.mkPair (dℓrec hS h (Γ := Γ))
    (Deriv.mkConst h.h10 (dObeys hS h.h8 (dQ hS h.h0 h.h1 h.hc h.hh) (dθrec hS h) (dℓrec hS h)))
    (dIntWit hS h)

/-- The credential `stamp(I_rec, e_rec, o_rec)`. -/
def dCred {Γ : Ctx} :=
  Deriv.mkStamp (dIrec hS h (Γ := Γ)) (Deriv.mkConst h.he .mkTyEvent)
    (Deriv.mkConst h.ho (Deriv.mkTyOrigin (by decide) (dIntWit hS h)
      (Deriv.mkConst h.he .mkTyEvent) (dIrec hS h)))
    (Deriv.mkTyStamped (dIntWit hS h) (by decide))

/-- The arguments `(Q, θ_rec)`. -/
def dArgs {Γ : Ctx} :=
  Deriv.mkSpineCons (Δ := [(.form, tap (.var 0))]) (dQ hS h.h0 h.h1 h.hc h.hh (Γ := Γ))
    (Deriv.mkSpineCons (Δ := []) (dθrec hS h) .mkSpineNil)

/-- `⊢_P Laid_rec(Q, θ_rec) type`. -/
def dLaid {Γ : Ctx} :=
  Deriv.mkTyFam hS h.h15 (dArgs hS h (Γ := Γ))

end Install

/-- `T_rec = gate_installLaying_rec(Q, θ_rec; stamp(I_rec, e_rec, o_rec))`. -/
abbrev Trec : Exp := .gate 16 (.cons Q (.cons θrec .nil)) (.stamp Irec (.const 17 0) (.const 17 1))
/-- `N_rec = node_installLaying_rec(Q, θ_rec; I_rec, e_rec)`, with label `ℓ`. -/
abbrev Nrec (ℓ : ℕ := 0) : Exp := .node 16 ℓ (.cons Q (.cons θrec .nil)) Irec (.const 17 0)
/-- The node of the second attestation `q'@I_rec`, with event `e'_rec`. -/
abbrev Nrec' : Exp := .node 16 0 (.cons Q (.cons θrec .nil)) Irec (.const 18 0)

/-- `⊢_P T_rec : Laid_rec(Q, θ_rec)`. -/
def dTrec := Deriv.mkGate full_wf decls_full.h16 (dArgs full_wf decls_full (Γ := []))
  (dCred full_wf decls_full) (dLaid full_wf decls_full)

/-- `⊢_P N_rec : Laid_rec(Q, θ_rec)`. -/
def dNrec (ℓ : ℕ) := Deriv.mkNode (ℓ := ℓ) full_wf decls_full.h16
  (dArgs full_wf decls_full (Γ := [])) (dIrec full_wf decls_full)
  (Deriv.mkConst decls_full.he .mkTyEvent) (dLaid full_wf decls_full)

/-- The effect of `T_rec`:
`𝟙_installLaying ⊕ ξ_Q ⊕ 𝟙_θrec ⊕ 1 ⊗ (𝟙_ℓrec ⊕ 𝟙_crec ⊕ 𝟙_erec ⊕ 𝟙_orec)`. -/
def effT : Eff :=
  Eff.unit (.decl 16 0) ⊓ (Eff.unit (.decl 3 0) ⊓ Eff.unit (.decl 4 0) ⊓ Eff.unit (.decl 5 0)) ⊓
    Eff.scale .gated (Eff.unit (.decl 9 0) ⊓ Eff.unit (.decl 10 0) ⊓ Eff.unit (.decl 17 0) ⊓
      Eff.unit (.decl 17 1))

/-- The effect of `N_rec`: the `o_rec` component is discarded. -/
def effN : Eff :=
  Eff.unit (.decl 16 0) ⊓ (Eff.unit (.decl 3 0) ⊓ Eff.unit (.decl 4 0) ⊓ Eff.unit (.decl 5 0)) ⊓
    Eff.scale .gated (Eff.unit (.decl 9 0) ⊓ Eff.unit (.decl 10 0) ⊓ Eff.unit (.decl 17 0))

/-- The installation of the recurrence reading. The public term contracts in one
record step to `N_rec = nf(T_rec)`, which retains the exact pair `I_rec` (no
projection is needed to recover its realizer) and the event `e_rec`; subject
reduction with effect improvement drops exactly the `o_rec` component;
`(ℓ, e_rec, e_rec) ∈ cross↓` and `e_rec ∈ events(N_rec)`, owned by `ℰ_rec`. -/
theorem install :
    Step Trec (Nrec 0) ∧ Normal (Nrec 0) ∧
    (∀ ρ A ε, Derivable Sfull true (.tm [] ρ Trec A ε) → ε = effT) ∧
    (∀ ℓ ρ A ε, Derivable Sfull true (.tm [] ρ (Nrec ℓ) A ε) → ε = effN) ∧
    (∀ ℓ, Cross [.record ℓ (.const 17 0)] (Nrec ℓ) ℓ (.const 17 0) (.const 17 0)) ∧
    Exp.const 17 0 ∈ (Nrec 0).events := by
  refine ⟨.record, Exp.redexFree_normal rfl, fun ρ A ε ⟨d⟩ => ?_, fun ℓ ρ A ε ⟨d⟩ => ?_,
    fun ℓ => ⟨by simp, 16, _, _, .refl⟩, by simp [Exp.events]⟩
  · rw [Deriv.effect_unique d dTrec]
    refine Rosette.eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
    · simp [effT, Eff.unit, Eff.scale]
    · simp only [effT, Eff.unit, Eff.scale, Pi.inf_apply, Atom.decl.injEq]
      split_ifs <;> simp_all
  · rw [Deriv.effect_unique d (dNrec ℓ)]
    refine Rosette.eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
    · simp [effN, Eff.unit, Eff.scale]
    · simp only [effN, Eff.unit, Eff.scale, Pi.inf_apply, Atom.decl.injEq]
      split_ifs <;> simp_all

/-- A second attestation of the same pair installs the same reading with a
different event: the two nodes are distinct normal forms, not definitionally
equal, with the same erasure, which forgets `e_rec` and `o_rec`. -/
theorem second_attestation :
    Normal Nrec' ∧ ¬Conv (Nrec 0) Nrec' ∧ (Nrec 0).erase Sfull = Nrec'.erase Sfull := by
  refine ⟨Exp.redexFree_normal rfl, fun hc => ?_, rfl⟩
  have := Normal.eq_of_conv (Exp.redexFree_normal rfl) (Exp.redexFree_normal rfl) hc
  simp at this

/-- Nothing relates the two endpoints: `θ_rec` and `θ_div` are distinct normal
forms and not definitionally equal. "The same palette, laid twice" is two
readings beside one unchanged `Q`. -/
theorem two_readings : ¬Conv θrec θdiv := by
  intro hc
  have := Normal.eq_of_conv (Exp.redexFree_normal rfl) (Exp.redexFree_normal rfl) hc
  simp at this

/-- `prop:profile-conservative` for the two profiles: `ℳ_rec ++ ℳ_div` is a
fresh-witness-family module over the base, so after either or both, every closed
term of an old grade-free type of a non-rendering role normalizes to an old term:
`c_Q`, `h_Q`, `Q` and every old closed form are the same old terms with the same
equalities. -/
theorem profiles_fresh : FreshWitnessFamily base.length (Mrec ++ Mdiv) := by
  intro e he
  simp only [Mrec, Mdiv, profile, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, 7, _, rfl, rfl, by simp [base, artforms]⟩
  · exact .inr ⟨_, _, 8, _, rfl, rfl, by simp [base, artforms]⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, 11, _, rfl, rfl, by simp [base, artforms]⟩
  · exact .inr ⟨_, _, 12, _, rfl, rfl, by simp [base, artforms]⟩

theorem profiles_wf : SigWF (base ++ (Mrec ++ Mdiv)) := by
  have h : SigWF ((base ++ (Mrec ++ Mdiv)) ++ (Grec ++ (Erec ++ Erec'))) := by
    have := full_wf
    simp only [Sfull, List.append_assoc] at this ⊢
    exact this
  exact h.prefix

/-- `prop:attested-installation` for `ℰ_rec`: the attestation is an evidence-inhabitant
module over the signature with the profiles and the installation gate. -/
theorem Erec_evidence : EvidenceInhabitant (((base ++ Mrec) ++ Mdiv) ++ Grec).length Erec :=
  (attested_installation (S := ((base ++ Mrec) ++ Mdiv) ++ Grec) (A := intWit 7 Q θrec)
    (I := Irec) (by simp [Exp.Old, base, artforms, Mrec, Mdiv, Grec, profile, Exp.ren])
    (by simp [Exp.Old, base, artforms, Mrec, Mdiv, Grec, profile]) 16 0 .nil).1
end Interp

end Book

end Artform.Roles.Calculus
