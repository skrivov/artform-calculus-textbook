import ArtformRoles.Calculus.Book

/-!
# Why the extension theorems need grade-freedom

Remarks 10.3 (`rem:gradefree-boundary`) and 10.4 (`rem:gate-interface`) of the
paper. Three families serve throughout: `G` at the rendering role, `W` at the
witness role and `B` at the form role.

* Remark 10.3, under the present rules. A rendering-only module adding `r :_R G`
  creates the closed normal term `λ^0(f :_F F_R). f r`, which is not old, at the
  type `Π^0(f :_F F_R). B`, where `F_R = Π^∞(x :_R G). B`. That type is formed
  over the base at the form role but is not grade-free, and no old term is
  convertible to the new one. An evidence bundle adding `a_d :_W W` likewise
  creates `λ^0(f :_F F_W). f a_d`, with `F_W = Π^1(x :_W W). B`; it is not old,
  and it holds no record, so no event of the module occurs in it. Hence
  Lemma 10.2 (i) and Theorem 10.7 are false without their grade-free hypothesis
  (`extension_support_needs_gradefree`, `no_silent_enabling_needs_gradefree`).
* `SigWF₀`: signature formation under the earlier Sig-Gate rule, which required
  only a gate's result type to be grade-free. A signature well formed under the
  present rules is well formed under the earlier one (`SigWF.toSigWF₀`).
* Remark 10.4, under the earlier rule. The base signature of `Remark104` has a
  certificate bundle, whose stamp `c` serves as a credential, and two gates of
  result `B` whose parameter types `Π^0(h :_F F_R). B` and `Π^0(h :_F F_W). B`
  are not grade-free. It meets `SigWF₀` but not `SigWF`. After the
  rendering-only module adding `r`, the public term `gate(λ^0 h. h r; c)` of the
  old grade-free type `B` reduces to a node that keeps `r` in its parameter, so
  Lemma 10.2 (i) fails (`extension_support_fails_old_rule`). After the evidence
  bundle adding `a_d`, `gate(λ^0 h. h a_d; c)` reduces to a node that keeps `a_d`
  but whose event is old, so Theorem 10.7 fails
  (`no_silent_enabling_fails_old_rule`).
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## The earlier gate rule -/

/-- Signature formation under the earlier Sig-Gate rule (Remark 10.4), which
required only the result type of a gate to be grade-free, not its parameter and
payload types. The other rules are those of `SigWF`. -/
inductive SigWF₀ : Sig → Prop
  | nil : SigWF₀ []
  | family {S Δ ρ δ} : SigWF₀ S → Derivable S true (.tel [] Δ δ) →
      (∀ p ∈ Δ, demand p.1 ρ = .free) → SigWF₀ (S ++ [.family Δ ρ])
  | prim {S ρ A α} : SigWF₀ S → Derivable S true (.ty [] ρ A α) → A.gradefree →
      OrdinaryHead S A → SigWF₀ (S ++ [.prim ρ A])
  | cert {S σ A α} : SigWF₀ S → Derivable S true (.ty [] σ A α) → σ ≠ .rendering →
      A.gradefree → OrdinaryHead S A → SigWF₀ (S ++ [.cert σ A])
  | attest {S A t θ} : SigWF₀ S → Derivable S true (.tm [] .witness t A θ) → t.IsPublic →
      A.gradefree → WData S A → SigWF₀ (S ++ [.attest A t])
  | gate {S Δ σ A ρ B δ α β} : SigWF₀ S → Derivable S true (.tel [] Δ δ) →
      Derivable S true (.ty Δ.reverse σ A α) → Derivable S true (.ty Δ.reverse ρ B β) →
      (ρ = .form ∨ ρ = .presentation) → σ ≠ .rendering →
      (∀ p ∈ Δ, demand p.1 ρ = .free) → demand σ ρ ≤ .gated → B.gradefree →
      SigWF₀ (S ++ [.gate Δ σ A ρ B])

/-- A signature well formed under the present rules is well formed under the
earlier gate rule. -/
theorem SigWF.toSigWF₀ {S : Sig} (h : SigWF S) : SigWF₀ S := by
  induction h with
  | nil => exact .nil
  | family _ hΔ hd ih => exact .family ih hΔ hd
  | prim _ hA hgf hh ih => exact .prim ih hA hgf hh
  | cert _ hA hσ hgf hh ih => exact .cert ih hA hσ hgf hh
  | attest _ ht hp hgf hw ih => exact .attest ih ht hp hgf hw
  | gate _ hΔ hA hB hρ hσ hd hσρ hBgf _ _ ih => exact .gate ih hΔ hA hB hρ hσ hd hσρ hBgf

/-- A derivation of `t : A` is a derivation of `t : A'` when `A = A'`. -/
def Deriv.retype {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {t A A' : Exp} {ε : Eff}
    (h : A = A') (d : Deriv S acc (.tm Γ ρ t A ε)) : Deriv S acc (.tm Γ ρ t A' ε) :=
  h ▸ d

namespace GradeFreedom

/-! ## Three families -/

/-- `G`, a rendering family, at declaration `0`. -/
abbrev G : Exp := .fam 0 .nil
/-- `W`, a witness family, at declaration `1`. -/
abbrev W : Exp := .fam 1 .nil
/-- `B`, a form family, at declaration `2`. -/
abbrev B : Exp := .fam 2 .nil
/-- `F_R = Π^∞(x :_R G). B`. -/
abbrev FR : Exp := .pi .absent .rendering G B
/-- `F_W = Π^1(x :_W W). B`. -/
abbrev FW : Exp := .pi .gated .witness W B
/-- `Π^0(f :_F F). B`: a type of the form role, not grade-free when `F` is not. -/
abbrev over (F : Exp) : Exp := .pi .free .form F B
/-- `λ^0(f :_F F). f u`. -/
abbrev applyTo (F u : Exp) : Exp := .lam .free .form F (.app (.var 0) u)

/-- The three families `G`, `W` and `B`. -/
def families : Sig := [.family [] .rendering, .family [] .witness, .family [] .form]

/-- The three families, at their positions in a signature. -/
structure Fams (S : Sig) : Prop where
  h0 : S.family? 0 = some ([], .rendering)
  h1 : S.family? 1 = some ([], .witness)
  h2 : S.family? 2 = some ([], .form)

section Derivations

variable {S : Sig}

/-- `⊢_R G type`. -/
def dG (h : Fams S) {Γ : Ctx} := Deriv.mkTyFamOf (Γ := Γ) h.h0 (fun _ h => by cases h) .mkSpineNil
/-- `⊢_W W type`. -/
def dW (h : Fams S) {Γ : Ctx} := Deriv.mkTyFamOf (Γ := Γ) h.h1 (fun _ h => by cases h) .mkSpineNil
/-- `⊢_F B type`. -/
def dB (h : Fams S) {Γ : Ctx} := Deriv.mkTyFamOf (Γ := Γ) h.h2 (fun _ h => by cases h) .mkSpineNil

/-- `⊢_F F_R type`: the binder check `D(R, F) = ∞` forces the grade `∞`. -/
def dFR (h : Fams S) {Γ : Ctx} := Deriv.mkTyPi (q := .absent) (dG h (Γ := Γ)) (dB h) (by decide)

/-- `⊢_F F_W type`: the binder check `D(W, F) = 1`. -/
def dFW (h : Fams S) {Γ : Ctx} := Deriv.mkTyPi (q := .gated) (dW h (Γ := Γ)) (dB h) (by decide)

/-- `⊢_F Π^0(f :_F F). B type`. -/
def dOver (h : Fams S) {Γ : Ctx} {F : Exp} {α : Eff} (dF : Deriv S true (.ty Γ .form F α)) :=
  Deriv.mkTyPi (q := .free) dF (dB h) (by decide)

/-- `⊢_F λ^0(f :_F F_R). f u : Π^0(f :_F F_R). B`, for a closed `u :_R G`. -/
def dApplyR (h : Fams S) {u : Exp} {η : Eff}
    (du : Deriv S true (.tm [(.form, FR)] .rendering u G η)) :=
  Deriv.mkLam (q := .free) (B := B) (dFR h (Γ := []))
    (Deriv.mkApp (A := G) (B := B) (Deriv.mkVar (i := 0) (A := FR) rfl (dFR h)) du (dB h))
    (by rw [← Grade.bot_eq]; exact bot_le) (dOver h (dFR h))

/-- `⊢_F λ^0(f :_F F_W). f u : Π^0(f :_F F_W). B`, for a closed `u :_W W`. -/
def dApplyW (h : Fams S) {u : Exp} {η : Eff}
    (du : Deriv S true (.tm [(.form, FW)] .witness u W η)) :=
  Deriv.mkLam (q := .free) (B := B) (dFW h (Γ := []))
    (Deriv.mkApp (A := W) (B := B) (Deriv.mkVar (i := 0) (A := FW) rfl (dFW h)) du (dB h))
    (by rw [← Grade.bot_eq]; exact bot_le) (dOver h (dFW h))

end Derivations

theorem families_wf : SigWF families := by
  have h₀ : SigWF [.family [] .rendering] :=
    .family (S := []) .nil ⟨.mkTelNil⟩ (fun _ h => by cases h)
  have h₁ : SigWF [.family [] .rendering, .family [] .witness] :=
    .family (S := [.family [] .rendering]) h₀ ⟨.mkTelNil⟩ (fun _ h => by cases h)
  exact .family (S := [.family [] .rendering, .family [] .witness]) h₁ ⟨.mkTelNil⟩
    (fun _ h => by cases h)

/-- A normal term that is not old is convertible to no old term. -/
theorem not_conv_old {N : ℕ} {t n : Exp} (hs : Steps t n) (hn : Normal n) (hnew : ¬n.Old N) :
    ¬∃ w, w.Old N ∧ Conv t w := by
  rintro ⟨w, hw, hc⟩
  obtain ⟨v, h₁, h₂⟩ := ((Conv.of_steps hs).symm.trans hc).joinable
  rw [← hn.eq_of_steps h₁] at h₂
  exact hnew (h₂.old hw)

/-! ## Remark 10.3: types that are not grade-free -/

namespace Remark103

/-- The rendering-only module adding `r :_R G`, at declaration `3`. -/
def MR : Sig := [.prim .rendering G]
/-- The evidence-inhabitant module adding the bundle `(a_d, e_d, o_d) : W`, at
declaration `3`. -/
def MW : Sig := [.cert .witness W]

/-- `r :_R G`. -/
abbrev r : Exp := .const 3 0
/-- `a_d :_W W`. -/
abbrev ad : Exp := .const 3 0
/-- `λ^0(f :_F F_R). f r`. -/
abbrev tR : Exp := applyTo FR r
/-- `λ^0(f :_F F_W). f a_d`. -/
abbrev tW : Exp := applyTo FW ad

theorem MR_wf : SigWF (families ++ MR) :=
  .prim families_wf ⟨dG ⟨rfl, rfl, rfl⟩ (Γ := [])⟩ trivial ⟨0, .nil, rfl, rfl⟩

theorem MW_wf : SigWF (families ++ MW) :=
  .cert families_wf ⟨dW ⟨rfl, rfl, rfl⟩ (Γ := [])⟩ (by decide) trivial ⟨1, .nil, rfl, rfl⟩

theorem MR_rendering : RenderingOnly MR := by
  intro e he
  simp only [MR, List.mem_singleton] at he
  exact .inr ⟨_, he⟩

theorem MW_evidence : EvidenceInhabitant families.length MW :=
  ⟨by simp [MW], fun e he => .inl ⟨W, by simpa [MW] using he, by simp [Exp.Old, families]⟩⟩

/-- `⊢_F λ^0(f :_F F_R). f r : Π^0(f :_F F_R). B` over `families + MR`. -/
def dtR := dApplyR (S := families ++ MR) ⟨rfl, rfl, rfl⟩
  (Deriv.mkConst (i := 3) (k := 0) rfl (dG ⟨rfl, rfl, rfl⟩))

/-- `⊢_F λ^0(f :_F F_W). f a_d : Π^0(f :_F F_W). B` over `families + MW`. -/
def dtW := dApplyW (S := families ++ MW) ⟨rfl, rfl, rfl⟩
  (Deriv.mkConst (i := 3) (k := 0) rfl (dW ⟨rfl, rfl, rfl⟩))

/-- **Remark 10.3**, rendering version. The rendering-only module `MR` creates
the closed normal public term `λ^0(f :_F F_R). f r`, which is not old, at the type
`Π^0(f :_F F_R). B` of the form role, formed over the base but not grade-free; no
old term is convertible to it. -/
theorem rendering_boundary :
    RenderingOnly MR ∧ SigWF (families ++ MR) ∧
    (∃ α, Derivable families true (.ty [] .form (over FR) α)) ∧ ¬(over FR).gradefree ∧
    (∃ ε, Derivable (families ++ MR) true (.tm [] .form tR (over FR) ε)) ∧
    Normal tR ∧ tR.IsPublic ∧ ¬tR.Old families.length ∧
    ¬∃ w, w.Old families.length ∧ Conv tR w := by
  have hnew : ¬tR.Old families.length := by simp [Exp.Old, families]
  have hn : Normal tR := Exp.redexFree_normal rfl
  exact ⟨MR_rendering, MR_wf, ⟨_, ⟨dOver ⟨rfl, rfl, rfl⟩ (dFR ⟨rfl, rfl, rfl⟩ (Γ := []))⟩⟩,
    fun h => by simp [Exp.gradefree] at h, ⟨_, ⟨dtR⟩⟩, hn, by simp [Exp.IsPublic], hnew,
    not_conv_old .refl hn hnew⟩

/-- **Remark 10.3**, evidence version. The evidence bundle `MW` creates the closed
normal public term `λ^0(f :_F F_W). f a_d`, which is not old, at the type
`Π^0(f :_F F_W). B` of the form role, formed over the base but not grade-free. It
contains no record, so no event of the module occurs in it. -/
theorem evidence_boundary :
    EvidenceInhabitant families.length MW ∧ SigWF (families ++ MW) ∧
    (∃ α, Derivable families true (.ty [] .form (over FW) α)) ∧ ¬(over FW).gradefree ∧
    (∃ ε, Derivable (families ++ MW) true (.tm [] .form tW (over FW) ε)) ∧
    Normal tW ∧ tW.IsPublic ∧ ¬tW.Old families.length ∧ tW.events = [] := by
  exact ⟨MW_evidence, MW_wf, ⟨_, ⟨dOver ⟨rfl, rfl, rfl⟩ (dFW ⟨rfl, rfl, rfl⟩ (Γ := []))⟩⟩,
    fun h => by simp [Exp.gradefree] at h, ⟨_, ⟨dtW⟩⟩, Exp.redexFree_normal rfl,
    by simp [Exp.IsPublic], by simp [Exp.Old, families], rfl⟩

/-- Lemma 10.2 (i) and the term conservativity of Theorem 10.5 are false without
their grade-free hypothesis: a rendering-only module can create a normal term
that is not old at an old type of the form role. -/
theorem extension_support_needs_gradefree :
    ¬∀ {S M : Sig}, SigWF (S ++ M) → RenderingOnly M → ∀ {ρ : Role}, ρ ≠ .rendering →
      ∀ {A : Exp}, A.Old S.length → ∀ {n : Exp} {ε : Eff},
        Deriv (S ++ M) true (.tm [] ρ n A ε) → Normal n → n.Old S.length := by
  intro h
  obtain ⟨-, -, -, -, -, hn, -, hnew, -⟩ := rendering_boundary
  exact hnew (h MR_wf MR_rendering (ρ := .form) (by decide)
    (by simp [Exp.Old, families]) dtR hn)

/-- Theorem 10.7 is false without its grade-free hypothesis: an evidence bundle
can create a public normal term that is not old, at an old type of the form role,
with no event of the module in it. -/
theorem no_silent_enabling_needs_gradefree :
    ¬∀ {S M : Sig}, SigWF (S ++ M) → EvidenceInhabitant S.length M →
      ∀ {ρ : Role}, (ρ = .form ∨ ρ = .presentation) → ∀ {A : Exp}, A.Old S.length →
      ∀ {t : Exp} {ε : Eff}, Deriv (S ++ M) true (.tm [] ρ t A ε) → t.IsPublic →
      ∀ {n : Exp}, Steps t n → Normal n → ¬n.Old S.length →
        ∃ e ∈ n.events, ModuleEvent S M e := by
  intro h
  obtain ⟨-, -, -, -, -, hn, hpub, hnew, hev⟩ := evidence_boundary
  obtain ⟨e, he, -⟩ := h MW_wf MW_evidence (ρ := .form) (.inl rfl)
    (by simp [Exp.Old, families]) dtW hpub .refl hn hnew
  rw [hev] at he
  cases he

end Remark103

/-! ## Remark 10.4: the earlier gate rule -/

namespace Remark104

/-- The base: the three families; a certificate bundle `(a₃, e₃, o₃) : W` at
declaration `3`, whose stamp `c` serves as a credential; the gate
`g_R : (h :_F Π^0(f :_F F_R). B); Stamped_W(W) ⇒_F B` at `4`; and the gate
`g_W : (h :_F Π^0(f :_F F_W). B); Stamped_W(W) ⇒_F B` at `5`. -/
def base : Sig :=
  families ++ [.cert .witness W, .gate [(.form, over FR)] .witness W .form B,
    .gate [(.form, over FW)] .witness W .form B]

/-- The rendering-only module adding `r :_R G`, at declaration `6`. -/
def MR : Sig := [.prim .rendering G]
/-- The evidence-inhabitant module adding the bundle `(a_d, e_d, o_d) : W`, at
declaration `6`. -/
def MW : Sig := [.cert .witness W]

/-- The credential `c = stamp(a₃, e₃, o₃) : Stamped_W(W)`, from the base. -/
abbrev c : Exp := .stamp (.const 3 0) (.const 3 1) (.const 3 2)
/-- `r :_R G`. -/
abbrev r : Exp := .const 6 0
/-- `a_d :_W W`. -/
abbrev ad : Exp := .const 6 0
/-- `gate_{g_R}(λ^0(h :_F F_R). h r; c)`. -/
abbrev gR : Exp := .gate 4 (.cons (applyTo FR r) .nil) c
/-- Its normal form, a node whose parameter keeps `r`. -/
abbrev nR : Exp := .node 4 0 (.cons (applyTo FR r) .nil) (.const 3 0) (.const 3 1)
/-- `gate_{g_W}(λ^0(h :_F F_W). h a_d; c)`. -/
abbrev gW : Exp := .gate 5 (.cons (applyTo FW ad) .nil) c
/-- Its normal form, a node whose parameter keeps `a_d` and whose event is `e₃`. -/
abbrev nW : Exp := .node 5 0 (.cons (applyTo FW ad) .nil) (.const 3 0) (.const 3 1)

section Derivations

variable {S : Sig}

/-- The base certificate's constants in a signature. -/
structure Cert (S : Sig) : Prop where
  ha : S.const? 3 0 = some (.witness, W)
  he : S.const? 3 1 = some (.witness, .event)
  ho : S.const? 3 2 = some (.witness, .origin W (.const 3 1) (.const 3 0))

/-- `⊢_W c : Stamped_W(W)`. -/
def dc (h : Fams S) (hc : Cert S) {Γ : Ctx} :=
  Deriv.mkStamp (Deriv.mkConst hc.ha (dW h (Γ := Γ))) (Deriv.mkConst hc.he .mkTyEvent)
    (Deriv.mkConst hc.ho (Deriv.mkTyOrigin (by decide) (dW h)
      (Deriv.mkConst hc.he .mkTyEvent) (Deriv.mkConst hc.ha (dW h))))
    (Deriv.mkTyStamped (dW h) (by decide))

/-- The derivation of `gate_g(p; c) : B` for a gate `g` declared with parameter
type `P`, payload `W` and result `B`, and a closed parameter `p : P`. -/
def dGate (h : Fams S) (hc : Cert S) {g : ℕ} {P p : Exp} {θ : Eff}
    (hg : S.gate? g = some ([(.form, P)], .witness, W, .form, B))
    (dp : Deriv S true (.tm [] .form p P θ)) :=
  Deriv.retype (A' := B) rfl <| Deriv.mkGateOf (Δ := [(.form, P)]) hg (.inl rfl)
    (by simp [demand]) (Deriv.mkSpineCons (Δ := []) dp .mkSpineNil) (dc h hc) (dB h)

/-- The derivation of `node_g(p; a₃, e₃) : B`. -/
def dNode (h : Fams S) (hc : Cert S) {g : ℕ} {P p : Exp} {θ : Eff}
    (hg : S.gate? g = some ([(.form, P)], .witness, W, .form, B))
    (dp : Deriv S true (.tm [] .form p P θ)) :=
  Deriv.retype (A' := B) rfl <| Deriv.mkNodeOf (Δ := [(.form, P)]) (ℓ := 0) hg (.inl rfl)
    (by simp [demand]) (by decide) (Deriv.mkSpineCons (Δ := []) dp .mkSpineNil)
    (Deriv.mkConst hc.ha (dW h)) (Deriv.mkConst hc.he .mkTyEvent) (dB h)

end Derivations

theorem base_wf₀ : SigWF₀ base := by
  have h3 : SigWF (families ++ [.cert .witness W]) :=
    .cert families_wf ⟨dW ⟨rfl, rfl, rfl⟩ (Γ := [])⟩ (by decide) trivial ⟨1, .nil, rfl, rfl⟩
  have h4 : SigWF₀ ((families ++ [.cert .witness W]) ++
      [.gate [(.form, over FR)] .witness W .form B]) :=
    .gate h3.toSigWF₀ ⟨Deriv.mkTelCons (dOver ⟨rfl, rfl, rfl⟩ (dFR ⟨rfl, rfl, rfl⟩))
      .mkTelNil⟩ ⟨dW ⟨rfl, rfl, rfl⟩⟩ ⟨dB ⟨rfl, rfl, rfl⟩⟩ (.inl rfl) (by decide)
      (by simp [demand]) (by decide) trivial
  exact .gate h4 ⟨Deriv.mkTelCons (dOver ⟨rfl, rfl, rfl⟩ (dFW ⟨rfl, rfl, rfl⟩)) .mkTelNil⟩
    ⟨dW ⟨rfl, rfl, rfl⟩⟩ ⟨dB ⟨rfl, rfl, rfl⟩⟩ (.inl rfl) (by decide) (by simp [demand])
    (by decide) trivial

/-- The base is not well formed under the present rules: the parameter type of
`g_R` is not grade-free. -/
theorem base_not_wf : ¬SigWF base := fun h => by
  have := (h.gate_gradefree (g := 4) (Δ := [(.form, over FR)]) (σ := .witness) (A := W)
    (ρ := .form) (B := B) rfl).1 _ (List.mem_singleton_self _)
  simp [Exp.gradefree] at this

theorem MR_wf₀ : SigWF₀ (base ++ MR) :=
  .prim base_wf₀ ⟨dG ⟨rfl, rfl, rfl⟩ (Γ := [])⟩ trivial ⟨0, .nil, rfl, rfl⟩

theorem MW_wf₀ : SigWF₀ (base ++ MW) :=
  .cert base_wf₀ ⟨dW ⟨rfl, rfl, rfl⟩ (Γ := [])⟩ (by decide) trivial ⟨1, .nil, rfl, rfl⟩

theorem MR_rendering : RenderingOnly MR := by
  intro e he
  simp only [MR, List.mem_singleton] at he
  exact .inr ⟨_, he⟩

theorem MW_evidence : EvidenceInhabitant base.length MW :=
  ⟨by simp [MW], fun e he => .inl ⟨W, by simpa [MW] using he, by simp [Exp.Old, base, families]⟩⟩

/-- `⊢_F λ^0(h :_F F_R). h r : Π^0(h :_F F_R). B` over `base + MR`. -/
def dpR := dApplyR (S := base ++ MR) ⟨rfl, rfl, rfl⟩
  (Deriv.mkConst (i := 6) (k := 0) rfl (dG ⟨rfl, rfl, rfl⟩))

/-- `⊢_F λ^0(h :_F F_W). h a_d : Π^0(h :_F F_W). B` over `base + MW`. -/
def dpW := dApplyW (S := base ++ MW) ⟨rfl, rfl, rfl⟩
  (Deriv.mkConst (i := 6) (k := 0) rfl (dW ⟨rfl, rfl, rfl⟩))

/-- `⊢_F gR : B` over `base + MR`. -/
def dgR := dGate (S := base ++ MR) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (g := 4) rfl dpR
/-- `⊢_F nR : B` over `base + MR`. -/
def dnR := dNode (S := base ++ MR) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (g := 4) rfl dpR
/-- `⊢_F gW : B` over `base + MW`. -/
def dgW := dGate (S := base ++ MW) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (g := 5) rfl dpW
/-- `⊢_F nW : B` over `base + MW`. -/
def dnW := dNode (S := base ++ MW) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (g := 5) rfl dpW

/-- **Remark 10.4**, rendering version. Under the earlier gate rule, the
rendering-only module `MR` turns the public term `gate_{g_R}(λ^0 h. h r; c)` of the
old grade-free form type `B` into the normal node `nR`, which keeps `r` in its
parameter and is not old; no old term is convertible to the gate term. -/
theorem rendering_gate :
    SigWF₀ (base ++ MR) ∧ ¬SigWF (base ++ MR) ∧ RenderingOnly MR ∧
    B.Old base.length ∧ B.gradefree ∧
    (∃ ε, Derivable (base ++ MR) true (.tm [] .form gR B ε)) ∧ gR.IsPublic ∧
    Steps gR nR ∧ Normal nR ∧ (∃ ε, Derivable (base ++ MR) true (.tm [] .form nR B ε)) ∧
    ¬nR.Old base.length ∧ ¬∃ w, w.Old base.length ∧ Conv gR w := by
  have hnew : ¬nR.Old base.length := by simp [Exp.Old, base, families]
  have hs : Steps gR nR := .single .record
  have hn : Normal nR := Exp.redexFree_normal rfl
  exact ⟨MR_wf₀, fun h => base_not_wf h.prefix, MR_rendering, by simp [Exp.Old, base, families],
    trivial, ⟨_, ⟨dgR⟩⟩, by simp [Exp.IsPublic], hs, hn, ⟨_, ⟨dnR⟩⟩, hnew,
    not_conv_old hs hn hnew⟩

/-- **Remark 10.4**, evidence version. Under the earlier gate rule, the evidence
bundle `MW` turns the public term `gate_{g_W}(λ^0 h. h a_d; c)` of `B` into the
normal node `nW`, which keeps the new payload `a_d` and is not old, while its only
event is the old `e₃`: no event of the module occurs in it. -/
theorem evidence_gate :
    SigWF₀ (base ++ MW) ∧ ¬SigWF (base ++ MW) ∧ EvidenceInhabitant base.length MW ∧
    (∃ ε, Derivable (base ++ MW) true (.tm [] .form gW B ε)) ∧ gW.IsPublic ∧
    Steps gW nW ∧ Normal nW ∧ ¬nW.Old base.length ∧ nW.events = [.const 3 1] ∧
    ¬∃ e ∈ nW.events, ModuleEvent base MW e := by
  have hev : nW.events = [.const 3 1] := rfl
  refine ⟨MW_wf₀, fun h => base_not_wf h.prefix, MW_evidence, ⟨_, ⟨dgW⟩⟩,
    by simp [Exp.IsPublic], .single .record, Exp.redexFree_normal rfl,
    by simp [Exp.Old, base, families], hev, ?_⟩
  rintro ⟨e, he, i, hi, h⟩
  rw [hev, List.mem_singleton] at he
  subst he
  rcases h with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩
  · cases he
    simp [base, families] at hi
  · cases he

/-- Under the earlier gate rule, Lemma 10.2 (i) is false: a rendering-only module
can create a normal term that is not old at an old grade-free type of the form
role. -/
theorem extension_support_fails_old_rule :
    ¬∀ {S M : Sig}, SigWF₀ (S ++ M) → RenderingOnly M → ∀ {ρ : Role}, ρ ≠ .rendering →
      ∀ {A : Exp}, A.Old S.length → A.gradefree → ∀ {n : Exp} {ε : Eff},
        Deriv (S ++ M) true (.tm [] ρ n A ε) → Normal n → n.Old S.length := by
  intro h
  obtain ⟨-, -, -, hB, hgf, -, -, -, hn, -, hnew, -⟩ := rendering_gate
  exact hnew (h MR_wf₀ MR_rendering (ρ := .form) (by decide) hB hgf dnR hn)

/-- Under the earlier gate rule, Theorem 10.7 is false: an evidence bundle can
create, from a public term at an old grade-free type of the form role, a normal
form that is not old with no event of the module in it. -/
theorem no_silent_enabling_fails_old_rule :
    ¬∀ {S M : Sig}, SigWF₀ (S ++ M) → EvidenceInhabitant S.length M →
      ∀ {ρ : Role}, (ρ = .form ∨ ρ = .presentation) → ∀ {A : Exp}, A.Old S.length →
      A.gradefree → ∀ {t : Exp} {ε : Eff}, Deriv (S ++ M) true (.tm [] ρ t A ε) →
      t.IsPublic → ∀ {n : Exp}, Steps t n → Normal n → ¬n.Old S.length →
        ∃ e ∈ n.events, ModuleEvent S M e := by
  intro h
  obtain ⟨-, -, -, -, hpub, hs, hn, hnew, -, hno⟩ := evidence_gate
  exact hno (h (A := B) MW_wf₀ MW_evidence (ρ := .form) (.inl rfl)
    (by simp [Exp.Old, base, families]) trivial dgW hpub hs hn hnew)

end Remark104

end GradeFreedom

end Artform.Roles.Calculus
