import ArtformRoles.Calculus.Paths

/-!
# Gate adequacy: mediation in normal forms

§9.1 of the paper, after path mediation (Theorem 9.1, in `Paths`).

* Lemma 9.2 (positive-function realization): `positive_function`. A closed
  normal function of grade `1` is a lambda whose parameter has grade `1` or
  `∞` in its body; an argument therefore enters the result of an application at
  grade `1` or not at all.
* Lemma 9.3 (no latent protected escape): `Deriv.free_outside_nodes`. In a
  normal term of a grade-free type at a protected role, outside private nodes
  every path costs `0`: no application edge of positive grade and no gate
  occur there. The lemma holds in every context whose variables have
  protected roles and grade-free types, so in particular for closed terms.
* Lemma 9.4 (grade-free normal-form mediation): `Deriv.gradefree_mediation`.
  Every path of such a term from an atom of policy demand `1` enters a private
  node, and no atom of demand `∞` has a live path.

Grade-freedom is read on graded skeletons (`GSkel.GF`), which conversion,
reduction and substitution keep (Lemma 8.6).
-/

namespace Artform.Roles.Calculus

open Exp

/-! ## Grade-free skeletons -/

/-- All the function grades of a graded skeleton are `0`. -/
def GSkel.GF : GSkel → Prop
  | .stmp _ τ => τ.GF
  | .arr q _ τ υ => q = .free ∧ τ.GF ∧ υ.GF
  | .prod _ τ υ => τ.GF ∧ υ.GF
  | _ => True

theorem gskel_gf {A : Exp} (h : A.gradefree) : (gskel A).GF := by
  induction A with
  | stamped σ A ih => exact ih h
  | pi q σ A B ihA ihB => exact ⟨h.1, ihA h.2.1, ihB h.2.2⟩
  | sigma ρ A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | _ => trivial

theorem GSkel.Desc.gf {τ ω : GSkel} (h : Desc τ ω) (hτ : τ.GF) : ω.GF := by
  induction h with
  | refl => exact hτ
  | arr _ ih => exact ih hτ.2.2
  | fst _ ih => exact ih hτ.1
  | snd _ ih => exact ih hτ.2

/-- The types of the constants of a well-formed signature are grade-free. -/
theorem SigWF.const_gf {S : Sig} (hS : SigWF S) {i k : ℕ} {ρ : Role} {T : Exp}
    (h : S.const? i k = some (ρ, T)) : (gskel T).GF := by
  rcases hS.const_cases h with ⟨hg, -⟩ | ⟨-, rfl, -⟩ | ⟨-, hT⟩
  · exact gskel_gf hg
  · trivial
  · rcases hT with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial

/-- A context whose variables have protected roles and grade-free types. -/
def CtxGF (Γ : Ctx) : Prop :=
  ∀ p ∈ Γ, (p.1 = .form ∨ p.1 = .presentation) ∧ (gskel p.2).GF

theorem CtxGF.nil : CtxGF [] := fun _ h => by cases h

/-- Only a protected role may flow freely into a protected role. -/
theorem protected_of_demand {σ ρ : Role} (h : demand σ ρ ≤ .free)
    (hρ : ρ = .form ∨ ρ = .presentation) : σ = .form ∨ σ = .presentation := by
  revert h
  cases σ <;> rcases hρ with rfl | rfl <;> decide

/-- The binder check of a well-formed dependent function type. -/
theorem Deriv.tyPi_demand {S : Sig} {acc : Bool} {Γ : Ctx} {ρ σ : Role} {q : Grade}
    {A B : Exp} {ε : Eff} (d : Deriv S acc (.ty Γ ρ (.pi q σ A B) ε)) : demand σ ρ ≤ q := by
  cases d with
  | tyPi _ _ hq => exact hq

theorem Path.cost_eq_of_edges {p p' : Path} (h : p.edges = p'.edges) : p.cost = p'.cost := by
  simp only [Path.cost, h]

/-! ## Heads of neutral terms -/

/-- The head of a normal neutral term is a variable, a constant, or a gate or
node, and the type of the term is reached from the type of its head through
codomains and projections. -/
theorem Deriv.neutral_head {S : Sig} (hS : SigWF S) {acc : Bool} :
    ∀ (t : Exp) {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}, Deriv S acc (.tm Γ ρ t C ε) →
      Normal t → NotIntro t →
      (∃ (i : ℕ) (A : Exp), Γ[i]? = some (ρ, A) ∧ GSkel.Desc (gskel A) (gskel C)) ∨
      (∃ i k T, S.const? i k = some (ρ, T) ∧ GSkel.Desc (gskel T) (gskel C)) ∨
      (∃ g Δ σ A B, S.gate? g = some (Δ, σ, A, ρ, B) ∧ GSkel.Desc (gskel B) (gskel C)) := by
  intro t
  induction t with
  | var i =>
    intro Γ ρ C ε d _ _
    obtain ⟨A₀, hΓ, hconv, -, hf⟩ := d.inv_var
    obtain ⟨γ, hC⟩ := d.tm_ty
    refine .inl ⟨i, A₀, hΓ, ?_⟩
    rw [← gskel_ren A₀ (· + (i + 1)), gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)]
    exact .refl _
  | const i k =>
    intro Γ ρ C ε d _ _
    obtain ⟨A₀, hc, hconv, -, hf⟩ := d.inv_const
    obtain ⟨γ, hC⟩ := d.tm_ty
    refine .inr (.inl ⟨i, k, A₀, hc, ?_⟩)
    rw [gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC)]
    exact .refl _
  | app f u ihf _ =>
    intro Γ ρ C ε d hn _
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
    rcases ihf df hnf hfi with ⟨i, A₀, h₁, h₂⟩ | ⟨i, k, T, h₁, h₂⟩ | ⟨g, Δ, σg, Ag, Bg, h₁, h₂⟩
    · exact .inl ⟨i, A₀, h₁, h₂.trans (.arr (.refl _))⟩
    · exact .inr (.inl ⟨i, k, T, h₁, h₂.trans (.arr (.refl _))⟩)
    · exact .inr (.inr ⟨g, Δ, σg, Ag, Bg, h₁, h₂.trans (.arr (.refl _))⟩)
  | fst p ihp =>
    intro Γ ρ C ε d hn _
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
    rcases ihp dp hnp hpi with ⟨i, A₀, h₁, h₂⟩ | ⟨i, k, T, h₁, h₂⟩ | ⟨g, Δ, σg, Ag, Bg, h₁, h₂⟩
    · exact .inl ⟨i, A₀, h₁, h₂.trans (.fst (.refl _))⟩
    · exact .inr (.inl ⟨i, k, T, h₁, h₂.trans (.fst (.refl _))⟩)
    · exact .inr (.inr ⟨g, Δ, σg, Ag, Bg, h₁, h₂.trans (.fst (.refl _))⟩)
  | snd p ihp =>
    intro Γ ρ C ε d hn _
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
    rcases ihp dp hnp hpi with ⟨i, A₀, h₁, h₂⟩ | ⟨i, k, T, h₁, h₂⟩ | ⟨g, Δ, σg, Ag, Bg, h₁, h₂⟩
    · exact .inl ⟨i, A₀, h₁, h₂.trans (.snd (.refl _))⟩
    · exact .inr (.inl ⟨i, k, T, h₁, h₂.trans (.snd (.refl _))⟩)
    · exact .inr (.inr ⟨g, Δ, σg, Ag, Bg, h₁, h₂.trans (.snd (.refl _))⟩)
  | gate g ds s _ _ =>
    intro Γ ρ C ε d _ _
    obtain ⟨Δ, σ, A, B, δ, η, hg, hconv, -, -, -, hf⟩ := d.inv_gate
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
    refine .inr (.inr ⟨g, Δ, σ, A, B, hg, ?_⟩)
    rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
      (gskel_instType dB.tyShape_ty ds Δ).1]
    exact .refl _
  | node g ℓ ds a e _ _ _ =>
    intro Γ ρ C ε d _ _
    obtain ⟨Δ, σ, A, B, δ, θ, η, hg, hconv, -, -, -, -, hf⟩ := d.inv_node
    obtain ⟨γ, hC⟩ := d.tm_ty
    obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
    refine .inr (.inr ⟨g, Δ, σ, A, B, hg, ?_⟩)
    rw [← gskel_conv hconv (TyShape.of_ex hf) (TyShape.of_ty hC),
      (gskel_instType dB.tyShape_ty ds Δ).1]
    exact .refl _
  | lam | pair | stamp => intro Γ ρ C ε _ _ hi; exact absurd hi id
  | fam | event | origin | stamped | pi | sigma | nil | cons =>
    intro Γ ρ C ε d; exact d.isTermHead.elim

/-! ## Lemma 9.3: no latent protected escape -/

/-- **Lemma 9.3** (no latent protected escape). Let `n` be a normal term at a
protected role `ρ` in a context whose variables have protected roles and
grade-free types (for instance the empty context), and let its type be
grade-free, or `n` neutral. Then its type is grade-free, and every path of its
derivation that enters no private node costs `0`. In particular, outside
private nodes no path ends in an application edge of grade `1` or `∞` (part
(i) of the paper), and no gate occurs, so no gate carries a public occurrence
in its credential (part (ii)). -/
theorem Deriv.free_outside_nodes {S : Sig} (hS : SigWF S) {acc : Bool} {Γ : Ctx} {ρ : Role}
    {n C : Exp} {ε : Eff} (d : Deriv S acc (.tm Γ ρ n C ε)) (hn : Normal n)
    (hρ : ρ = .form ∨ ρ = .presentation) (hctx : CtxGF Γ) (hC : (gskel C).GF ∨ NotIntro n) :
    (gskel C).GF ∧ ∀ p ∈ d.paths, (∀ e ∈ p.edges, ¬e.kind.IsNode) → p.cost = ⊥ := by
  generalize hj : Judg.tm Γ ρ n C ε = j at d
  induction d generalizing Γ ρ n C ε with
  | var hΓi hCeq _ _ _ _ =>
    cases hj
    refine ⟨?_, ?_⟩
    · rw [hCeq, gskel_ren]; exact (hctx _ (List.mem_of_getElem? hΓi)).2
    · intro p hp _
      simp only [Deriv.paths, List.mem_singleton] at hp
      subst hp; rfl
  | const hc _ _ _ _ =>
    cases hj
    refine ⟨hS.const_gf hc, ?_⟩
    intro p hp _
    simp only [Deriv.paths, List.mem_singleton] at hp
    subst hp; rfl
  | @lam Γ' q σ ρ' A B t α θ γ ε' dA dt hq dC hε _ _ iht _ =>
    cases hj
    obtain ⟨hq0, hAgf, hBgf⟩ : (gskel (.pi q σ A B)).GF := hC.resolve_right id
    have hσ := protected_of_demand (hq0 ▸ dC.tyPi_demand) hρ
    have hctx' : CtxGF ((σ, A) :: Γ') := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hσ, hAgf⟩
      · exact hctx p hp
    obtain ⟨-, hpt⟩ := iht (Normal.lam hn).2 hρ hctx' (.inl hBgf) rfl
    refine ⟨⟨hq0, hAgf, hBgf⟩, ?_⟩
    intro p hp hno
    obtain ⟨p', hp', hed, -⟩ := mem_unbindPaths hp
    obtain ⟨p'', hp'', rfl⟩ := mem_map_via hp'
    rw [Path.cost_eq_of_edges hed, Path.cost_via,
      hpt p'' hp'' (fun e he => hno e (hed ▸ List.mem_cons_of_mem _ he))]
    simp [ordE]
  | @app Γ' q σ ρ' A B f u C' φ η γ ε' df du hCeq _ _ _ ihf ihu _ =>
    cases hj
    obtain ⟨hnf, hnu, hnl⟩ := hn.app
    have hfi : NotIntro f := by
      cases f with
      | lam q' σ' A' b => exact hnl _ _ _ _ rfl
      | pair => exact df.not_pair_of_pi
      | stamp => exact df.not_stamp_of_pi
      | _ => trivial
    obtain ⟨⟨hq0, hAgf, hBgf⟩, hpf⟩ := ihf hnf hρ hctx (.inr hfi) rfl
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    have hσ := protected_of_demand (hq0 ▸ dpi.tyPi_demand) hρ
    obtain ⟨-, hpu⟩ := ihu hnu hσ hctx (.inl hAgf) rfl
    refine ⟨?_, ?_⟩
    · rw [hCeq, (gskel_subst dpi.tyShape_ty.2 _).1]; exact hBgf
    · intro p hp hno
      simp only [Deriv.paths] at hp
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨p', hp', rfl⟩ := mem_map_via h
        rw [Path.cost_via, hpf p' hp' (fun e he => hno e (List.mem_cons_of_mem _ he))]
        simp [ordE]
      · obtain ⟨p', hp', rfl⟩ := mem_map_via h
        rw [Path.cost_via, hpu p' hp' (fun e he => hno e (List.mem_cons_of_mem _ he))]
        simp [hq0, ← Grade.bot_eq]
  | @pair Γ' ρ' A B t u θ η γ ε' dt du dC hε _ iht ihu _ =>
    cases hj
    obtain ⟨hAgf, hBgf⟩ : (gskel (.sigma _ A B)).GF := hC.resolve_right id
    obtain ⟨hnt, hnu⟩ := hn.pair
    obtain ⟨-, hpt⟩ := iht hnt hρ hctx (.inl hAgf) rfl
    obtain ⟨-, -, β, ⟨dB⟩⟩ := dC.inv_tySigma
    have hBt : (gskel (B.inst t)).GF := by rw [(gskel_subst dB.tyShape_ty _).1]; exact hBgf
    obtain ⟨-, hpu⟩ := ihu hnu hρ hctx (.inl hBt) rfl
    refine ⟨⟨hAgf, hBgf⟩, ?_⟩
    intro p hp hno
    simp only [Deriv.paths] at hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨p', hp', rfl⟩ := mem_map_via h
      rw [Path.cost_via, hpt p' hp' (fun e he => hno e (List.mem_cons_of_mem _ he))]
      simp [ordE]
    · obtain ⟨p', hp', rfl⟩ := mem_map_via h
      rw [Path.cost_via, hpu p' hp' (fun e he => hno e (List.mem_cons_of_mem _ he))]
      simp [ordE]
  | @fst Γ' ρ' A B p π γ dp dA _ ihp _ =>
    cases hj
    obtain ⟨hnp, hnpair⟩ := hn.fst
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨⟨hAgf, -⟩, hpp⟩ := ihp hnp hρ hctx (.inr hpi) rfl
    refine ⟨hAgf, ?_⟩
    intro p' hp' hno
    obtain ⟨p'', hp'', rfl⟩ := mem_map_via hp'
    rw [Path.cost_via, hpp p'' hp'' (fun e he => hno e (List.mem_cons_of_mem _ he))]
    simp [ordE]
  | @snd Γ' ρ' A B C' p π γ dp hCeq _ _ ihp _ =>
    cases hj
    obtain ⟨hnp, hnpair⟩ := hn.snd
    have hpi : NotIntro p := by
      cases p with
      | lam => exact dp.not_lam_of_sigma
      | pair a b => exact hnpair a b rfl
      | stamp => exact dp.not_stamp_of_sigma
      | _ => trivial
    obtain ⟨⟨-, hBgf⟩, hpp⟩ := ihp hnp hρ hctx (.inr hpi) rfl
    obtain ⟨γp, ⟨ds⟩⟩ := dp.tm_ty
    refine ⟨?_, ?_⟩
    · rw [hCeq, (gskel_subst ds.tyShape_ty.2 _).1]; exact hBgf
    · intro p' hp' hno
      obtain ⟨p'', hp'', rfl⟩ := mem_map_via hp'
      rw [Path.cost_via, hpp p'' hp'' (fun e he => hno e (List.mem_cons_of_mem _ he))]
      simp [ordE]
  | stamp =>
    cases hj
    rcases hρ with h | h <;> cases h
  | @gate Γ' g ds s Δ σ A ρ' B C' δ η γ ε' hg dds dst _ _ _ _ _ _ _ =>
    cases hj
    exfalso
    obtain ⟨-, hns, hnst⟩ := hn.gate
    have hsi : NotIntro s := by
      cases s with
      | lam => exact dst.not_lam_of_stamped
      | pair => exact dst.not_pair_of_stamped
      | stamp a e o => exact hnst a e o rfl
      | _ => trivial
    rcases Deriv.neutral_head hS s dst hns hsi with ⟨i, A₀, hΓi, -⟩ | ⟨i, k, T, hc, hdesc⟩ |
        ⟨g', Δ', σ', A', B', hg', -⟩
    · obtain ⟨h, -⟩ := hctx _ (List.mem_of_getElem? hΓi)
      rcases h with h | h <;> cases h
    · rcases const_desc hS hc hdesc with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · cases h
      · cases h
    · rcases (hS.gate_cond hg').2.1 with h | h <;> cases h
  | @node Γ' g ℓ ds t e Δ σ A ρ' B C' δ θ η γ ε' hg dds dt de hCeq _ _ _ _ _ _ _ =>
    cases hj
    refine ⟨?_, ?_⟩
    · obtain ⟨-, -, -, -, hBg⟩ := hS.gate_cond hg
      obtain ⟨-, β, ⟨dB⟩⟩ := hS.gate_formed hg
      rw [hCeq, (gskel_instType dB.tyShape_ty _ _).1]
      exact gskel_gf hBg
    · intro p hp hno
      simp only [Deriv.paths] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exfalso
        rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_append.mp hp with hp | hp
          · obtain ⟨p', -, rfl⟩ := mem_map_via hp
            exact hno _ (List.mem_cons_self ..) ⟨g, ℓ, rfl, rfl⟩
          · obtain ⟨p', -, rfl⟩ := mem_map_via hp
            exact hno _ (List.mem_cons_self ..) ⟨g, ℓ, rfl, rfl⟩
        · obtain ⟨p', -, rfl⟩ := mem_map_via hp
          exact hno _ (List.mem_cons_self ..) ⟨g, ℓ, rfl, rfl⟩
  | @conv Γ' ρ' t A B θ γ dt hAB dB iht _ =>
    cases hj
    obtain ⟨γ', hA⟩ := dt.tm_ty
    have hsk : gskel A = gskel B := gskel_conv hAB (TyShape.of_ty hA) dB.tyShape_ty
    obtain ⟨hAgf, hp⟩ := iht hn hρ hctx (hC.imp (fun h => hsk ▸ h) id) rfl
    exact ⟨hsk ▸ hAgf, hp⟩
  | tyFam | tyEvent | tyOrigin | tyStamped | tyPi | tySigma | spineNil | spineCons | telNil
    | telCons => cases hj

/-! ## Lemma 9.4: grade-free normal-form mediation -/

/-- **Lemma 9.4** (grade-free normal-form mediation). Let `n` be a normal term
of a grade-free type at a protected role `ρ`, closed or in a context whose
variables have protected roles and grade-free types. Every path of its
derivation from an atom of policy demand `1` enters a private node, live or
not; and no atom of demand `∞` has a live path. -/
theorem Deriv.gradefree_mediation {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {n C : Exp}
    {ε : Eff} (d : Deriv S true (.tm Γ ρ n C ε)) (hn : Normal n)
    (hρ : ρ = .form ∨ ρ = .presentation) (hctx : CtxGF Γ) (hC : (gskel C).GF)
    {p : Path} (hp : p ∈ d.paths) {σ : Role} (hσ : roleOf S Γ p.atom = some σ) :
    (demand σ ρ = .gated → ∃ e ∈ p.edges, e.kind.IsNode) ∧
    (demand σ ρ = .absent → ¬p.cost < ⊤) := by
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · by_contra hno
    have hno' : ∀ e ∈ p.edges, ¬e.kind.IsNode := fun e he hn' => hno ⟨e, he, hn'⟩
    have h0 := (d.free_outside_nodes hS hn hρ hctx (.inl hC)).2 p hp hno'
    have hle := d.demand_le_cost (ρ := ρ) rfl hp hσ
    rw [hd, h0] at hle
    exact absurd hle (by decide)
  · have := ((d.mediation (ρ := ρ) rfl hp hσ).2 hd).1
    rw [this]; exact lt_irrefl _

/-! ## Lemma 9.2: positive-function realization -/

/-- **Lemma 9.2** (positive-function realization). A closed normal term of type
`Π^1(x :_σ A). B` is a lambda `λ^1(x :_σ A'). b` with `A'` convertible to `A`.
In every derivation of its body the parameter has grade `1` or `∞`, and grade
`1` when it lies on a live path of the body. Applied to an argument of effect
`η`, the function reduces in one step to the instantiated body, whose effect
is `θ ∖ x ⊕ θ(x) ⊗ η`: the argument enters through the gated body paths or
not at all. -/
theorem positive_function {S : Sig} (hS : SigWF S) {ρ σ : Role} {t A B : Exp} {ε : Eff}
    (d : Deriv S true (.tm [] ρ t (.pi .gated σ A B) ε)) (hn : Normal t) :
    ∃ A' b, t = .lam .gated σ A' b ∧ ∃ B' θ, Conv (.pi .gated σ A' B') (.pi .gated σ A B) ∧
      ∃ db : Deriv S true (.tm [(σ, A')] ρ b B' θ),
        (θ (.var 0) = .gated ∨ θ (.var 0) = .absent) ∧
        (∀ p ∈ db.paths, p.atom = .var 0 → p.cost < ⊤ → θ (.var 0) = .gated) ∧
        ∀ u η, Deriv S true (.tm [] σ u A' η) →
          Step (.app t u) (b.inst u) ∧
          Derivable S true (.tm [] ρ (b.inst u) (B'.inst u)
            (θ.unbind ⊓ Eff.scale (θ (.var 0)) η)) := by
  obtain ⟨A', b, rfl⟩ := canonical_lam hS d hn (by decide)
  obtain ⟨B', θ, hconv, hq, -, -, ⟨db⟩, -⟩ := d.inv_lam
  refine ⟨A', b, rfl, B', θ, hconv, db, ?_, ?_, ?_⟩
  · revert hq; cases θ (.var 0) <;> decide
  · intro p hp hz hlive
    have hle : θ (.var 0) ≤ p.cost := by
      have h := pathEff_le hp
      rw [← db.eff_eq_pathEff, hz] at h
      exact h
    revert hq hle hlive; cases θ (.var 0) <;> cases p.cost <;> decide
  · intro u η du
    exact ⟨.beta, db.inst_tm hS (.nil hS) du⟩

end Artform.Roles.Calculus
