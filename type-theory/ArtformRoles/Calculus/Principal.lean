import ArtformRoles.Calculus.Skeleton

/-!
# Role functionality and principal effects

* Lemma 6.2 (role functionality): a type has at most one admissible outer role
  (`Deriv.role_unique`), and the role of a term judgment is the outer role of
  its type (`Deriv.tm_role`).
* Generation lemmas: inversion of every term rule through any chain of
  conversions (`Deriv.inv_var`, …, `Deriv.inv_node`).
* The graded skeleton of a term's type is unique (`Deriv.gskel_unique`): the
  types of a term may differ (a pair has many dependent sum types), but never
  in a former, a role or a grade.
* Theorem 8.2, uniqueness: the effect of a typable expression is unique
  (`Deriv.effect_unique`, `Deriv.spine_effect_unique`, `Deriv.ty_effect_unique`),
  and an explicit lambda grade is accepted exactly when
  `D(σ, ρ) ≤ q ≤ θ(x)` (`lam_grade_iff`).
-/

namespace Artform.Roles.Calculus

open Exp

/-- Lemma 6.2: every well-formed type has exactly one admissible outer role. -/
theorem Deriv.role_unique {S : Sig} {acc acc' : Bool} {Γ : Ctx} {A : Exp} {ρ ρ' : Role}
    {α α' : Eff} (d : Deriv S acc (.ty Γ ρ A α)) (d' : Deriv S acc' (.ty Γ ρ' A α')) :
    ρ = ρ' := by
  induction A generalizing Γ ρ ρ' α α' with
  | fam a args =>
    cases d with
    | tyFam h₁ =>
      cases d' with
      | tyFam h₂ => rw [h₁] at h₂; cases h₂; rfl
  | event => cases d; cases d'; rfl
  | origin => cases d; cases d'; rfl
  | stamped => cases d; cases d'; rfl
  | pi q σ A B _ ihB =>
    cases d with
    | tyPi _ dB =>
      cases d' with
      | tyPi _ dB' => exact ihB dB dB'
  | sigma ρ₀ A B =>
    cases d; cases d'; rfl
  | _ => cases d

/-- The role of a term judgment is the outer role of its type. -/
theorem Deriv.tm_role {S : Sig} {acc acc' : Bool} {Γ : Ctx} {t A : Exp} {ρ ρ' : Role}
    {ε α : Eff} (d : Deriv S acc (.tm Γ ρ t A ε)) (dA : Deriv S acc' (.ty Γ ρ' A α)) :
    ρ = ρ' := by
  obtain ⟨γ, ⟨dA'⟩⟩ := d.tm_ty
  exact dA'.role_unique dA

/-! ## Generation lemmas -/

section Generation

variable {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff}

theorem Deriv.inv_var {i : ℕ} (d : Deriv S acc (.tm Γ ρ (.var i) C ε)) :
    ∃ A₀, Γ[i]? = some (ρ, A₀) ∧ Conv (A₀.ren (· + (i + 1))) C ∧ ε = Eff.unit (.var i) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ (A₀.ren (· + (i + 1))) γ) := by
  generalize hj : Judg.tm Γ ρ (.var i) C ε = j at d
  induction d generalizing C with
  | var hΓ hC dC hε _ =>
    cases hj; subst hC
    exact ⟨_, hΓ, Conv.refl _, hε, _, ⟨dC⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨A₀, h₁, hc, h₂, h₃⟩ := iht rfl
    exact ⟨A₀, h₁, hc.trans hAB, h₂, h₃⟩
  | _ => cases hj

theorem Deriv.inv_const {i k : ℕ} (d : Deriv S acc (.tm Γ ρ (.const i k) C ε)) :
    ∃ A₀, S.const? i k = some (ρ, A₀) ∧ Conv A₀ C ∧ ε = Eff.unit (.decl i k) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ A₀ γ) := by
  generalize hj : Judg.tm Γ ρ (.const i k) C ε = j at d
  induction d generalizing C with
  | const hc dA hε _ =>
    cases hj
    exact ⟨_, hc, Conv.refl _, hε, _, ⟨dA⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨A₀, h₁, hc, h₂, h₃⟩ := iht rfl
    exact ⟨A₀, h₁, hc.trans hAB, h₂, h₃⟩
  | _ => cases hj

theorem Deriv.inv_app {f u : Exp} (d : Deriv S acc (.tm Γ ρ (.app f u) C ε)) :
    ∃ q σ A B φ η, Conv (B.inst u) C ∧ ε = φ ⊓ Eff.scale q η ∧
      Derivable S acc (.tm Γ ρ f (.pi q σ A B) φ) ∧ Derivable S acc (.tm Γ σ u A η) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ (B.inst u) γ) := by
  generalize hj : Judg.tm Γ ρ (.app f u) C ε = j at d
  induction d generalizing C with
  | app df du hC dC hε _ =>
    cases hj; subst hC
    exact ⟨_, _, _, _, _, _, Conv.refl _, hε, ⟨df⟩, ⟨du⟩, _, ⟨dC⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨q, σ, A, B, φ, η, hc, h₁, h₂, h₃, h₄⟩ := iht rfl
    exact ⟨q, σ, A, B, φ, η, hc.trans hAB, h₁, h₂, h₃, h₄⟩
  | _ => cases hj

theorem Deriv.inv_fst {p : Exp} (d : Deriv S acc (.tm Γ ρ (.fst p) C ε)) :
    ∃ A B, Conv A C ∧ Derivable S acc (.tm Γ ρ p (.sigma ρ A B) ε) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ A γ) := by
  generalize hj : Judg.tm Γ ρ (.fst p) C ε = j at d
  induction d generalizing C with
  | fst dp dA _ =>
    cases hj
    exact ⟨_, _, Conv.refl _, ⟨dp⟩, _, ⟨dA⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨A, B, hc, h₁, h₂⟩ := iht rfl
    exact ⟨A, B, hc.trans hAB, h₁, h₂⟩
  | _ => cases hj

theorem Deriv.inv_snd {p : Exp} (d : Deriv S acc (.tm Γ ρ (.snd p) C ε)) :
    ∃ A B, Conv (B.inst (.fst p)) C ∧ Derivable S acc (.tm Γ ρ p (.sigma ρ A B) ε) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ (B.inst (.fst p)) γ) := by
  generalize hj : Judg.tm Γ ρ (.snd p) C ε = j at d
  induction d generalizing C with
  | snd dp hC dC _ =>
    cases hj; subst hC
    exact ⟨_, _, Conv.refl _, ⟨dp⟩, _, ⟨dC⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨A, B, hc, h₁, h₂⟩ := iht rfl
    exact ⟨A, B, hc.trans hAB, h₁, h₂⟩
  | _ => cases hj

theorem Deriv.inv_gate {g : ℕ} {ds s : Exp} (d : Deriv S acc (.tm Γ ρ (.gate g ds s) C ε)) :
    ∃ Δ σ A B δ η, S.gate? g = some (Δ, σ, A, ρ, B) ∧ Conv (instType ds Δ B) C ∧
      ε = Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated η ∧
      Derivable S acc (.spine Γ ds Δ δ) ∧
      Derivable S acc (.tm Γ .witness s (.stamped σ (instType ds Δ A)) η) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ (instType ds Δ B) γ) := by
  generalize hj : Judg.tm Γ ρ (.gate g ds s) C ε = j at d
  induction d generalizing C with
  | gate hg dds dst hC dC hε _ =>
    cases hj; subst hC
    exact ⟨_, _, _, _, _, _, hg, Conv.refl _, hε, ⟨dds⟩, ⟨dst⟩, _, ⟨dC⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨Δ, σ, A, B, δ, η, h₀, hc, h₁, h₂, h₃, h₄⟩ := iht rfl
    exact ⟨Δ, σ, A, B, δ, η, h₀, hc.trans hAB, h₁, h₂, h₃, h₄⟩
  | _ => cases hj

theorem Deriv.inv_node {g ℓ : ℕ} {ds t e : Exp}
    (d : Deriv S acc (.tm Γ ρ (.node g ℓ ds t e) C ε)) :
    ∃ Δ σ A B δ θ η, S.gate? g = some (Δ, σ, A, ρ, B) ∧ Conv (instType ds Δ B) C ∧
      ε = Eff.unit (.decl g 0) ⊓ δ ⊓ Eff.scale .gated (θ ⊓ η) ∧
      Derivable S acc (.spine Γ ds Δ δ) ∧ Derivable S acc (.tm Γ σ t (instType ds Δ A) θ) ∧
      Derivable S acc (.tm Γ .witness e .event η) ∧
      ∃ γ, Derivable S acc (.ty Γ ρ (instType ds Δ B) γ) := by
  generalize hj : Judg.tm Γ ρ (.node g ℓ ds t e) C ε = j at d
  induction d generalizing C with
  | node hg dds dt de hC dC hε _ =>
    cases hj; subst hC
    exact ⟨_, _, _, _, _, _, _, hg, Conv.refl _, hε, ⟨dds⟩, ⟨dt⟩, ⟨de⟩, _, ⟨dC⟩⟩
  | conv _ hAB _ iht _ =>
    cases hj
    obtain ⟨Δ, σ, A, B, δ, θ, η, h₀, hc, h₁, h₂, h₃, h₄, h₅⟩ := iht rfl
    exact ⟨Δ, σ, A, B, δ, θ, η, h₀, hc.trans hAB, h₁, h₂, h₃, h₄, h₅⟩
  | _ => cases hj

/-- The heads of terms: the subject of every term judgment has one. -/
def Exp.IsTermHead : Exp → Prop
  | .var _ | .const .. | .lam .. | .app .. | .pair .. | .fst _ | .snd _ | .stamp ..
  | .gate .. | .node .. => True
  | _ => False

theorem Deriv.termHead {j : Judg} (d : Deriv S acc j) :
    match j with
    | .tm _ _ t _ _ => t.IsTermHead
    | _ => True := by
  induction d with
  | conv _ _ _ ih _ => exact ih
  | _ => trivial

theorem Deriv.isTermHead {t : Exp} (d : Deriv S acc (.tm Γ ρ t C ε)) : t.IsTermHead :=
  d.termHead

end Generation

/-! ## Unique skeletons and effects -/

theorem Exp.TyShape.of_ty {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp} {α : Eff}
    (h : Derivable S acc (.ty Γ ρ A α)) : A.TyShape := let ⟨d⟩ := h; d.tyShape_ty

theorem Exp.TyShape.of_ex {S : Sig} {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp}
    (h : ∃ α, Derivable S acc (.ty Γ ρ A α)) : A.TyShape :=
  let ⟨_, ⟨d⟩⟩ := h; d.tyShape_ty

/-- The types of a term have one graded skeleton, and the term one role: its types
never differ in a former, a role or a grade. -/
theorem Deriv.gskel_unique {S : Sig} {acc acc' : Bool} :
    ∀ (t : Exp) {Γ : Ctx} {ρ ρ' : Role} {A A' : Exp} {ε ε' : Eff},
      Deriv S acc (.tm Γ ρ t A ε) → Deriv S acc' (.tm Γ ρ' t A' ε') →
        gskel A = gskel A' ∧ ρ = ρ' := by
  intro t
  induction t with
  | var i =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨A₀, h₁, hc, -, hf⟩ := d.inv_var
    obtain ⟨A₀', h₁', hc', -, hf'⟩ := d'.inv_var
    rw [h₁] at h₁'; cases h₁'
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    refine ⟨?_, rfl⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
  | const i k =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨A₀, h₁, hc, -, hf⟩ := d.inv_const
    obtain ⟨A₀', h₁', hc', -, hf'⟩ := d'.inv_const
    rw [h₁] at h₁'; cases h₁'
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    refine ⟨?_, rfl⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
  | lam q σ A₀ b _ ihb =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨B, θ, hc, -, -, -, ⟨db⟩, hf⟩ := d.inv_lam
    obtain ⟨B', θ', hc', -, -, -, ⟨db'⟩, hf'⟩ := d'.inv_lam
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨hB, hρ⟩ := ihb db db'
    refine ⟨?_, hρ⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    simp only [gskel, hB]
  | app f u ihf _ =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨q, σ, A₁, B, φ, η, hc, -, ⟨df⟩, -, hf⟩ := d.inv_app
    obtain ⟨q', σ', A₁', B', φ', η', hc', -, ⟨df'⟩, -, hf'⟩ := d'.inv_app
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨h, hρ⟩ := ihf df df'
    refine ⟨?_, hρ⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    obtain ⟨γf, ⟨dpi⟩⟩ := df.tm_ty
    obtain ⟨γf', ⟨dpi'⟩⟩ := df'.tm_ty
    have hB := dpi.tyShape_ty.2
    have hB' := dpi'.tyShape_ty.2
    simp only [gskel, GSkel.arr.injEq] at h
    rw [(gskel_subst hB _).1, (gskel_subst hB' _).1, h.2.2.2]
  | pair t u iht ihu =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨A₁, B, θ, η, hc, -, ⟨dt⟩, ⟨du⟩, hf⟩ := d.inv_pair
    obtain ⟨A₁', B', θ', η', hc', -, ⟨dt'⟩, ⟨du'⟩, hf'⟩ := d'.inv_pair
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨h₁, hρ⟩ := iht dt dt'
    obtain ⟨h₂, -⟩ := ihu du du'
    refine ⟨?_, hρ⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    have hs := TyShape.of_ex hf
    have hs' := TyShape.of_ex hf'
    rw [(gskel_subst hs.2 _).1, (gskel_subst hs'.2 _).1] at h₂
    simp only [gskel, h₁, h₂, hρ]
  | fst p ihp =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨A₁, B, hc, ⟨dp⟩, hf⟩ := d.inv_fst
    obtain ⟨A₁', B', hc', ⟨dp'⟩, hf'⟩ := d'.inv_fst
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨h, hρ⟩ := ihp dp dp'
    refine ⟨?_, hρ⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    simp only [gskel, GSkel.prod.injEq] at h
    exact h.2.1
  | snd p ihp =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨A₁, B, hc, ⟨dp⟩, hf⟩ := d.inv_snd
    obtain ⟨A₁', B', hc', ⟨dp'⟩, hf'⟩ := d'.inv_snd
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨h, hρ⟩ := ihp dp dp'
    refine ⟨?_, hρ⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    obtain ⟨γp, ⟨ds⟩⟩ := dp.tm_ty
    obtain ⟨γp', ⟨ds'⟩⟩ := dp'.tm_ty
    simp only [gskel, GSkel.prod.injEq] at h
    rw [(gskel_subst ds.tyShape_ty.2 _).1, (gskel_subst ds'.tyShape_ty.2 _).1]
    exact h.2.2
  | stamp t e o iht _ _ =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨σ, A₁, θ, η, ω, hρ, hc, -, ⟨dt⟩, -, -, hf⟩ := d.inv_stamp
    obtain ⟨σ', A₁', θ', η', ω', hρ', hc', -, ⟨dt'⟩, -, -, hf'⟩ := d'.inv_stamp
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    obtain ⟨h, hσ⟩ := iht dt dt'
    refine ⟨?_, hρ.trans hρ'.symm⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
    simp only [gskel, h, hσ]
  | gate g ds s _ _ =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨Δ, σ, A₁, B, δ, η, hg, hc, -, -, -, hf⟩ := d.inv_gate
    obtain ⟨Δ', σ', A₁', B', δ', η', hg', hc', -, -, -, hf'⟩ := d'.inv_gate
    rw [hg] at hg'; cases hg'
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    refine ⟨?_, rfl⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
  | node g ℓ ds t e _ _ _ =>
    intro Γ ρ ρ' A A' ε ε' d d'
    obtain ⟨Δ, σ, A₁, B, δ, θ, η, hg, hc, -, -, -, -, hf⟩ := d.inv_node
    obtain ⟨Δ', σ', A₁', B', δ', θ', η', hg', hc', -, -, -, -, hf'⟩ := d'.inv_node
    rw [hg] at hg'; cases hg'
    obtain ⟨γ, hA⟩ := d.tm_ty
    obtain ⟨γ', hA'⟩ := d'.tm_ty
    refine ⟨?_, rfl⟩
    rw [← gskel_conv hc (TyShape.of_ex hf) (TyShape.of_ty hA),
      ← gskel_conv hc' (TyShape.of_ex hf') (TyShape.of_ty hA')]
  | fam | event | origin | stamped | pi | sigma | nil | cons =>
    intro Γ ρ ρ' A A' ε ε' d d'
    exact d.isTermHead.elim

/-- Theorem 8.2 (uniqueness): the effect of a typable term, and of a typable
argument list, is unique. -/
theorem Deriv.effect_unique' {S : Sig} {acc acc' : Bool} :
    ∀ (t : Exp),
      (∀ {Γ : Ctx} {ρ ρ' : Role} {A A' : Exp} {ε ε' : Eff},
        Deriv S acc (.tm Γ ρ t A ε) → Deriv S acc' (.tm Γ ρ' t A' ε') → ε = ε') ∧
      (∀ {Γ : Ctx} {Δ Δ' : Tel} {δ δ' : Eff},
        Deriv S acc (.spine Γ t Δ δ) → Deriv S acc' (.spine Γ t Δ' δ') → δ = δ') := by
  intro t
  induction t with
  | var i =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨-, -, -, h, -⟩ := d.inv_var
    obtain ⟨-, -, -, h', -⟩ := d'.inv_var
    rw [h, h']
  | const i k =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨-, -, -, h, -⟩ := d.inv_const
    obtain ⟨-, -, -, h', -⟩ := d'.inv_const
    rw [h, h']
  | lam q σ A₀ b _ ihb =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨B, θ, -, -, h, -, ⟨db⟩, -⟩ := d.inv_lam
    obtain ⟨B', θ', -, -, h', -, ⟨db'⟩, -⟩ := d'.inv_lam
    rw [h, h', ihb.1 db db']
  | app f u ihf ihu =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨q, σ, A₁, B, φ, η, -, h, ⟨df⟩, ⟨du⟩, -⟩ := d.inv_app
    obtain ⟨q', σ', A₁', B', φ', η', -, h', ⟨df'⟩, ⟨du'⟩, -⟩ := d'.inv_app
    have hq := (Deriv.gskel_unique f df df').1
    simp only [gskel, GSkel.arr.injEq] at hq
    rw [h, h', ihf.1 df df', ihu.1 du du', hq.1]
  | pair a b iha ihb =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨A₁, B, θ, η, -, h, ⟨da⟩, ⟨db⟩, -⟩ := d.inv_pair
    obtain ⟨A₁', B', θ', η', -, h', ⟨da'⟩, ⟨db'⟩, -⟩ := d'.inv_pair
    rw [h, h', iha.1 da da', ihb.1 db db']
  | fst p ihp =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨A₁, B, -, ⟨dp⟩, -⟩ := d.inv_fst
    obtain ⟨A₁', B', -, ⟨dp'⟩, -⟩ := d'.inv_fst
    exact ihp.1 dp dp'
  | snd p ihp =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨A₁, B, -, ⟨dp⟩, -⟩ := d.inv_snd
    obtain ⟨A₁', B', -, ⟨dp'⟩, -⟩ := d'.inv_snd
    exact ihp.1 dp dp'
  | stamp a e o iha ihe iho =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨σ, A₁, θ, η, ω, -, -, h, ⟨da⟩, ⟨de⟩, ⟨dorg⟩, -⟩ := d.inv_stamp
    obtain ⟨σ', A₁', θ', η', ω', -, -, h', ⟨da'⟩, ⟨de'⟩, ⟨dorg'⟩, -⟩ := d'.inv_stamp
    rw [h, h', iha.1 da da', ihe.1 de de', iho.1 dorg dorg']
  | gate g ds s ihds ihs =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨Δ, σ, A₁, B, δ, η, -, -, h, ⟨dds⟩, ⟨dst⟩, -⟩ := d.inv_gate
    obtain ⟨Δ', σ', A₁', B', δ', η', -, -, h', ⟨dds'⟩, ⟨dst'⟩, -⟩ := d'.inv_gate
    rw [h, h', ihds.2 dds dds', ihs.1 dst dst']
  | node g ℓ ds a e ihds iha ihe =>
    refine ⟨fun d d' => ?_, fun d _ => by cases d⟩
    obtain ⟨Δ, σ, A₁, B, δ, θ, η, -, -, h, ⟨dds⟩, ⟨da⟩, ⟨de⟩, -⟩ := d.inv_node
    obtain ⟨Δ', σ', A₁', B', δ', θ', η', -, -, h', ⟨dds'⟩, ⟨da'⟩, ⟨de'⟩, -⟩ := d'.inv_node
    rw [h, h', ihds.2 dds dds', iha.1 da da', ihe.1 de de']
  | nil =>
    refine ⟨fun d _ => d.isTermHead.elim, fun d d' => ?_⟩
    cases d with
    | spineNil h => cases d' with
      | spineNil h' => rw [h, h']
  | cons a b iha ihb =>
    refine ⟨fun d _ => d.isTermHead.elim, fun d d' => ?_⟩
    cases d with
    | spineCons da db h => cases d' with
      | spineCons da' db' h' => rw [h, h', iha.1 da da', ihb.2 db db']
  | fam | event | origin | stamped | pi | sigma =>
    exact ⟨fun d _ => d.isTermHead.elim, fun d _ => by cases d⟩

/-- Theorem 8.2: the effect of a typable term is unique. -/
theorem Deriv.effect_unique {S : Sig} {acc acc' : Bool} {Γ : Ctx} {ρ ρ' : Role} {t A A' : Exp}
    {ε ε' : Eff} (d : Deriv S acc (.tm Γ ρ t A ε)) (d' : Deriv S acc' (.tm Γ ρ' t A' ε')) :
    ε = ε' :=
  (Deriv.effect_unique' t).1 d d'

/-- Theorem 8.2: the effect of a typable argument list is unique. -/
theorem Deriv.spine_effect_unique {S : Sig} {acc acc' : Bool} {Γ : Ctx} {ts : Exp}
    {Δ Δ' : Tel} {δ δ' : Eff} (d : Deriv S acc (.spine Γ ts Δ δ))
    (d' : Deriv S acc' (.spine Γ ts Δ' δ')) : δ = δ' :=
  (Deriv.effect_unique' ts).2 d d'

/-- Theorem 8.2: the effect of a well-formed type is unique. -/
theorem Deriv.ty_effect_unique {S : Sig} {acc acc' : Bool} :
    ∀ (A : Exp) {Γ : Ctx} {ρ ρ' : Role} {α α' : Eff},
      Deriv S acc (.ty Γ ρ A α) → Deriv S acc' (.ty Γ ρ' A α') → α = α' := by
  intro A
  induction A with
  | fam a args =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tyFam _ dargs h => cases d' with
      | tyFam _ dargs' h' => rw [h, h', Deriv.spine_effect_unique dargs dargs']
  | event =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tyEvent h => cases d' with
      | tyEvent h' => rw [h, h']
  | origin A₀ e t ihA _ _ =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tyOrigin dA de dt h => cases d' with
      | tyOrigin dA' de' dt' h' =>
        rw [h, h', ihA dA dA', Deriv.effect_unique de de', Deriv.effect_unique dt dt']
  | stamped σ A₀ ih =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tyStamped dA _ h => cases d' with
      | tyStamped dA' _ h' => rw [h, h', ih dA dA']
  | pi q σ A₀ B ihA ihB =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tyPi dA dB _ h => cases d' with
      | tyPi dA' dB' _ h' => rw [h, h', ihA dA dA', ihB dB dB']
  | sigma ρ₀ A₀ B ihA ihB =>
    intro Γ ρ ρ' α α' d d'
    cases d with
    | tySigma dA dB h => cases d' with
      | tySigma dA' dB' h' => rw [h, h', ihA dA dA', ihB dB dB']
  | _ =>
    intro Γ ρ ρ' α α' d d'
    cases d

/-- The restriction of a valid effect is valid in the smaller context. -/
theorem Valid.unbind {S : Sig} {Γ : Ctx} {σ ρ : Role} {A : Exp} {θ : Eff}
    (h : Valid S ((σ, A) :: Γ) ρ θ) : Valid S Γ ρ θ.unbind := by
  intro z r hz
  cases z with
  | var i => exact h (.var (i + 1)) r (by simpa [roleOf] using hz)
  | decl a k => exact h (.decl a k) r hz

/-- The maximal grade `θ(x)` is admissible: a valid body uses its parameter at
least as the binder policy demands. -/
theorem lam_max_grade {S : Sig} {Γ : Ctx} {σ ρ : Role} {A : Exp} {θ : Eff}
    (h : Valid S ((σ, A) :: Γ) ρ θ) : demand σ ρ ≤ θ (.var 0) :=
  h (.var 0) σ (by simp [roleOf])

/-- Theorem 8.2: an explicit lambda grade is accepted exactly when
`D(σ, ρ) ≤ q ≤ θ(x)`, where `θ` is the principal effect of the body. -/
theorem lam_grade_iff {S : Sig} {Γ : Ctx} {σ ρ : Role} {A B t : Exp} {θ α β : Eff}
    (dA : Deriv S true (.ty Γ σ A α)) (dB : Deriv S true (.ty ((σ, A) :: Γ) ρ B β))
    (dt : Deriv S true (.tm ((σ, A) :: Γ) ρ t B θ)) (q : Grade) :
    (∃ ε, Derivable S true (.tm Γ ρ (.lam q σ A t) (.pi q σ A B) ε)) ↔
      demand σ ρ ≤ q ∧ q ≤ θ (.var 0) := by
  constructor
  · rintro ⟨ε, ⟨d⟩⟩
    obtain ⟨B', θ', -, hq, -, -, ⟨dt'⟩, γ, ⟨dpi⟩⟩ := d.inv_lam
    cases dpi with
    | tyPi _ _ hD _ _ =>
      refine ⟨hD, ?_⟩
      rw [Deriv.effect_unique dt dt']
      exact hq
  · rintro ⟨hD, hq⟩
    have hvα := dA.valid_ty
    have hvβ := dB.valid_ty
    have hvθ := dt.valid_tm
    have hpi : Valid S Γ ρ (Eff.scale q α ⊓ β.unbind) := by
      refine Valid.inf (fun z r hz => ?_) hvβ.unbind
      calc demand r ρ ≤ demand r σ ⊔ demand σ ρ := demand_pathClosed r σ ρ
        _ ≤ α z ⊔ q := sup_le_sup (hvα z r hz) hD
        _ = q ⊔ α z := sup_comm _ _
    exact ⟨_, ⟨.lam dA dt hq (.tyPi dA dB hD rfl (fun _ => hpi)) rfl
      (fun _ => hvθ.unbind)⟩⟩

end Artform.Roles.Calculus
