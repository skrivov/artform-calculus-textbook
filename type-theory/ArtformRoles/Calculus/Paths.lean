import ArtformRoles.Calculus.Canonical

/-!
# Effects as path semantics

§8.1 (Lemma 8.1) and §9.1 (Theorem 9.1, path mediation) of the paper.

Every effect-bearing premise of a rule is an edge, labelled by the coefficient
in its effect equation: ordinary computational premises have grade `0`, the
domain of Ty-Pi and the argument of App have the latent grade `q`, and the
credential of a gate and the payload and event of a node have grade `1`.
Formation premises that only validate a displayed type carry no path, and
conversion adds no edge. Binders delete the paths that begin at their bound
variable.

`Deriv.paths d` lists the paths of a derivation from an atom occurrence to the
root. Each edge records its grade, its kind, and the child of the expression it
enters. The kinds name the gate or node an edge enters, with the node's label,
so that a path says which private node it passes through. The cost of a path is
the maximum of its grades; a path is live when its cost is below `∞`.

* Lemma 8.1 (path characterization): `Deriv.eff_eq_pathEff`; the effect of a
  derivation is, at each atom, the minimum cost of the paths from that atom.
* Theorem 9.1 (path mediation): `Deriv.mediation`.
-/

namespace Artform.Roles.Calculus

open Exp

/-- The kinds of effect edges. -/
inductive EdgeKind
  /-- An ordinary computational premise. -/
  | ord
  /-- The domain of a dependent function type, at its grade. -/
  | piDom
  /-- The argument of an application, at the latent grade of the function. -/
  | appArg
  /-- The parameters of the gate `g`. -/
  | gateArgs (g : ℕ)
  /-- The credential of the gate `g`. -/
  | gateCred (g : ℕ)
  /-- The parameters of a node of the gate `g` with label `ℓ`. -/
  | nodeArgs (g ℓ : ℕ)
  /-- The payload of a node of the gate `g` with label `ℓ`. -/
  | nodePayload (g ℓ : ℕ)
  /-- The event of a node of the gate `g` with label `ℓ`. -/
  | nodeEvent (g ℓ : ℕ)
  deriving DecidableEq, Repr

/-- An edge: its grade, its kind, and the child of the expression it enters. -/
structure Edge where
  grade : Grade
  kind : EdgeKind
  child : ℕ
  deriving DecidableEq, Repr

/-- The edge enters a private node of the gate `g` with label `ℓ`. -/
def EdgeKind.InNode (g ℓ : ℕ) : EdgeKind → Prop
  | .nodeArgs g' ℓ' | .nodePayload g' ℓ' | .nodeEvent g' ℓ' => g' = g ∧ ℓ' = ℓ
  | _ => False

/-- The edge enters some private node. -/
def EdgeKind.IsNode (k : EdgeKind) : Prop := ∃ g ℓ, k.InNode g ℓ

/-- The grade an edge of this kind has in a derivation: `0` for ordinary and
parameter premises, `1` for credentials, payloads and events, and the latent
grade (any grade) for the domain of Ty-Pi and the argument of App. -/
def EdgeKind.GradeOK : EdgeKind → Grade → Prop
  | .ord, q | .gateArgs _, q | .nodeArgs _ _, q => q = ⊥
  | .gateCred _, q | .nodePayload _ _, q | .nodeEvent _ _, q => q = .gated
  | .piDom, _ | .appArg, _ => True

/-- A path from an atom occurrence to the root; its edges are listed from the
root down. -/
structure Path where
  atom : Atom
  edges : List Edge
  deriving DecidableEq, Repr

namespace Path

/-- The cost of a path: the maximum of its grades, `0` when it has no edge. -/
def cost (p : Path) : Grade := p.edges.foldr (fun e c => e.grade ⊔ c) ⊥

/-- The position of the path's atom occurrence, as the list of children. -/
def pos (p : Path) : List ℕ := p.edges.map Edge.child

/-- Extend a path by one edge at the root. -/
def via (e : Edge) (p : Path) : Path := ⟨p.atom, e :: p.edges⟩

/-- The path seen outside a binder: deleted when it starts at the bound
variable, its variable renumbered otherwise. -/
def unbind? : Path → Option Path
  | ⟨.var 0, _⟩ => none
  | ⟨.var (i + 1), es⟩ => some ⟨.var i, es⟩
  | ⟨.decl a k, es⟩ => some ⟨.decl a k, es⟩

/-- The effect of one path: its cost at its atom, `∞` elsewhere. -/
def eff (p : Path) : Eff := fun z => if p.atom = z then p.cost else ⊤

@[simp] theorem atom_via (e : Edge) (p : Path) : (p.via e).atom = p.atom := rfl

@[simp] theorem edges_via (e : Edge) (p : Path) : (p.via e).edges = e :: p.edges := rfl

@[simp] theorem cost_via (e : Edge) (p : Path) : (p.via e).cost = e.grade ⊔ p.cost := rfl

theorem eff_via (e : Edge) (p : Path) : (p.via e).eff = Eff.scale e.grade p.eff := by
  funext z
  change (if p.atom = z then e.grade ⊔ p.cost else ⊤) =
    e.grade ⊔ (if p.atom = z then p.cost else ⊤)
  split_ifs <;> simp

/-- The cost of a path is the grade of one of its edges, or `0`. -/
theorem cost_mem (p : Path) : p.cost = ⊥ ∨ ∃ e ∈ p.edges, e.grade = p.cost := by
  obtain ⟨a, es⟩ := p
  induction es with
  | nil => exact .inl rfl
  | cons e es ih =>
    change e.grade ⊔ Path.cost ⟨a, es⟩ = ⊥ ∨
      ∃ e' ∈ e :: es, e'.grade = e.grade ⊔ Path.cost ⟨a, es⟩
    rcases le_total e.grade (Path.cost ⟨a, es⟩) with h | h
    · rw [sup_eq_right.mpr h]
      rcases ih with h' | ⟨e', he', h'⟩
      · exact .inl h'
      · exact .inr ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · rw [sup_eq_left.mpr h]
      exact .inr ⟨e, List.mem_cons_self .., rfl⟩

theorem grade_le_cost {p : Path} {e : Edge} (he : e ∈ p.edges) : e.grade ≤ p.cost := by
  obtain ⟨a, es⟩ := p
  induction es with
  | nil => cases he
  | cons e' es ih =>
    change e.grade ≤ e'.grade ⊔ Path.cost ⟨a, es⟩
    rcases List.mem_cons.mp he with rfl | h
    · exact le_sup_left
    · exact le_sup_of_le_right (ih h)

end Path

/-- The paths seen outside a binder. -/
def unbindPaths (ps : List Path) : List Path := ps.filterMap Path.unbind?

/-- The ordinary edge into child `i`. -/
def ordE (i : ℕ) : Edge := ⟨⊥, .ord, i⟩

/-- The paths of a derivation, listed rule by rule. -/
def Deriv.paths {S : Sig} {acc : Bool} : {j : Judg} → Deriv S acc j → List Path
  | _, .tyFam (a := a) _ dargs _ _ => ⟨.decl a 0, []⟩ :: dargs.paths.map (·.via (ordE 0))
  | _, .tyEvent _ => []
  | _, .tyOrigin dA de dt _ _ =>
    dA.paths.map (·.via (ordE 0)) ++ de.paths.map (·.via (ordE 1)) ++
      dt.paths.map (·.via (ordE 2))
  | _, .tyStamped dA _ _ _ => dA.paths.map (·.via (ordE 0))
  | _, .tyPi (q := q) dA dB _ _ _ =>
    dA.paths.map (·.via ⟨q, .piDom, 0⟩) ++ unbindPaths (dB.paths.map (·.via (ordE 1)))
  | _, .tySigma dA dB _ _ =>
    dA.paths.map (·.via (ordE 0)) ++ unbindPaths (dB.paths.map (·.via (ordE 1)))
  | _, .var (i := i) _ _ _ _ _ => [⟨.var i, []⟩]
  | _, .const (i := i) (k := k) _ _ _ _ => [⟨.decl i k, []⟩]
  | _, .lam _ dt _ _ _ _ => unbindPaths (dt.paths.map (·.via (ordE 1)))
  | _, .app (q := q) df du _ _ _ _ =>
    df.paths.map (·.via (ordE 0)) ++ du.paths.map (·.via ⟨q, .appArg, 1⟩)
  | _, .pair dt du _ _ _ => dt.paths.map (·.via (ordE 0)) ++ du.paths.map (·.via (ordE 1))
  | _, .fst dp _ _ => dp.paths.map (·.via (ordE 0))
  | _, .snd dp _ _ _ => dp.paths.map (·.via (ordE 0))
  | _, .stamp dt de dorg _ _ _ =>
    dt.paths.map (·.via (ordE 0)) ++ de.paths.map (·.via (ordE 1)) ++
      dorg.paths.map (·.via (ordE 2))
  | _, .gate (g := g) _ dds dst _ _ _ _ =>
    ⟨.decl g 0, []⟩ :: (dds.paths.map (·.via ⟨⊥, .gateArgs g, 0⟩) ++
      dst.paths.map (·.via ⟨.gated, .gateCred g, 1⟩))
  | _, .node (g := g) (ℓ := ℓ) _ dds dt de _ _ _ _ =>
    ⟨.decl g 0, []⟩ :: (dds.paths.map (·.via ⟨⊥, .nodeArgs g ℓ, 0⟩) ++
      dt.paths.map (·.via ⟨.gated, .nodePayload g ℓ, 1⟩) ++
      de.paths.map (·.via ⟨.gated, .nodeEvent g ℓ, 2⟩))
  | _, .conv dt _ _ => dt.paths
  | _, .spineNil _ => []
  | _, .spineCons dt dts _ => dt.paths.map (·.via (ordE 0)) ++ dts.paths.map (·.via (ordE 1))
  | _, .telNil _ => []
  | _, .telCons dA dΔ _ =>
    dA.paths.map (·.via (ordE 0)) ++ unbindPaths (dΔ.paths.map (·.via (ordE 1)))

/-! ## Lemma 8.1: the effect is the minimum cost of the paths -/

/-- The effect read off a list of paths: at each atom, the minimum cost of the
paths starting there, `∞` when there is none. -/
def pathEff : List Path → Eff
  | [] => ⊤
  | p :: ps => p.eff ⊓ pathEff ps

@[simp] theorem pathEff_nil : pathEff [] = ⊤ := rfl

@[simp] theorem pathEff_cons (p : Path) (ps : List Path) :
    pathEff (p :: ps) = p.eff ⊓ pathEff ps := rfl

theorem pathEff_append (ps qs : List Path) : pathEff (ps ++ qs) = pathEff ps ⊓ pathEff qs := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.cons_append, pathEff_cons, ih, inf_assoc]

theorem pathEff_via (e : Edge) (ps : List Path) :
    pathEff (ps.map (·.via e)) = Eff.scale e.grade (pathEff ps) := by
  induction ps with
  | nil => exact (Eff.scale_top_right _).symm
  | cons p ps ih => simp only [List.map_cons, pathEff_cons, ih, Eff.scale_inf, Path.eff_via]

theorem Path.eff_unbind (p : Path) :
    p.eff.unbind = match p.unbind? with
      | none => ⊤
      | some p' => p'.eff := by
  obtain ⟨a, es⟩ := p
  funext z
  rcases a with ⟨_ | i⟩ | ⟨a, k⟩ <;> rcases z with j | ⟨b, l⟩ <;>
    simp [Path.eff, Path.unbind?, Eff.unbind, Path.cost]

theorem pathEff_unbind (ps : List Path) : pathEff (unbindPaths ps) = (pathEff ps).unbind := by
  induction ps with
  | nil => exact Eff.unbind_top.symm
  | cons p ps ih =>
    rw [pathEff_cons, Eff.unbind_inf, ← ih, Path.eff_unbind]
    simp only [unbindPaths, List.filterMap_cons]
    cases p.unbind? with
    | none => simp
    | some p' => simp

theorem pathEff_leaf (z : Atom) : pathEff [⟨z, []⟩] = Eff.unit z := by
  funext y
  simp only [pathEff_cons, pathEff_nil, inf_top_eq, Path.eff, Eff.unit, Path.cost,
    List.foldr_nil, eq_comm]

/-- Every path's cost bounds the effect at its atom. -/
theorem pathEff_le {ps : List Path} {p : Path} (hp : p ∈ ps) : pathEff ps p.atom ≤ p.cost := by
  induction ps with
  | nil => cases hp
  | cons p' ps ih =>
    rcases List.mem_cons.mp hp with rfl | h
    · exact inf_le_of_left_le (by simp [Path.eff])
    · exact inf_le_of_right_le (ih h)

/-- The effect of a judgment. -/
def Judg.eff : Judg → Eff
  | .ty _ _ _ ε => ε
  | .tm _ _ _ _ ε => ε
  | .spine _ _ _ ε => ε
  | .tel _ _ ε => ε

/-- **Lemma 8.1** (path characterization): the effect of a derivation is, at
every atom, the minimum cost of its paths from that atom (`∞` when there is
none). -/
theorem Deriv.eff_eq_pathEff {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    j.eff = pathEff d.paths := by
  induction d with
  | tyFam _ _ hε _ ih =>
    simp only [Judg.eff] at ih ⊢
    rw [Deriv.paths, hε, pathEff_cons, pathEff_via, ordE, Eff.scale_free, ← ih,
      ← pathEff_leaf]
    simp
  | tyEvent hε => exact hε
  | tyOrigin _ _ _ hε _ ihA ihe iht =>
    simp only [Judg.eff] at ihA ihe iht ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_via, ordE, Eff.scale_free, ← ihA, ← ihe, ← iht]
  | tyStamped _ _ hε _ ih =>
    simp only [Judg.eff] at ih ⊢
    rw [Deriv.paths, hε, pathEff_via, ordE, Eff.scale_free, ← ih]
  | tyPi _ _ _ hε _ ihA ihB =>
    simp only [Judg.eff] at ihA ihB ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_unbind, pathEff_via, ordE, Eff.scale_free, ← ihA, ← ihB]
  | tySigma _ _ hε _ ihA ihB =>
    simp only [Judg.eff] at ihA ihB ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_unbind, pathEff_via, ordE, Eff.scale_free, ← ihA, ← ihB]
  | var _ _ _ hε _ _ =>
    simp only [Judg.eff]
    rw [Deriv.paths, hε, pathEff_leaf]
  | const _ _ hε _ _ =>
    simp only [Judg.eff]
    rw [Deriv.paths, hε, pathEff_leaf]
  | lam _ _ _ _ hε _ _ iht _ =>
    simp only [Judg.eff] at iht ⊢
    rw [Deriv.paths, hε, pathEff_unbind, pathEff_via, ordE, Eff.scale_free, ← iht]
  | app _ _ _ _ hε _ ihf ihu _ =>
    simp only [Judg.eff] at ihf ihu ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_via, ordE, Eff.scale_free, ← ihf, ← ihu]
  | pair _ _ _ hε _ iht ihu _ =>
    simp only [Judg.eff] at iht ihu ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_via, ordE, Eff.scale_free, ← iht, ← ihu]
  | fst _ _ _ ihp _ =>
    simp only [Judg.eff] at ihp ⊢
    rw [Deriv.paths, pathEff_via, ordE, Eff.scale_free, ← ihp]
  | snd _ _ _ _ ihp _ =>
    simp only [Judg.eff] at ihp ⊢
    rw [Deriv.paths, pathEff_via, ordE, Eff.scale_free, ← ihp]
  | stamp _ _ _ _ hε _ iht ihe iho _ =>
    simp only [Judg.eff] at iht ihe iho ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_via, ordE, Eff.scale_free, ← iht, ← ihe, ← iho]
  | gate _ _ _ _ _ hε _ ihds ihs _ =>
    simp only [Judg.eff] at ihds ihs ⊢
    rw [Deriv.paths, hε, pathEff_cons, ← pathEff_leaf]
    simp only [pathEff_append, pathEff_via, Eff.scale_free, ← ihds, ← ihs, pathEff_cons,
      pathEff_nil, inf_top_eq, inf_assoc]
  | node _ _ _ _ _ _ hε _ ihds iht ihe _ =>
    simp only [Judg.eff] at ihds iht ihe ⊢
    rw [Deriv.paths, hε, pathEff_cons, ← pathEff_leaf]
    simp only [pathEff_append, pathEff_via, Eff.scale_free, ← ihds, ← iht, ← ihe, pathEff_cons,
      pathEff_nil, inf_top_eq, inf_assoc, Eff.scale_inf]
  | conv _ _ _ iht _ => exact iht
  | spineNil hε => exact hε
  | spineCons _ _ hε iht ihts =>
    simp only [Judg.eff] at iht ihts ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_via, ordE, Eff.scale_free, ← iht, ← ihts]
  | telNil hε => exact hε
  | telCons _ _ hε ihA ihΔ =>
    simp only [Judg.eff] at ihA ihΔ ⊢
    rw [Deriv.paths, hε]
    simp only [pathEff_append, pathEff_unbind, pathEff_via, ordE, Eff.scale_free, ← ihA, ← ihΔ]

/-! ## The grades of the edges -/

theorem mem_map_via {ps : List Path} {e : Edge} {p : Path} (h : p ∈ ps.map (·.via e)) :
    ∃ p' ∈ ps, p = p'.via e := by
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp h
  exact ⟨p', hp', rfl⟩

theorem mem_unbindPaths {ps : List Path} {p : Path} (h : p ∈ unbindPaths ps) :
    ∃ p' ∈ ps, p.edges = p'.edges ∧
      (∀ a k, p.atom = .decl a k → p'.atom = .decl a k) ∧
      (∀ i, p.atom = .var i → p'.atom = .var (i + 1)) := by
  obtain ⟨p', hp', hu⟩ := List.mem_filterMap.mp h
  refine ⟨p', hp', ?_⟩
  obtain ⟨a, es⟩ := p'
  rcases a with ⟨_ | i⟩ | ⟨a, k⟩
  · cases hu
  · obtain rfl : (⟨.var i, es⟩ : Path) = p := Option.some.inj hu
    exact ⟨rfl, fun _ _ h => (by cases h), fun _ h => (by cases h; rfl)⟩
  · obtain rfl : (⟨.decl a k, es⟩ : Path) = p := Option.some.inj hu
    exact ⟨rfl, fun _ _ h => h, fun _ h => (by cases h)⟩

/-- A property of all the edges of a list of paths. -/
def AllEdges (P : Edge → Prop) (ps : List Path) : Prop := ∀ p ∈ ps, ∀ e ∈ p.edges, P e

namespace AllEdges

variable {P : Edge → Prop}

theorem via {ps : List Path} {e₀ : Edge} (h₀ : P e₀) (h : AllEdges P ps) :
    AllEdges P (ps.map (·.via e₀)) := by
  intro p hp e he
  obtain ⟨p', hp', rfl⟩ := mem_map_via hp
  rcases List.mem_cons.mp he with rfl | he'
  · exact h₀
  · exact h p' hp' e he'

theorem unbind {ps : List Path} (h : AllEdges P ps) : AllEdges P (unbindPaths ps) := by
  intro p hp e he
  obtain ⟨p', hp', hedges, -⟩ := mem_unbindPaths hp
  exact h p' hp' e (hedges ▸ he)

theorem nil : AllEdges P [] := fun _ hp => by cases hp

theorem leaf (z : Atom) : AllEdges P [⟨z, []⟩] := by
  intro p hp e he
  rw [List.mem_singleton.mp hp] at he
  cases he

theorem append {ps qs : List Path} (h₁ : AllEdges P ps) (h₂ : AllEdges P qs) :
    AllEdges P (ps ++ qs) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h₁ p h
  · exact h₂ p h

theorem cons_leaf {z : Atom} {ps : List Path} (h : AllEdges P ps) :
    AllEdges P ((⟨z, []⟩ : Path) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h'
  · intro e he; cases he
  · exact h p h'

end AllEdges

/-- Every edge of a derivation has the grade its kind allows. -/
theorem Deriv.edge_gradeOK {S : Sig} {acc : Bool} {j : Judg} (d : Deriv S acc j) :
    AllEdges (fun e => e.kind.GradeOK e.grade) d.paths := by
  induction d with
  | tyFam _ _ _ _ ih => exact .cons_leaf (.via rfl ih)
  | tyEvent => exact .nil
  | tyOrigin _ _ _ _ _ ihA ihe iht =>
    exact .append (.append (.via rfl ihA) (.via rfl ihe)) (.via rfl iht)
  | tyStamped _ _ _ _ ih => exact .via rfl ih
  | tyPi _ _ _ _ _ ihA ihB => exact .append (.via trivial ihA) (.unbind (.via rfl ihB))
  | tySigma _ _ _ _ ihA ihB => exact .append (.via rfl ihA) (.unbind (.via rfl ihB))
  | var => exact .leaf _
  | const => exact .leaf _
  | lam _ _ _ _ _ _ _ iht _ => exact .unbind (.via rfl iht)
  | app _ _ _ _ _ _ ihf ihu _ => exact .append (.via rfl ihf) (.via trivial ihu)
  | pair _ _ _ _ _ iht ihu _ => exact .append (.via rfl iht) (.via rfl ihu)
  | fst _ _ _ ihp _ => exact .via rfl ihp
  | snd _ _ _ _ ihp _ => exact .via rfl ihp
  | stamp _ _ _ _ _ _ iht ihe iho _ =>
    exact .append (.append (.via rfl iht) (.via rfl ihe)) (.via rfl iho)
  | gate _ _ _ _ _ _ _ ihds ihs _ => exact .cons_leaf (.append (.via rfl ihds) (.via rfl ihs))
  | node _ _ _ _ _ _ _ _ ihds iht ihe _ =>
    exact .cons_leaf (.append (.append (.via rfl ihds) (.via rfl iht)) (.via rfl ihe))
  | conv _ _ _ iht _ => exact iht
  | spineNil => exact .nil
  | spineCons _ _ _ iht ihts => exact .append (.via rfl iht) (.via rfl ihts)
  | telNil => exact .nil
  | telCons _ _ _ ihA ihΔ => exact .append (.via rfl ihA) (.unbind (.via rfl ihΔ))

/-! ## Theorem 9.1: path mediation -/

/-- The result role of a type or term judgment. -/
def Judg.role? : Judg → Option Role
  | .ty _ ρ _ _ => some ρ
  | .tm _ ρ _ _ _ => some ρ
  | _ => none

/-- An accepted type or term derivation has a policy-valid effect. -/
theorem Deriv.valid_root {S : Sig} {j : Judg} (d : Deriv S true j) {ρ : Role}
    (hρ : j.role? = some ρ) : Valid S j.ctx ρ j.eff := by
  cases j with
  | ty Γ ρ' A α => cases hρ; exact d.valid_ty
  | tm Γ ρ' t A ε => cases hρ; exact d.valid_tm
  | spine => cases hρ
  | tel => cases hρ

/-- Every path of an accepted derivation costs at least the policy demand of its
atom's role into the result role. -/
theorem Deriv.demand_le_cost {S : Sig} {j : Judg} (d : Deriv S true j) {ρ σ : Role}
    (hρ : j.role? = some ρ) {p : Path} (hp : p ∈ d.paths)
    (hσ : roleOf S j.ctx p.atom = some σ) : demand σ ρ ≤ p.cost := by
  have h := d.valid_root hρ p.atom σ hσ
  rw [d.eff_eq_pathEff] at h
  exact h.trans (pathEff_le hp)

/-- **Theorem 9.1** (path mediation). Let an accepted type or term derivation
have result role `ρ`, and let `σ` be the role of the atom of one of its paths.
(i) If `D(σ, ρ) = 1` and the path is live, the path has an edge of grade `1`,
and every such edge is a gate credential, a node payload or event, a grade-`1`
Ty-Pi domain or a latent grade-`1` App argument. (ii) If `D(σ, ρ) = ∞`, the path
is not live: it has an edge of grade `∞`. -/
theorem Deriv.mediation {S : Sig} {j : Judg} (d : Deriv S true j) {ρ σ : Role}
    (hρ : j.role? = some ρ) {p : Path} (hp : p ∈ d.paths)
    (hσ : roleOf S j.ctx p.atom = some σ) :
    (demand σ ρ = .gated → p.cost < ⊤ →
      (∃ e ∈ p.edges, e.grade = .gated) ∧
      ∀ e ∈ p.edges, e.grade = .gated →
        (∃ g, e.kind = .gateCred g) ∨ (∃ g ℓ, e.kind = .nodePayload g ℓ) ∨
        (∃ g ℓ, e.kind = .nodeEvent g ℓ) ∨ e.kind = .piDom ∨ e.kind = .appArg) ∧
    (demand σ ρ = .absent → p.cost = ⊤ ∧ ∃ e ∈ p.edges, e.grade = ⊤) := by
  have hle := d.demand_le_cost hρ hp hσ
  have hok := d.edge_gradeOK p hp
  refine ⟨fun hd hlive => ⟨?_, ?_⟩, fun hd => ?_⟩
  · rw [hd] at hle
    have hc : p.cost = .gated := by
      revert hle hlive; cases p.cost <;> decide
    rcases p.cost_mem with h | ⟨e, he, h⟩
    · rw [hc] at h; cases h
    · exact ⟨e, he, h.trans hc⟩
  · intro e he hg
    have : e.kind.GradeOK e.grade := hok e he
    cases hk : e.kind with
    | ord => rw [hk] at this; rw [this] at hg; cases hg
    | gateArgs g => rw [hk] at this; rw [this] at hg; cases hg
    | nodeArgs g ℓ => rw [hk] at this; rw [this] at hg; cases hg
    | gateCred g => exact .inl ⟨g, rfl⟩
    | nodePayload g ℓ => exact .inr (.inl ⟨g, ℓ, rfl⟩)
    | nodeEvent g ℓ => exact .inr (.inr (.inl ⟨g, ℓ, rfl⟩))
    | piDom => exact .inr (.inr (.inr (.inl rfl)))
    | appArg => exact .inr (.inr (.inr (.inr rfl)))
  · rw [hd] at hle
    have hc : p.cost = ⊤ := top_le_iff.mp hle
    refine ⟨hc, ?_⟩
    rcases p.cost_mem with h | ⟨e, he, h⟩
    · rw [hc] at h; cases h
    · exact ⟨e, he, h.trans hc⟩

/-- Theorem 9.1, stability: reduction cannot create a path below the policy
demand. After any number of steps from an accepted term derivation there is an
accepted derivation of the reduct whose effect is pointwise larger, and its
paths again cost at least the policy demand. -/
theorem Deriv.mediation_steps {S : Sig} (hS : SigWF S) {Γ : Ctx} {ρ : Role} {t A : Exp}
    {ε : Eff} (hΓ : CtxWF S Γ) (d : Deriv S true (.tm Γ ρ t A ε)) {t' : Exp}
    (h : Steps t t') :
    ∃ ε', ε ≤ ε' ∧ ∃ d' : Deriv S true (.tm Γ ρ t' A ε'),
      ∀ p ∈ d'.paths, ∀ σ, roleOf S Γ p.atom = some σ → demand σ ρ ≤ p.cost := by
  obtain ⟨ε', hle, ⟨d'⟩⟩ := d.subject_reduction_steps hS hΓ h
  exact ⟨ε', hle, d', fun p hp σ hσ => d'.demand_le_cost rfl hp hσ⟩

end Artform.Roles.Calculus
