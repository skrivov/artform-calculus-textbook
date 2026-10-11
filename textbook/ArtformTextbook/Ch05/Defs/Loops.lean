import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.List.Chain
import Mathlib.Data.Quot
import ArtformTextbook.Ch05.Defs.Curvature

/-!
# Paths without backtracks, spanning trees, and the edge-loop group
(Section 5.13)

A path `γ = e_k ⋯ e₁` of the transport skeleton is written with the edge
traversed first on the right, and `Path.edges` lists it in that order. This
file adds what Section 5.13 needs about paths:
* joining is associative, and a path is determined by its list of edges;
* a path is *reduced* when it never steps straight back along the edge it has
  just crossed;
* a *spanning tree* is a set of edges such that any two vertices are joined by
  exactly one reduced path along it;
* the combinatorial fundamental group `π₁(K, v)` of a canvas: the based edge
  loops at `v`, modulo deletion of immediate backtracks and insertion or
  deletion of declared face-boundary words (Theorem 5.29), with the group
  structure of joining loops.
-/

namespace Artform

namespace Skeleton

variable {X : Skeleton}

namespace Path

/-- Joining the empty path at the start changes nothing. -/
@[simp]
theorem comp_nil {u v : X.V} (γ : X.Path u v) : γ.comp (.nil u) = γ := by
  induction γ with
  | nil => rfl
  | cons e γ ih => simp only [comp, ih]

/-- Joining paths is associative. -/
theorem comp_assoc {u v w x : X.V} (γ : X.Path w x) (δ : X.Path v w) (ε : X.Path u v) :
    (γ.comp δ).comp ε = γ.comp (δ.comp ε) := by
  induction γ with
  | nil => rfl
  | cons e γ ih => simp only [comp, ih]

/-- The edges of `γ δ` are those of `γ`, then those of `δ`, in the book's
order. -/
@[simp]
theorem edges_comp {u v w : X.V} (γ : X.Path v w) (δ : X.Path u v) :
    (γ.comp δ).edges = γ.edges ++ δ.edges := by
  induction γ with
  | nil => rfl
  | cons e γ ih => simp only [comp, edges, ih, List.cons_append]

/-- Renaming the ends of a path keeps its edges. -/
@[simp]
theorem edges_cast {u u' v v' : X.V} (hu : u = u') (hv : v = v') (γ : X.Path u v) :
    (γ.cast hu hv).edges = γ.edges := by
  subst hu hv
  rfl

/-- The one step `ē`. -/
@[simp]
theorem edges_back (e : X.E) : (Path.back e).edges = [X.rev e] := by
  simp [Path.back, edges]

/-- The reversed path crosses the reversed edges in the reverse order. -/
@[simp]
theorem edges_reverse {u v : X.V} (γ : X.Path u v) :
    γ.reverse.edges = (γ.edges.map X.rev).reverse := by
  induction γ with
  | nil => rfl
  | cons e γ ih => simp [Path.reverse, edges, ih]

/-- Two paths that start at one vertex and cross the same edges end at one
vertex and are the same path. -/
theorem eq_of_edges_eq_aux {u : X.V} :
    ∀ {v v' : X.V} (γ : X.Path u v) (δ : X.Path u v'), γ.edges = δ.edges →
      v = v' ∧ HEq γ δ
  | _, _, .nil _, .nil _, _ => ⟨rfl, HEq.rfl⟩
  | _, _, .nil _, .cons _ _, h => by simp [edges] at h
  | _, _, .cons _ _, .nil _, h => by simp [edges] at h
  | _, _, .cons e γ, .cons e' δ, h => by
    simp only [edges, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨_, h'⟩ := eq_of_edges_eq_aux γ δ h
    obtain rfl := eq_of_heq h'
    exact ⟨rfl, HEq.rfl⟩

/-- A path is determined by its ends and its edges. -/
theorem eq_of_edges_eq {u v : X.V} {γ δ : X.Path u v} (h : γ.edges = δ.edges) : γ = δ :=
  eq_of_heq (eq_of_edges_eq_aux γ δ h).2

/-- The reverse of `γ δ` is `δ̄ γ̄`. -/
theorem reverse_comp {u v w : X.V} (γ : X.Path v w) (δ : X.Path u v) :
    (γ.comp δ).reverse = δ.reverse.comp γ.reverse :=
  eq_of_edges_eq (by simp)

/-- Reversing twice gives the path back. -/
@[simp]
theorem reverse_reverse {u v : X.V} (γ : X.Path u v) : γ.reverse.reverse = γ :=
  eq_of_edges_eq (by simp [List.map_reverse, Function.comp_def, X.rev_rev])

/-- A reduced path, one without immediate backtracks (Section 5.13):
in `γ = e_k ⋯ e₁` no `e_{j+1}` is `ē_j`, so the path never steps straight back
along the edge it has just crossed. -/
def Reduced {u v : X.V} (γ : X.Path u v) : Prop :=
  γ.edges.IsChain fun a b => a ≠ X.rev b

end Path

/-- A spanning tree of the transport skeleton, as Theorem 5.28 uses the term: a
set `τ` of edges, taken with both traversals (`e ∈ τ` exactly when `ē ∈ τ`),
such that any two vertices are joined by exactly one path along `τ` without
immediate backtracks. This is the usual characterization of a spanning tree,
any two vertices joined by a unique path in the tree; on a skeleton, which may
have loops and parallel edges, a path is a walk without immediate
backtracks. -/
def IsSpanningTree (τ : Set X.E) : Prop :=
  (∀ e, e ∈ τ ↔ X.rev e ∈ τ) ∧
  ∀ u v : X.V, ∃! γ : X.Path u v, (∀ e ∈ γ.edges, e ∈ τ) ∧ γ.Reduced

end Skeleton

namespace Canvas

variable (K : Canvas)

/-- An immediate backtrack, as a loop at the source of `e`: it crosses `e` and
straight back, `ē e`. -/
def IsBacktrack {w : K.V} (δ : K.skeleton.Path w w) : Prop :=
  ∃ e, δ.edges = [K.skeleton.rev e, e]

/-- A declared face-boundary word, read as a loop from one of its corners: the
boundary cycle of a face `f`, rotated to start at its `i`-th step, written with
the first step on the right. -/
def IsFaceLoop {w : K.V} (δ : K.skeleton.Path w w) : Prop :=
  ∃ (f : K.F) (i : ℕ), δ.edges = ((K.boundary f).rotate i).reverse

/-- One insertion into a based loop at `v`: the loop `γ = β α`, which runs along
`α` from `v` to `w` and then along `β` back to `v`, becomes `β δ α`, where `δ`
is an immediate backtrack or a declared face-boundary word at `w`. A deletion
is an insertion read backwards. -/
def LoopMove (v : K.V) (γ γ' : K.skeleton.Path v v) : Prop :=
  ∃ (w : K.V) (α : K.skeleton.Path v w) (β : K.skeleton.Path w v) (δ : K.skeleton.Path w w),
    (K.IsBacktrack δ ∨ K.IsFaceLoop δ) ∧ γ = β.comp α ∧ γ' = β.comp (δ.comp α)

/-- The edge-loop group `π₁(K, v)` of Theorem 5.29, defined combinatorially: the
based edge loops at `v`, modulo deletion of immediate backtracks and insertion
or deletion of declared face-boundary words (the equivalence relation that
`LoopMove` generates). Loops multiply by joining them. -/
def EdgeLoopGroup (v : K.V) : Type := Quot (K.LoopMove v)

namespace EdgeLoopGroup

variable {K} {v : K.V}

/-- The class `[γ]` of a based loop. -/
def mk (γ : K.skeleton.Path v v) : K.EdgeLoopGroup v := Quot.mk _ γ

open Skeleton.Path

/-- Inserting a backtrack or a face word into a loop does not change its
class. -/
theorem mk_insert {w : K.V} (α : K.skeleton.Path v w) (β : K.skeleton.Path w v)
    (δ : K.skeleton.Path w w) (hδ : K.IsBacktrack δ ∨ K.IsFaceLoop δ) :
    mk (β.comp (δ.comp α)) = mk (β.comp α) :=
  (Quot.sound ⟨w, α, β, δ, hδ, rfl, rfl⟩).symm

/-- A detour along a path `q` and straight back, `q̄ q`, does not change the
class of a loop: it is a sequence of immediate backtracks. -/
theorem mk_cancel {w : K.V} (α : K.skeleton.Path v w) (β : K.skeleton.Path w v) :
    ∀ {x : K.V} (q : K.skeleton.Path w x),
      mk (β.comp ((q.reverse.comp q).comp α)) = mk (β.comp α)
  | _, .nil _ => rfl
  | _, .cons e q => by
    have hbt : K.IsBacktrack ((Skeleton.Path.back e).comp (.cons e (.nil _))) :=
      ⟨e, by simp [Skeleton.Path.edges]⟩
    have h1 : β.comp ((((Skeleton.Path.cons e q).reverse).comp (.cons e q)).comp α) =
        (β.comp q.reverse).comp
          (((Skeleton.Path.back e).comp (.cons e (.nil _))).comp (q.comp α)) :=
      eq_of_edges_eq (by simp [Skeleton.Path.edges])
    have h2 : (β.comp q.reverse).comp (q.comp α) = β.comp ((q.reverse.comp q).comp α) :=
      eq_of_edges_eq (by simp)
    rw [h1, mk_insert _ _ _ (Or.inl hbt), h2, mk_cancel α β q]

/-- Inserting a backtrack or a face word read backwards does not change the
class of a loop either. -/
theorem mk_insert_reverse {w : K.V} (α : K.skeleton.Path v w) (β : K.skeleton.Path w v)
    (δ : K.skeleton.Path w w) (hδ : K.IsBacktrack δ ∨ K.IsFaceLoop δ) :
    mk (β.comp (δ.reverse.comp α)) = mk (β.comp α) := by
  have h1 : β.comp (δ.reverse.comp α) = (β.comp δ.reverse).comp α :=
    (comp_assoc _ _ _).symm
  have h2 : (β.comp δ.reverse).comp (δ.comp α) = β.comp ((δ.reverse.comp δ).comp α) :=
    eq_of_edges_eq (by simp)
  rw [h1, ← mk_insert α (β.comp δ.reverse) δ hδ, h2, mk_cancel]

/-- Joining a loop on the left respects the moves. -/
theorem loopMove_comp_left (γ : K.skeleton.Path v v) {δ₁ δ₂ : K.skeleton.Path v v}
    (h : K.LoopMove v δ₁ δ₂) : K.LoopMove v (γ.comp δ₁) (γ.comp δ₂) := by
  obtain ⟨w, α, β, δ, hδ, rfl, rfl⟩ := h
  exact ⟨w, α, γ.comp β, δ, hδ, (comp_assoc _ _ _).symm, (comp_assoc _ _ _).symm⟩

/-- Joining a loop on the right respects the moves. -/
theorem loopMove_comp_right {γ₁ γ₂ : K.skeleton.Path v v} (δ : K.skeleton.Path v v)
    (h : K.LoopMove v γ₁ γ₂) : K.LoopMove v (γ₁.comp δ) (γ₂.comp δ) := by
  obtain ⟨w, α, β, ε, hε, rfl, rfl⟩ := h
  exact ⟨w, α.comp δ, β, ε, hε, comp_assoc _ _ _,
    by rw [comp_assoc, comp_assoc]⟩

/-- Reversing a loop respects the classes. -/
theorem mk_reverse_eq {γ γ' : K.skeleton.Path v v} (h : K.LoopMove v γ γ') :
    mk γ.reverse = mk γ'.reverse := by
  obtain ⟨w, α, β, δ, hδ, rfl, rfl⟩ := h
  rw [reverse_comp, reverse_comp, reverse_comp, comp_assoc, mk_insert_reverse _ _ _ hδ]

instance : Mul (K.EdgeLoopGroup v) :=
  ⟨Quot.map₂ (fun γ δ => γ.comp δ) (fun γ _ _ h => loopMove_comp_left γ h)
    (fun _ _ δ h => loopMove_comp_right δ h)⟩

instance : One (K.EdgeLoopGroup v) := ⟨mk (.nil _)⟩

instance : Inv (K.EdgeLoopGroup v) :=
  ⟨Quot.lift (fun γ => mk γ.reverse) fun _ _ h => mk_reverse_eq h⟩

/-- `[γ] [δ] = [γ δ]`: the loop `δ` first, then `γ`. -/
theorem mk_mul (γ δ : K.skeleton.Path v v) : mk γ * mk δ = mk (γ.comp δ) := rfl

/-- `[γ]⁻¹ = [γ̄]`. -/
theorem mk_inv (γ : K.skeleton.Path v v) : (mk γ)⁻¹ = mk γ.reverse := rfl

/-- The class of the empty loop is the unit. -/
theorem mk_nil : mk (.nil _) = (1 : K.EdgeLoopGroup v) := rfl

/-- Every element is the class of a loop. -/
theorem mk_surjective : Function.Surjective (mk : K.skeleton.Path v v → K.EdgeLoopGroup v) :=
  Quot.mk_surjective

/-- The edge-loop group is a group under joining loops. -/
instance : Group (K.EdgeLoopGroup v) :=
  Group.ofLeftAxioms
    (by
      rintro ⟨γ⟩ ⟨δ⟩ ⟨ε⟩
      exact congrArg mk (comp_assoc γ δ ε))
    (by
      rintro ⟨γ⟩
      rfl)
    (by
      rintro ⟨γ⟩
      change mk (γ.reverse.comp γ) = mk (.nil _)
      have h := mk_cancel (.nil _) (.nil _) γ
      rwa [comp_nil] at h)

end EdgeLoopGroup

variable (G : Type*) [Group G]

/-- The set `{face-flat connections}/gauge` of Theorem 5.29: face-flat link
tables, two of them identified when they are gauge equivalent. -/
def FaceFlatClasses : Type _ :=
  Quot fun U U' : {U : K.skeleton.LinkTable G // FaceFlat U} =>
    Skeleton.GaugeEquivalent U.1 U'.1

/-- The set `Hom(π₁(K, v), G)/G` of Theorem 5.29: homomorphisms from the
edge-loop group to `G`, with `G` acting by conjugating all values. -/
def HomClasses (v : K.V) : Type _ :=
  Quot fun φ ψ : K.EdgeLoopGroup v →* G => ∃ k : G, ∀ x, ψ x = k * φ x * k⁻¹

end Canvas

end Artform
