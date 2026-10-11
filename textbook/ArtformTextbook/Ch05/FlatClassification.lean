import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import ArtformTextbook.Ch05.Statements.Gauge

/-!
# Classification of face-flat connections (Theorem 5.29)

The book states the theorem without a proof. The proof here is the standard
one for the edge-path group.

* Holonomy is a homomorphism on `π₁(K, v)`: an immediate backtrack has
  holonomy `U_ē U_e = 1`, and on a face-flat table a face word has holonomy
  `1`, so neither move changes the holonomy of a loop.
* Gauge equivalent tables give conjugate homomorphisms, since
  `Hol_{U^h}(γ) = h_v Hol_U(γ) h_v⁻¹` on a loop at `v` (Theorem 5.23).
* Injective: choose a path `p_w` from `v` to every vertex `w`. If
  `Hol_{U'} = k Hol_U k⁻¹` on every loop at `v`, then
  `h_w = Hol_{U'}(p_w) k Hol_U(p_w)⁻¹` carries `U` to `U'`, as one sees on the
  loop `p̄_{t(e)} e p_{s(e)}` through each edge `e`.
* Surjective: from a homomorphism `φ`, put `U_e = φ[p̄_{t(e)} e p_{s(e)}]`.
  The holonomy of a path `γ` from `a` to `b` telescopes to
  `φ[p̄_b γ p_a]`, so on loops at `v` it is `φ` conjugated by `φ[p_v]`, and each
  face word, which may be deleted, has holonomy `1`.
* Pure gauge is loop-flat (Theorem 5.27), which is the trivial homomorphism.
-/

namespace Artform

open Skeleton Skeleton.Path Canvas Canvas.EdgeLoopGroup

namespace Canvas

variable {K : Canvas} {G : Type*} [Group G]

/-- An immediate backtrack has holonomy `U_ē U_e = 1`. -/
private theorem hol_backtrack (U : K.skeleton.LinkTable G) {w : K.V}
    {δ : K.skeleton.Path w w} (hδ : K.IsBacktrack δ) : hol U δ = 1 := by
  obtain ⟨e, he⟩ := hδ
  rw [hol_eq_prod, he, List.map_cons, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_cons, List.prod_nil, mul_one, U.reversal, inv_mul_cancel]

/-- On a face-flat table, a face word has holonomy `1`. -/
private theorem hol_faceLoop {U : K.skeleton.LinkTable G} (hU : FaceFlat U) {w : K.V}
    {δ : K.skeleton.Path w w} (hδ : K.IsFaceLoop δ) : hol U δ = 1 := by
  obtain ⟨f, i, hfi⟩ := hδ
  rw [hol_eq_prod, hfi, List.map_reverse]
  exact hU f i

/-- On a face-flat table, holonomy is a homomorphism `π₁(K, v) → G`. -/
private noncomputable def holHom (U : K.skeleton.LinkTable G) (hU : FaceFlat U) (v : K.V) :
    K.EdgeLoopGroup v →* G where
  toFun := Quot.lift (hol U) fun γ γ' h => by
    obtain ⟨w, α, β, δ, hδ, rfl, rfl⟩ := h
    have h1 : hol U δ = 1 := hδ.elim (hol_backtrack U) (hol_faceLoop hU)
    rw [hol_comp, hol_comp, hol_comp, h1, one_mul]
  map_one' := rfl
  map_mul' := by
    rintro ⟨γ⟩ ⟨δ⟩
    exact hol_comp U γ δ

private theorem holHom_mk (U : K.skeleton.LinkTable G) (hU : FaceFlat U) {v : K.V}
    (γ : K.skeleton.Path v v) : holHom U hU v (EdgeLoopGroup.mk γ) = hol U γ := rfl

/-- A walk along steps, in the order they are taken, from `u` to `w`. -/
private def Walks (X : Skeleton) : X.V → X.V → List X.E → Prop
  | u, w, [] => u = w
  | u, w, a :: l => X.src a = u ∧ Walks X (X.tgt a) w l

/-- A walk is a path, written with the step taken first on the right. -/
private theorem exists_path_of_walks {X : Skeleton} :
    ∀ (l : List X.E) {u w : X.V}, Walks X u w l → ∃ γ : X.Path u w, γ.edges = l.reverse
  | [], u, w, h => by
    obtain rfl : u = w := h
    exact ⟨.nil u, rfl⟩
  | a :: l, u, w, h => by
    obtain ⟨ha, hl⟩ := h
    obtain ⟨γ, hγ⟩ := exists_path_of_walks l hl
    subst ha
    exact ⟨γ.comp (.cons a (.nil _)), by simp [hγ, Skeleton.Path.edges]⟩

/-- A chain of steps, each ending where the next starts, walks from the start
of the first to the start of the step after the last. -/
private theorem walks_of_isChain {X : Skeleton} :
    ∀ (l : List X.E) (a b : X.E),
      List.IsChain (fun x y => X.tgt x = X.src y) (a :: (l ++ [b])) →
        Walks X (X.src a) (X.src b) (a :: l)
  | [], a, b, h => by
    simp only [List.nil_append, List.isChain_cons_cons, List.IsChain.singleton,
      and_true] at h
    exact ⟨rfl, h⟩
  | c :: l, a, b, h => by
    rw [List.cons_append, List.isChain_cons_cons] at h
    refine ⟨rfl, ?_⟩
    rw [h.1]
    exact walks_of_isChain l c b h.2

/-- Every face has its boundary word as a loop, read from its first corner. -/
private theorem exists_faceLoop (f : K.F) :
    ∃ (w : K.V) (δ : K.skeleton.Path w w), δ.edges = (K.boundary f).reverse := by
  obtain ⟨hne, hc⟩ := K.closed f
  obtain ⟨a, l, hl⟩ := List.ne_nil_iff_exists_cons.mp hne
  rw [hl] at hc ⊢
  have hw : Walks K.skeleton (K.skeleton.src a) (K.skeleton.src a) (a :: l) :=
    walks_of_isChain (X := K.skeleton) l a a hc
  obtain ⟨δ, hδ⟩ := exists_path_of_walks _ hw
  exact ⟨_, δ, hδ⟩

/-- Read from another corner, the curvature of a face is conjugate to the
curvature read from its first corner. -/
private theorem curvature_conj (U : K.skeleton.LinkTable G) (f : K.F) (i : ℕ) :
    ∃ a : G, curvature U f i = a * curvature U f 0 * a⁻¹ := by
  unfold curvature
  rw [List.rotate_zero, List.rotate_eq_drop_append_take_mod]
  set n := i % (K.boundary f).length
  set A := (K.boundary f).take n
  set B := (K.boundary f).drop n
  have hL : K.boundary f = A ++ B := (List.take_append_drop n _).symm
  refine ⟨(A.map fun s => U s).reverse.prod, ?_⟩
  rw [hL]
  simp only [List.map_append, List.reverse_append, List.prod_append]
  group

/-- Flat at one corner is flat at every corner: the book's remark in
Definition 5.25. -/
private theorem flatAt_of_curvature_zero (U : K.skeleton.LinkTable G) (f : K.F)
    (h : curvature U f 0 = 1) : FlatAt U f := by
  intro i
  obtain ⟨a, ha⟩ := curvature_conj U f i
  rw [ha, h, mul_one, mul_inv_cancel]

end Canvas

/-! ### The table that a homomorphism gives -/

section Construction

variable {X : Skeleton} {v : X.V} (p : ∀ w, X.Path v w)

/-- The loop through the oriented edge `e`: out along `p_{s(e)}`, across `e`,
and back along `p_{t(e)}` reversed, `p̄_{t(e)} e p_{s(e)}`. -/
private def throughLoop (e : X.E) : X.Path v v :=
  (p (X.tgt e)).reverse.comp ((Path.cons e (.nil _)).comp (p (X.src e)))

/-- The loop through `ē` is the loop through `e` reversed. -/
private theorem throughLoop_rev (e : X.E) :
    throughLoop p (X.rev e) = (throughLoop p e).reverse := by
  apply eq_of_edges_eq
  have h1 : (p (X.tgt (X.rev e))).edges = (p (X.src e)).edges := by rw [X.tgt_rev]
  have h2 : (p (X.src (X.rev e))).edges = (p (X.tgt e)).edges := by rw [X.src_rev]
  simp only [throughLoop, edges_comp, edges_reverse, Skeleton.Path.edges, h1, h2]
  simp [List.map_reverse, Function.comp_def, X.rev_rev]

/-- The holonomy of the loop through `e`. -/
private theorem hol_throughLoop {G : Type*} [Group G] (U : X.LinkTable G) (e : X.E) :
    hol U (throughLoop p e) = (hol U (p (X.tgt e)))⁻¹ * (U e * hol U (p (X.src e))) := by
  simp [throughLoop, hol_comp, hol_reverse]

end Construction

namespace Canvas

variable {K : Canvas} {G : Type*} [Group G] {v : K.V} (p : ∀ w, K.skeleton.Path v w)

/-- The link table of a homomorphism `φ`: `U_e = φ[p̄_{t(e)} e p_{s(e)}]`. -/
private noncomputable def tableOf (φ : K.EdgeLoopGroup v →* G) : K.skeleton.LinkTable G where
  val e := φ (EdgeLoopGroup.mk (throughLoop p e))
  reversal e := by
    rw [throughLoop_rev, ← EdgeLoopGroup.mk_inv, map_inv]

/-- A detour from the base vertex and straight back is trivial. -/
private theorem mk_back {w : K.V} (q : K.skeleton.Path v w) :
    EdgeLoopGroup.mk (q.reverse.comp q) = 1 := by
  have h := EdgeLoopGroup.mk_cancel (.nil _) (.nil _) q
  rwa [comp_nil] at h

/-- The holonomy of the table of `φ` telescopes: along a path `γ` from `a` to
`b` it is `φ[p̄_b γ p_a]`. -/
private theorem hol_tableOf (φ : K.EdgeLoopGroup v →* G) {a : K.V} :
    ∀ {b : K.V} (γ : K.skeleton.Path a b),
      hol (tableOf p φ) γ = φ (EdgeLoopGroup.mk ((p b).reverse.comp (γ.comp (p a))))
  | _, .nil _ => by
    rw [hol_nil]
    change 1 = φ (EdgeLoopGroup.mk ((p a).reverse.comp (p a)))
    rw [mk_back, map_one]
  | _, .cons e γ => by
    rw [hol_cons, hol_tableOf φ γ]
    change φ (EdgeLoopGroup.mk (throughLoop p e)) * _ = _
    rw [← map_mul, EdgeLoopGroup.mk_mul]
    have h1 : (throughLoop p e).comp ((p (K.skeleton.src e)).reverse.comp (γ.comp (p _))) =
        ((p (K.skeleton.tgt e)).reverse.comp (Path.cons e (.nil _))).comp
          ((((p (K.skeleton.src e)).reverse).reverse.comp (p (K.skeleton.src e)).reverse).comp
            (γ.comp (p _))) :=
      eq_of_edges_eq (by simp [throughLoop, Skeleton.Path.edges])
    have h2 : ((p (K.skeleton.tgt e)).reverse.comp (Path.cons e (.nil _))).comp
          (γ.comp (p _)) = (p (K.skeleton.tgt e)).reverse.comp ((Path.cons e γ).comp (p _)) :=
      eq_of_edges_eq (by simp [Skeleton.Path.edges])
    rw [h1, EdgeLoopGroup.mk_cancel, h2]

/-- The table of `φ` is face-flat: a face word may be deleted. -/
private theorem faceFlat_tableOf (φ : K.EdgeLoopGroup v →* G) : FaceFlat (tableOf p φ) := by
  intro f
  apply flatAt_of_curvature_zero
  obtain ⟨w, δ, hδ⟩ := exists_faceLoop f
  have hface : K.IsFaceLoop δ := ⟨f, 0, by rw [List.rotate_zero, hδ]⟩
  have h1 : curvature (tableOf p φ) f 0 = hol (tableOf p φ) δ := by
    rw [hol_eq_prod, hδ, curvature, List.rotate_zero, List.map_reverse]
  rw [h1, hol_tableOf, EdgeLoopGroup.mk_insert _ _ _ (Or.inr hface), mk_back, map_one]

end Canvas

/-- Conjugation of homomorphisms is an equivalence relation. -/
private theorem homConj_equivalence {H : Type*} [Group H] (G : Type*) [Group G] :
    Equivalence fun φ ψ : H →* G => ∃ k : G, ∀ x, ψ x = k * φ x * k⁻¹ where
  refl φ := ⟨1, fun x => by simp⟩
  symm := by
    rintro φ ψ ⟨k, hk⟩
    exact ⟨k⁻¹, fun x => by rw [hk]; group⟩
  trans := by
    rintro φ ψ χ ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k' * k, fun x => by rw [hk', hk]; group⟩

/-- **Theorem 5.29** (classification of face-flat connections). On a connected
transport skeleton, holonomy induces a bijection
`{face-flat connections}/gauge ≅ Hom(π₁(K, v), G)/G`, and the pure-gauge
connections correspond to the trivial homomorphism. -/
@[book "thm:flat-classification"]
theorem flatClassification : Statement.flatClassification := by
  intro K G _ v hconn
  -- a path from the base vertex to every vertex
  let p : ∀ w, K.skeleton.Path v w := fun w => (hconn v w).some
  -- the classifying map
  let Φ : K.FaceFlatClasses G → K.HomClasses G v :=
    Quot.lift (fun U => Quot.mk _ (holHom U.1 U.2 v)) (by
      rintro ⟨U, hU⟩ ⟨U', hU'⟩ ⟨h, rfl⟩
      refine Quot.sound ⟨h v, fun x => ?_⟩
      induction x using Quot.ind with
      | mk γ => exact hol_gaugeAct U h γ)
  have hΦ : ∀ (U : {U : K.skeleton.LinkTable G // K.FaceFlat U}) (φ : K.EdgeLoopGroup v →* G),
      (∀ γ, φ (EdgeLoopGroup.mk γ) = hol U.1 γ) → Φ (Quot.mk _ U) = Quot.mk _ φ := by
    intro U φ hφ
    have : φ = holHom U.1 U.2 v := by
      ext x
      induction x using Quot.ind with
      | mk γ => exact hφ γ
    rw [this]
  refine ⟨fun U hU => ⟨holHom U hU v, fun γ => rfl⟩, Φ, hΦ, ⟨?_, ?_⟩, ?_⟩
  · -- injective: conjugate holonomies come from gauge equivalent tables
    rintro ⟨⟨U, hU⟩⟩ ⟨⟨U', hU'⟩⟩ h
    obtain ⟨k, hk⟩ := (homConj_equivalence G).eqvGen_iff.mp (Quot.eq.mp h)
    refine Quot.sound ⟨fun w => hol U' (p w) * k * (hol U (p w))⁻¹, ?_⟩
    change gaugeAct _ U = U'
    ext e
    have h1 : hol U' (throughLoop p e) = k * hol U (throughLoop p e) * k⁻¹ :=
      hk (EdgeLoopGroup.mk (throughLoop p e))
    rw [hol_throughLoop, hol_throughLoop] at h1
    have h3 : U' e = hol U' (p (K.skeleton.tgt e)) *
        (k * ((hol U (p (K.skeleton.tgt e)))⁻¹ * (U e * hol U (p (K.skeleton.src e)))) * k⁻¹) *
        (hol U' (p (K.skeleton.src e)))⁻¹ := by
      rw [← h1]
      group
    rw [gaugeAct_apply, h3]
    group
  · -- surjective: every homomorphism is the holonomy of a face-flat table
    rintro ⟨φ⟩
    refine ⟨Quot.mk _ ⟨tableOf p φ, faceFlat_tableOf p φ⟩,
      Quot.sound ⟨φ (EdgeLoopGroup.mk (p v)), fun x => ?_⟩⟩
    induction x using Quot.ind with
    | mk γ =>
      change φ (EdgeLoopGroup.mk γ) =
        φ (EdgeLoopGroup.mk (p v)) * hol (tableOf p φ) γ * (φ (EdgeLoopGroup.mk (p v)))⁻¹
      rw [hol_tableOf]
      change φ (EdgeLoopGroup.mk γ) = φ (EdgeLoopGroup.mk (p v)) *
        φ ((EdgeLoopGroup.mk (p v))⁻¹ * (EdgeLoopGroup.mk γ * EdgeLoopGroup.mk (p v))) *
          (φ (EdgeLoopGroup.mk (p v)))⁻¹
      rw [map_mul, map_mul, map_inv]
      group
  · -- pure gauge is the trivial homomorphism
    rintro ⟨U, hU⟩
    change PureGauge U ↔ Quot.mk _ (holHom U hU v) = Quot.mk _ 1
    rw [pureGauge K.skeleton G U hconn]
    constructor
    · intro hflat
      congr 1
      ext x
      induction x using Quot.ind with
      | mk γ => exact hflat v γ
    · intro h w γ
      obtain ⟨k, hk⟩ := (homConj_equivalence G).eqvGen_iff.mp (Quot.eq.mp h)
      have h1 : (1 : G) = k * hol U ((p w).reverse.comp (γ.comp (p w))) * k⁻¹ :=
        hk (EdgeLoopGroup.mk ((p w).reverse.comp (γ.comp (p w))))
      rw [hol_comp, hol_comp, hol_reverse] at h1
      have h2 := conj_eq_one_iff.mp h1.symm
      have h3 : (hol U (p w))⁻¹ * hol U γ * ((hol U (p w))⁻¹)⁻¹ = 1 := by
        rw [inv_inv, mul_assoc]
        exact h2
      exact conj_eq_one_iff.mp h3

/-! ## Non-vacuity

The canvas `K°` of `fig:flat-with-hole`: the two squares with the left face
removed, keeping its four edges and corners (vertices `v₀, …, v₅` as `0, …, 5`,
edges `e₁, …, e₇` as `0, …, 6`). Its one face, `f_R`, runs along `e₅`, `e₆`,
`e₇` and then against `e₂`. Over `C₃`, the connection with `r` on `e₂` and on
`e₅` and `1` elsewhere is face-flat, `F_R = 1 − 1 = 0` in the book's numbers,
but the loop `e₄ e₃ e₂ e₁` round the hole has holonomy `r`. -/

/-- The canvas `K°`. -/
private abbrev holeCanvas : Canvas where
  V := Fin 6
  E := Fin 7
  F := Unit
  src := ![0, 1, 2, 3, 1, 4, 5]
  tgt := ![1, 2, 3, 0, 4, 5, 2]
  boundary := fun _ => [(4, true), (5, true), (6, true), (1, false)]
  closed := fun _ => by unfold IsClosedWalk; decide

/-- The connection of `fig:flat-with-hole`. -/
private def holeTable : holeCanvas.skeleton.LinkTable (Multiplicative (ZMod 3)) :=
  LinkTable.ofGraph fun e => if e = 1 ∨ e = 4 then Multiplicative.ofAdd 1 else 1

/-- A path from `v₀` along the given steps. -/
private theorem path_from_zero (l : List holeCanvas.skeleton.E) {w : Fin 6}
    (h : Canvas.Walks holeCanvas.skeleton 0 w l) :
    ∃ γ : holeCanvas.skeleton.Path 0 w, γ.edges = l.reverse :=
  Canvas.exists_path_of_walks l h

/-- The hypotheses of Theorem 5.29 are met on `K°`: its transport skeleton is
connected, and the connection of `fig:flat-with-hole` is face-flat; yet the
loop round the hole has holonomy `r`, so the connection is not loop-flat. -/
example : holeCanvas.skeleton.Connected ∧ holeCanvas.FaceFlat holeTable ∧
    ∃ γ : holeCanvas.skeleton.Path 0 0, hol holeTable γ = Multiplicative.ofAdd 1 := by
  refine ⟨connected_of_base (0 : Fin 6) fun w => ?_, ?_, ?_⟩
  · fin_cases w
    · exact ⟨(path_from_zero [] rfl).choose⟩
    · exact ⟨(path_from_zero [(0, true)] ⟨rfl, rfl⟩).choose⟩
    · exact ⟨(path_from_zero [(0, true), (1, true)] ⟨rfl, rfl, rfl⟩).choose⟩
    · exact ⟨(path_from_zero [(3, false)] ⟨rfl, rfl⟩).choose⟩
    · exact ⟨(path_from_zero [(0, true), (4, true)] ⟨rfl, rfl, rfl⟩).choose⟩
    · exact ⟨(path_from_zero [(0, true), (4, true), (5, true)] ⟨rfl, rfl, rfl, rfl⟩).choose⟩
  · rintro ⟨⟩ i
    have hlen : (holeCanvas.boundary ()).length = 4 := rfl
    rw [curvature, ← List.rotate_mod, hlen]
    have : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize i % 4 = j at this
    interval_cases j <;> decide
  · obtain ⟨γ, hγ⟩ := path_from_zero (w := 0) [(0, true), (1, true), (2, true), (3, true)]
      ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨γ, ?_⟩
    rw [hol_eq_prod, hγ]
    decide

end Artform
