import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.NatCard
import ArtformTextbook.Ch05.Statements.Gauge

/-!
# Spanning-tree gauge fixing (Theorem 5.28)

The proof is the book's. Root the tree `τ` at a vertex `r` and let `p_v` be the
reduced path along `τ` from `r` to `v`. Put `h_v = Hol_U(p_v)⁻¹`. For a tree
edge `e` from `u` to `v`, either `p_v = e p_u` or `p_u = ē p_v`, so
`Hol(p_v) = U_e Hol(p_u)` and `U^h_e = 1`. A gauge change that keeps every tree
label equal to `1` has `h_v = h_u` along every tree edge, so it is constant,
and a constant gauge change conjugates every label by the same element.

For the count, the normalized table is read on the chords, the edges of `E⁺(K)`
off the tree. Two tables are gauge equivalent exactly when their chord values
are simultaneously conjugate, and every family of chord values occurs. The
tree has `|C₀(K)| − 1` edges in `E⁺(K)`: each vertex other than the root is
the end of exactly one tree edge that points away from the root, the last edge
of its path `p_v`.
-/

namespace Artform

namespace Skeleton

variable {X : Skeleton}

namespace Path

/-- A path whose last edge is `a` is a path to the source of `a`, then `a`. -/
private theorem exists_of_edges_cons {u : X.V} :
    ∀ {w : X.V} (γ : X.Path u w) {a : X.E} {l : List X.E}, γ.edges = a :: l →
      X.tgt a = w ∧ ∃ γ' : X.Path u (X.src a), γ'.edges = l
  | _, .nil _, _, _, h => by simp [edges] at h
  | _, .cons _ γ, _, _, h => by
    simp only [edges, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, γ, rfl⟩

/-- A path that crosses no edge ends where it starts. -/
private theorem eq_of_edges_nil {u : X.V} :
    ∀ {w : X.V} (γ : X.Path u w), γ.edges = [] → u = w
  | _, .nil _, _ => rfl
  | _, .cons _ _, h => by simp [edges] at h

end Path

variable {G : Type*} [Group G]

/-- The reduced paths along a set `τ` of edges from a root `r`, one to every
vertex, each the only reduced path along `τ` with its ends. -/
private structure TreePaths (τ : Set X.E) (r : X.V) where
  p : ∀ v, X.Path r v
  tau : ∀ v, ∀ e ∈ (p v).edges, e ∈ τ
  red : ∀ v, (p v).Reduced
  uniq : ∀ v (γ : X.Path r v), (∀ e ∈ γ.edges, e ∈ τ) → γ.Reduced → γ = p v

/-- A spanning tree gives the reduced paths from any root. -/
private noncomputable def treePaths {τ : Set X.E} (hτ : X.IsSpanningTree τ) (r : X.V) :
    TreePaths τ r where
  p v := (hτ.2 r v).exists.choose
  tau v := (hτ.2 r v).exists.choose_spec.1
  red v := (hτ.2 r v).exists.choose_spec.2
  uniq v _ h1 h2 := (hτ.2 r v).unique ⟨h1, h2⟩ (hτ.2 r v).exists.choose_spec

namespace TreePaths

variable {τ : Set X.E} {r : X.V} (P : TreePaths τ r)

private theorem edges_congr {w w' : X.V} (h : w = w') : (P.p w).edges = (P.p w').edges := by
  subst h
  rfl

private theorem edges_root : (P.p r).edges = [] := by
  rw [← P.uniq r (.nil r) (by simp [Path.edges]) (by simp [Path.Reduced, Path.edges])]
  rfl

/-- Dropping the last edge of a reduced path along `τ` from `r` gives the path
`p` to its source. -/
private theorem edges_of_cons {w : X.V} {a : X.E} {l : List X.E}
    (h : (P.p w).edges = a :: l) : X.tgt a = w ∧ l = (P.p (X.src a)).edges := by
  obtain ⟨hta, γ', hγ'⟩ := Path.exists_of_edges_cons _ h
  refine ⟨hta, ?_⟩
  have hτ' : ∀ b ∈ γ'.edges, b ∈ τ := fun b hb =>
    P.tau w b (by rw [h, ← hγ']; exact List.mem_cons_of_mem _ hb)
  have hred' : γ'.Reduced := by
    have := P.red w
    unfold Path.Reduced at this ⊢
    rw [h] at this
    rw [hγ']
    exact this.tail
  rw [← hγ', P.uniq _ γ' hτ' hred']

/-- Along a tree edge `e`, either `p_{t(e)} = e p_{s(e)}`, or
`p_{s(e)} = ē p_{t(e)}`. -/
private theorem dichotomy {e : X.E} (he : e ∈ τ) :
    (P.p (X.tgt e)).edges = e :: (P.p (X.src e)).edges ∨
      (P.p (X.src e)).edges = X.rev e :: (P.p (X.tgt e)).edges := by
  by_cases hb : (P.p (X.src e)).edges.head? = some (X.rev e)
  · right
    obtain ⟨l, hl⟩ : ∃ l, (P.p (X.src e)).edges = X.rev e :: l := by
      cases h : (P.p (X.src e)).edges with
      | nil => rw [h] at hb; simp at hb
      | cons a l =>
        rw [h, List.head?_cons, Option.some.injEq] at hb
        exact ⟨l, by rw [hb]⟩
    obtain ⟨-, hl'⟩ := P.edges_of_cons hl
    rw [hl, hl', P.edges_congr (X.src_rev e)]
  · left
    have hc : (Path.cons e (P.p (X.src e))).Reduced := by
      unfold Path.Reduced
      refine List.IsChain.cons (P.red _) fun y hy hey => hb ?_
      rw [Option.mem_def.mp hy, hey, X.rev_rev]
    have hτc : ∀ a ∈ (Path.cons e (P.p (X.src e))).edges, a ∈ τ := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact he
      · exact P.tau _ a ha
    rw [← P.uniq _ _ hτc hc]
    rfl

/-- Along a tree edge `e`, `Hol_U(p_{t(e)}) = U_e Hol_U(p_{s(e)})`. -/
private theorem hol_tgt {e : X.E} (he : e ∈ τ) (U : X.LinkTable G) :
    hol U (P.p (X.tgt e)) = U e * hol U (P.p (X.src e)) := by
  rcases P.dichotomy he with h | h
  · rw [hol_eq_prod, h, hol_eq_prod, List.map_cons, List.prod_cons]
  · rw [hol_eq_prod U (P.p (X.src e)), h, List.map_cons, List.prod_cons, ← hol_eq_prod,
      U.reversal, mul_inv_cancel_left]

/-- The tree edge `e` points away from the root: `p_{t(e)} = e p_{s(e)}`. -/
private def Down (e : X.E) : Prop := (P.p (X.tgt e)).edges = e :: (P.p (X.src e)).edges

private theorem down_or {e : X.E} (he : e ∈ τ) : P.Down e ∨ P.Down (X.rev e) := by
  rcases P.dichotomy he with h | h
  · exact Or.inl h
  · right
    unfold Down
    rw [P.edges_congr (X.tgt_rev e), P.edges_congr (X.src_rev e)]
    exact h

private theorem not_down_and (e : X.E) : ¬ (P.Down e ∧ P.Down (X.rev e)) := by
  rintro ⟨h1, h2⟩
  unfold Down at h2
  rw [P.edges_congr (X.tgt_rev e), P.edges_congr (X.src_rev e)] at h2
  have := congrArg List.length h1
  have := congrArg List.length h2
  simp only [List.length_cons] at *
  omega

private theorem tgt_ne_root {e : X.E} (h : P.Down e) : X.tgt e ≠ r := by
  intro ht
  have h' := h
  unfold Down at h'
  rw [P.edges_congr ht, P.edges_root] at h'
  exact List.cons_ne_nil _ _ h'.symm

private theorem down_unique {e e' : X.E} (h : P.Down e) (h' : P.Down e')
    (ht : X.tgt e = X.tgt e') : e = e' := by
  unfold Down at h h'
  rw [P.edges_congr ht, h'] at h
  exact (List.cons.inj h).1.symm

/-- Every vertex other than the root is the end of a tree edge pointing away
from the root: the last edge of its path. -/
private theorem exists_down {v : X.V} (hv : v ≠ r) : ∃ a ∈ τ, P.Down a ∧ X.tgt a = v := by
  cases h : (P.p v).edges with
  | nil => exact absurd (Path.eq_of_edges_nil _ h).symm hv
  | cons a l =>
    obtain ⟨hta, hl⟩ := P.edges_of_cons h
    refine ⟨a, P.tau v a (by rw [h]; exact List.mem_cons_self), ?_, hta⟩
    unfold Down
    rw [P.edges_congr hta, h, hl]

/-- The table gauged to `1` on the tree: `h_v = Hol_U(p_v)⁻¹`. -/
private noncomputable def gfix (U : X.LinkTable G) : X.LinkTable G :=
  gaugeAct (fun v => (hol U (P.p v))⁻¹) U

private theorem gfix_tree {e : X.E} (he : e ∈ τ) (U : X.LinkTable G) : P.gfix U e = 1 := by
  rw [gfix, gaugeAct_apply, P.hol_tgt he U, inv_inv]
  group

/-- Gauging first by `h` changes the normalized table by the constant `h_r`. -/
private theorem gfix_gaugeAct (h : X.V → G) (U : X.LinkTable G) :
    P.gfix (gaugeAct h U) = gaugeAct (fun _ => h r) (P.gfix U) := by
  rw [gfix, gfix, gaugeAct_gaugeAct, gaugeAct_gaugeAct]
  congr 1
  funext v
  simp only [Pi.mul_apply, hol_gaugeAct, mul_inv_rev, inv_inv]
  group

/-- A table that is already `1` on the tree is its own normalization. -/
private theorem gfix_of_tree (U : X.LinkTable G) (hU : ∀ e ∈ τ, U e = 1) : P.gfix U = U := by
  have h1 : ∀ v, hol U (P.p v) = 1 := by
    intro v
    rw [hol_eq_prod]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hU e (P.tau v e he)
  have h2 : (fun v => (hol U (P.p v))⁻¹) = (1 : X.V → G) := by
    funext v
    rw [h1, inv_one, Pi.one_apply]
  rw [gfix, h2, gaugeAct_one]

end TreePaths

omit [Group G] in
/-- A gauge change that keeps every tree label `1` is constant along any path
along the tree. -/
private theorem const_along {τ : Set X.E} (h : X.V → G)
    (hh : ∀ e ∈ τ, h (X.tgt e) = h (X.src e)) {u : X.V} :
    ∀ {w : X.V} (γ : X.Path u w), (∀ e ∈ γ.edges, e ∈ τ) → h w = h u
  | _, .nil _, _ => rfl
  | _, .cons e γ, hγ => by
    rw [hh e (hγ e List.mem_cons_self),
      const_along h hh γ fun a ha => hγ a (List.mem_cons_of_mem _ ha)]

/-- The link table with the chord values `a` on the chords, `1` on the tree,
and the reversal law on the other traversals. -/
private noncomputable def chordTable (τ Eplus : Set X.E) (hrev : ∀ e, e ∈ τ ↔ X.rev e ∈ τ)
    (hE : ∀ e, e ∈ Eplus ↔ X.rev e ∉ Eplus) (a : ↥(Eplus \ τ) → G) : X.LinkTable G := by
  classical
  exact
  { val e :=
      if he : e ∈ τ then 1
      else if hp : e ∈ Eplus then a ⟨e, hp, he⟩
      else (a ⟨X.rev e, (hE (X.rev e)).mpr (by rwa [X.rev_rev]),
        fun h => he ((hrev e).mpr h)⟩)⁻¹
    reversal e := by
      by_cases he : e ∈ τ
      · have he' : X.rev e ∈ τ := (hrev e).mp he
        simp only [he, he', dite_true, inv_one]
      · have he' : X.rev e ∉ τ := fun h => he ((hrev e).mpr h)
        by_cases hp : e ∈ Eplus
        · have hp' : X.rev e ∉ Eplus := (hE e).mp hp
          simp only [he, he', hp, hp', dite_false, dite_true]
          congr 2
          exact Subtype.ext (X.rev_rev e)
        · have hp' : X.rev e ∈ Eplus := (hE (X.rev e)).mpr (by rwa [X.rev_rev])
          simp only [he, he', hp, hp', dite_false, dite_true, inv_inv] }

private theorem chordTable_tree (τ Eplus : Set X.E) (hrev : ∀ e, e ∈ τ ↔ X.rev e ∈ τ)
    (hE : ∀ e, e ∈ Eplus ↔ X.rev e ∉ Eplus) (a : ↥(Eplus \ τ) → G) :
    ∀ e ∈ τ, chordTable τ Eplus hrev hE a e = 1 := by
  intro e he
  simp [chordTable, he]

private theorem chordTable_chord (τ Eplus : Set X.E) (hrev : ∀ e, e ∈ τ ↔ X.rev e ∈ τ)
    (hE : ∀ e, e ∈ Eplus ↔ X.rev e ∉ Eplus) (a : ↥(Eplus \ τ) → G) (c : ↥(Eplus \ τ)) :
    chordTable τ Eplus hrev hE a c.1 = a c := by
  obtain ⟨e, hp, he⟩ := c
  simp [chordTable, he, hp]

end Skeleton

/-- A map that respects and reflects two relations, the second an equivalence,
and is onto, gives a bijection of the quotients. -/
private theorem nonempty_quot_equiv {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (hs : Equivalence s) (F : α → β) (h1 : ∀ a b, r a b → s (F a) (F b))
    (h2 : ∀ a b, s (F a) (F b) → r a b) (h3 : Function.Surjective F) :
    Nonempty (Quot r ≃ Quot s) := by
  refine ⟨Equiv.ofBijective (Quot.map F h1) ⟨?_, ?_⟩⟩
  · rintro ⟨a⟩ ⟨b⟩ h
    exact Quot.sound (h2 a b (hs.eqvGen_iff.mp (Quot.eq.mp h)))
  · rintro ⟨b⟩
    obtain ⟨a, rfl⟩ := h3 b
    exact ⟨Quot.mk r a, rfl⟩

/-- Simultaneous conjugation of families. -/
private def ConjRel (G ι : Type*) [Group G] (a b : ι → G) : Prop :=
  ∃ k : G, ∀ i, b i = k * a i * k⁻¹

private theorem conjRel_equivalence (G ι : Type*) [Group G] : Equivalence (ConjRel G ι) where
  refl a := ⟨1, fun i => by simp⟩
  symm := by
    rintro a b ⟨k, hk⟩
    exact ⟨k⁻¹, fun i => by rw [hk]; group⟩
  trans := by
    rintro a b c ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k' * k, fun i => by rw [hk', hk]; group⟩

/-- Renaming the index set of the families. -/
private theorem nonempty_conj_reindex (G : Type*) [Group G] {ι κ : Type*} (e : ι ≃ κ) :
    Nonempty (Quot (ConjRel G ι) ≃ Quot (ConjRel G κ)) := by
  refine nonempty_quot_equiv (conjRel_equivalence G κ) (fun a i => a (e.symm i)) ?_ ?_ ?_
  · rintro a b ⟨k, hk⟩
    exact ⟨k, fun i => hk _⟩
  · rintro a b ⟨k, hk⟩
    exact ⟨k, fun i => by simpa using hk (e i)⟩
  · intro a
    exact ⟨fun i => a (e i), by simp⟩

open Skeleton

/-- **Theorem 5.28** (spanning-tree gauge fixing). On a finite connected
transport skeleton with a spanning tree `τ`, every link table is gauge
equivalent to one that is `1` on `τ`; the gauge changes keeping that
normalization are the constant ones, which conjugate every label by the same
element; and `LinkTable(K, G)/𝒢_K ≅ G^{|E⁺(K)| − |C₀(K)| + 1}/G`. -/
@[book "thm:tree-gauge-fixing"]
theorem treeGaugeFixing : Statement.treeGaugeFixing := by
  intro X _ _ G _ τ hne _ htree
  obtain ⟨r⟩ := hne
  have hrev := htree.1
  let P := treePaths htree r
  refine ⟨fun U => ⟨P.gfix U, ⟨_, rfl⟩, fun e he => P.gfix_tree he U⟩, ?_, ?_, ?_⟩
  · -- the gauge changes that keep the normalization are the constant ones
    intro U hU h
    constructor
    · intro hh
      have hh' : ∀ e ∈ τ, h (X.tgt e) = h (X.src e) := by
        intro e he
        have := hh e he
        rw [gaugeAct_apply, hU e he, mul_one, mul_inv_eq_one] at this
        exact this
      exact ⟨h r, fun v => const_along h hh' (P.p v) (P.tau v)⟩
    · rintro ⟨k, hk⟩ e he
      rw [gaugeAct_apply, hU e he, hk, hk, mul_one, mul_inv_cancel]
  · -- a constant gauge change conjugates every label
    intro U _ k e _
    rfl
  · -- the count
    intro Eplus hE
    -- the chord values of the normalized table
    let F : X.LinkTable G → ↥(Eplus \ τ) → G := fun U c => P.gfix U c.1
    have hA : Nonempty (Quot (GaugeEquivalent (X := X) (G := G)) ≃
        Quot (ConjRel G ↥(Eplus \ τ))) := by
      refine nonempty_quot_equiv (conjRel_equivalence G _) F ?_ ?_ ?_
      · rintro U U' ⟨h, rfl⟩
        exact ⟨h r, fun c => by simp only [F, P.gfix_gaugeAct, gaugeAct_apply]⟩
      · rintro U U' ⟨k, hk⟩
        have hfix : P.gfix U' = gaugeAct (fun _ => k) (P.gfix U) := by
          ext e
          rw [gaugeAct_apply]
          by_cases he : e ∈ τ
          · rw [P.gfix_tree he, P.gfix_tree he, mul_one, mul_inv_cancel]
          · by_cases hp : e ∈ Eplus
            · exact hk ⟨e, hp, he⟩
            · have hc : X.rev e ∈ Eplus \ τ :=
                ⟨(hE (X.rev e)).mpr (by rwa [X.rev_rev]), fun h => he ((hrev e).mpr h)⟩
              have h1 := hk ⟨X.rev e, hc⟩
              simp only [F, (P.gfix U').reversal, (P.gfix U).reversal] at h1
              rw [← inv_inv (P.gfix U' e), h1]
              group
        have e1 : GaugeEquivalent U (P.gfix U) := ⟨_, rfl⟩
        have e2 : GaugeEquivalent U' (P.gfix U') := ⟨_, rfl⟩
        have e3 : GaugeEquivalent (P.gfix U) (P.gfix U') := ⟨_, hfix.symm⟩
        exact gaugeEquivalent_equivalence.trans (gaugeEquivalent_equivalence.trans e1 e3)
          (gaugeEquivalent_equivalence.symm e2)
      · intro a
        refine ⟨chordTable τ Eplus hrev hE a, funext fun c => ?_⟩
        simp only [F]
        rw [P.gfix_of_tree _ (chordTable_tree τ Eplus hrev hE a), chordTable_chord]
    -- the tree has `|C₀(K)| − 1` edges in `E⁺(K)`
    have htree_card : Nat.card ↥(Eplus ∩ τ) + 1 = Nat.card X.V := by
      classical
      -- each tree edge, or its reverse, points away from the root
      have hd : ∀ x ∈ τ, ∃ y, P.Down y ∧
          X.tgt y = (if P.Down x then X.tgt x else X.src x) ∧ (x = y ∨ x = X.rev y) := by
        intro x hx
        by_cases h : P.Down x
        · exact ⟨x, h, by rw [ite_eq_left h], Or.inl rfl⟩
        · refine ⟨X.rev x, (P.down_or hx).resolve_left h, by rw [ite_eq_right h, X.tgt_rev],
            Or.inr (X.rev_rev x).symm⟩
      have hne : ∀ x ∈ τ, (if P.Down x then X.tgt x else X.src x) ≠ r := by
        intro x hx
        obtain ⟨y, hy, hty, -⟩ := hd x hx
        rw [← hty]
        exact P.tgt_ne_root hy
      let f : ↥(Eplus ∩ τ) → {v // v ≠ r} := fun e =>
        ⟨if P.Down e.1 then X.tgt e.1 else X.src e.1, hne e.1 e.2.2⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨x, hp, hx⟩ ⟨x', hp', hx'⟩ hxx
          have hv := congrArg Subtype.val hxx
          obtain ⟨y, hy, hty, hxy⟩ := hd x hx
          obtain ⟨y', hy', hty', hxy'⟩ := hd x' hx'
          have hyy : y = y' := P.down_unique hy hy' (by rw [hty, hty']; exact hv)
          subst hyy
          refine Subtype.ext ?_
          rcases hxy with rfl | rfl <;> rcases hxy' with rfl | rfl
          · rfl
          · exact absurd hp' ((hE x).mp hp)
          · exact absurd hp ((hE x').mp hp')
          · rfl
        · rintro ⟨v, hv⟩
          obtain ⟨a, ha, hda, hta⟩ := P.exists_down hv
          by_cases hp : a ∈ Eplus
          · refine ⟨⟨a, hp, ha⟩, Subtype.ext ?_⟩
            change (if P.Down a then X.tgt a else X.src a) = v
            rw [ite_eq_left hda, hta]
          · have hp' : X.rev a ∈ Eplus := (hE (X.rev a)).mpr (by rwa [X.rev_rev])
            refine ⟨⟨X.rev a, hp', (hrev a).mp ha⟩, Subtype.ext ?_⟩
            change (if P.Down (X.rev a) then X.tgt (X.rev a) else X.src (X.rev a)) = v
            rw [ite_eq_right fun h => P.not_down_and a ⟨hda, h⟩, X.src_rev, hta]
      rw [Nat.card_eq_of_bijective f hf, ← Finite.card_option,
        Nat.card_congr (Equiv.optionSubtypeNe r)]
    have hcard : Nat.card ↥(Eplus \ τ) = Nat.card Eplus + 1 - Nat.card X.V := by
      have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard Eplus τ
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
      omega
    obtain ⟨φ₁⟩ := hA
    obtain ⟨φ₂⟩ := nonempty_conj_reindex G ((Finite.equivFin ↥(Eplus \ τ)).trans (finCongr hcard))
    exact ⟨φ₁.trans φ₂⟩

/-! ## Non-vacuity

The book's example: on the two squares, the top edges and the three uprights,
`e₂, e₃, e₄, e₆, e₇`, form a spanning tree, and `e₁`, `e₅` are its chords. The
stored directions are one orientation of each edge. To check that the five
edges form a tree, the reduced paths along them are compared through a free
group: each edge is a generator, the holonomy of a path along the tree
telescopes to `c_w c_u⁻¹`, and a reduced path is the reduced word it spells. -/

namespace Skeleton

variable {X : Skeleton}

namespace Path

open Classical in
/-- `e` after the path `γ`, with an immediate backtrack cancelled. -/
private noncomputable def consRed {u : X.V} (e : X.E) :
    ∀ {w : X.V}, X.Path u w → w = X.src e → X.Path u (X.tgt e)
  | _, .nil _, h => .cons e ((Path.nil u).cast rfl h)
  | _, .cons e' γ, h =>
    if hb : e' = X.rev e then γ.cast rfl (by rw [hb, X.src_rev])
    else .cons e ((Path.cons e' γ).cast rfl h)

private theorem consRed_spec {u : X.V} (e : X.E) :
    ∀ {w : X.V} (γ : X.Path u w) (h : w = X.src e),
      (∀ a ∈ (consRed e γ h).edges, a = e ∨ a ∈ γ.edges) ∧
        (γ.Reduced → (consRed e γ h).Reduced)
  | _, .nil _, h => by
    subst h
    refine ⟨fun a ha => ?_, fun _ => ?_⟩
    · simp only [consRed, edges, edges_cast, List.mem_singleton] at ha
      exact Or.inl ha
    · simp [consRed, Reduced, edges]
  | _, .cons e' γ, h => by
    by_cases hb : e' = X.rev e
    · simp only [consRed, hb, dite_true, edges_cast]
      refine ⟨fun a ha => Or.inr (List.mem_cons_of_mem _ ha), fun hr => ?_⟩
      unfold Reduced at hr ⊢
      rw [edges_cast]
      exact hr.tail
    · simp only [consRed, hb, dite_false]
      refine ⟨fun a ha => ?_, fun hr => ?_⟩
      · simp only [edges, edges_cast, List.mem_cons] at ha
        rcases ha with rfl | rfl | ha
        · exact Or.inl rfl
        · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ ha)
      · unfold Reduced at hr ⊢
        simp only [edges, edges_cast] at hr ⊢
        refine List.IsChain.cons hr fun y hy hey => hb ?_
        rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        rw [hey, X.rev_rev]
        exact hy

/-- Free reduction: the path with its immediate backtracks cancelled. -/
private noncomputable def reduce {u : X.V} : ∀ {v : X.V}, X.Path u v → X.Path u v
  | _, .nil _ => .nil _
  | _, .cons e γ => consRed e (reduce γ) rfl

private theorem reduce_spec {u : X.V} : ∀ {v : X.V} (γ : X.Path u v),
    (∀ a ∈ (reduce γ).edges, a ∈ γ.edges) ∧ (reduce γ).Reduced
  | _, .nil _ => ⟨by simp [reduce, edges], by simp [reduce, Reduced, edges]⟩
  | _, .cons e γ => by
    obtain ⟨h1, h2⟩ := reduce_spec γ
    obtain ⟨h3, h4⟩ := consRed_spec e (reduce γ) rfl
    refine ⟨fun a ha => ?_, h4 h2⟩
    rcases h3 a ha with rfl | ha'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h1 a ha')

end Path

open Classical in
/-- A set of edges is a spanning tree if it joins every two vertices and its
edges can be named by distinct generators `ℓ(e)` of a free group, with
`ℓ(ē) = ℓ(e)⁻¹`, so that each generator is `c_{t(e)} c_{s(e)}⁻¹` for some
elements `c_v`: then the reduced paths along it with given ends spell one
reduced word, `c_w c_u⁻¹`. -/
private theorem isSpanningTree_of_certificate {α : Type*} (τ : Set X.E)
    (hrev : ∀ e, e ∈ τ ↔ X.rev e ∈ τ) (ℓ : X.E → α × Bool)
    (hℓrev : ∀ e ∈ τ, ℓ (X.rev e) = ((ℓ e).1, !(ℓ e).2))
    (hℓinj : ∀ e ∈ τ, ∀ e' ∈ τ, ℓ e = ℓ e' → e = e')
    (c : X.V → FreeGroup α)
    (hc : ∀ e ∈ τ, FreeGroup.mk [ℓ e] = c (X.tgt e) * (c (X.src e))⁻¹)
    (hconn : ∀ u v, ∃ γ : X.Path u v, ∀ e ∈ γ.edges, e ∈ τ) : X.IsSpanningTree τ := by
  have tele : ∀ {u w : X.V} (γ : X.Path u w), (∀ e ∈ γ.edges, e ∈ τ) →
      FreeGroup.mk (γ.edges.map ℓ) = c w * (c u)⁻¹ := by
    intro u w γ hγ
    induction γ with
    | nil =>
      rw [mul_inv_cancel]
      rfl
    | cons e γ ih =>
      have he : e ∈ τ := hγ e List.mem_cons_self
      have := ih fun a ha => hγ a (List.mem_cons_of_mem _ ha)
      rw [Path.edges, List.map_cons, ← List.singleton_append, ← FreeGroup.mul_mk, this,
        hc e he]
      group
  have red : ∀ l : List X.E, (∀ e ∈ l, e ∈ τ) → l.IsChain (fun a b => a ≠ X.rev b) →
      FreeGroup.IsReduced (l.map ℓ) := by
    intro l hl hch
    unfold FreeGroup.IsReduced
    rw [List.isChain_map]
    refine hch.imp_of_mem_imp fun a b ha hb hab h1 => ?_
    by_contra h2
    apply hab
    refine hℓinj a (hl a ha) (X.rev b) ((hrev b).mp (hl b hb)) ?_
    rw [hℓrev b (hl b hb)]
    refine Prod.ext h1 ?_
    revert h2
    cases (ℓ a).2 <;> cases (ℓ b).2 <;> simp
  have inj : ∀ l l' : List X.E, (∀ e ∈ l, e ∈ τ) → (∀ e ∈ l', e ∈ τ) →
      l.map ℓ = l'.map ℓ → l = l' := by
    intro l
    induction l with
    | nil => intro l' _ _ h; exact (List.map_eq_nil_iff.mp h.symm).symm
    | cons a l ih =>
      intro l' hl hl' h
      cases l' with
      | nil => simp at h
      | cons b l' =>
        simp only [List.map_cons, List.cons.injEq] at h
        rw [hℓinj a (hl a List.mem_cons_self) b (hl' b List.mem_cons_self) h.1,
          ih l' (fun x hx => hl x (List.mem_cons_of_mem _ hx))
            (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) h.2]
  refine ⟨hrev, fun u v => ?_⟩
  obtain ⟨γ, hγ⟩ := hconn u v
  have hr := Path.reduce_spec γ
  have hrτ : ∀ e ∈ (Path.reduce γ).edges, e ∈ τ := fun e he => hγ e (hr.1 e he)
  refine ⟨Path.reduce γ, ⟨hrτ, hr.2⟩, ?_⟩
  rintro δ ⟨hδτ, hδred⟩
  refine Path.eq_of_edges_eq (inj _ _ hδτ hrτ ?_)
  rw [← (FreeGroup.isReduced_iff_reduce_eq).mp (red _ hδτ hδred),
    ← (FreeGroup.isReduced_iff_reduce_eq).mp (red _ hrτ hr.2), ← FreeGroup.toWord_mk,
    ← FreeGroup.toWord_mk, tele δ hδτ, tele _ hrτ]

namespace TwoSquares

open Vertex Edge

/-- The spanning tree of the two squares: the top edges and the three uprights,
`e₂, e₃, e₄, e₆, e₇`, with both traversals. -/
private def tree : Set skeleton.E := {s | s.1 ≠ e₁ ∧ s.1 ≠ e₅}

/-- One orientation of each edge: the stored one. -/
private def stored : Set skeleton.E := {s | s.2 = true}

/-- The paths along the tree from `v₂`. -/
private def fromV₂ : (v : Vertex) → skeleton.Path v₂ v
  | v₀ => .cons (along e₄) (.cons (along e₃) (.nil _))
  | v₁ => .cons (against e₂) (.nil _)
  | v₂ => .nil _
  | v₃ => .cons (along e₃) (.nil _)
  | v₄ => .cons (against e₆) (.cons (against e₇) (.nil _))
  | v₅ => .cons (against e₇) (.nil _)

/-- The elements `c_v` of the certificate: the word of the path from `v₂`. -/
private def word : Vertex → FreeGroup Edge
  | v₀ => FreeGroup.of e₄ * FreeGroup.of e₃
  | v₁ => (FreeGroup.of e₂)⁻¹
  | v₂ => 1
  | v₃ => FreeGroup.of e₃
  | v₄ => (FreeGroup.of e₆)⁻¹ * (FreeGroup.of e₇)⁻¹
  | v₅ => (FreeGroup.of e₇)⁻¹

private theorem tree_rev : ∀ e, e ∈ tree ↔ skeleton.rev e ∈ tree := fun _ => Iff.rfl

private theorem isSpanningTree_tree : skeleton.IsSpanningTree tree := by
  refine isSpanningTree_of_certificate tree tree_rev id (fun _ _ => rfl)
    (fun _ _ _ _ h => h) word ?_ fun u v => ?_
  · rintro ⟨x, b⟩ hx
    change x ≠ e₁ ∧ x ≠ e₅ at hx
    have hf : ∀ a : Edge, FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := fun _ => rfl
    have ht : ∀ a : Edge, FreeGroup.mk [(a, true)] = FreeGroup.of a := fun _ => rfl
    cases x <;> cases b <;> simp_all [word, Edge.src, Edge.tgt, stepStart, stepEnd]
  · have hτ : ∀ v, ∀ e ∈ (fromV₂ v).edges, e ∈ tree := by
      intro v
      cases v <;> simp [fromV₂, Path.edges, tree, along, against]
    refine ⟨(fromV₂ v).comp (fromV₂ u).reverse, fun e he => ?_⟩
    rw [Path.edges_comp, Path.edges_reverse, List.mem_append, List.mem_reverse,
      List.mem_map] at he
    rcases he with he | ⟨a, ha, rfl⟩
    · exact hτ v e he
    · exact (tree_rev a).mp (hτ u a ha)

private theorem finite_vertex : Finite Vertex :=
  Finite.of_surjective ![v₀, v₁, v₂, v₃, v₄, v₅] fun v => by
    cases v
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

private theorem finite_edge : Finite Edge :=
  Finite.of_surjective ![e₁, e₂, e₃, e₄, e₅, e₆, e₇] fun e => by
    cases e
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]

/-- The hypotheses of Theorem 5.28 are met on the two squares: they have a
vertex, they are connected, the five edges `e₂, e₃, e₄, e₆, e₇` form a spanning
tree, and the stored directions are one orientation of each edge. -/
example : Nonempty skeleton.V ∧ skeleton.Connected ∧ skeleton.IsSpanningTree tree ∧
    ∀ e, e ∈ stored ↔ skeleton.rev e ∉ stored :=
  ⟨⟨v₀⟩, connected, isSpanningTree_tree, by rintro ⟨e, _ | _⟩ <;> simp [stored]⟩

/-- By Theorem 5.28, the link table of `fig:square-gauge` is gauge equivalent to
one that is `0` on the five tree edges. -/
example : ∃ U', GaugeEquivalent curvedTable U' ∧ ∀ e ∈ tree, U' e = 1 := by
  have := finite_vertex
  have := finite_edge
  exact (treeGaugeFixing skeleton _ tree ⟨v₀⟩ connected isSpanningTree_tree).1 curvedTable

end TwoSquares

end Skeleton

end Artform
