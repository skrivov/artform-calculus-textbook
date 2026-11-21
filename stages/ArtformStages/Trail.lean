import ArtformStages.Carry

/-!
# The trail

The map of a stage has a dot for every law and a line for every act at every dot. The
*trail* of a walk is what it leaves on the lines: crossings forward less crossings back
(THEORY.md §3.2). In the literature it is the Fox derivative of the walk's word, read in
the group ring, and the *geometric flow* of its path on the Cayley graph.

* `Stage.Chain`: a whole number on every line. `Stage.shift`: a chain looked at from a dot.
* `Stage.Magnus`: a dot with a chain. The walks act on these, and `Stage.magnus` sends a
  walk to its dot and its trail: Magnus's embedding.
* **Lemma 1** of THEORY.md: `trail_mul`, `trail_inv`, `trail_conj`.
* **Lemma 2.4**, the theorem of Magnus and Fox: a closed walk has the trail 0 exactly when
  it is made of commutators of closed walks (`trail_eq_zero_iff`).
* **T4(a)**: in the richest carry two walks are one law exactly when they end at one dot
  and leave one trail (`keep_law_eq_iff`).

The proof of Lemma 2.4 follows THEORY.md's, with any choice of a walk to each dot in place
of the first walks: no spanning tree is needed.
-/

noncomputable section

namespace Artform.Stages

open Subgroup

variable {α : Type*}

namespace Stage

variable (S : Stage α)

/-- A chain: a whole number on every line of the map. The line `(a, g)` runs from the dot
`g` by the act `a`. -/
abbrev Chain : Type _ := (α × S.World) →₀ ℤ

/-- A chain looked at from the dot `g`. -/
def shift (g : S.World) : S.Chain →+ S.Chain :=
  Finsupp.mapDomain.addMonoidHom fun p => (p.1, g * p.2)

theorem shift_single (g h : S.World) (a : α) (k : ℤ) :
    S.shift g (Finsupp.single (a, h) k) = Finsupp.single (a, g * h) k :=
  Finsupp.mapDomain_single

theorem shift_one (c : S.Chain) : S.shift 1 c = c := by
  have h : (fun p : α × S.World => (p.1, 1 * p.2)) = id := by
    funext p
    simp
  rw [shift, Finsupp.mapDomain.addMonoidHom_apply, h, Finsupp.mapDomain_id]

theorem shift_mul (g h : S.World) (c : S.Chain) : S.shift (g * h) c = S.shift g (S.shift h c) := by
  have hc : (fun p : α × S.World => (p.1, g * h * p.2)) =
      (fun p : α × S.World => (p.1, g * p.2)) ∘ fun p : α × S.World => (p.1, h * p.2) := by
    funext p
    simp [mul_assoc]
  simp only [shift, Finsupp.mapDomain.addMonoidHom_apply]
  rw [hc, Finsupp.mapDomain_comp]

/-- A dot with a chain: what the richest carry keeps of a walk. -/
@[ext]
structure Magnus where
  /-- The chain. -/
  chain : S.Chain
  /-- The dot. -/
  dot : S.World

namespace Magnus

variable {S}

instance : Mul S.Magnus := ⟨fun x y => ⟨x.chain + S.shift x.dot y.chain, x.dot * y.dot⟩⟩

instance : One S.Magnus := ⟨⟨0, 1⟩⟩

instance : Inv S.Magnus := ⟨fun x => ⟨-S.shift x.dot⁻¹ x.chain, x.dot⁻¹⟩⟩

@[simp]
theorem mul_chain (x y : S.Magnus) : (x * y).chain = x.chain + S.shift x.dot y.chain := rfl

@[simp]
theorem mul_dot (x y : S.Magnus) : (x * y).dot = x.dot * y.dot := rfl

@[simp]
theorem one_chain : (1 : S.Magnus).chain = 0 := rfl

@[simp]
theorem one_dot : (1 : S.Magnus).dot = 1 := rfl

@[simp]
theorem inv_chain (x : S.Magnus) : x⁻¹.chain = -S.shift x.dot⁻¹ x.chain := rfl

@[simp]
theorem inv_dot (x : S.Magnus) : x⁻¹.dot = x.dot⁻¹ := rfl

instance : Group S.Magnus :=
  Group.ofLeftAxioms
    (fun x y z => Magnus.ext (by simp [shift_mul, add_assoc]) (by simp [mul_assoc]))
    (fun x => Magnus.ext (by simp [shift_one]) (by simp))
    (fun x => Magnus.ext (by simp) (by simp))

/-- The dot, as a homomorphism. -/
def dotHom : S.Magnus →* S.World where
  toFun := dot
  map_one' := rfl
  map_mul' _ _ := rfl

end Magnus

/-- The dot and the trail of a walk, as one homomorphism: Magnus's embedding. -/
def magnus : FreeGroup α →* S.Magnus :=
  FreeGroup.lift fun a => ⟨Finsupp.single (a, 1) 1, S.law (FreeGroup.of a)⟩

/-- The trail of a walk begun at rest: on each line, crossings forward less back. -/
def trail (w : FreeGroup α) : S.Chain := (S.magnus w).chain

theorem magnus_dot (w : FreeGroup α) : (S.magnus w).dot = S.law w := by
  have h : Magnus.dotHom.comp S.magnus = S.law :=
    FreeGroup.ext_hom _ _ fun a => by simp [magnus, Magnus.dotHom]
  exact DFunLike.congr_fun h w

@[simp]
theorem trail_one : S.trail 1 = 0 := by
  rw [trail, map_one]
  rfl

theorem trail_of (a : α) : S.trail (FreeGroup.of a) = Finsupp.single (a, 1) 1 := by
  simp [trail, magnus]

/-- **Lemma 1.2.** The trail adds along a walk: the second part is looked at from the dot
where the first part ends. This is Fox's rule, `∂(uv) = ∂u + u·∂v`. -/
theorem trail_mul (u v : FreeGroup α) :
    S.trail (u * v) = S.trail u + S.shift (S.law u) (S.trail v) := by
  rw [trail, map_mul, Magnus.mul_chain, magnus_dot]
  rfl

/-- **Lemma 1.3.** The trail of a walk undone. -/
theorem trail_inv (u : FreeGroup α) : S.trail u⁻¹ = -S.shift (S.law u)⁻¹ (S.trail u) := by
  rw [trail, map_inv, Magnus.inv_chain, magnus_dot]
  rfl

/-- **Lemma 1.6.** After a closed walk the trail simply adds. -/
theorem trail_mul_of_mem_rest {n : FreeGroup α} (hn : n ∈ S.rest) (w : FreeGroup α) :
    S.trail (n * w) = S.trail n + S.trail w := by
  rw [trail_mul, S.law_eq_one_iff.mpr hn, shift_one]

/-- **Lemma 1.6.** A closed walk undone has the opposite trail. -/
theorem trail_inv_of_mem_rest {n : FreeGroup α} (hn : n ∈ S.rest) :
    S.trail n⁻¹ = -S.trail n := by
  rw [trail_inv, S.law_eq_one_iff.mpr hn, inv_one, shift_one]

/-- **Lemma 1.7.** A closed walk made at the end of a walk `w`, and `w` undone after it, has
the trail of the closed walk looked at from the dot of `w`. -/
theorem trail_conj (w : FreeGroup α) {n : FreeGroup α} (hn : n ∈ S.rest) :
    S.trail (w * n * w⁻¹) = S.shift (S.law w) (S.trail n) := by
  rw [trail_mul, trail_mul, trail_inv, map_mul, S.law_eq_one_iff.mpr hn, mul_one, map_neg,
    ← shift_mul, mul_inv_cancel, shift_one]
  abel

/-- The trail of a closed walk, as a homomorphism to the chains. -/
def trailRest : S.rest →* Multiplicative S.Chain where
  toFun n := Multiplicative.ofAdd (S.trail n)
  map_one' := by simp
  map_mul' n m := by
    change Multiplicative.ofAdd (S.trail ((n : FreeGroup α) * m)) = _
    rw [S.trail_mul_of_mem_rest n.2]
    rfl

/-- The easy half of Lemma 2.4: commutators of closed walks leave no trail. -/
theorem trail_eq_zero_of_mem_commutator {n : FreeGroup α} (hn : n ∈ ⁅S.rest, S.rest⁆) :
    S.trail n = 0 := by
  rw [← S.rest.map_subtype_commutator] at hn
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
  have h : x ∈ S.trailRest.ker := Abelianization.commutator_subset_ker S.trailRest hx
  exact h

/-! ### A walk to every dot -/

/-- A choice of a walk to every dot, the empty walk to rest. THEORY.md takes the first
walks; any choice serves here. -/
structure Walks where
  /-- The walk to a dot. -/
  walk : S.World → FreeGroup α
  /-- It ends at that dot. -/
  law_walk : ∀ g, S.law (walk g) = g
  /-- The walk to rest is the empty walk. -/
  walk_one : walk 1 = 1

theorem nonempty_walks : Nonempty S.Walks := by
  classical
  refine ⟨⟨fun g => if g = 1 then 1 else Function.surjInv S.law_surjective g, fun g => ?_, ?_⟩⟩
  · by_cases hg : g = 1
    · simp [hg]
    · simpa [hg] using Function.surjInv_eq S.law_surjective g
  · simp

variable {S}

/-- The walk `w` made from the dot `g`, closed up by the chosen walks: out to `g`, then
`w`, then home from where `w` ends. -/
def Walks.across (t : S.Walks) (g : S.World) (w : FreeGroup α) : S.rest :=
  ⟨t.walk g * w * (t.walk (g * S.law w))⁻¹, by
    rw [← S.law_eq_one_iff]
    simp [t.law_walk]⟩

theorem Walks.across_one (t : S.Walks) (g : S.World) : t.across g 1 = 1 := by
  ext
  simp [Walks.across]

theorem Walks.across_mul (t : S.Walks) (g : S.World) (x y : FreeGroup α) :
    t.across g (x * y) = t.across g x * t.across (g * S.law x) y := by
  ext
  simp [Walks.across, mul_assoc]

theorem Walks.across_inv (t : S.Walks) (g : S.World) (x : FreeGroup α) :
    t.across g x⁻¹ = (t.across (g * (S.law x)⁻¹) x)⁻¹ := by
  ext
  simp [Walks.across, mul_assoc]

/-- The count of a chain: each line stands for its loop, the chosen walk out, along the
line, and the chosen walk home, counted up to commutators of closed walks. -/
def Walks.count (t : S.Walks) : S.Chain →+ Additive (Abelianization S.rest) :=
  Finsupp.liftAddHom fun p =>
    zmultiplesHom _ (Additive.ofMul (Abelianization.of (t.across p.2 (FreeGroup.of p.1))))

theorem Walks.count_single (t : S.Walks) (a : α) (g : S.World) :
    t.count (Finsupp.single (a, g) 1) =
      Additive.ofMul (Abelianization.of (t.across g (FreeGroup.of a))) := by
  simp [Walks.count]

/-- The heart of Lemma 2.4: the count of the trail of a walk, looked at from a dot, is the
walk made from that dot and closed up, up to commutators of closed walks. -/
theorem Walks.count_shift_trail (t : S.Walks) (w : FreeGroup α) :
    ∀ g, t.count (S.shift g (S.trail w)) = Additive.ofMul (Abelianization.of (t.across g w)) := by
  induction w using FreeGroup.induction_on with
  | one =>
    intro g
    rw [trail_one, map_zero, map_zero, t.across_one, map_one]
    rfl
  | of a =>
    intro g
    rw [trail_of, shift_single, mul_one, t.count_single]
  | inv_of a ih =>
    intro g
    rw [trail_inv, map_neg, map_neg, ← shift_mul, ih, t.across_inv, map_inv]
    rfl
  | mul x y hx hy =>
    intro g
    rw [trail_mul, map_add, map_add, ← shift_mul, hx, hy, t.across_mul, map_mul]
    rfl

variable (S)

/-- **Lemma 2.4** (Magnus, Fox). A closed walk has the trail 0 exactly when it is made of
commutators of closed walks. -/
theorem trail_eq_zero_iff {n : FreeGroup α} (hn : n ∈ S.rest) :
    S.trail n = 0 ↔ n ∈ ⁅S.rest, S.rest⁆ := by
  refine ⟨fun h0 => ?_, S.trail_eq_zero_of_mem_commutator⟩
  obtain ⟨t⟩ := S.nonempty_walks
  have h := t.count_shift_trail n 1
  rw [shift_one, h0, map_zero] at h
  have hn' : t.across 1 n = ⟨n, hn⟩ := by
    ext
    simp [Walks.across, t.walk_one, S.law_eq_one_iff.mpr hn]
  rw [hn'] at h
  have hker : (⟨n, hn⟩ : S.rest) ∈ (Abelianization.of (G := S.rest)).ker := h.symm
  rw [Abelianization.ker_of] at hker
  rw [← S.rest.map_subtype_commutator]
  exact Subgroup.mem_map.mpr ⟨⟨n, hn⟩, hker, rfl⟩

/-- **T4(a).** In the richest carry two walks are one law exactly when they end at one dot
and leave one trail. So a law there is a dot with a trail. -/
theorem keep_law_eq_iff {u v : FreeGroup α} :
    S.keep.law u = S.keep.law v ↔ S.law u = S.law v ∧ S.trail u = S.trail v := by
  rw [S.keep.law_eq_law_iff, rest_keep]
  have key : S.law u = S.law v → S.trail (u * v⁻¹) = S.trail u - S.trail v := by
    intro h
    rw [trail_mul, trail_inv, map_neg, ← shift_mul, h, mul_inv_cancel, shift_one, sub_eq_add_neg]
  constructor
  · intro h
    have hrest : u * v⁻¹ ∈ S.rest := commutator_le_left _ _ h
    have hlaw : S.law u = S.law v := S.law_eq_law_iff.mpr hrest
    refine ⟨hlaw, ?_⟩
    have h0 := (S.trail_eq_zero_iff hrest).mpr h
    rw [key hlaw, sub_eq_zero] at h0
    exact h0
  · rintro ⟨hlaw, htrail⟩
    have hrest : u * v⁻¹ ∈ S.rest := S.law_eq_law_iff.mp hlaw
    refine (S.trail_eq_zero_iff hrest).mp ?_
    rw [key hlaw, htrail, sub_self]

end Stage

end Artform.Stages

end
