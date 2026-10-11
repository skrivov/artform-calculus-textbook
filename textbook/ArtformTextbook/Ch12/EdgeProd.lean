import ArtformTextbook.Ch12.VertexInvariants

/-!
# Products of the two ends of an edge

In the book's order of the twelve modes of an edge (`x` before `y`, each end ordered as one
vertex), the product `u ⊗ w` of a table at `x` and a table at `y` behaves as the book's product
of states:

* a creation at `x` acts on the left factor, `a†_{x m} (u ⊗ w) = (a†_m u) ⊗ w`, since no mode of
  `y` precedes a mode of `x`; a creation at `y` acts on the right factor when `x` is empty;
* so the basis table of the edge is `|n_x ⊔ n_y⟩ = a†_{x…} ⋯ a†_{y…} ⋯ |0⟩ = |n_x⟩ ⊗ |n_y⟩`, and
  the colour rotations of the two ends act factor by factor:
  `Γ(diag(g, h) ⊗ 1) (u ⊗ w) = (Γ(g) u) ⊗ (Γ(h) w)` (`Edge.secondQuant_diag_prod`).

Hence products of invariants of the two ends are zero-flux states, and the zero-flux sector of
each model is spanned by products of the states of one vertex.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open FockCalc Spin

namespace Edge

/-! ### The book's order as a numbering -/

theorem code_lt (m : Mode (Fin 3) (Fin 2)) : code m < 12 := by
  rcases m with m | m <;> simp only [code, Sum.elim_inl, Sum.elim_inr] <;>
    have := Vertex.code_lt m <;> omega

theorem numbering : Numbering code 12 bookOrd where
  inj := code_injective
  lt := code_lt
  surj := by
    intro i hi
    by_cases h6 : i < 6
    · obtain ⟨m, hm⟩ := Vertex.numbering.surj i h6
      exact ⟨Sum.inl m, hm⟩
    · obtain ⟨m, hm⟩ := Vertex.numbering.surj (i - 6) (by omega)
      exact ⟨Sum.inr m, by simp only [code, Sum.elim_inr]; omega⟩
  ord_lt _ _ := Iff.rfl

theorem lt_inl_iff (a : Mode (Fin 3) (Fin 2)) (m : Fin 3 × Fin 2) :
    bookOrd.lt a (Sum.inl m) ↔ ∃ m', a = Sum.inl m' ∧ Vertex.bookOrd.lt m' m := by
  change code a < code (Sum.inl m) ↔ _
  rcases a with m' | m'
  · simp only [code, Sum.elim_inl, Sum.inl.injEq, exists_eq_left']
    rfl
  · simp only [code, Sum.elim_inr, Sum.elim_inl, reduceCtorEq, false_and, exists_false,
      iff_false, not_lt]
    have := Vertex.code_lt m
    omega

theorem lt_inr_iff (a : Mode (Fin 3) (Fin 2)) (m : Fin 3 × Fin 2) :
    bookOrd.lt a (Sum.inr m) ↔ a.isLeft ∨ ∃ m', a = Sum.inr m' ∧ Vertex.bookOrd.lt m' m := by
  change code a < code (Sum.inr m) ↔ _
  rcases a with m' | m'
  · simp only [code, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, true_or, iff_true]
    have := Vertex.code_lt m'
    omega
  · simp only [code, Sum.elim_inr, Sum.isLeft_inr, Bool.false_eq_true, Sum.inr.injEq,
      exists_eq_left', false_or]
    change 6 + Vertex.code m' < 6 + Vertex.code m ↔ Vertex.code m' < Vertex.code m
    omega

/-! ### Products of tables -/

theorem prod_ket (a b : Finset (Fin 3 × Fin 2)) :
    prod (Fock.ket a) (Fock.ket b) = Fock.ket (a.disjSum b) := by
  funext n
  simp only [prod, Fock.ket, Pi.single_apply]
  by_cases h : n = a.disjSum b
  · subst h
    simp
  · rw [ite_eq_right h]
    by_cases ha : n.toLeft = a
    · by_cases hb : n.toRight = b
      · exact absurd (by rw [← ha, ← hb, Finset.toLeft_disjSum_toRight]) h
      · simp [hb]
    · simp [ha]

theorem prod_add_left (u u' w : Finset (Fin 3 × Fin 2) → ℂ) :
    prod (u + u') w = prod u w + prod u' w := by
  funext n
  simp [prod, add_mul]

theorem prod_add_right (u w w' : Finset (Fin 3 × Fin 2) → ℂ) :
    prod u (w + w') = prod u w + prod u w' := by
  funext n
  simp [prod, mul_add]

theorem prod_smul_left (c : ℂ) (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    prod (c • u) w = c • prod u w := by
  funext n
  simp [prod, mul_assoc]

theorem prod_smul_right (c : ℂ) (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    prod u (c • w) = c • prod u w := by
  funext n
  simp [prod, mul_left_comm]

theorem prod_sum_left {ι : Type*} (s : Finset ι) (u : ι → Finset (Fin 3 × Fin 2) → ℂ)
    (w : Finset (Fin 3 × Fin 2) → ℂ) : prod (∑ i ∈ s, u i) w = ∑ i ∈ s, prod (u i) w := by
  funext n
  simp [prod, Finset.sum_mul]

theorem prod_sum_right {ι : Type*} (s : Finset ι) (u : Finset (Fin 3 × Fin 2) → ℂ)
    (w : ι → Finset (Fin 3 × Fin 2) → ℂ) : prod u (∑ i ∈ s, w i) = ∑ i ∈ s, prod u (w i) := by
  funext n
  simp [prod, Finset.mul_sum]

/-- A table is the sum of its coefficients times the basis tables. -/
theorem eq_sum_ket {M : Type*} [Fintype M] [DecidableEq M] (u : Finset M → ℂ) :
    u = ∑ a, u a • Fock.ket a := by
  funext n
  simp [Fock.ket, Pi.single_apply]

/-! ### Creations at the two ends -/

theorem precCount_inl (a b : Finset (Fin 3 × Fin 2)) (m : Fin 3 × Fin 2) :
    Fock.precCount bookOrd (a.disjSum b) (Sum.inl m) = Fock.precCount Vertex.bookOrd a m := by
  unfold Fock.precCount
  refine Finset.card_bij (fun x hx => Sum.getLeft x ?_) ?_ ?_ ?_
  · rw [Finset.mem_filter] at hx
    obtain ⟨m', rfl, -⟩ := (lt_inl_iff x m).mp hx.2
    rfl
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨m', rfl, hlt⟩ := (lt_inl_iff x m).mp hx.2
    exact ⟨Finset.inl_mem_disjSum.mp hx.1, hlt⟩
  · intro x hx x' hx' h
    rw [Finset.mem_filter] at hx hx'
    obtain ⟨m', rfl, -⟩ := (lt_inl_iff x m).mp hx.2
    obtain ⟨m'', rfl, -⟩ := (lt_inl_iff x' m).mp hx'.2
    simpa using h
  · intro y hy
    rw [Finset.mem_filter] at hy
    exact ⟨Sum.inl y, Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hy.1,
      (lt_inl_iff _ m).mpr ⟨y, rfl, hy.2⟩⟩, rfl⟩

theorem precCount_inr (b : Finset (Fin 3 × Fin 2)) (m : Fin 3 × Fin 2) :
    Fock.precCount bookOrd ((∅ : Finset (Fin 3 × Fin 2)).disjSum b) (Sum.inr m) =
      Fock.precCount Vertex.bookOrd b m := by
  unfold Fock.precCount
  refine Finset.card_bij (fun x hx => Sum.getRight x ?_) ?_ ?_ ?_
  · rw [Finset.mem_filter] at hx
    rcases (lt_inr_iff x m).mp hx.2 with h | ⟨m', rfl, -⟩
    · rcases x with x | x
      · simp at hx
      · simp at h
    · rfl
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    rcases (lt_inr_iff x m).mp hx.2 with h | ⟨m', rfl, hlt⟩
    · rcases x with x | x
      · simp at hx
      · simp at h
    · exact ⟨Finset.inr_mem_disjSum.mp hx.1, hlt⟩
  · intro x hx x' hx' h
    rcases x with x | x
    · simp [Finset.mem_filter] at hx
    rcases x' with x' | x'
    · simp [Finset.mem_filter] at hx'
    simpa using h
  · intro y hy
    rw [Finset.mem_filter] at hy
    exact ⟨Sum.inr y, Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mpr hy.1,
      (lt_inr_iff _ m).mpr (Or.inr ⟨y, rfl, hy.2⟩)⟩, rfl⟩

/-- A creation at `x` acts on the left factor. -/
theorem creation_inl_prod (m : Fin 3 × Fin 2) (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.creation bookOrd (Sum.inl m) *ᵥ prod u w =
      prod (Fock.creation Vertex.bookOrd m *ᵥ u) w := by
  have key : ∀ a b, Fock.creation bookOrd (Sum.inl m) *ᵥ prod (Fock.ket a) (Fock.ket b) =
      prod (Fock.creation Vertex.bookOrd m *ᵥ Fock.ket a) (Fock.ket b) := by
    intro a b
    rw [prod_ket, Fock.creation_mulVec_ket, Fock.creation_mulVec_ket]
    by_cases hm : m ∈ a
    · rw [ite_eq_left (Finset.inl_mem_disjSum.mpr hm), ite_eq_left hm]
      funext n
      simp [prod]
    · rw [ite_eq_right (by simpa using hm), ite_eq_right hm, prod_smul_left, prod_ket,
        precCount_inl]
      congr 2
      ext x
      rcases x with x | x <;> simp
  rw [eq_sum_ket u, eq_sum_ket w]
  simp only [prod_sum_left, prod_sum_right, prod_smul_left, prod_smul_right, Matrix.mulVec_sum,
    Matrix.mulVec_smul, key]

/-- A creation at `y` acts on the right factor when `x` is empty. -/
theorem creation_inr_prod_empty (m : Fin 3 × Fin 2) (w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.creation bookOrd (Sum.inr m) *ᵥ prod (Fock.ket ∅) w =
      prod (Fock.ket ∅) (Fock.creation Vertex.bookOrd m *ᵥ w) := by
  have key : ∀ b, Fock.creation bookOrd (Sum.inr m) *ᵥ prod (Fock.ket ∅) (Fock.ket b) =
      prod (Fock.ket ∅) (Fock.creation Vertex.bookOrd m *ᵥ Fock.ket b) := by
    intro b
    rw [prod_ket, Fock.creation_mulVec_ket, Fock.creation_mulVec_ket]
    by_cases hm : m ∈ b
    · rw [ite_eq_left (Finset.inr_mem_disjSum.mpr hm), ite_eq_left hm]
      funext n
      simp [prod]
    · rw [ite_eq_right (by simpa using hm), ite_eq_right hm, prod_smul_right, prod_ket,
        precCount_inr]
      congr 2
      ext x
      rcases x with x | x <;> simp
  rw [eq_sum_ket w]
  simp only [prod_sum_right, prod_smul_right, Matrix.mulVec_sum, Matrix.mulVec_smul, key]

/-! ### The colour rotations of the two ends act factor by factor -/

/-- `g ⊗ 1` on the six modes of one vertex. -/
abbrev kron (g : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) g (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem tc_inl (g h : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 3 × Fin 2) :
    Fock.transformedCreation bookOrd (diag g h) (Sum.inl m) =
      ∑ m' : Fin 3 × Fin 2, kron g m' m • Fock.creation bookOrd (Sum.inl m') := by
  rw [Fock.transformedCreation, Fintype.sum_sum_type]
  simp [diag]

theorem tc_inr (g h : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 3 × Fin 2) :
    Fock.transformedCreation bookOrd (diag g h) (Sum.inr m) =
      ∑ m' : Fin 3 × Fin 2, kron h m' m • Fock.creation bookOrd (Sum.inr m') := by
  rw [Fock.transformedCreation, Fintype.sum_sum_type]
  simp [diag]

theorem tc_inl_prod (g h : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 3 × Fin 2)
    (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.transformedCreation bookOrd (diag g h) (Sum.inl m) *ᵥ prod u w =
      prod (Fock.transformedCreation Vertex.bookOrd (kron g) m *ᵥ u) w := by
  rw [tc_inl, Fock.transformedCreation]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, creation_inl_prod, prod_sum_left,
    prod_smul_left]

theorem tc_inr_prod_empty (g h : Matrix (Fin 3) (Fin 3) ℂ) (m : Fin 3 × Fin 2)
    (w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.transformedCreation bookOrd (diag g h) (Sum.inr m) *ᵥ prod (Fock.ket ∅) w =
      prod (Fock.ket ∅) (Fock.transformedCreation Vertex.bookOrd (kron h) m *ᵥ w) := by
  rw [tc_inr, Fock.transformedCreation]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, creation_inr_prod_empty, prod_sum_right,
    prod_smul_right]

theorem trProd_inl_prod (g h : Matrix (Fin 3) (Fin 3) ℂ) (L : List (Fin 3 × Fin 2))
    (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.trProd bookOrd (diag g h) (L.map Sum.inl) *ᵥ prod u w =
      prod (Fock.trProd Vertex.bookOrd (kron g) L *ᵥ u) w := by
  induction L generalizing u with
  | nil => simp [Fock.trProd]
  | cons m L ih =>
    simp only [Fock.trProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [← Matrix.mulVec_mulVec, ih, tc_inl_prod, Matrix.mulVec_mulVec]

theorem trProd_inr_prod_empty (g h : Matrix (Fin 3) (Fin 3) ℂ) (L : List (Fin 3 × Fin 2))
    (w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.trProd bookOrd (diag g h) (L.map Sum.inr) *ᵥ prod (Fock.ket ∅) w =
      prod (Fock.ket ∅) (Fock.trProd Vertex.bookOrd (kron h) L *ᵥ w) := by
  induction L generalizing w with
  | nil => simp [Fock.trProd]
  | cons m L ih =>
    simp only [Fock.trProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [← Matrix.mulVec_mulVec, ih, tc_inr_prod_empty, Matrix.mulVec_mulVec]

theorem ket_empty_eq_prod :
    (Fock.ket ∅ : Finset (Mode (Fin 3) (Fin 2)) → ℂ) = prod (Fock.ket ∅) (Fock.ket ∅) := by
  rw [prod_ket]
  rfl

theorem crProd_eq_trProd_one (L : List (Mode (Fin 3) (Fin 2))) :
    Fock.crProd bookOrd L = Fock.trProd bookOrd (diag 1 1) L := by
  rw [Fock.crProd, Fock.trProd, diag_one]
  congr 1
  exact List.map_congr_left fun m _ => (Fock.transformedCreation_one bookOrd m).symm

theorem exists_crProd {M : Type*} [Fintype M] [DecidableEq M] (ord : LinearOrder M)
    (n : Finset M) : ∃ L : List M, Fock.crProd ord L *ᵥ Fock.ket ∅ = Fock.ket n :=
  ⟨_, Fock.crProd_sort_mulVec_vacuum ord n⟩

theorem trProd_one_vertex (L : List (Fin 3 × Fin 2)) :
    Fock.trProd Vertex.bookOrd (kron 1) L = Fock.crProd Vertex.bookOrd L := by
  rw [kron, Matrix.one_kronecker_one, Fock.trProd, Fock.crProd]
  congr 1
  exact List.map_congr_left fun m _ => Fock.transformedCreation_one Vertex.bookOrd m

/-- The basis table of the edge is the product of the creations of its modes at `x`, then at
`y`, on the empty edge. -/
theorem ket_disjSum {a b : Finset (Fin 3 × Fin 2)} {xs ys : List (Fin 3 × Fin 2)}
    (hx : Fock.crProd Vertex.bookOrd xs *ᵥ Fock.ket ∅ = Fock.ket a)
    (hy : Fock.crProd Vertex.bookOrd ys *ᵥ Fock.ket ∅ = Fock.ket b) :
    Fock.ket (a.disjSum b) =
      Fock.crProd bookOrd (xs.map Sum.inl ++ ys.map Sum.inr) *ᵥ Fock.ket ∅ := by
  rw [crProd_eq_trProd_one, Fock.trProd, List.map_append, List.prod_append, ← Fock.trProd,
    ← Fock.trProd, ← Matrix.mulVec_mulVec, ket_empty_eq_prod, trProd_inr_prod_empty,
    trProd_inl_prod, trProd_one_vertex, trProd_one_vertex, hx, hy, prod_ket]

/-- **The colour rotations of the two ends act factor by factor**:
`Γ(diag(g, h) ⊗ 1) (u ⊗ w) = (Γ(g) u) ⊗ (Γ(h) w)`. -/
theorem secondQuant_diag_prod (g h : Matrix (Fin 3) (Fin 3) ℂ)
    (u w : Finset (Fin 3 × Fin 2) → ℂ) :
    Fock.secondQuant bookOrd (diag g h) *ᵥ prod u w =
      prod (Fock.vertexGamma Vertex.bookOrd g *ᵥ u) (Fock.vertexGamma Vertex.bookOrd h *ᵥ w) := by
  have key : ∀ a b, Fock.secondQuant bookOrd (diag g h) *ᵥ prod (Fock.ket a) (Fock.ket b) =
      prod (Fock.vertexGamma Vertex.bookOrd g *ᵥ Fock.ket a)
        (Fock.vertexGamma Vertex.bookOrd h *ᵥ Fock.ket b) := by
    intro a b
    obtain ⟨xs, hx⟩ := exists_crProd Vertex.bookOrd a
    obtain ⟨ys, hy⟩ := exists_crProd Vertex.bookOrd b
    rw [prod_ket, ket_disjSum hx hy, Fock.secondQuant_mulVec_crProd, Fock.trProd,
      List.map_append, List.prod_append, ← Fock.trProd, ← Fock.trProd, ← Matrix.mulVec_mulVec,
      ket_empty_eq_prod, trProd_inr_prod_empty, trProd_inl_prod, ← hx, ← hy, Fock.vertexGamma,
      Fock.vertexGamma, Fock.secondQuant_mulVec_crProd, Fock.secondQuant_mulVec_crProd]
  rw [eq_sum_ket u, eq_sum_ket w]
  simp only [prod_sum_left, prod_sum_right, prod_smul_left, prod_smul_right, Matrix.mulVec_sum,
    Matrix.mulVec_smul, key]

end Edge

end Artform
