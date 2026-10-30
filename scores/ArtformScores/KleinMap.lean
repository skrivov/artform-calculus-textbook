import ArtformScores.ExtentTable

/-!
# The regular map of a dial

The ledger's finding 038, Theorem U (Klein 1878-79). The vertices are the primitive states of `Z/n`
up to sign, the edges the pairs with determinant `±1`, the faces the triangles `{u, v, u + v}`.
- **The map.** `PSL(2, Z/n)` acts simply transitively on the directed edges: a directed edge is the
  pair of columns of a law, up to sign. Orbit and stabilizer give `V = |PSL|/n`, `E = |PSL|/2` and
  `F = |PSL|/3`.
- **The steps are turns.** The kick fixes `E` and turns its link, and the move fixes `B`.
- **The tick.** By `tr g · det(u, v) = det(g u, v) + det(u, g v)`, a law that fixes a vertex has the
  trace `±2`, one that flips an edge `0`, and one that turns a face `±1`.
-/

namespace Artform.Scores.Klein

open Matrix (SpecialLinearGroup)
open Bells

variable {n : ℕ}

theorem cls_eq_iff {u v : State n} : cls u = cls v ↔ u = v ∨ u = -v :=
  Quotient.eq (r := signSetoid n)

theorem act_mul (g h : SpecialLinearGroup (Fin 2) (ZMod n)) (u : State n) :
    act (g * h) u = act g (act h u) := by
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Prod.mk.injEq]
  constructor <;> ring

theorem act_one (u : State n) : act 1 u = u := by
  simp [act]

theorem act_neg (g : SpecialLinearGroup (Fin 2) (ZMod n)) (u : State n) :
    act g (-u) = -act g u := by
  simp only [act, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, Prod.mk.injEq]
  constructor <;> ring

theorem act_neg_left (g : SpecialLinearGroup (Fin 2) (ZMod n)) (u : State n) :
    act (-g) u = -act g u := by
  simp only [act, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Prod.neg_mk, Prod.mk.injEq]
  constructor <;> ring

theorem act_add (g : SpecialLinearGroup (Fin 2) (ZMod n)) (u v : State n) :
    act g (u + v) = act g u + act g v := by
  simp only [act, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem det2_act (g : SpecialLinearGroup (Fin 2) (ZMod n)) (u v : State n) :
    det2 (act g u) (act g v) = det2 u v := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  simp only [det2, act]
  linear_combination (u.1 * v.2 - u.2 * v.1) * h

/-- The law with the columns `u` and `v`. -/
def ofColumns (u v : State n) (h : det2 u v = 1) : SpecialLinearGroup (Fin 2) (ZMod n) :=
  ⟨!![u.1, v.1; u.2, v.2], by
    rw [Matrix.det_fin_two_of]
    simp only [det2] at h
    linear_combination h⟩

theorem act_ofColumns_eB (u v : State n) (h : det2 u v = 1) : act (ofColumns u v h) eB = u := by
  simp [act, ofColumns, eB]

theorem act_ofColumns_eE (u v : State n) (h : det2 u v = 1) : act (ofColumns u v h) eE = v := by
  simp [act, ofColumns, eE]

theorem det2_eB_eE : det2 (eB : State n) eE = 1 := by
  simp [det2, eB, eE]

theorem law_ext {g h : SpecialLinearGroup (Fin 2) (ZMod n)} (h1 : act g eB = act h eB)
    (h2 : act g eE = act h eE) : g = h := by
  simp only [act, eB, eE, Prod.mk.injEq, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1.1
  · exact h2.1
  · exact h1.2
  · exact h2.2

local notation "SLn" => SpecialLinearGroup (Fin 2) (ZMod n)

theorem toDir_mem (g : SLn) : toDir g ∈ dirEdges n :=
  ⟨act g eB, act g eE, by rw [det2_act, det2_eB_eE], rfl, rfl⟩

/-- `SL(2, Z/n)` is onto the directed edges. -/
theorem toDir_surj {p : Cls n × Cls n} (hp : p ∈ dirEdges n) : ∃ g : SLn, toDir g = p := by
  obtain ⟨u, v, h, h1, h2⟩ := hp
  refine ⟨ofColumns u v h, ?_⟩
  rw [toDir, act_ofColumns_eB, act_ofColumns_eE, h1, h2]

/-- Two laws have the same directed edge exactly when they differ by a sign, for `n ≥ 3`. -/
theorem toDir_eq_iff (hn : 3 ≤ n) (g h : SLn) : toDir g = toDir h ↔ g = h ∨ g = -h := by
  constructor
  · intro e
    simp only [toDir, Prod.mk.injEq, cls_eq_iff] at e
    obtain ⟨e1, e2⟩ := e
    have hdet : det2 (act g eB) (act g eE) = det2 (act h eB) (act h eE) := by
      rw [det2_act, det2_act]
    have h1 : det2 (act h eB) (act h eE) = 1 := by rw [det2_act, det2_eB_eE]
    have htwo := two_ne_zero_of hn
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact Or.inl (law_ext e1 e2)
    · exfalso
      rw [e1, e2] at hdet
      have : det2 (act h eB) (-act h eE) = -det2 (act h eB) (act h eE) := by
        simp only [det2, Prod.snd_neg, Prod.fst_neg]
        ring
      rw [this, h1] at hdet
      apply htwo
      linear_combination -hdet
    · exfalso
      rw [e1, e2] at hdet
      have : det2 (-act h eB) (act h eE) = -det2 (act h eB) (act h eE) := by
        simp only [det2, Prod.snd_neg, Prod.fst_neg]
        ring
      rw [this, h1] at hdet
      apply htwo
      linear_combination -hdet
    · right
      apply law_ext
      · rw [act_neg_left, e1]
      · rw [act_neg_left, e2]
  · rintro (rfl | rfl)
    · rfl
    · simp [toDir, act_neg_left, cls_eq_iff]

theorem smul_cls (g : SLn) (u : State n) : g • cls u = cls (act g u) := rfl

theorem smul_eq_iff_cls {g : SLn} {u : State n} :
    (fun x : SLn => x • cls (eB : State n)) g = cls u ↔ cls (act g eB) = cls u := Iff.rfl

open scoped Pointwise

theorem det2_ne_of_cls {u v : State n} (hn : 3 ≤ n) (h : det2 u v = 1) : cls u ≠ cls v := by
  intro e
  have : Fact (1 < n) := ⟨by omega⟩
  rcases cls_eq_iff.mp e with rfl | rfl
  · simp [det2, mul_comm] at h
  · simp [det2, mul_comm] at h

/-- The directed edges are one orbit, and `{±1}` fixes each. -/
theorem dirEdges_eq_orbit :
    dirEdges n = MulAction.orbit SLn (cls (eB : State n), cls (eE : State n)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨g, rfl⟩ := toDir_surj hp
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact toDir_mem g

theorem vertices_eq_orbit : vertices n = MulAction.orbit SLn (cls (eB : State n)) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, b, hab⟩, rfl⟩
    have hdet : det2 u ((-b, a) : State n) = 1 := by
      simp only [det2]
      linear_combination hab
    exact ⟨ofColumns u (-b, a) hdet, by rw [smul_eq_iff_cls, act_ofColumns_eB]⟩
  · rintro ⟨g, rfl⟩
    refine ⟨act g eB, ⟨g.1 1 1, -g.1 0 1, ?_⟩, rfl⟩
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simp only [act, eB, mul_one, mul_zero, add_zero]
    linear_combination h

/-- The base edge and the base face. -/
def edge₀ (n : ℕ) : Set (Cls n) := {cls (eB : State n), cls (eE : State n)}

/-- The base face. -/
def face₀ (n : ℕ) : Set (Cls n) :=
  {cls (eB : State n), cls (eE : State n), cls ((eB : State n) + eE)}

theorem smul_edge₀ (g : SLn) : g • edge₀ n = {cls (act g eB), cls (act g eE)} := by
  simp [edge₀, Set.smul_set_insert, smul_cls]

theorem smul_face₀ (g : SLn) :
    g • face₀ n = {cls (act g eB), cls (act g eE), cls (act g eB + act g eE)} := by
  simp [face₀, Set.smul_set_insert, smul_cls, act_add]

theorem edges_eq_orbit : edges n = MulAction.orbit SLn (edge₀ n) := by
  ext S
  constructor
  · rintro ⟨u, v, h, rfl⟩
    refine ⟨ofColumns u v h, ?_⟩
    change ofColumns u v h • edge₀ n = _
    rw [smul_edge₀, act_ofColumns_eB, act_ofColumns_eE]
  · rintro ⟨g, rfl⟩
    refine ⟨act g eB, act g eE, by rw [det2_act, det2_eB_eE], ?_⟩
    exact smul_edge₀ g

theorem faces_eq_orbit : faces n = MulAction.orbit SLn (face₀ n) := by
  ext S
  constructor
  · rintro ⟨u, v, h, rfl⟩
    refine ⟨ofColumns u v h, ?_⟩
    change ofColumns u v h • face₀ n = _
    rw [smul_face₀, act_ofColumns_eB, act_ofColumns_eE]
  · rintro ⟨g, rfl⟩
    refine ⟨act g eB, act g eE, by rw [det2_act, det2_eB_eE], ?_⟩
    exact smul_face₀ g

/-- A subgroup containing `-1`, whose elements are `±b j` for laws `b j` with distinct directed
edges, has `2 |α|` elements. -/
theorem card_stab (hn : 3 ≤ n) {α : Type*} (b : α → SLn)
    (hb : Function.Injective (toDir ∘ b)) (H : Subgroup SLn) (h1 : ∀ j, b j ∈ H) (h2 : -1 ∈ H)
    (h3 : ∀ g ∈ H, ∃ j, toDir g = toDir (b j)) : Nat.card H = 2 * Nat.card α := by
  have hne : (1 : SLn) ≠ -1 := by
    intro e
    have : ((1 : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0 =
        ((-1 : SLn) : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0 := by
      rw [← e]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply two_ne_zero_of hn
    linear_combination this
  have hsplit : ∀ (j : α) (g : SLn), g = b j ∨ g = -b j → g ∈ H := by
    rintro j g (rfl | rfl)
    · exact h1 j
    · rw [← neg_one_mul]
      exact H.mul_mem h2 (h1 j)
  let F : Bool × α → H := fun p =>
    ⟨if p.1 then -b p.2 else b p.2, by
      split_ifs
      · exact hsplit p.2 _ (Or.inr rfl)
      · exact hsplit p.2 _ (Or.inl rfl)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ε, j⟩ ⟨ε', j'⟩ e
      have e' : (if ε then -b j else b j) = (if ε' then -b j' else b j') := congrArg Subtype.val e
      have hdir : toDir (b j) = toDir (b j') := by
        have h4 : ∀ (ε : Bool) (j : α), toDir (if ε then -b j else b j) = toDir (b j) := by
          intro ε j
          cases ε
          · rfl
          · exact (toDir_eq_iff hn (-b j) (b j)).mpr (Or.inr rfl)
        rw [← h4 ε j, ← h4 ε' j', e']
      have hj : j = j' := hb hdir
      subst hj
      have hbne : b j ≠ -b j := by
        intro e2
        apply hne
        have := congrArg (fun x => x * (b j)⁻¹) e2
        simpa [neg_mul] using this
      cases ε <;> cases ε'
      · rfl
      · exact absurd e' hbne
      · exact absurd e'.symm hbne
      · rfl
    · rintro ⟨g, hg⟩
      obtain ⟨j, hj⟩ := h3 g hg
      rcases (toDir_eq_iff hn _ _).mp hj with e | e
      · exact ⟨(false, j), Subtype.ext e.symm⟩
      · exact ⟨(true, j), Subtype.ext e.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]
  simp

/-- The upper unipotent law. -/
def upper (k : ZMod n) : SLn := ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem act_upper (k : ZMod n) (u : State n) : act (upper k) u = (u.1 + k * u.2, u.2) := by
  simp [act, upper]

theorem card_stab_vertex (hn : 3 ≤ n) [NeZero n] :
    Nat.card (MulAction.stabilizer SLn (cls (eB : State n))) = 2 * n := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hc := card_stab hn (fun k : ZMod n => upper k) ?_
    (MulAction.stabilizer SLn (cls (eB : State n))) ?_ ?_ ?_
  · rwa [Nat.card_zmod] at hc
  · intro k k' e
    simp only [Function.comp, toDir, Prod.mk.injEq, cls_eq_iff, act_upper] at e
    have htwo := two_ne_zero_of hn
    rcases e.2 with e2 | e2
    · simpa [eE] using e2
    · exfalso
      simp only [eE, Prod.mk.injEq, Prod.neg_mk] at e2
      apply htwo
      have := e2.2
      linear_combination this
  · intro k
    rw [MulAction.mem_stabilizer_iff, smul_cls, act_upper]
    simp [eB]
  · rw [MulAction.mem_stabilizer_iff, smul_cls, cls_eq_iff]
    right
    simp [act, Matrix.SpecialLinearGroup.coe_neg, eB]
  · intro g hg
    rw [MulAction.mem_stabilizer_iff, smul_cls, cls_eq_iff] at hg
    have h1 := g.2
    rw [Matrix.det_fin_two] at h1
    simp only [act, eB, mul_one, mul_zero, add_zero, Prod.neg_mk, Prod.mk.injEq, neg_zero] at hg
    rcases hg with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · refine ⟨g.1 0 1, ?_⟩
      rw [ha, hc, one_mul, mul_zero, sub_zero] at h1
      apply (toDir_eq_iff hn _ _).mpr (Or.inl ?_)
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upper, ha, hc, h1]
    · refine ⟨-g.1 0 1, ?_⟩
      rw [ha, hc, mul_zero, sub_zero] at h1
      apply (toDir_eq_iff hn _ _).mpr (Or.inr ?_)
      have hd : g.1 1 1 = -1 := by linear_combination -h1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upper, ha, hc, hd]

/-- The quarter turn `S`: `B → E`, `E → -B`. -/
def quarter : SLn := ofColumns eE (-eB) (by simp [det2, eB, eE])

/-- The sixth turn `R`: `B → B + E`, `E → -B`. -/
def sixth : SLn := ofColumns ((eB : State n) + eE) (-eB) (by simp [det2, eB, eE])

theorem act_quarter (u : State n) : act quarter u = (-u.2, u.1) := by
  simp [act, quarter, ofColumns, eB, eE]

theorem act_sixth (u : State n) : act sixth u = (u.1 - u.2, u.1) := by
  simp [act, sixth, ofColumns, eB, eE, sub_eq_add_neg]

theorem cls_neg (u : State n) : cls (-u) = cls u := cls_eq_iff.mpr (Or.inr rfl)

theorem one_ne_zero_of (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero

theorem cls_eB_ne_eE (hn : 3 ≤ n) : cls (eB : State n) ≠ cls (eE : State n) := by
  have h1 := one_ne_zero_of hn
  intro e
  rcases cls_eq_iff.mp e with e | e <;> simp [eB, eE, h1] at e

/-- The stabilizer of the base edge: `±1` and `±S`. -/
theorem card_stab_edge (hn : 3 ≤ n) [NeZero n] :
    Nat.card (MulAction.stabilizer SLn (edge₀ n)) = 4 := by
  have h1' := one_ne_zero_of hn
  have htwo := two_ne_zero_of hn
  have hc := card_stab hn (![1, quarter] : Fin 2 → SLn) ?_
    (MulAction.stabilizer SLn (edge₀ n)) ?_ ?_ ?_
  · simpa using hc
  · have hne := cls_eB_ne_eE hn
    intro i j e
    have e1 := congrArg Prod.fst e
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply hne
      simpa [toDir, act_one, act_quarter, eB, eE] using e1
    · exfalso
      apply hne
      simpa [toDir, act_one, act_quarter, eB, eE] using e1.symm
    · rfl
  · intro j
    rw [MulAction.mem_stabilizer_iff, smul_edge₀]
    fin_cases j
    · simp [act_one, edge₀]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, act_quarter, edge₀]
      rw [Set.pair_comm]
      have h2 : ((-(eB : State n).2, (eB : State n).1) : State n) = eE := by simp [eB, eE]
      have h3 : ((-(eE : State n).2, (eE : State n).1) : State n) = -eB := by simp [eB, eE]
      rw [h2, h3, cls_neg]
  · rw [MulAction.mem_stabilizer_iff, smul_edge₀, act_neg_left, act_neg_left, act_one, act_one,
      cls_neg, cls_neg]
    rfl
  · intro g hg
    rw [MulAction.mem_stabilizer_iff, smul_edge₀] at hg
    have hB : cls (act g eB) ∈ edge₀ n := by rw [← hg]; simp
    have hE : cls (act g eE) ∈ edge₀ n := by rw [← hg]; simp
    have hd : det2 (act g eB) (act g eE) = 1 := by rw [det2_act, det2_eB_eE]
    have hne := det2_ne_of_cls hn hd
    rcases hB with hB | hB <;> rcases hE with hE | hE
    · exact absurd (hB.trans hE.symm) hne
    · refine ⟨0, ?_⟩
      simp only [toDir, Matrix.cons_val_zero, act_one, hB]
      rw [show cls (act g eE) = cls eE from hE]
    · refine ⟨1, ?_⟩
      simp only [toDir, Matrix.cons_val_one, Matrix.cons_val_fin_one, act_quarter, Prod.mk.injEq]
      constructor
      · rw [show cls (act g eB) = cls eE from hB]
        congr 1
        simp [eB, eE]
      · rw [hE]
        have h3 : ((-(eE : State n).2, (eE : State n).1) : State n) = -eB := by simp [eB, eE]
        rw [h3, cls_neg]
    · have hB' : cls (act g eB) = cls eE := hB
      have hE' : cls (act g eE) = cls eE := hE
      exact absurd (hB'.trans hE'.symm) hne

/-- The stabilizer of the base directed edge: `±1`. -/
theorem card_stab_dir (hn : 3 ≤ n) [NeZero n] :
    Nat.card (MulAction.stabilizer SLn ((cls (eB : State n), cls (eE : State n)))) = 2 := by
  have hc := card_stab hn (fun _ : Unit => (1 : SLn)) (fun _ _ _ => rfl)
    (MulAction.stabilizer SLn ((cls (eB : State n), cls (eE : State n)))) ?_ ?_ ?_
  · simpa using hc
  · intro _
    exact Subgroup.one_mem _
  · rw [MulAction.mem_stabilizer_iff, Prod.smul_mk, smul_cls, smul_cls, act_neg_left, act_neg_left,
      act_one, act_one, cls_neg, cls_neg]
  · intro g hg
    refine ⟨(), ?_⟩
    rw [MulAction.mem_stabilizer_iff, Prod.smul_mk, smul_cls, smul_cls] at hg
    simpa [toDir, act_one] using hg

/-- The classes of the base face. -/
theorem cls_face_cases {x : Cls n} (hx : x ∈ face₀ n) :
    x = cls eB ∨ x = cls eE ∨ x = cls ((eB : State n) + eE) := hx

theorem act_sixth_sq (u : State n) : act (sixth * sixth) u = (-u.2, u.1 - u.2) := by
  rw [act_mul, act_sixth, act_sixth]
  exact Prod.ext (by change u.1 - u.2 - u.1 = -u.2; ring) rfl

/-- Two pairs of classes with `det = 1` on the first and `det = 1` on the second have the same
sum, up to sign. -/
theorem sum_cls_pos (hn : 3 ≤ n) {x y a b : State n} (hx : cls x = cls a) (hy : cls y = cls b)
    (hd : det2 x y = 1) (hab : det2 a b = 1) : cls (x + y) = cls (a + b) := by
  have htwo := two_ne_zero_of hn
  have hneg : ∀ u v : State n, det2 (-u) v = -det2 u v := by
    intro u v
    simp only [det2, Prod.fst_neg, Prod.snd_neg]
    ring
  have hneg' : ∀ u v : State n, det2 u (-v) = -det2 u v := by
    intro u v
    simp only [det2, Prod.fst_neg, Prod.snd_neg]
    ring
  rcases cls_eq_iff.mp hx with rfl | rfl <;> rcases cls_eq_iff.mp hy with rfl | rfl
  · rfl
  · exfalso
    rw [hneg', hab] at hd
    apply htwo
    linear_combination -hd
  · exfalso
    rw [hneg, hab] at hd
    apply htwo
    linear_combination -hd
  · rw [show -a + -b = -(a + b) by simp [add_comm], cls_neg]

theorem sum_cls_neg (hn : 3 ≤ n) {x y a b : State n} (hx : cls x = cls a) (hy : cls y = cls b)
    (hd : det2 x y = 1) (hab : det2 a b = -1) : cls (x + y) = cls (a - b) := by
  have h1 : cls y = cls (-b) := by rw [cls_neg, hy]
  have h2 : det2 a (-b) = 1 := by
    simp only [det2, Prod.fst_neg, Prod.snd_neg] at hab ⊢
    linear_combination -hab
  rw [sum_cls_pos hn hx h1 hd h2, sub_eq_add_neg]

/-- The stabilizer of the base face: `±1`, `±R`, `±R²`. -/
theorem card_stab_face (hn : 3 ≤ n) [NeZero n] :
    Nat.card (MulAction.stabilizer SLn (face₀ n)) = 6 := by
  have h1' := one_ne_zero_of hn
  have htwo := two_ne_zero_of hn
  have hBE := cls_eB_ne_eE hn
  have hdet1 : det2 (eB : State n) ((eB : State n) + eE) = 1 := by simp [det2, eB, eE]
  have hdet2 : det2 (eE : State n) ((eB : State n) + eE) = -1 := by simp [det2, eB, eE]
  have hBS : cls (eB : State n) ≠ cls ((eB : State n) + eE) := det2_ne_of_cls hn hdet1
  have hES : cls (eE : State n) ≠ cls ((eB : State n) + eE) := by
    have : det2 (eE : State n) (-((eB : State n) + eE)) = 1 := by simp [det2, eB, eE]
    have := det2_ne_of_cls hn this
    rwa [cls_neg] at this
  have t0 : toDir (1 : SLn) = (cls eB, cls eE) := by simp [toDir, act_one]
  have t1 : toDir (sixth : SLn) = (cls ((eB : State n) + eE), cls eB) := by
    simp only [toDir, act_sixth, Prod.mk.injEq]
    constructor
    · congr 1
      simp [eB, eE]
    · rw [← cls_neg (eB : State n)]
      congr 1
      simp [eB, eE]
  have t2 : toDir (sixth * sixth : SLn) = (cls eE, cls ((eB : State n) + eE)) := by
    simp only [toDir, act_sixth_sq, Prod.mk.injEq]
    constructor
    · congr 1
      simp [eB, eE]
    · rw [← cls_neg ((eB : State n) + eE)]
      congr 1
      simp [eB, eE]
  have hc := card_stab hn (![1, sixth, sixth * sixth] : Fin 3 → SLn) ?_
    (MulAction.stabilizer SLn (face₀ n)) ?_ ?_ ?_
  · simpa using hc
  · intro i j e
    have e1 := congrArg Prod.fst e
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa [t0, t1] using e1) hBS
    · exact absurd (by simpa [t0, t2] using e1) hBE
    · exact absurd (by simpa [t0, t1] using e1.symm) hBS
    · rfl
    · exact absurd (by simpa [t1, t2] using e1.symm) hES
    · exact absurd (by simpa [t0, t2] using e1.symm) hBE
    · exact absurd (by simpa [t1, t2] using e1) hES
    · rfl
  · have hR : (sixth : SLn) • face₀ n = face₀ n := by
      rw [smul_face₀, act_sixth, act_sixth]
      have e1 : (((eB : State n).1 - (eB : State n).2, (eB : State n).1) : State n) =
          (eB : State n) + eE := by simp [eB, eE]
      have e2 : (((eE : State n).1 - (eE : State n).2, (eE : State n).1) : State n) = -eB := by
        simp [eB, eE]
      rw [e1, e2, cls_neg, show (eB : State n) + eE + -eB = eE by simp [eB, eE], face₀,
        Set.insert_comm, Set.pair_comm (cls eE), Set.insert_comm (cls eB)]
    intro j
    rw [MulAction.mem_stabilizer_iff]
    fin_cases j
    · exact one_smul _ _
    · exact hR
    · change (sixth * sixth) • face₀ n = face₀ n
      rw [mul_smul, hR, hR]
  · rw [MulAction.mem_stabilizer_iff, smul_face₀, act_neg_left, act_neg_left, act_one, act_one,
      cls_neg, cls_neg, show -(eB : State n) + -eE = -((eB : State n) + eE) by simp [add_comm],
      cls_neg]
    rfl
  · intro g hg
    rw [MulAction.mem_stabilizer_iff, smul_face₀] at hg
    have hB : cls (act g eB) ∈ face₀ n := by rw [← hg]; simp
    have hE : cls (act g eE) ∈ face₀ n := by rw [← hg]; simp
    have hS : cls (act g eB + act g eE) ∈ face₀ n := by rw [← hg]; simp
    have hd : det2 (act g eB) (act g eE) = 1 := by rw [det2_act, det2_eB_eE]
    have hne := det2_ne_of_cls hn hd
    have hnot : ∀ w : State n, cls w ∈ face₀ n → (w.1 = 1 ∧ w.2 = 0) ∨ (w.1 = -1 ∧ w.2 = 0) ∨
        (w.1 = 0 ∧ w.2 = 1) ∨ (w.1 = 0 ∧ w.2 = -1) ∨ (w.1 = 1 ∧ w.2 = 1) ∨
        (w.1 = -1 ∧ w.2 = -1) := by
      intro w hw
      rcases cls_face_cases hw with hw | hw | hw <;> rcases cls_eq_iff.mp hw with hw | hw <;>
        subst hw <;> simp [eB, eE]
    rcases cls_face_cases hB with hB | hB | hB <;> rcases cls_face_cases hE with hE | hE | hE
    · exact absurd (hB.trans hE.symm) hne
    · refine ⟨0, ?_⟩
      change toDir g = toDir 1
      rw [t0]
      exact Prod.ext hB hE
    · -- `(B, B + E)`: the sum is `2 B + E`
      exfalso
      rw [sum_cls_pos hn hB hE hd hdet1] at hS
      have a : ((eB : State n) + (eB + eE)).1 = 2 := by simp [eB, eE, one_add_one_eq_two]
      have b : ((eB : State n) + (eB + eE)).2 = 1 := by simp [eB, eE]
      rcases hnot _ hS with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h1' (by linear_combination e2 - b)
      · exact h1' (by linear_combination e2 - b)
      · exact htwo (by linear_combination e1 - a)
      · exact htwo (by linear_combination e1 - a)
      · exact h1' (by linear_combination e1 - a)
      · exact htwo (by linear_combination e2 - b)
    · -- `(E, B)`: the sum is `E - B`
      exfalso
      have hdet3 : det2 (eE : State n) eB = -1 := by simp [det2, eB, eE]
      rw [sum_cls_neg hn hB hE hd hdet3] at hS
      have a : ((eE : State n) - eB).1 = -1 := by simp [eB, eE]
      have b : ((eE : State n) - eB).2 = 1 := by simp [eB, eE]
      rcases hnot _ hS with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h1' (by linear_combination e2 - b)
      · exact h1' (by linear_combination e2 - b)
      · exact h1' (by linear_combination a - e1)
      · exact h1' (by linear_combination a - e1)
      · exact htwo (by linear_combination a - e1)
      · exact htwo (by linear_combination e2 - b)
    · exact absurd (hB.trans hE.symm) hne
    · refine ⟨2, ?_⟩
      change toDir g = toDir (sixth * sixth)
      rw [t2]
      exact Prod.ext hB hE
    · refine ⟨1, ?_⟩
      change toDir g = toDir sixth
      rw [t1]
      exact Prod.ext hB hE
    · -- `(B + E, E)`: the sum is `B + 2 E`
      exfalso
      have hdet4 : det2 ((eB : State n) + eE) eE = 1 := by simp [det2, eB, eE]
      rw [sum_cls_pos hn hB hE hd hdet4] at hS
      have a : ((eB : State n) + eE + eE).1 = 1 := by simp [eB, eE]
      have b : ((eB : State n) + eE + eE).2 = 2 := by simp [eB, eE, one_add_one_eq_two]
      rcases hnot _ hS with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact htwo (by linear_combination e2 - b)
      · exact htwo (by linear_combination e2 - b)
      · exact h1' (by linear_combination e1 - a)
      · exact h1' (by linear_combination e1 - a)
      · exact h1' (by linear_combination e2 - b)
      · exact htwo (by linear_combination e1 - a)
    · exact absurd (hB.trans hE.symm) hne

/-- The order of `SL(2, Z/n)` is twice that of `PSL(2, Z/n)`. -/
theorem card_SL_eq (hn : 3 ≤ n) : Nat.card SLn = Nat.card (PSLZ n) * 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pmOne n)
  rwa [card_pmOne hn] at h

/-- The orbit-stabilizer count. -/
theorem card_orbit {X : Type*} [MulAction SLn X] [NeZero n] {x : X} {m : ℕ}
    (hm : Nat.card (MulAction.stabilizer SLn x) = m) :
    Nat.card SLn = (MulAction.orbit SLn x).ncard * m := by
  have h1 := MulAction.index_stabilizer SLn x
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer SLn x)
  rw [hm, h1] at h2
  rw [← h2, mul_comm]

/-- The counts of Klein's map: `V = |PSL|/n`, `E = |PSL|/2`, `F = |PSL|/3`, and one directed edge
for each element of `PSL`. -/
theorem counts (hn : 3 ≤ n) [NeZero n] :
    Nat.card (PSLZ n) = (dirEdges n).ncard ∧ Nat.card (PSLZ n) = (vertices n).ncard * n ∧
    Nat.card (PSLZ n) = (edges n).ncard * 2 ∧ Nat.card (PSLZ n) = (faces n).ncard * 3 := by
  have h0 := card_SL_eq (n := n) hn
  have h1 := card_orbit (card_stab_dir (n := n) hn)
  have h2 := card_orbit (card_stab_vertex (n := n) hn)
  have h3 := card_orbit (card_stab_edge (n := n) hn)
  have h4 := card_orbit (card_stab_face (n := n) hn)
  rw [← dirEdges_eq_orbit] at h1
  rw [← vertices_eq_orbit] at h2
  rw [← edges_eq_orbit] at h3
  rw [← faces_eq_orbit] at h4
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [h0] at h2
  have : Nat.card (PSLZ n) * 2 = (vertices n).ncard * n * 2 := by rw [h2]; ring
  omega

/-- The neighbours of `E` are the classes `[1 : e]`, one for each `e`. -/
theorem neighbours_eE (hn : 3 ≤ n) [NeZero n] :
    (neighbours (cls (eE : State n))).ncard = n := by
  have h1' := one_ne_zero_of hn
  have htwo := two_ne_zero_of hn
  have hset : neighbours (cls (eE : State n)) =
      Set.range fun e : ZMod n => cls ((1, e) : State n) := by
    ext y
    constructor
    · rintro ⟨u, v, hd, hu, rfl⟩
      rcases cls_eq_iff.mp hu with rfl | rfl
      · simp only [det2, eE] at hd
        refine ⟨-v.2, ?_⟩
        change cls ((1, -v.2) : State n) = cls v
        rw [← cls_neg v]
        refine congrArg cls (Prod.ext ?_ rfl)
        change (1 : ZMod n) = -v.1
        linear_combination -hd
      · simp only [det2, eE, Prod.fst_neg, Prod.snd_neg] at hd
        refine ⟨v.2, ?_⟩
        refine congrArg cls (Prod.ext ?_ rfl)
        change (1 : ZMod n) = v.1
        linear_combination -hd
    · rintro ⟨e, rfl⟩
      exact ⟨-eE, (1, e), by simp [det2, eE], cls_neg _, rfl⟩
  rw [hset, ← Set.image_univ, Set.ncard_image_of_injective, Set.ncard_univ, Nat.card_zmod]
  intro e e' h
  rcases cls_eq_iff.mp h with h | h
  · exact congrArg Prod.snd h
  · exfalso
    apply htwo
    have := congrArg Prod.fst h
    simp only [Prod.fst_neg] at this
    linear_combination this

/-- The two faces on an edge are different: `[u + v] ≠ [u - v]`. -/
theorem cls_sum_ne_sub (hn : 3 ≤ n) {u v : State n} (huv : det2 u v = 1) :
    cls (u + v) ≠ cls (u - v) := by
  have htwo := two_ne_zero_of hn
  have hdet := huv
  simp only [det2] at hdet
  intro e
  rcases cls_eq_iff.mp e with e | e
  · -- `2 v = 0`
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2
    apply htwo
    linear_combination (-u.2) * e1 + u.1 * e2 - 2 * hdet
  · -- `2 u = 0`
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
      at e1 e2
    apply htwo
    linear_combination v.2 * e1 - v.1 * e2 - 2 * hdet

/-- The triangles of the graph are the faces: three classes pairwise joined by directed edges of
determinant `±1` form a face. -/
theorem triangle_is_face {u v w : State n} (huv : det2 u v = 1)
    (huw : det2 u w = 1 ∨ det2 u w = -1) (hvw : det2 v w = 1 ∨ det2 v w = -1) :
    ({cls u, cls v, cls w} : Set (Cls n)) ∈ faces n := by
  -- `w = α u + β v` with `β = det(u, w)` and `α = -det(v, w)`
  have hw : w = (-det2 v w) • u + det2 u w • v := by
    simp only [det2] at huv ⊢
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination (-w.1) * huv
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination (-w.2) * huv
  rcases huw with h1 | h1 <;> rcases hvw with h2 | h2 <;> rw [h1, h2] at hw
  · -- `w = -u + v`: the face of `(v, -u)`
    refine ⟨v, -u, by
      simp only [det2, Prod.fst_neg, Prod.snd_neg] at huv ⊢
      linear_combination huv, ?_⟩
    rw [cls_neg, hw, Set.insert_comm]
    congr 3
    simp [add_comm]
  · -- `w = u + v`
    refine ⟨u, v, huv, ?_⟩
    rw [hw]
    congr 3
    simp
  · -- `w = -u - v`
    refine ⟨u, v, huv, ?_⟩
    rw [hw]
    rw [show (-(1 : ZMod n)) • u + (-1 : ZMod n) • v = -(u + v) by simp [add_comm], cls_neg]
  · -- `w = u - v`: the face of `(v, -u)`
    refine ⟨v, -u, by
      simp only [det2, Prod.fst_neg, Prod.snd_neg] at huv ⊢
      linear_combination huv, ?_⟩
    rw [cls_neg, hw, Set.insert_comm]
    rw [show (- -(1 : ZMod n)) • u + (-1 : ZMod n) • v = -(v + -u) by simp, cls_neg]

section Turns

/-- The kick on a state. -/
theorem act_kick (κ : ZMod n) (u : State n) :
    act (Step.kick κ).sl u = (u.1, κ * u.1 + u.2) := by
  simp [act, Step.sl, Step.mat]

/-- The move on a state: `M(-ℓ)`. -/
theorem act_move (ℓ : ZMod n) (u : State n) :
    act (Step.move (-ℓ)).sl u = (u.1 - ℓ * u.2, u.2) := by
  simp [act, Step.sl, Step.mat, sub_eq_add_neg]

/-- The steps are turns (Theorem U, part 2), and the criterion for an edge (part 3). -/
theorem turns (κ ℓ : ZMod n) :
    act (Step.kick κ).sl eE = eE ∧ (∀ e : ZMod n, act (Step.kick κ).sl (1, e) = (1, e + κ)) ∧
    act (Step.move (-ℓ)).sl eB = eB ∧ (∀ b : ZMod n, act (Step.move (-ℓ)).sl (b, 1) = (b - ℓ, 1)) ∧
    det2 (eE : State n) eB = -1 ∧
    (∀ u : State n, det2 u (act (Step.kick κ).sl u) = κ * u.1 ^ 2) ∧
    ∀ u : State n, det2 u (act (Step.move (-ℓ)).sl u) = ℓ * u.2 ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [act_kick, eE]
  · intro e
    simp [act_kick, add_comm]
  · simp [act_move, eB]
  · intro b
    simp [act_move]
  · simp [det2, eB, eE]
  · intro u
    simp only [act_kick, det2]
    ring
  · intro u
    simp only [act_move, det2]
    ring

/-- The trace by determinants: `tr g · det(u, v) = det(g u, v) + det(u, g v)`. -/
theorem trace_det2 (g : SLn) (u v : State n) :
    Matrix.trace g.1 * det2 u v = det2 (act g u) v + det2 u (act g v) := by
  simp only [Matrix.trace_fin_two, det2, act]
  ring

theorem det2_neg_left (u v : State n) : det2 (-u) v = -det2 u v := by
  simp only [det2, Prod.fst_neg, Prod.snd_neg]
  ring

theorem det2_neg_right (u v : State n) : det2 u (-v) = -det2 u v := by
  simp only [det2, Prod.fst_neg, Prod.snd_neg]
  ring

theorem det2_self (u : State n) : det2 u u = 0 := by
  simp only [det2]
  ring

/-- The trace of a law that fixes a primitive class is `±2`. -/
theorem trace_of_fixed_vertex (g : SLn) {x : Cls n} (hx : x ∈ vertices n) (hg : g • x = x) :
    Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2 := by
  obtain ⟨u, ⟨a, b, hab⟩, rfl⟩ := hx
  have hd : det2 u ((-b, a) : State n) = 1 := by
    simp only [det2]
    linear_combination hab
  set v : State n := (-b, a)
  have htr := trace_det2 g u v
  have hdet := det2_act g u v
  rw [hd, mul_one] at htr
  rw [hd] at hdet
  rw [smul_cls, cls_eq_iff] at hg
  rcases hg with hg | hg
  · left
    rw [hg] at htr hdet
    rw [htr, hd, hdet]
    norm_num
  · right
    rw [hg, det2_neg_left, hd] at htr
    rw [hg, det2_neg_left] at hdet
    have : det2 u (act g v) = -1 := by linear_combination -hdet
    rw [htr, this]
    norm_num

/-- The trace of a law that fixes an edge as a set is `0` or `±2`. -/
theorem trace_of_fixed_edge (g : SLn) {S : Set (Cls n)} (hS : S ∈ edges n)
    (hg : g • S = S) : Matrix.trace g.1 = 0 ∨ Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2 := by
  obtain ⟨u, v, hd, rfl⟩ := hS
  have hprim : ∀ {w z : State n}, det2 w z = 1 → cls w ∈ vertices n := by
    intro w z h
    refine ⟨w, ⟨z.2, -z.1, ?_⟩, rfl⟩
    simp only [det2] at h
    linear_combination h
  have hprim2 : ∀ {w z : State n}, det2 w z = 1 → cls z ∈ vertices n := by
    intro w z h
    refine ⟨z, ⟨-w.2, w.1, ?_⟩, rfl⟩
    simp only [det2] at h
    linear_combination h
  have hu : g • cls u ∈ ({cls u, cls v} : Set (Cls n)) := by
    rw [← hg]
    exact Set.smul_mem_smul_set (by simp)
  have hv : g • cls v ∈ ({cls u, cls v} : Set (Cls n)) := by
    rw [← hg]
    exact Set.smul_mem_smul_set (by simp)
  rcases hu with hu | hu
  · have := trace_of_fixed_vertex g (hprim hd) hu
    tauto
  · have hu' : g • cls u = cls v := hu
    rcases hv with hv | hv
    · -- a flip
      left
      have htr := trace_det2 g u v
      rw [hd, mul_one] at htr
      rw [smul_cls, cls_eq_iff] at hu' hv
      rename' hu' => hu
      have h1 : det2 (act g u) v = 0 := by
        rcases hu with hu | hu <;> rw [hu]
        · exact det2_self v
        · rw [det2_neg_left, det2_self, neg_zero]
      have h2 : det2 u (act g v) = 0 := by
        rcases hv with hv | hv <;> rw [hv]
        · exact det2_self u
        · rw [det2_neg_right, det2_self, neg_zero]
      rw [htr, h1, h2, add_zero]
    · have : g • cls v = cls v := hv
      have := trace_of_fixed_vertex g (hprim2 hd) this
      tauto

/-- The trace of a law that fixes a face as a set is `±1` or `±2`. -/
theorem trace_of_fixed_face (hn : 3 ≤ n) (g : SLn) {S : Set (Cls n)} (hS : S ∈ faces n)
    (hg : g • S = S) : Matrix.trace g.1 = 1 ∨ Matrix.trace g.1 = -1 ∨ Matrix.trace g.1 = 2 ∨
      Matrix.trace g.1 = -2 := by
  obtain ⟨u, v, hd, rfl⟩ := hS
  have hmem : ∀ x ∈ ({cls u, cls v, cls (u + v)} : Set (Cls n)),
      g • x ∈ ({cls u, cls v, cls (u + v)} : Set (Cls n)) := by
    intro x hx
    rw [← hg]
    exact Set.smul_mem_smul_set hx
  have hprim : ∀ {w z : State n}, det2 w z = 1 → cls w ∈ vertices n := by
    intro w z h
    refine ⟨w, ⟨z.2, -z.1, ?_⟩, rfl⟩
    simp only [det2] at h
    linear_combination h
  have hduv : det2 u (u + v) = 1 := by
    simp only [det2, Prod.fst_add, Prod.snd_add] at hd ⊢
    linear_combination hd
  have hdvu : det2 v (-u) = 1 := by
    rw [det2_neg_right]
    simp only [det2] at hd ⊢
    linear_combination hd
  have hdsu : det2 (u + v) (-u) = 1 := by
    rw [det2_neg_right]
    simp only [det2, Prod.fst_add, Prod.snd_add] at hd ⊢
    linear_combination hd
  have hdsv : det2 (u + v) v = 1 := by
    simp only [det2, Prod.fst_add, Prod.snd_add] at hd ⊢
    linear_combination hd
  have hfix : ∀ x ∈ vertices n, g • x = x → Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2 :=
    fun x hx h => trace_of_fixed_vertex g hx h
  have hne12 : cls u ≠ cls v := det2_ne_of_cls hn hd
  have hne13 : cls u ≠ cls (u + v) := det2_ne_of_cls hn hduv
  have hne23 : cls v ≠ cls (u + v) := by
    have h := det2_ne_of_cls hn hdsu
    have h2 := det2_ne_of_cls hn hdvu
    intro e
    have h3 := det2_ne_of_cls hn hdsv
    exact h3 e.symm
  have htr := trace_det2 g u v
  rw [hd, mul_one] at htr
  rcases hmem _ (Or.inl rfl) with h1 | h1 | h1
  · have := hfix _ (hprim hd) h1
    tauto
  · have h1' : g • cls u = cls v := h1
    rcases hmem _ (Or.inr (Or.inl rfl)) with h2 | h2 | h2
    · -- `u → v → u`: the third class is fixed
      have h2' : g • cls v = cls u := h2
      rcases hmem _ (Or.inr (Or.inr rfl)) with h3 | h3 | h3
      · exact absurd (MulAction.injective g (h3.trans h2'.symm)) hne23.symm
      · have h3' : g • cls (u + v) = cls v := h3
        exact absurd (MulAction.injective g (h3'.trans h1'.symm)) hne13.symm
      · have h3' : g • cls (u + v) = cls (u + v) := h3
        have := hfix _ (hprim hdsu) h3'
        tauto
    · have h2' : g • cls v = cls v := h2
      have := hfix _ (hprim hdvu) h2'
      tauto
    · -- `u → v → u + v`
      have h2' : g • cls v = cls (u + v) := h2
      rw [smul_cls, cls_eq_iff] at h1' h2'
      have e1 : det2 (act g u) v = 0 := by
        rcases h1' with h | h <;> rw [h]
        · exact det2_self v
        · rw [det2_neg_left, det2_self, neg_zero]
      rw [e1, zero_add] at htr
      rcases h2' with h | h <;> rw [h] at htr
      · left
        rw [htr, hduv]
      · right; left
        rw [htr, det2_neg_right, hduv]
  · have h1' : g • cls u = cls (u + v) := h1
    rcases hmem _ (Or.inr (Or.inl rfl)) with h2 | h2 | h2
    · -- `u → u + v`, `v → u`
      rw [smul_cls, cls_eq_iff] at h1' h2
      have e2 : det2 u (act g v) = 0 := by
        rcases h2 with h | h <;> rw [h]
        · exact det2_self u
        · rw [det2_neg_right, det2_self, neg_zero]
      rw [e2, add_zero] at htr
      rcases h1' with h | h <;> rw [h] at htr
      · left
        rw [htr, hdsv]
      · right; left
        rw [htr, det2_neg_left, hdsv]
    · have h2' : g • cls v = cls v := h2
      have := hfix _ (hprim hdvu) h2'
      tauto
    · have h2' : g • cls v = cls (u + v) := h2
      exact absurd (MulAction.injective g (h1'.trans h2'.symm)) hne12

theorem act_tickN (μ : ZMod n) (u : State n) :
    act (tickN μ) u = ((1 - μ) * u.1 - μ * u.2, u.1 + u.2) := by
  have : tickN μ = (Step.move (-μ)).sl * (Step.kick 1).sl := by
    simp [tickN, realize]
  rw [this, act_mul, act_kick, act_move]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring

theorem trace_tickN (μ : ZMod n) : Matrix.trace (tickN μ).1 = 2 - μ := by
  have h : tickN μ = (Step.move (-μ)).sl * (Step.kick 1).sl := by
    simp [tickN, realize]
  rw [h, Matrix.SpecialLinearGroup.coe_mul, Step.coe_sl, Step.coe_sl]
  simp only [Step.mat, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  ring

/-- The cells that the crystallographic ticks fix, on every dial (Theorem U, part 4). -/
theorem tick_cells :
    tickN (0 : ZMod n) • cls (eE : State n) = cls eE ∧
    tickN (1 : ZMod n) • ({cls eB, cls eE, cls ((1, -1) : State n)} : Set (Cls n)) =
      {cls eB, cls eE, cls ((1, -1) : State n)} ∧
    tickN (2 : ZMod n) • ({cls eB, cls ((1, -1) : State n)} : Set (Cls n)) =
      {cls eB, cls ((1, -1) : State n)} ∧
    tickN (3 : ZMod n) •
        ({cls eB, cls ((-2, 1) : State n), cls ((1, -1) : State n)} : Set (Cls n)) =
      {cls eB, cls ((-2, 1) : State n), cls ((1, -1) : State n)} ∧
    tickN (4 : ZMod n) • cls ((-2, 1) : State n) = cls ((-2, 1) : State n) := by
  have cB : ∀ μ : ZMod n, act (tickN μ) eB = (1 - μ, 1) := by
    intro μ
    rw [act_tickN]
    simp [eB]
  have cC : ∀ μ : ZMod n, act (tickN μ) ((1, -1) : State n) = (1, 0) := by
    intro μ
    rw [act_tickN]
    simp
  have cD : ∀ μ : ZMod n, act (tickN μ) ((-2, 1) : State n) = (-2 + μ, -1) := by
    intro μ
    rw [act_tickN]
    refine Prod.ext ?_ ?_
    · simp only
      ring
    · simp only
      ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_cls, act_tickN]
    congr 1
    simp [eE]
  · rw [Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton, smul_cls, smul_cls,
      smul_cls, cB, cC, act_tickN]
    have e1 : ((1 - 1, 1) : State n) = eE := by simp [eE]
    have e2 : (((1 - (1 : ZMod n)) * (eE : State n).1 - 1 * (eE : State n).2,
        (eE : State n).1 + (eE : State n).2) : State n) = -((1, -1) : State n) := by simp [eE]
    rw [e1, e2, cls_neg, show ((1, 0) : State n) = eB from rfl]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · rw [Set.smul_set_insert, Set.smul_set_singleton, smul_cls, smul_cls, cB, cC]
    have e1 : ((1 - 2, 1) : State n) = -((1, -1) : State n) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_neg]
        norm_num
      · simp
    rw [e1, cls_neg, Set.pair_comm]
    rfl
  · rw [Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton, smul_cls, smul_cls,
      smul_cls, cB, cC, cD]
    have e1 : ((1 - 3, 1) : State n) = (-2, 1) := by
      refine Prod.ext ?_ rfl
      simp only
      norm_num
    have e2 : ((-2 + 3, -1) : State n) = (1, -1) := by
      refine Prod.ext ?_ rfl
      simp only
      norm_num
    rw [e1, e2, show ((1, 0) : State n) = eB from rfl]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · rw [smul_cls, cD, ← cls_neg ((-2, 1) : State n)]
    refine congrArg cls (Prod.ext ?_ rfl)
    simp only [Prod.fst_neg]
    norm_num

theorem natCast_ne_zero_of_lt {k : ℕ} (h0 : 0 < k) (hk : k < n) : ((k : ℕ) : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have := Nat.le_of_dvd h0 hd
  omega

/-- For `n ≥ 9` the tick at the exploding mode `μ = 8` fixes no vertex, edge or face (Theorem U,
part 5). -/
theorem exploding_free (hn : 9 ≤ n) :
    (∀ x ∈ vertices n, tickN (8 : ZMod n) • x ≠ x) ∧
    (∀ S ∈ edges n, tickN (8 : ZMod n) • S ≠ S) ∧
    ∀ S ∈ faces n, tickN (8 : ZMod n) • S ≠ S := by
  have h4 : (4 : ZMod n) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (k := 4) (by norm_num) (by omega)
  have h5 : (5 : ZMod n) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (k := 5) (by norm_num) (by omega)
  have h6 : (6 : ZMod n) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (k := 6) (by norm_num) (by omega)
  have h7 : (7 : ZMod n) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (k := 7) (by norm_num) (by omega)
  have h8 : (8 : ZMod n) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (k := 8) (by norm_num) (by omega)
  have htr := trace_tickN (8 : ZMod n)
  have t2 : (2 - 8 : ZMod n) ≠ 2 := fun e => h8 (by linear_combination -e)
  have tm2 : (2 - 8 : ZMod n) ≠ -2 := fun e => h4 (by linear_combination -e)
  have t0 : (2 - 8 : ZMod n) ≠ 0 := fun e => h6 (by linear_combination -e)
  have t1 : (2 - 8 : ZMod n) ≠ 1 := fun e => h7 (by linear_combination -e)
  have tm1 : (2 - 8 : ZMod n) ≠ -1 := fun e => h5 (by linear_combination -e)
  refine ⟨fun x hx h => ?_, fun S hS h => ?_, fun S hS h => ?_⟩
  · rcases trace_of_fixed_vertex _ hx h with e | e <;> rw [htr] at e
    · exact t2 e
    · exact tm2 e
  · rcases trace_of_fixed_edge _ hS h with e | e | e <;> rw [htr] at e
    · exact t0 e
    · exact t2 e
    · exact tm2 e
  · rcases trace_of_fixed_face (by omega) _ hS h with e | e | e | e <;> rw [htr] at e
    · exact t1 e
    · exact tm1 e
    · exact t2 e
    · exact tm2 e

end Turns

section Dials

/-- Every unit squares to `±1`. -/
def SquaresPM (n : ℕ) : Prop := ∀ u : (ZMod n)ˣ, ((u : ZMod n)) ^ 2 = 1 ∨ ((u : ZMod n)) ^ 2 = -1

theorem SquaresPM.of_dvd {d n : ℕ} [NeZero n] (hd : d ∣ n) (h : SquaresPM n) : SquaresPM d := by
  intro u
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hd u
  have hcast : ((ZMod.unitsMap hd v : (ZMod d)ˣ) : ZMod d) =
      ZMod.castHom hd (ZMod d) (v : ZMod n) := rfl
  rw [hcast]
  rcases h v with e | e
  · left
    rw [← map_pow, e, map_one]
  · right
    rw [← map_pow, e, map_neg, map_one]

theorem not_squares_of_prime {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : ¬ SquaresPM p := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := p) (k := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := p) (k := 3) (by norm_num) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := p) (k := 5) (by norm_num) (by omega)
  rcases h (Units.mk0 2 h2) with e | e <;> simp only [Units.val_mk0] at e
  · exact h3 (by linear_combination e)
  · exact h5 (by linear_combination e)

theorem not_squares_9 : ¬ SquaresPM 9 := by unfold SquaresPM; decide +kernel
theorem not_squares_15 : ¬ SquaresPM 15 := by unfold SquaresPM; decide +kernel
theorem not_squares_16 : ¬ SquaresPM 16 := by unfold SquaresPM; decide +kernel
theorem not_squares_20 : ¬ SquaresPM 20 := by unfold SquaresPM; decide +kernel
theorem not_squares_25 : ¬ SquaresPM 25 := by unfold SquaresPM; decide +kernel

theorem squares_of_mem {n : ℕ} (h : n ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12, 24]) : SquaresPM n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold SquaresPM <;>
    decide +kernel

/-- Every unit squares to `±1` exactly on the dials `1, 2, 3, 4, 5, 6, 8, 10, 12, 24` (Theorem U,
part 3). -/
theorem squares_iff (n : ℕ) (hn : n ≠ 0) :
    SquaresPM n ↔ n ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12, 24] := by
  have : NeZero n := ⟨hn⟩
  constructor
  · intro h
    have hdiv : n ∣ 120 := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro p k hp hpk
      cases k with
      | zero => simp
      | succ k =>
        have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by omega)) hpk
        have hP := SquaresPM.of_dvd hpn h
        have hle : p < 7 := by
          by_contra hge
          exact not_squares_of_prime hp (by omega) hP
        interval_cases p
        · exact absurd hp (by norm_num)
        · exact absurd hp (by norm_num)
        · -- `p = 2`
          by_cases hk : k + 1 ≤ 3
          · exact dvd_trans (pow_dvd_pow 2 hk) (by norm_num)
          · exfalso
            have : (16 : ℕ) ∣ n := dvd_trans (by
              rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
              exact pow_dvd_pow 2 (by omega)) hpk
            exact not_squares_16 (SquaresPM.of_dvd this h)
        · -- `p = 3`
          by_cases hk : k + 1 ≤ 1
          · exact dvd_trans (pow_dvd_pow 3 hk) (by norm_num)
          · exfalso
            have : (9 : ℕ) ∣ n := dvd_trans (by
              rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
              exact pow_dvd_pow 3 (by omega)) hpk
            exact not_squares_9 (SquaresPM.of_dvd this h)
        · exact absurd hp (by norm_num)
        · -- `p = 5`
          by_cases hk : k + 1 ≤ 1
          · exact dvd_trans (pow_dvd_pow 5 hk) (by norm_num)
          · exfalso
            have : (25 : ℕ) ∣ n := dvd_trans (by
              rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
              exact pow_dvd_pow 5 (by omega)) hpk
            exact not_squares_25 (SquaresPM.of_dvd this h)
        · exact absurd hp (by norm_num)
    have hle : n ≤ 120 := Nat.le_of_dvd (by norm_num) hdiv
    have h15 : ¬ 15 ∣ n := fun hd => not_squares_15 (SquaresPM.of_dvd hd h)
    have h20 : ¬ 20 ∣ n := fun hd => not_squares_20 (SquaresPM.of_dvd hd h)
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    clear h
    interval_cases n <;> first | decide | omega
  · exact squares_of_mem

end Dials

section Orders

theorem order_of_pows {G : Type*} [Group G] {x : G} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1)
    (hd : ∀ p ∈ n.primeFactors, x ^ (n / p) ≠ 1) : orderOf x = n :=
  orderOf_eq_of_pow_and_pow_div_prime hn h fun p hp hpn =>
    hd p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)

/-- The orders of the exploding mode. -/
theorem exploding_orders : orderOf (tickN (8 : ZMod 36)) = 12 ∧
    orderOf (tickN (8 : ZMod 120)) = 24 ∧
    orderOf (tickN (8 : ZMod 360)) = 24 ∧ orderOf (tickN (8 : ZMod 3600)) = 240 := by
  have h12 : Nat.primeFactors 12 = {2, 3} := by decide +kernel
  have h24 : Nat.primeFactors 24 = {2, 3} := by decide +kernel
  have h240 : Nat.primeFactors 240 = {2, 3, 5} := by decide +kernel
  refine ⟨order_of_pows (by norm_num) (by decide +kernel) ?_,
    order_of_pows (by norm_num) (by decide +kernel) ?_,
    order_of_pows (by norm_num) (by decide +kernel) ?_,
    order_of_pows (by norm_num) (by decide +kernel) ?_⟩
  · rw [h12]
    decide +kernel
  · rw [h24]
    decide +kernel
  · rw [h24]
    decide +kernel
  · rw [h240]
    decide +kernel

end Orders

end Artform.Scores.Klein

namespace Artform.Scores

open Matrix (SpecialLinearGroup)
open Klein Bells
open scoped Pointwise

/-- **T13** (Theorem U, part 1: the regular map). -/
@[ledger "T13"]
theorem regularMap : Statement.regularMap := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := counts (n := n) hn
  refine ⟨toDir_mem, fun p hp => toDir_surj hp, fun g h => ?_, h1, h2, h3, h4, ?_,
    neighbours_eE hn, ?_, ?_, ?_, ?_⟩
  · rw [toDir_eq_iff hn]
    have := mk_eq_iff g h
    simpa only [QuotientGroup.mk'_apply] using this.symm
  · have : ((vertices n).ncard : ℤ) * n = Nat.card (PSLZ n) := by exact_mod_cast h2.symm
    have h5 : ((edges n).ncard : ℤ) * 2 = Nat.card (PSLZ n) := by exact_mod_cast h3.symm
    have h6 : ((faces n).ncard : ℤ) * 3 = Nat.card (PSLZ n) := by exact_mod_cast h4.symm
    linear_combination 6 * this - 3 * n * h5 + 2 * n * h6
  · intro u v w huv huw hvw
    exact triangle_is_face huv huw hvw
  · intro u v huv
    exact cls_sum_ne_sub hn huv
  · intro g S hS
    rw [edges_eq_orbit] at hS ⊢
    obtain ⟨h, rfl⟩ := hS
    exact ⟨g * h, mul_smul g h _⟩
  · intro g S hS
    rw [faces_eq_orbit] at hS ⊢
    obtain ⟨h, rfl⟩ := hS
    exact ⟨g * h, mul_smul g h _⟩

/-- The order of `PSL(2, Z/n)`, from a checked word. -/
theorem card_PSL_of_check {n : ℕ} [NeZero n] {N w : ℕ} (hN : 0 < N)
    (h : checkRun (nextQuad n) (codePSL n) (digits N w) (oneQuad n) = true) :
    Nat.card (PSLZ n) = N := by
  rw [← encSL_one] at h
  exact (modelPSL n).card_of_check closure_KM_PSL hN h

/-- **T13** (Theorem U, part 1: the tetrahedron, the octahedron and the icosahedron). -/
@[ledger "T13"]
theorem platonicSolids : Statement.platonicSolids := by
  have c3 : Nat.card (PSLZ 3) = 12 :=
    card_PSL_of_check (w := Cert.wordPSL3) (by norm_num) (by decide +kernel)
  have c4 : Nat.card (PSLZ 4) = 24 :=
    card_PSL_of_check (w := Cert.wordPSL4) (by norm_num) (by decide +kernel)
  have c5 : Nat.card (PSLZ 5) = 60 :=
    card_PSL_of_check (w := Cert.wordPSL5) (by norm_num) (by decide +kernel)
  obtain ⟨-, a2, a3, a4⟩ := counts (n := 3) (by norm_num)
  obtain ⟨-, b2, b3, b4⟩ := counts (n := 4) (by norm_num)
  obtain ⟨-, d2, d3, d4⟩ := counts (n := 5) (by norm_num)
  refine ⟨⟨c3, by omega, by omega, by omega⟩, ⟨c4, by omega, by omega, by omega⟩,
    ⟨c5, by omega, by omega, by omega⟩⟩

/-- **T13** (Theorem U, parts 2 and 3: the steps are turns). -/
@[ledger "T13"]
theorem stepsAreTurns : Statement.stepsAreTurns :=
  ⟨fun _ κ ℓ => turns κ ℓ, squares_iff⟩

/-- **T13** (Theorem U, parts 4 and 5: the cells that a tick fixes). -/
@[ledger "T13"]
theorem tickCells : Statement.tickCells := by
  refine ⟨fun n g x hx hg => trace_of_fixed_vertex g hx hg,
    fun n g S hS hg => trace_of_fixed_edge g hS hg,
    fun n hn g S hS hg => trace_of_fixed_face hn g hS hg, fun n => trace_tickN, fun n => tick_cells,
    fun n hn => exploding_free hn, ?_, exploding_orders⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show (8 : ZMod 3) = 2 by decide]
    exact tick_cells.2.2.1
  · rw [show (8 : ZMod 4) = 0 by decide]
    exact tick_cells.1
  · rw [show (8 : ZMod 5) = 3 by decide]
    exact tick_cells.2.2.2.1

/-! ## Non-vacuity

On the dial `Z/7` the map is Klein's quartic: `|PSL(2, 7)| = 168`, so `24` vertices, `84` edges,
`56` faces and the Euler characteristic `-4`, genus `3`.
-/

example : (vertices 7).ncard = 24 ∧ (edges 7).ncard = 84 ∧ (faces 7).ncard = 56 := by
  have c7 : Nat.card (PSLZ 7) = 168 :=
    card_PSL_of_check (w := Cert.wordPSL7) (by norm_num) (by decide +kernel)
  obtain ⟨-, a2, a3, a4⟩ := counts (n := 7) (by norm_num)
  omega

end Artform.Scores
