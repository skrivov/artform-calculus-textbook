import ArtformStages.Solid
import ArtformStages.Trail

/-!
# The derived canvas is the cubic torus (finding 1016)

Road G, the bridge campaign, wave D. The metatheory's wave 581 builds a canvas from the six acts of
the first stage's dial, `Fin 2 × Fin 3`, a sense from the row of period 2 and an axis from the row
of period 3: the free stage lays every commutator of two acts, and the canvas lays "opposite steps
cancel". Its world is the lattice `ℤ³`, and the dial's step acts on it as the signed 3-cycle. Here
that canvas is carried onto the library's cubic torus of `Solid.lean`.

* `canvasEquiv`, `canvasEquiv_step` (D1(a)): wave 581's canvas, in the library.
* `toTorus`, `toTorus_g`, `toTorus_surjective`, `toTorus_eq_iff`, `toTorus_step` (D1(b), (c)): the
  torus `(ℤ/n)³` is the canvas modulo `n`, and the dial's step goes to the torus's tick.
* `lineOf`, `lineOf_boundary`, `torusChain`, `face_eq_trail`, `trail_same_axis`,
  `cube_faces_cancel` (D2): an act at a point is a line of the torus, and the trail of a laid
  commutator is a face.
* `fineCorner`, `fineLines`, `fineFaces`, `fineCubes`, `refine_gauge`, `refine_incidence`,
  `refine_boundary`, `refine_tick` (D3): refinement as multiplication by `d`, from the torus of
  side `n` to the torus of side `d n`, commutes with the gauge, the incidence, the boundary and
  the tick.
* `tickLines`, `tickFaces`, `tickCubes`, `tick_gauge`, `tick_incidence`, `tick_boundary`,
  `cubeTick_three`, `cubeTick_six` (D4): the tick is a symmetry of the cell complex, with the
  signs `-1` on lines, `+1` on faces and `-1` on cubes; three ticks are `w ↦ -w`, six are the
  identity.

None of the mathematics is new: the torus as a quotient of `ℤ³`, the chain maps of a
subdivision and the symmetries of the cube are classical. Wave 581's canvas is copied, with its
proofs; wave 760 of the metatheory has the tick as a signed permutation of the steps, which D4
carries to the whole cell complex.
-/

open Matrix
open scoped commutatorElement

namespace Artform.Stages.DialCanvas

/-! ### The canvas of the six-dial (the metatheory's wave 581) -/

/-- The six-dial's positions: a sense and an axis. -/
abbrev Pos := Fin 2 × Fin 3

/-- The step to a position, as a walk. -/
def s (p : Pos) : FreeGroup Pos := FreeGroup.of p

/-- The dial's step. -/
def step (p : Pos) : Pos := (p.1 + 1, p.2 + 1)

/-- Steps pass each other. -/
def passRules : Set (FreeGroup Pos) := {w | ∃ p q : Pos, w = ⁅s p, s q⁆}

/-- Opposite steps cancel. -/
def oppositeRules : Set (FreeGroup Pos) :=
  {w | ∃ (b : Fin 2) (a : Fin 3), w = s (b, a) * s (b + 1, a)}

/-- The free canvas of the six steps. -/
def free : Stage Pos := ⟨passRules⟩

/-- The canvas: opposite steps cancel. -/
def canvas : Stage Pos := free.lay oppositeRules

section Common

variable (T : Stage Pos)

/-- The law of a step. -/
def g (p : Pos) : T.World := T.law (s p)

theorem of_eq_g (p : Pos) : (PresentedGroup.of p : T.World) = g T p := rfl

theorem law_eq_one {w : FreeGroup Pos} (hw : w ∈ T.rules) : T.law w = 1 :=
  T.law_eq_one_iff.mpr (T.rules_subset_rest hw)

theorem g_comm (hT : passRules ⊆ T.rules) (p q : Pos) : g T p * g T q = g T q * g T p := by
  have h := law_eq_one T (hT ⟨p, q, rfl⟩)
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h

theorem closure_g : Subgroup.closure (Set.range (g T)) = ⊤ :=
  PresentedGroup.closure_range_of T.rules

/-- With the steps passing each other, the whole world is commutative. -/
theorem world_comm (hT : passRules ⊆ T.rules) (x y : T.World) : x * y = y * x := by
  have hcen : ∀ (p : Pos) (z : T.World), g T p * z = z * g T p := by
    intro p z
    have hle : Subgroup.closure (Set.range (g T)) ≤ Subgroup.centralizer {g T p} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact g_comm T hT p q
    rw [closure_g] at hle
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top z))) _ rfl
  have hle : Subgroup.closure (Set.range (g T)) ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (hcen q x).symm
  rw [closure_g] at hle
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top y))) _ rfl

theorem g_opp (hT : oppositeRules ⊆ T.rules) (b : Fin 2) (a : Fin 3) :
    g T (b + 1, a) = (g T (b, a))⁻¹ := by
  have h := law_eq_one T (hT ⟨b, a, rfl⟩)
  rw [map_mul] at h
  exact eq_inv_of_mul_eq_one_right h

theorem g_one (hT : oppositeRules ⊆ T.rules) (a : Fin 3) : g T (1, a) = (g T (0, a))⁻¹ :=
  g_opp T hT 0 a

end Common

/-- The sign of a sense. -/
def sgn (b : Fin 2) : ℤ := if b = 0 then 1 else -1

theorem sgn_succ (b : Fin 2) : sgn (b + 1) = -sgn b := by
  fin_cases b <;> decide

theorem canvas_pass : passRules ⊆ canvas.rules := fun _ h => Or.inl h

theorem canvas_opp : oppositeRules ⊆ canvas.rules := fun _ h => Or.inr h

instance : CommGroup canvas.World :=
  { (inferInstance : Group canvas.World) with mul_comm := world_comm canvas canvas_pass }

/-- Where a step goes in the lattice: `(-1)ᵇ e a`. -/
def e3 (p : Pos) : Multiplicative (Fin 3 → ℤ) := Multiplicative.ofAdd (sgn p.1 • Pi.single p.2 1)

/-- The canvas's world to the lattice. -/
def toLattice : canvas.World →* Multiplicative (Fin 3 → ℤ) :=
  PresentedGroup.toGroup (f := e3) (by
    rintro r (⟨p, q, rfl⟩ | ⟨b, a, rfl⟩)
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    · simp only [s, map_mul, FreeGroup.lift_apply_of, e3, ← ofAdd_add, ← add_smul, sgn_succ,
        add_neg_cancel, zero_smul, ofAdd_zero])

theorem toLattice_g (p : Pos) : toLattice (g canvas p) = e3 p := PresentedGroup.toGroup.of _

/-- The lattice to the canvas's world: `v ↦ ∏ g (0, a) ^ v a`. -/
def fromLatticeAdd : (Fin 3 → ℤ) →+ Additive canvas.World where
  toFun v := ∑ i, v i • Additive.ofMul (g canvas (0, i))
  map_zero' := by simp
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]

/-- The lattice to the canvas's world, multiplicatively. -/
def fromLattice : Multiplicative (Fin 3 → ℤ) →* canvas.World :=
  AddMonoidHom.toMultiplicativeLeft fromLatticeAdd

theorem fromLattice_apply (v : Multiplicative (Fin 3 → ℤ)) :
    fromLattice v = g canvas (0, 0) ^ (v.toAdd 0) * g canvas (0, 1) ^ (v.toAdd 1) *
      g canvas (0, 2) ^ (v.toAdd 2) := by
  simp [fromLattice, fromLatticeAdd, Fin.sum_univ_three, toMul_add, toMul_zsmul]

theorem from_to (x : canvas.World) : fromLattice (toLattice x) = x := by
  have h : fromLattice.comp toLattice = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨b, a⟩
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, of_eq_g, toLattice_g, fromLattice_apply]
    fin_cases b <;> fin_cases a <;>
      simp [e3, sgn, g_one canvas canvas_opp]
  exact DFunLike.congr_fun h x

theorem to_from (v : Multiplicative (Fin 3 → ℤ)) : toLattice (fromLattice v) = v := by
  rw [fromLattice_apply]
  simp only [map_mul, map_zpow, toLattice_g]
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [e3, sgn]

/-- **D1(a)**, wave 581's item 2. The canvas's world is the library's lattice in three. -/
def canvasEquiv : canvas.World ≃* Multiplicative (Fin 3 → ℤ) :=
  MonoidHom.toMulEquiv toLattice fromLattice (MonoidHom.ext from_to) (MonoidHom.ext to_from)

theorem canvasEquiv_g (b : Fin 2) (a : Fin 3) :
    canvasEquiv (g canvas (b, a)) = Multiplicative.ofAdd (sgn b • Pi.single a 1) :=
  toLattice_g (b, a)

/-- The dial's step sends rules to rules, so it acts on the canvas's world. -/
def stepHom : canvas.World →* canvas.World :=
  PresentedGroup.toGroup (f := fun p => g canvas (step p)) (by
    rintro r (⟨p, q, rfl⟩ | ⟨b, a, rfl⟩)
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    · have h := law_eq_one canvas (canvas_opp ⟨b + 1, a + 1, rfl⟩)
      rw [map_mul] at h
      simp only [s, map_mul, FreeGroup.lift_apply_of]
      exact h)

theorem stepHom_g (p : Pos) : stepHom (g canvas p) = g canvas (step p) :=
  PresentedGroup.toGroup.of _

/-- The signed 3-cycle `e a ↦ -e (a + 1)`, read on coordinates: `v ↦ (i ↦ -v (i - 1))`. -/
def negCAdd : (Fin 3 → ℤ) →+ (Fin 3 → ℤ) where
  toFun v := fun i => -v (i - 1)
  map_zero' := by funext i; simp
  map_add' v w := by funext i; simp [add_comm]

/-- The signed 3-cycle, multiplicatively. -/
def negC : Multiplicative (Fin 3 → ℤ) →* Multiplicative (Fin 3 → ℤ) :=
  AddMonoidHom.toMultiplicative negCAdd

theorem negC_apply (v : Multiplicative (Fin 3 → ℤ)) (i : Fin 3) :
    (negC v).toAdd i = -(v.toAdd (i - 1)) := rfl

/-- **D1(a)**, wave 581's item 3. Under the isomorphism the dial's step is the signed 3-cycle. -/
theorem canvasEquiv_step (x : canvas.World) : canvasEquiv (stepHom x) = negC (canvasEquiv x) := by
  have h : (canvasEquiv.toMonoidHom.comp stepHom) = negC.comp canvasEquiv.toMonoidHom := by
    apply PresentedGroup.ext
    rintro ⟨b, a⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, of_eq_g, stepHom_g, step]
    rw [canvasEquiv_g, canvasEquiv_g]
    apply Multiplicative.toAdd.injective
    funext i
    rw [negC_apply]
    fin_cases b <;> fin_cases a <;> fin_cases i <;> decide
  exact DFunLike.congr_fun h x

/-! ### D1: the torus is the canvas modulo `n` -/

variable (n : ℕ)

/-- The torus's tick: the signed 3-cycle read on `(ℤ/n)³`, `w ↦ (i ↦ -w (i - 1))`. -/
def cubeTick : CubePoint n →+ CubePoint n where
  toFun w := fun i => -w (i - 1)
  map_zero' := by funext i; simp
  map_add' v w := by funext i; simp [add_comm]

theorem cubeTick_apply (w : CubePoint n) (i : Fin 3) : cubeTick n w i = -w (i - 1) := rfl

/-- Lattice coordinates read modulo `n`. -/
def reduce : (Fin 3 → ℤ) →+ CubePoint n :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod n)) (Fin 3)

theorem reduce_apply (v : Fin 3 → ℤ) (i : Fin 3) : reduce n v i = (v i : ZMod n) := rfl

/-- **D1(b).** The canvas's world onto the torus `(ℤ/n)³`. -/
def toTorus : canvas.World →* Multiplicative (CubePoint n) :=
  (AddMonoidHom.toMultiplicative (reduce n)).comp canvasEquiv.toMonoidHom

theorem toTorus_apply (x : canvas.World) :
    (toTorus n x).toAdd = reduce n (canvasEquiv x).toAdd := rfl

/-- **D1(b).** The act `(b, a)` goes to `(-1)ᵇ` times the torus's step along `a`. -/
theorem toTorus_g (b : Fin 2) (a : Fin 3) :
    (toTorus n (g canvas (b, a))).toAdd = sgn b • cubeStep n a := by
  rw [toTorus_apply, canvasEquiv_g, toAdd_ofAdd]
  funext i
  fin_cases b <;> by_cases h : i = a <;> simp [reduce_apply, sgn, cubeStep, h]

/-- **D1(b).** Every corner of the torus is the image of a point of the canvas. -/
theorem toTorus_surjective : Function.Surjective (toTorus n) := by
  intro y
  choose f hf using fun i => ZMod.intCast_surjective (n := n) (y.toAdd i)
  refine ⟨canvasEquiv.symm (Multiplicative.ofAdd f), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toTorus_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  funext i
  rw [reduce_apply, hf]

/-- **D1(b).** Two points of the canvas go to one corner exactly when their lattice coordinates
differ by multiples of `n`. -/
theorem toTorus_eq_iff (x y : canvas.World) :
    toTorus n x = toTorus n y ↔
      ∀ i, (n : ℤ) ∣ (canvasEquiv y).toAdd i - (canvasEquiv x).toAdd i := by
  rw [← Multiplicative.toAdd.injective.eq_iff, toTorus_apply, toTorus_apply, funext_iff]
  simp only [reduce_apply, ZMod.intCast_eq_intCast_iff_dvd_sub]

/-- **D1(c).** The dial's step goes to the torus's tick. -/
theorem toTorus_step (x : canvas.World) :
    (toTorus n (stepHom x)).toAdd = cubeTick n (toTorus n x).toAdd := by
  rw [toTorus_apply, toTorus_apply, canvasEquiv_step]
  funext i
  rw [cubeTick_apply, reduce_apply, reduce_apply, negC_apply, Int.cast_neg]

/-! ### D2: lines and faces -/

/-- **D2(a).** The torus line of the act `p` at the canvas point `x`, with its sign: `(0, a)` is
the line `(x, a)` forward, and `(1, a)` the line `(x - e a, a)` backward. -/
noncomputable def lineOf (p : Pos) (x : canvas.World) : CubePoint n × Fin 3 → ℝ :=
  if p.1 = 0 then Pi.single ((toTorus n x).toAdd, p.2) 1
  else -Pi.single ((toTorus n x).toAdd - cubeStep n p.2, p.2) 1

theorem toTorus_mul_g (x : canvas.World) (b : Fin 2) (a : Fin 3) :
    (toTorus n (x * g canvas (b, a))).toAdd = (toTorus n x).toAdd + sgn b • cubeStep n a := by
  rw [map_mul, toAdd_mul, toTorus_g]

/-- **D2(b).** The library's chains on the canvas's lines, carried to the torus's lines. -/
noncomputable def torusChain : canvas.Chain →+ (CubePoint n × Fin 3 → ℝ) :=
  Finsupp.liftAddHom fun pr => zmultiplesHom _ (lineOf n pr.1 pr.2)

theorem torusChain_single (p : Pos) (x : canvas.World) (m : ℤ) :
    torusChain n (Finsupp.single (p, x) m) = m • lineOf n p x := by
  simp [torusChain]

theorem trail_s (p : Pos) : canvas.trail (s p) = Finsupp.single (p, 1) 1 := Stage.trail_of _ _

theorem law_s (p : Pos) : canvas.law (s p) = g canvas p := rfl

/-- The trail of the commutator of two acts on the canvas: the four sides of a square. -/
theorem trail_comm (p q : Pos) :
    canvas.trail ⁅s p, s q⁆ = Finsupp.single (p, 1) 1 + Finsupp.single (q, g canvas p) 1 -
      Finsupp.single (p, g canvas q) 1 - Finsupp.single (q, 1) 1 := by
  rw [commutatorElement_def, Stage.trail_mul, Stage.trail_mul, Stage.trail_mul, Stage.trail_inv,
    Stage.trail_inv]
  simp only [trail_s, map_mul, map_inv, law_s, map_neg, Stage.shift_single, mul_one]
  rw [mul_comm (g canvas p) (g canvas q), mul_inv_cancel_right, mul_inv_cancel]
  abel

/-- **D2(c).** The face of the torus across `k`, at the image of `x`, is the trail of the laid
commutator of the steps along `k + 1` and `k + 2`, looked at from `x`. -/
theorem face_eq_trail (x : canvas.World) (k : Fin 3) :
    (fun ℓ => cubeIncidence n ((toTorus n x).toAdd, k) ℓ) =
      torusChain n (canvas.shift x (canvas.trail ⁅s (0, k + 1), s (0, k + 2)⁆)) := by
  rw [trail_comm]
  simp only [map_add, map_sub, Stage.shift_single, torusChain_single, one_smul, mul_one]
  funext ℓ
  simp only [lineOf, toTorus_mul_g, sgn, ite_true, one_smul, Pi.add_apply, Pi.sub_apply,
    Pi.single_apply, cubeIncidence, Matrix.of_apply]
  ring

/-- **D2(d).** The commutator of an act with itself, and with its opposite, leaves no chain on the
torus. -/
theorem trail_same_axis (b : Fin 2) (a : Fin 3) :
    torusChain n (canvas.trail ⁅s (b, a), s (b, a)⁆) = 0 ∧
      torusChain n (canvas.trail ⁅s (b, a), s (b + 1, a)⁆) = 0 := by
  refine ⟨by rw [commutatorElement_self, Stage.trail_one, map_zero], ?_⟩
  rw [trail_comm]
  simp only [map_add, map_sub, torusChain_single, one_smul]
  have hg : ∀ c : Fin 2, (toTorus n (g canvas (c, a))).toAdd = sgn c • cubeStep n a :=
    fun c => toTorus_g n c a
  fin_cases b <;>
    simp [lineOf, hg, sgn]

variable [NeZero n]

/-- **D2(a).** The boundary of an act's line is its end point less its start point. -/
theorem lineOf_boundary (p : Pos) (x : canvas.World) :
    (cubeGauge n)ᵀ *ᵥ lineOf n p x =
      Pi.single (toTorus n (x * g canvas p)).toAdd 1 - Pi.single (toTorus n x).toAdd 1 := by
  obtain ⟨b, a⟩ := p
  funext w
  rw [toTorus_mul_g]
  fin_cases b <;>
    simp [lineOf, mulVec, dotProduct, transpose_apply, cubeGauge, Pi.single_apply, sgn, eq_comm,
      sub_eq_add_neg]

/-- **D2(e).** On each cube the six faces, with the signs of `V`, cancel. -/
theorem cube_faces_cancel (c : CubePoint n) (ℓ : CubePoint n × Fin 3) :
    ∑ k, (cubeIncidence n (c + cubeStep n k, k) ℓ - cubeIncidence n (c, k) ℓ) = 0 := by
  have h := congrFun (congrFun (cube_boundary_mul_incidence n) c) ℓ
  rw [← cubeBoundary_mulVec n (fun σ => cubeIncidence n σ ℓ) c]
  simpa [mulVec, dotProduct, Matrix.mul_apply] using h

/-! ### D4: the tick as a symmetry of the cell complex -/

omit [NeZero n] in
theorem cubeTick_step (i : Fin 3) : cubeTick n (cubeStep n i) = -cubeStep n (i + 1) := by
  funext j
  simp [cubeTick_apply, cubeStep, Pi.single_apply, sub_eq_iff_eq_add]

/-- **D4(a).** The tick's pullback on the lines: the line along `i` at `w` reads the line along
`i + 1` at `tick w - e (i + 1)`, with the sign `-1`. -/
def tickLines (A : CubePoint n × Fin 3 → ℝ) : CubePoint n × Fin 3 → ℝ :=
  fun ℓ => -A (cubeTick n ℓ.1 - cubeStep n (ℓ.2 + 1), ℓ.2 + 1)

/-- **D4(a).** The tick's pullback on the faces: the face across `k` at `w` reads the face across
`k + 1` at `tick w - e (k + 2) - e k`, with the sign `+1`. -/
def tickFaces (B : CubePoint n × Fin 3 → ℝ) : CubePoint n × Fin 3 → ℝ :=
  fun σ => B (cubeTick n σ.1 - cubeStep n (σ.2 + 2) - cubeStep n σ.2, σ.2 + 1)

/-- **D4(a).** The tick's pullback on the cubes: the cube at `c` reads the cube at
`tick c - e 0 - e 1 - e 2`, with the sign `-1`. -/
def tickCubes (ρ : CubePoint n → ℝ) : CubePoint n → ℝ :=
  fun c => -ρ (cubeTick n c - cubeStep n 0 - cubeStep n 1 - cubeStep n 2)

/-- **D4(b).** The tick commutes with the gauge. -/
theorem tick_gauge (f : CubePoint n → ℝ) :
    cubeGauge n *ᵥ (f ∘ cubeTick n) = tickLines n (cubeGauge n *ᵥ f) := by
  funext ℓ
  simp only [tickLines, cubeGauge_mulVec, Function.comp_apply, map_add, cubeTick_step,
    sub_add_cancel, ← sub_eq_add_neg]
  ring

/-- **D4(c).** The tick commutes with the incidence. -/
theorem tick_incidence (A : CubePoint n × Fin 3 → ℝ) :
    cubeIncidence n *ᵥ tickLines n A = tickFaces n (cubeIncidence n *ᵥ A) := by
  funext σ
  obtain ⟨w, k⟩ := σ
  simp only [cubeIncidence_mulVec, tickLines, tickFaces, map_add, cubeTick_step]
  fin_cases k <;> simp only [Fin.isValue, Fin.reduceAdd, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> abel_nf

/-- **D4(d).** The tick commutes with the boundary. -/
theorem tick_boundary (B : CubePoint n × Fin 3 → ℝ) :
    cubeBoundary n *ᵥ tickFaces n B = tickCubes n (cubeBoundary n *ᵥ B) := by
  funext c
  simp only [cubeBoundary_mulVec, tickFaces, tickCubes, map_add, cubeTick_step, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  abel_nf

omit [NeZero n] in
/-- **D4(e).** Three ticks send every corner to its opposite. -/
theorem cubeTick_three (w : CubePoint n) : cubeTick n (cubeTick n (cubeTick n w)) = -w := by
  funext i
  simp only [cubeTick_apply, Pi.neg_apply, neg_neg]
  congr 2
  fin_cases i <;> rfl

omit [NeZero n] in
/-- **D4(e).** Six ticks are the identity. -/
theorem cubeTick_six (w : CubePoint n) :
    cubeTick n (cubeTick n (cubeTick n (cubeTick n (cubeTick n (cubeTick n w))))) = w := by
  rw [cubeTick_three, cubeTick_three, neg_neg]

/-! ### D3: refinement as multiplication by `d` -/

variable (d : ℕ)

/-- Multiplication by `d`, from `ℤ/n` to `ℤ/(d n)`. -/
def scaleBy : ZMod n →+ ZMod (d * n) :=
  ZMod.lift n ⟨zmultiplesHom (ZMod (d * n)) (d : ZMod (d * n)), by
    rw [zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, Nat.mul_comm,
      ZMod.natCast_self]⟩

omit [NeZero n] in
theorem scaleBy_one : scaleBy n d 1 = d := by
  have h : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := by rw [Int.cast_one]
  rw [h, scaleBy, ZMod.lift_coe, zmultiplesHom_apply, one_smul]

/-- **D3(a).** A corner of the torus of side `n` as a corner of the torus of side `d n`. -/
def fineCorner : CubePoint n →+ CubePoint (d * n) := AddMonoidHom.compLeft (scaleBy n d) (Fin 3)

omit [NeZero n] in
theorem fineCorner_step (i : Fin 3) :
    fineCorner n d (cubeStep n i) = d • cubeStep (d * n) i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [fineCorner, cubeStep, scaleBy_one]
  · simp [fineCorner, cubeStep, h]

/-- **D3(a).** A field on the fine lines read on a coarse line: the sum over its `d` pieces. -/
def fineLines (A : CubePoint (d * n) × Fin 3 → ℝ) : CubePoint n × Fin 3 → ℝ :=
  fun ℓ => ∑ j ∈ Finset.range d, A (fineCorner n d ℓ.1 + j • cubeStep (d * n) ℓ.2, ℓ.2)

/-- **D3(a).** A field on the fine faces read on a coarse face: the sum over its `d²` pieces. -/
def fineFaces (B : CubePoint (d * n) × Fin 3 → ℝ) : CubePoint n × Fin 3 → ℝ :=
  fun σ => ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d,
    B (fineCorner n d σ.1 + j • cubeStep (d * n) (σ.2 + 1) + j' • cubeStep (d * n) (σ.2 + 2), σ.2)

/-- **D3(a).** A field on the fine cubes read on a coarse cube: the sum over its `d³` pieces. -/
def fineCubes (ρ : CubePoint (d * n) → ℝ) : CubePoint n → ℝ :=
  fun c => ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d,
    ρ (fineCorner n d c + j₀ • cubeStep (d * n) 0 + j₁ • cubeStep (d * n) 1 +
      j₂ • cubeStep (d * n) 2)

/-- Two telescoping sums over a square of pieces. -/
theorem tele_square (a b : ℕ → ℕ → ℝ) :
    ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d, (a j j' + b (j + 1) j' - a j (j' + 1) - b j j') =
      ∑ j ∈ Finset.range d, a j 0 + ∑ j' ∈ Finset.range d, b d j' -
        ∑ j ∈ Finset.range d, a j d - ∑ j' ∈ Finset.range d, b 0 j' := by
  have ha : ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d, (a j j' - a j (j' + 1)) =
      ∑ j ∈ Finset.range d, (a j 0 - a j d) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_range_sub' (a j) d
  have hb : ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d, (b (j + 1) j' - b j j') =
      ∑ j' ∈ Finset.range d, (b d j' - b 0 j') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => Finset.sum_range_sub (fun j => b j j') d
  have hsplit : ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d,
      (a j j' + b (j + 1) j' - a j (j' + 1) - b j j') =
      ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d, (a j j' - a j (j' + 1)) +
        ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d, (b (j + 1) j' - b j j') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j' _ => by ring
  rw [hsplit, ha, hb, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

variable [NeZero d]

instance : NeZero (d * n) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne n)⟩

/-- **D3(b).** Refinement commutes with the gauge: the `d` pieces of a coarse line telescope. -/
theorem refine_gauge (f : CubePoint (d * n) → ℝ) :
    fineLines n d (cubeGauge (d * n) *ᵥ f) = cubeGauge n *ᵥ (f ∘ fineCorner n d) := by
  funext ℓ
  obtain ⟨w, i⟩ := ℓ
  simp only [fineLines, cubeGauge_mulVec, Function.comp_apply, map_add, fineCorner_step]
  have h : ∀ j : ℕ, fineCorner n d w + j • cubeStep (d * n) i + cubeStep (d * n) i =
      fineCorner n d w + (j + 1) • cubeStep (d * n) i := fun j => by rw [succ_nsmul, add_assoc]
  simp only [h]
  rw [Finset.sum_range_sub (fun j => f (fineCorner n d w + j • cubeStep (d * n) i)) d, zero_smul,
    add_zero]

/-- **D3(c).** Refinement commutes with the incidence: the `d²` pieces of a coarse face
telescope to its four sides. -/
theorem refine_incidence (A : CubePoint (d * n) × Fin 3 → ℝ) :
    fineFaces n d (cubeIncidence (d * n) *ᵥ A) = cubeIncidence n *ᵥ fineLines n d A := by
  funext σ
  obtain ⟨w, k⟩ := σ
  simp only [fineFaces, fineLines, cubeIncidence_mulVec, map_add, fineCorner_step]
  have h1 : ∀ j j' : ℕ, fineCorner n d w + j • cubeStep (d * n) (k + 1) +
      j' • cubeStep (d * n) (k + 2) + cubeStep (d * n) (k + 1) = fineCorner n d w +
      (j + 1) • cubeStep (d * n) (k + 1) + j' • cubeStep (d * n) (k + 2) := fun j j' => by
    rw [succ_nsmul]; abel
  have h2 : ∀ j j' : ℕ, fineCorner n d w + j • cubeStep (d * n) (k + 1) +
      j' • cubeStep (d * n) (k + 2) + cubeStep (d * n) (k + 2) = fineCorner n d w +
      j • cubeStep (d * n) (k + 1) + (j' + 1) • cubeStep (d * n) (k + 2) := fun j j' => by
    rw [succ_nsmul]; abel
  simp only [h1, h2]
  rw [tele_square d (fun j j' => A (fineCorner n d w + j • cubeStep (d * n) (k + 1) +
      j' • cubeStep (d * n) (k + 2), k + 1)) (fun j j' => A (fineCorner n d w +
      j • cubeStep (d * n) (k + 1) + j' • cubeStep (d * n) (k + 2), k + 2))]
  simp only [zero_smul, add_zero]
  have h3 : ∀ j : ℕ, fineCorner n d w + j • cubeStep (d * n) (k + 1) +
      d • cubeStep (d * n) (k + 2) = fineCorner n d w + d • cubeStep (d * n) (k + 2) +
      j • cubeStep (d * n) (k + 1) := fun j => by abel
  simp only [h3]

omit [NeZero d] in
/-- Telescoping a cube of pieces along its first direction. -/
theorem tele_cube₀ (φ : ℕ → ℕ → ℕ → ℝ) :
    ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d,
      (φ (j₀ + 1) j₁ j₂ - φ j₀ j₁ j₂) =
      ∑ j₁ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d, (φ d j₁ j₂ - φ 0 j₁ j₂) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j₂ _ => Finset.sum_range_sub (fun j₀ => φ j₀ j₁ j₂) d

omit [NeZero d] in
/-- Telescoping a cube of pieces along its second direction. -/
theorem tele_cube₁ (φ : ℕ → ℕ → ℕ → ℝ) :
    ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d,
      (φ j₀ (j₁ + 1) j₂ - φ j₀ j₁ j₂) =
      ∑ j₀ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d, (φ j₀ d j₂ - φ j₀ 0 j₂) := by
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j₂ _ => Finset.sum_range_sub (fun j₁ => φ j₀ j₁ j₂) d

omit [NeZero d] in
/-- Telescoping a cube of pieces along its third direction. -/
theorem tele_cube₂ (φ : ℕ → ℕ → ℕ → ℝ) :
    ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d,
      (φ j₀ j₁ (j₂ + 1) - φ j₀ j₁ j₂) =
      ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d, (φ j₀ j₁ d - φ j₀ j₁ 0) :=
  Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j₁ _ =>
    Finset.sum_range_sub (fun j₂ => φ j₀ j₁ j₂) d

/-- **D3(d).** Refinement commutes with the boundary: the `d³` pieces of a coarse cube telescope
to its six faces. -/
theorem refine_boundary (B : CubePoint (d * n) × Fin 3 → ℝ) :
    fineCubes n d (cubeBoundary (d * n) *ᵥ B) = cubeBoundary n *ᵥ fineFaces n d B := by
  funext c
  have p₀ : ∀ j₀ j₁ j₂ : ℕ, fineCorner n d c + j₀ • cubeStep (d * n) 0 +
      j₁ • cubeStep (d * n) 1 + j₂ • cubeStep (d * n) 2 + cubeStep (d * n) 0 =
      fineCorner n d c + (j₀ + 1) • cubeStep (d * n) 0 + j₁ • cubeStep (d * n) 1 +
        j₂ • cubeStep (d * n) 2 := fun j₀ j₁ j₂ => by rw [succ_nsmul]; abel
  have p₁ : ∀ j₀ j₁ j₂ : ℕ, fineCorner n d c + j₀ • cubeStep (d * n) 0 +
      j₁ • cubeStep (d * n) 1 + j₂ • cubeStep (d * n) 2 + cubeStep (d * n) 1 =
      fineCorner n d c + j₀ • cubeStep (d * n) 0 + (j₁ + 1) • cubeStep (d * n) 1 +
        j₂ • cubeStep (d * n) 2 := fun j₀ j₁ j₂ => by rw [succ_nsmul]; abel
  have p₂ : ∀ j₀ j₁ j₂ : ℕ, fineCorner n d c + j₀ • cubeStep (d * n) 0 +
      j₁ • cubeStep (d * n) 1 + j₂ • cubeStep (d * n) 2 + cubeStep (d * n) 2 =
      fineCorner n d c + j₀ • cubeStep (d * n) 0 + j₁ • cubeStep (d * n) 1 +
        (j₂ + 1) • cubeStep (d * n) 2 := fun j₀ j₁ j₂ => by rw [succ_nsmul]; abel
  have t₀ := tele_cube₀ d (fun a b e => B (fineCorner n d c + a • cubeStep (d * n) 0 +
    b • cubeStep (d * n) 1 + e • cubeStep (d * n) 2, 0))
  have t₁ := tele_cube₁ d (fun a b e => B (fineCorner n d c + a • cubeStep (d * n) 0 +
    b • cubeStep (d * n) 1 + e • cubeStep (d * n) 2, 1))
  have t₂ := tele_cube₂ d (fun a b e => B (fineCorner n d c + a • cubeStep (d * n) 0 +
    b • cubeStep (d * n) 1 + e • cubeStep (d * n) 2, 2))
  simp only [fineCubes, cubeBoundary_mulVec, Fin.sum_univ_three, Fin.isValue, p₀, p₁, p₂,
    Finset.sum_add_distrib]
  rw [t₀, t₁, t₂]
  simp only [fineFaces, map_add, fineCorner_step, Fin.isValue, Fin.reduceAdd, zero_smul,
    add_zero, Finset.sum_sub_distrib]
  have r₁ : ∀ x : CubePoint (d * n), ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d,
      B (fineCorner n d c + x + j • cubeStep (d * n) 2 + j' • cubeStep (d * n) 0, 1) =
      ∑ j₀ ∈ Finset.range d, ∑ j₂ ∈ Finset.range d,
        B (fineCorner n d c + j₀ • cubeStep (d * n) 0 + x + j₂ • cubeStep (d * n) 2, 1) := by
    intro x
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j₂ _ => by
      congr 2; abel
  have r₂ : ∀ x : CubePoint (d * n), ∑ j ∈ Finset.range d, ∑ j' ∈ Finset.range d,
      B (fineCorner n d c + x + j • cubeStep (d * n) 0 + j' • cubeStep (d * n) 1, 2) =
      ∑ j₀ ∈ Finset.range d, ∑ j₁ ∈ Finset.range d,
        B (fineCorner n d c + j₀ • cubeStep (d * n) 0 + j₁ • cubeStep (d * n) 1 + x, 2) :=
    fun x => Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j₁ _ => by
      congr 2; abel
  have r₁' := r₁ 0
  simp only [add_zero] at r₁'
  rw [r₁, r₂, r₁']

omit [NeZero n] [NeZero d] in
/-- **D3(e).** Refinement commutes with the tick. -/
theorem refine_tick (w : CubePoint n) :
    fineCorner n d (cubeTick n w) = cubeTick (d * n) (fineCorner n d w) := by
  funext i
  simp [fineCorner, cubeTick_apply]

end Artform.Stages.DialCanvas
