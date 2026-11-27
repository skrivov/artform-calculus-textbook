import Mathlib

/-!
# A split square forces its weights' inverses to add (finding 1059)

Road G, the bridge campaign, wave C2. The metatheory's wave 417 cuts every square of a periodic
board along one diagonal and gives the two triangle sorts their own additive weights `K` and `J`.
Its static comparison theorem: every old edge potential has a lift with zero kick on each new
diagonal and the old unit-weight kick on every old line exactly when `K` and `J` are bijective and
`K⁻¹ + J⁻¹ = 1`; the lift is then unique. Here it is proved for every finite abelian group.

* `Line`, `circ`, `lower`, `upper`, `lower_add_upper`, `Balanced` (C2(a)): the board
  `ZMod n × ZMod m`, its lines, a square's circulation, the two triangles of a square cut along the
  diagonal from `(i, j)` to `(i + 1, j + 1)`, and a balanced lift.
* `inverses_add` (C2(b)): if every old potential has a balanced lift, `K` and `J` are bijective and
  `K r = J s` implies `r + s = K r`.
* `balanced_of_inverses` (C2(c)): conversely, right inverses `K'`, `J'` with `K' x + J' x = x` give
  every old potential a balanced lift.
* `balanced_unique` (C2(d)): a balanced lift is unique.
* `equal_weights_fail` (C2(e)): in a group of exponent two, one weight on both triangles never
  balances every potential.
* `omegaK`, `omegaJ`: the two nontrivial scalars of the four-element field on `ZMod 2 × ZMod 2`,
  wave 417's smallest solution, which balance every potential on the `2 × 2` board.

None of the mathematics is new: it is the algebra of two weights in parallel. The theorem and its
proof on paper are the metatheory's wave 417; the proof of `inverses_add` uses one dipole and three
squares.
-/

namespace Artform.Stages.SplitSquare

variable {n m : ℕ} {A : Type*} [AddCommGroup A]

/-- The lines of the periodic board `ZMod n × ZMod m`: `(false, i, j)` is the horizontal line from
`(i, j)` to `(i + 1, j)`, and `(true, i, j)` the vertical line from `(i, j)` to `(i, j + 1)`. -/
abbrev Line (n m : ℕ) := Bool × ZMod n × ZMod m

/-- The circulation of the square at `(i, j)`: its bottom and right sides less its top and left. -/
def circ (q : Line n m → A) (i : ZMod n) (j : ZMod m) : A :=
  q (false, i, j) + q (true, i + 1, j) - q (false, i, j + 1) - q (true, i, j)

/-- The lower triangle of the square at `(i, j)`, below the diagonal from `(i, j)` to
`(i + 1, j + 1)`, which carries the potential `d (i, j)`: the bottom and right sides less the
diagonal. -/
def lower (q : Line n m → A) (d : ZMod n × ZMod m → A) (i : ZMod n) (j : ZMod m) : A :=
  q (false, i, j) + q (true, i + 1, j) - d (i, j)

/-- The upper triangle: the diagonal less the top and left sides. -/
def upper (q : Line n m → A) (d : ZMod n × ZMod m → A) (i : ZMod n) (j : ZMod m) : A :=
  d (i, j) - q (false, i, j + 1) - q (true, i, j)

/-- C2(a). The two triangles' circulations sum to the square's. -/
theorem lower_add_upper (q : Line n m → A) (d : ZMod n × ZMod m → A) (i : ZMod n) (j : ZMod m) :
    lower q d i j + upper q d i j = circ q i j := by
  simp only [lower, upper, circ]
  abel

/-- C2(a). A balanced lift `d` of the old potential `q`: Pair's kick with the weight `K` on the
lower triangles and `J` on the upper ones is zero on every diagonal, and on every old line it is
the old kick with the unit weight. The horizontal line `(false, i, j)` is the bottom of the lower
triangle at `(i, j)` and the top of the upper one at `(i, j - 1)`; the vertical line
`(true, i, j)` is the right side of the lower triangle at `(i - 1, j)` and the left side of the
upper one at `(i, j)`. -/
def Balanced (K J : A →+ A) (q : Line n m → A) (d : ZMod n × ZMod m → A) : Prop :=
  (∀ i j, K (lower q d i j) = J (upper q d i j)) ∧
  (∀ i j, K (lower q d i j) - J (upper q d i (j - 1)) = circ q i j - circ q i (j - 1)) ∧
  (∀ i j, K (lower q d (i - 1) j) - J (upper q d i j) = circ q (i - 1) j - circ q i j)

/-- The dipole: the unit `a` on the horizontal line `(false, 0, 1)` and zero elsewhere. -/
def dipole (n m : ℕ) (a : A) : Line n m → A := fun e => if e = (false, 0, 1) then a else 0

theorem circ_dipole_one (hm : (1 : ZMod m) ≠ 0) (a : A) : circ (dipole n m a) 0 1 = a := by
  have h2 : (1 + 1 : ZMod m) ≠ 1 := by
    intro h
    exact hm (by simpa using h)
  simp [circ, dipole, h2]

theorem circ_dipole_ten (hn : (1 : ZMod n) ≠ 0) (a : A) : circ (dipole n m a) 1 0 = 0 := by
  simp [circ, dipole, hn]

/-- The heart of the forcing: from a balanced lift of the dipole, three squares and two old lines
give `x` and `y` with `K x = J y = x + y = a`. -/
theorem dipole_parts (hn : (1 : ZMod n) ≠ 0) (hm : (1 : ZMod m) ≠ 0) (K J : A →+ A) (a : A)
    (d : ZMod n × ZMod m → A) (h : Balanced K J (dipole n m a) d) :
    ∃ x y, K x = a ∧ J y = a ∧ x + y = a := by
  obtain ⟨hd, hh, hv⟩ := h
  set q := dipole n m a
  have e1 := hh 0 1
  have e2 := hv 1 0
  simp only [sub_self] at e1 e2
  have d00 := hd 0 0
  have d10 := hd 1 0
  have d01 := hd 0 1
  have c01 := circ_dipole_one (n := n) hm a
  have c10 := circ_dipole_ten (m := m) hn a
  have key : K (lower q d 0 1) - J (upper q d 1 0) = a := by
    calc K (lower q d 0 1) - J (upper q d 1 0)
        = (K (lower q d 0 1) - J (upper q d 0 0)) + (K (lower q d 0 0) - J (upper q d 1 0)) := by
          rw [d00]; abel
      _ = (circ q 0 1 - circ q 0 0) + (circ q 0 0 - circ q 1 0) := by rw [e1, e2]
      _ = a := by rw [sub_add_sub_cancel, c01, c10, sub_zero]
  refine ⟨lower q d 0 1 - lower q d 1 0, upper q d 0 1 - upper q d 1 0, ?_, ?_, ?_⟩
  · rw [map_sub, d10, key]
  · rw [map_sub, ← d01, key]
  · have s01 := lower_add_upper q d 0 1
    have s10 := lower_add_upper q d 1 0
    calc lower q d 0 1 - lower q d 1 0 + (upper q d 0 1 - upper q d 1 0)
        = (lower q d 0 1 + upper q d 0 1) - (lower q d 1 0 + upper q d 1 0) := by abel
      _ = a := by rw [s01, s10, c01, c10, sub_zero]

/-- C2(b). **The inverses add.** If every old potential has a balanced lift, the two weights are
bijective, and `K r = J s` implies `r + s = K r`: that is, `K⁻¹ + J⁻¹ = 1`. -/
theorem inverses_add [Finite A] (hn : (1 : ZMod n) ≠ 0) (hm : (1 : ZMod m) ≠ 0) (K J : A →+ A)
    (h : ∀ q : Line n m → A, ∃ d, Balanced K J q d) :
    Function.Bijective K ∧ Function.Bijective J ∧ ∀ r s, K r = J s → r + s = K r := by
  have parts : ∀ a : A, ∃ x y, K x = a ∧ J y = a ∧ x + y = a := by
    intro a
    obtain ⟨d, hd⟩ := h (dipole n m a)
    exact dipole_parts hn hm K J a d hd
  have sK : Function.Surjective K := fun a => by
    obtain ⟨x, _, hx, _⟩ := parts a
    exact ⟨x, hx⟩
  have sJ : Function.Surjective J := fun a => by
    obtain ⟨_, y, _, hy, _⟩ := parts a
    exact ⟨y, hy⟩
  have iK : Function.Injective K := Finite.injective_iff_surjective.mpr sK
  have iJ : Function.Injective J := Finite.injective_iff_surjective.mpr sJ
  refine ⟨⟨iK, sK⟩, ⟨iJ, sJ⟩, fun r s hrs => ?_⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := parts (K r)
  have hxr : x = r := iK hx
  have hys : y = s := iJ (hy.trans hrs)
  calc r + s = x + y := by rw [hxr, hys]
    _ = K r := hxy

/-- C2(c). **The converse.** With right inverses `K'` and `J'` whose sum is the identity, every
old potential has the balanced lift `d = (bottom and right sides) - K' (circ)`. -/
theorem balanced_of_inverses (K J K' J' : A →+ A) (hK : ∀ x, K (K' x) = x)
    (hJ : ∀ x, J (J' x) = x) (hT : ∀ x, K' x + J' x = x) (q : Line n m → A) :
    Balanced K J q
      (fun p => q (false, p.1, p.2) + q (true, p.1 + 1, p.2) - K' (circ q p.1 p.2)) := by
  set d : ZMod n × ZMod m → A :=
    fun p => q (false, p.1, p.2) + q (true, p.1 + 1, p.2) - K' (circ q p.1 p.2)
  have lo : ∀ i j, K (lower q d i j) = circ q i j := by
    intro i j
    have : lower q d i j = K' (circ q i j) := by
      simp only [lower, d]
      abel
    rw [this, hK]
  have up : ∀ i j, J (upper q d i j) = circ q i j := by
    intro i j
    have hs := lower_add_upper q d i j
    have hl : lower q d i j = K' (circ q i j) := by
      simp only [lower, d]
      abel
    rw [hl] at hs
    have : upper q d i j = J' (circ q i j) :=
      (eq_sub_of_add_eq' hs).trans (eq_sub_of_add_eq' (hT (circ q i j))).symm
    rw [this, hJ]
  refine ⟨fun i j => by rw [lo, up], fun i j => by rw [lo, up], fun i j => by rw [lo, up]⟩

/-- C2(d). **Uniqueness.** With `K` and `J` injective and the identity of `inverses_add`, a
balanced lift is unique: the zero diagonal kick alone makes each triangle's weighted circulation
the square's. -/
theorem balanced_unique (K J : A →+ A) (iK : Function.Injective K)
    (hT : ∀ r s, K r = J s → r + s = K r) {q : Line n m → A} {d d' : ZMod n × ZMod m → A}
    (h : Balanced K J q d) (h' : Balanced K J q d') : d = d' := by
  have key : ∀ e : ZMod n × ZMod m → A, Balanced K J q e → ∀ i j, K (lower q e i j) = circ q i j :=
    fun e he i j => by
      have := hT _ _ (he.1 i j)
      rw [lower_add_upper] at this
      exact this.symm
  funext p
  obtain ⟨i, j⟩ := p
  have hl : lower q d i j = lower q d' i j := iK ((key d h i j).trans (key d' h' i j).symm)
  simp only [lower] at hl
  exact neg_injective (add_left_cancel (a := q (false, i, j) + q (true, i + 1, j))
    (by simpa [sub_eq_add_neg] using hl))

/-- C2(e). **Equal weights fail.** In a group of exponent two with a nonzero element, one weight on
both triangles never balances every potential. -/
theorem equal_weights_fail [Finite A] (hn : (1 : ZMod n) ≠ 0) (hm : (1 : ZMod m) ≠ 0)
    (h2 : ∀ x : A, x + x = 0) (x : A) (hx : x ≠ 0) (K : A →+ A) :
    ¬ ∀ q : Line n m → A, ∃ d, Balanced K K q d := by
  intro h
  obtain ⟨⟨iK, _⟩, _, hT⟩ := inverses_add hn hm K K h
  have := hT x x rfl
  rw [h2] at this
  exact hx (iK (this.symm.trans (map_zero K).symm))

/-- The first nontrivial scalar of the four-element field on `ZMod 2 × ZMod 2`. -/
def omegaK : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun x := (x.2, x.1 + x.2)
  map_zero' := by simp
  map_add' x y := by
    ext
    · simp
    · simp only [Prod.fst_add, Prod.snd_add]
      abel

/-- The second nontrivial scalar, the square of the first. -/
def omegaJ : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun x := (x.1 + x.2, x.1)
  map_zero' := by simp
  map_add' x y := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add]
      abel
    · simp

theorem omega_laws :
    (∀ x, omegaK (omegaJ x) = x) ∧ (∀ x, omegaJ (omegaK x) = x) ∧
      (∀ x, omegaJ x + omegaK x = x) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;> obtain ⟨a, b⟩ := x <;>
    fin_cases a <;> fin_cases b <;> decide

section NonVacuity

/-- Wave 417's smallest solution balances every potential on the `2 × 2` board. -/
example (q : Line 2 2 → ZMod 2 × ZMod 2) : ∃ d, Balanced omegaK omegaJ q d :=
  ⟨_, balanced_of_inverses omegaK omegaJ omegaJ omegaK omega_laws.1 omega_laws.2.1
    omega_laws.2.2 q⟩

/-- `inverses_add` applies to it. -/
example : Function.Bijective omegaK ∧ Function.Bijective omegaJ ∧
    ∀ r s, omegaK r = omegaJ s → r + s = omegaK r :=
  inverses_add (n := 2) (m := 2) (by decide) (by decide) omegaK omegaJ fun q =>
    ⟨_, balanced_of_inverses omegaK omegaJ omegaJ omegaK omega_laws.1 omega_laws.2.1
      omega_laws.2.2 q⟩

end NonVacuity

end Artform.Stages.SplitSquare
