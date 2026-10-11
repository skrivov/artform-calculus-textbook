import ArtformTextbook.Ch12.ColourGroupsData
import ArtformTextbook.Ch12.Defs.ColourGroups
import ArtformTextbook.Ch12.Icosahedron

/-!
# The kernel's checks of the colour-group certificate

The data of `Ch12/ColourGroupsData.lean`, read as tables, and every claim about them that the
proofs of Chapter 12 use, each checked by `decide +kernel`:

* the packed tables of the icosahedral group agree with `Icosahedron.perm` and
  `Icosahedron.gE`, the product table `a5At` is right on the base edge, and two rotations
  generate the sixty;
* Valentiner's group: the coset representatives are unitary of determinant one, and a few
  products of matrices, those of the representatives with the generators, are checked exactly;
  the tables of products `c_i R_k` and `c_d c_i` follow from them along the trees of words; the
  cosets are told apart by `cᵀ c`; and the tables of inverses, classes and conjugators agree
  with the product;
* the cube group: its matrices are unitary of determinant one, and their powers and traces.

The kernel computes slowly with integers, and quickly with tables of natural numbers; so the
exact products of matrices are few, and the checks over many elements are recursions on
natural numbers (`allBelow`).
-/

namespace Artform.ColourGroups

open Exact Icosahedron

/-! ### Checks by recursion -/

/-- `P n` holds for every `n < m`, as a recursion the kernel runs in linear time. -/
def allBelow (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => P n && allBelow P n

theorem allBelow_iff (P : ℕ → Bool) (m : ℕ) : allBelow P m = true ↔ ∀ n < m, P n = true := by
  induction m with
  | zero => simp [allBelow]
  | succ m ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
      · exact h2 n h
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun n hn => h n (Nat.lt_succ_of_lt hn)⟩

/-- The number of `n < m` with `P n`. -/
def countBelow (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if P n then 1 else 0) + countBelow P n

theorem countBelow_eq (P : ℕ → Bool) (m : ℕ) :
    countBelow P m = ((Finset.range m).filter fun n => P n = true).card := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [countBelow, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), add_comm]
    · simp

/-! ### Reading the tables -/

/-- `perm k i`, read from the packed table. -/
def permAt (k i : ℕ) : ℕ := entry 4 permT (12 * k + i)

/-- The index of the product of the rotations `k` and `l`. -/
def a5At (k l : ℕ) : ℕ := entry 6 a5T (60 * k + l)

/-- A digit of the packed rotations, as an integer. -/
def gDigit (k n : ℕ) : ℤ := (entry 3 gT (18 * k + n) : ℤ) - 4

/-- An entry `a + b φ` of the doubled rotation `k`. -/
def gEntry (k r c : ℕ) : ZOP := ⟨gDigit k (6 * r + 2 * c), gDigit k (6 * r + 2 * c + 1), 0, 0⟩

/-- The doubled rotation `k`, read from the packed table. -/
def gAt (k : ℕ) : M3Z :=
  ⟨gEntry k 0 0, gEntry k 0 1, gEntry k 0 2, gEntry k 1 0, gEntry k 1 1, gEntry k 1 2,
   gEntry k 2 0, gEntry k 2 1, gEntry k 2 2⟩

/-- The parent of rotation `k` in the tree of words. -/
def a5Par (k : ℕ) : ℕ := entry 7 a5ParT k % 64

/-- The generator by which rotation `k` follows its parent. -/
def a5Gen (k : ℕ) : ℕ := if 64 ≤ entry 7 a5ParT k then a5GenA else a5GenB

/-- The depth of rotation `k` in the tree of words. -/
def a5Dep (k : ℕ) : ℕ := entry 4 a5DepT k

/-- `ω^j` in `ℤ[ω, φ]`, for any natural number `j`. -/
def omegaZ (j : ℕ) : ZOP := ZOP.omegaPow ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The doubled coset representative `i`, for any natural number `i`. -/
def cosetAt (i : ℕ) : M3Z := cosetE ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The power `ω^j` of an element `(j, k, i)`. -/
def jOf (x : ℕ) : ℕ := x / 360

/-- The rotation `R_k` of an element `(j, k, i)`. -/
def kOf (x : ℕ) : ℕ := x / 6 % 60

/-- The coset `c_i` of an element `(j, k, i)`. -/
def iOf (x : ℕ) : ℕ := x % 6

/-- The code of the element `(j, k, i)`. -/
def mkC (j k i : ℕ) : ℕ := j * 360 + k * 6 + i

/-- `c_i R_k`, coded. -/
def cRAt (i k : ℕ) : ℕ := entry 11 cRT (60 * i + k)

/-- `c_d c_i`, coded. -/
def ccAt (d i : ℕ) : ℕ := entry 11 ccT (6 * d + i)

/-- The product `ω^j R_k c ⋅ ω^{j'} R_{k'} c'` of two coded factors `r` and `s` whose cosets
meet in the middle, `c R_{k'} = 1`: `ω^{j + j'} R_k R_{k'} c'`. -/
def comb (r s : ℕ) : ℕ := mkC ((jOf r + jOf s) % 3) (a5At (kOf r) (kOf s)) (iOf s)

/-- The product of two elements of Valentiner's group, coded:
`ω^j R_k c_i ⋅ ω^{j'} R_{k'} c_{i'} = ω^{j + j' + a + e} R_k R_b R_f c_g`, where
`c_i R_{k'} = ω^a R_b c_d` and `c_d c_{i'} = ω^e R_f c_g`. -/
def mulC (x y : ℕ) : ℕ :=
  let r := cRAt (iOf x) (kOf y)
  let s := ccAt (iOf r) (iOf y)
  mkC ((jOf x + jOf y + jOf r + jOf s) % 3) (a5At (a5At (kOf x) (kOf r)) (kOf s)) (iOf s)

/-- The identity, `(0, 1, 0)`. -/
def oneC : ℕ := 6

/-- The inverse, read from the table. -/
def invAt (x : ℕ) : ℕ := entry 11 invT x

/-- The row of the class table of an element. -/
def labAt (x : ℕ) : ℕ := entry 5 labT x

/-- An element conjugating `x` to the representative of its class. -/
def conjAt (x : ℕ) : ℕ := entry 11 conjT x

/-- The representative of the class of row `l`. -/
def repAt (l : ℕ) : ℕ := entry 11 repT l

/-- Search for the order of `x` under the product `mul` with identity `one`: from `acc = x^n`,
the least `m ≥ n` with `x^m = one`, within `fuel` steps. -/
def ordAux (mul : ℕ → ℕ → ℕ) (one x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, n => n
  | fuel + 1, acc, n => if acc = one then n else ordAux mul one x fuel (mul x acc) (n + 1)

/-- The order of an element of Valentiner's group, by search. -/
def ordC (x : ℕ) : ℕ := ordAux mulC oneC x 60 (mulC x oneC) 1

/-- The order of a rotation, by search. -/
def ordA5 (k : ℕ) : ℕ := ordAux a5At 1 k 60 (a5At k 1) 1

/-- The code of the generator `a5GenA`, `(0, a5GenA, 0)`. -/
def genAC : ℕ := mkC 0 a5GenA 0

/-- The code of the generator `a5GenB`, `(0, a5GenB, 0)`. -/
def genBC : ℕ := mkC 0 a5GenB 0

/-- The code of `F = c_1`, `(0, 1, 1)`. -/
def genFC : ℕ := mkC 0 1 1

/-- `x ↦ t x t⁻¹`, coded. -/
def conjC (t x : ℕ) : ℕ := mulC (mulC t x) (invAt t)

/-- The doubled matrix of `F`: `2 [[1, 0, 0], [0, 0, ω], [0, -ω², 0]]`. -/
def fZ : M3Z :=
  ⟨z 2 0 0 0, z 0 0 0 0, z 0 0 0 0, z 0 0 0 0, z 0 0 0 0, z 0 0 2 0, z 0 0 0 0, z 2 0 2 0,
   z 0 0 0 0⟩

/-- The rotation by which `c_i` follows its parent: `a5GenA` or `a5GenB` for `g = 1, 2`. -/
def genRot (g : ℕ) : ℕ := if g = 1 then a5GenA else a5GenB

/-- `c_m g`, coded, for the generator `g` (`0` for `F`, `1, 2` for the rotations). -/
def nextC (m g : ℕ) : ℕ := if g = 0 then ccAt m 1 else cRAt m (genRot g)

/-- The parent of the representative `c_i` in its tree. -/
def parC (i : ℕ) : ℕ := (cosetParent ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩).1

/-- The generator by which `c_i` follows its parent. -/
def parG (i : ℕ) : ℕ := (cosetParent ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩).2

/-- The doubled generators of the coset representatives: `F`, `a5GenA` and `a5GenB`. -/
def genZ (g : Fin 3) : M3Z := ![fZ, gAt a5GenA, gAt a5GenB] g

/-- `cᵀ c` for the doubled representative `c`. -/
def qZ (i : Fin 6) : M3Z := M3Z.mul (M3Z.transpose (cosetE i)) (cosetE i)

/-! ### The icosahedral group -/

theorem permAt_eq : ∀ k : Fin 60, ∀ i : Fin 12, permAt k i = perm k i := by
  decide +kernel

theorem gAt_eq : ∀ k : Fin 60, gAt k = M3Z.ofM3 (gE k) := by
  decide +kernel

theorem a5At_check : allBelow (fun k => allBelow (fun l =>
    decide (a5At k l < 60) && permAt (a5At k l) 0 == permAt k (permAt l 0) &&
      permAt (a5At k l) 4 == permAt k (permAt l 4)) 60) 60 = true := by
  decide +kernel

theorem a5Par_check : allBelow (fun k => k == 1 ||
    (decide (a5Par k < 60) && decide (a5Dep (a5Par k) < a5Dep k) &&
      a5At (a5Gen k) (a5Par k) == k)) 60 = true := by
  decide +kernel

theorem a5Gen_lt : a5GenA < 60 ∧ a5GenB < 60 := by
  decide

theorem gAt_one : gAt 1 = M3Z.scalar (z 2 0 0 0) := by
  decide +kernel

theorem ordA5_check : allBelow (fun k => decide (ordA5 k ∣ 30) && decide (ordA5 k < 60))
    60 = true := by
  decide +kernel

theorem ordA5_gens : ordA5 a5GenA = 2 ∧ ordA5 a5GenB = 3 ∧ ordA5 0 = 5 := by
  decide +kernel

/-! ### Valentiner's group: exact products -/

theorem cosetE_unitary : ∀ i : Fin 6,
    M3Z.mul (cosetE i) (M3Z.star (cosetE i)) = M3Z.scalar (z 4 0 0 0) ∧
      M3Z.det (cosetE i) = z 8 0 0 0 := by
  decide +kernel

theorem cosetE_zero : cosetE 0 = M3Z.scalar (z 2 0 0 0) := by
  decide +kernel

theorem cosetE_one : cosetE 1 = fZ := by
  decide +kernel

/-- The representatives times the two generating rotations. -/
theorem gen_spec : ∀ i : Fin 6, ∀ g ∈ [a5GenA, a5GenB],
    M3Z.mul (cosetE i) (gAt g) =
      M3Z.smul (omegaZ (jOf (cRAt i g)))
        (M3Z.mul (gAt (kOf (cRAt i g))) (cosetAt (iOf (cRAt i g)))) := by
  decide +kernel

/-- The representatives times `F = c_1`. -/
theorem cc1_spec : ∀ d : Fin 6,
    M3Z.mul (cosetE d) (cosetE 1) =
      M3Z.smul (omegaZ (jOf (ccAt d 1)))
        (M3Z.mul (gAt (kOf (ccAt d 1))) (cosetAt (iOf (ccAt d 1)))) := by
  decide +kernel

theorem cosetParent_spec : ∀ i : Fin 6, i = 0 ∨
    ((cosetParent i).1 < i ∧
      M3Z.smul (z 2 0 0 0) (cosetE i) =
        M3Z.mul (cosetE (cosetParent i).1) (genZ (cosetParent i).2)) := by
  decide +kernel

theorem qZ_distinct : ∀ m m' : Fin 3, ∀ i i' : Fin 6,
    M3Z.smul (ZOP.omegaPow (2 * m)) (qZ i) = M3Z.smul (ZOP.omegaPow (2 * m')) (qZ i') →
      m = m' ∧ i = i' := by
  decide +kernel

/-- The traces of the representatives of the seventeen classes. -/
theorem rep_trace : ∀ l : Fin 17,
    omegaZ (jOf (repAt l)) * M3Z.trace (M3Z.mul (gAt (kOf (repAt l))) (cosetAt (iOf (repAt l)))) =
      z 4 0 0 0 * traceZ l := by
  decide +kernel

/-! ### Valentiner's group: tables -/

/-- `c_i R_k` along the tree of words in the generating rotations. -/
theorem cR_check : allBelow (fun i => allBelow (fun k =>
    if k = 1 then cRAt i 1 == mkC 0 1 i
    else cRAt i k == comb (cRAt i (a5Gen k)) (cRAt (iOf (cRAt i (a5Gen k))) (a5Par k))) 60)
      6 = true := by
  decide +kernel

/-- `c_d c_i` along the tree of the representatives. -/
theorem cc_check : allBelow (fun d => allBelow (fun i =>
    if i = 0 then ccAt d 0 == mkC 0 1 d
    else ccAt d i == comb (ccAt d (parC i)) (nextC (iOf (ccAt d (parC i))) (parG i))) 6)
      6 = true := by
  decide +kernel

theorem inv_check : allBelow (fun x => decide (invAt x < 1080) && mulC x (invAt x) == oneC)
    1080 = true := by
  decide +kernel

theorem labA_check : allBelow (fun x => decide (labAt x < 17) &&
    labAt (conjC genAC x) == labAt x) 1080 = true := by
  decide +kernel

theorem labB_check : allBelow (fun x => labAt (conjC genBC x) == labAt x) 1080 = true := by
  decide +kernel

theorem labF_check : allBelow (fun x => labAt (conjC genFC x) == labAt x) 1080 = true := by
  decide +kernel

theorem conj_check : allBelow (fun x => decide (conjAt x < 1080) &&
    mulC (conjAt x) x == mulC (repAt (labAt x)) (conjAt x)) 1080 = true := by
  decide +kernel

theorem rep_check : allBelow (fun l => decide (repAt l < 1080) && labAt (repAt l) == l)
    17 = true := by
  decide +kernel

theorem lab_count : ∀ l : Fin 17,
    countBelow (fun x => labAt x == l) 1080 = (s1080ClassTable l).size := by
  decide +kernel

theorem rep_order : ∀ l : Fin 17, ordC (repAt l) = (s1080ClassTable l).order := by
  decide +kernel

/-! ### The cube group -/

theorem cubeE_unitary : ∀ k : Fin 24,
    M3Z.mul (cubeE k) (M3Z.star (cubeE k)) = M3Z.scalar 1 ∧ M3Z.det (cubeE k) = 1 := by
  decide +kernel

theorem cubeE_injective : ∀ k l : Fin 24, cubeE k = cubeE l → k = l := by
  decide +kernel

end Artform.ColourGroups
