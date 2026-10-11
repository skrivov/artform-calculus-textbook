import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RepresentationTheory.Irreducible
import ArtformTextbook.Ch11.Defs.Colourless
import ArtformTextbook.Ch12.Defs.ColourGroups

/-!
# The cube group, element by element

The cube group of Chapter 12 (`cubeGroup`) is the group of the signed permutation matrices of
determinant one. Here its elements are enumerated: the pairs `(σ, s)` of a permutation of the
three axes and three signs with `sgn(σ) Π_i s_i = 1` (`CubeGroup.Pair`, a finite type that the
kernel enumerates) correspond one to one to the rotations (`CubeGroup.equiv`), the rotation of
`(σ, s)` being the matrix with the entry `s_i` in row `i` and column `σ(i)`. The trace of that
rotation is the sum of the signs on the fixed axes of `σ`, and its class (`cubeClassOf`) is read
off the pair (`CubeGroup.classOf`); counts of rotations are then decided by the kernel.

The triplet of the cube group, each rotation acting on `ℂ³` by its matrix (`cubeTriplet`), is
irreducible (`CubeGroup.isIrreducible_tripletRep`): the half-turns about the face axes project
any nonzero invariant subspace onto a coordinate axis, and a third-turn carries that axis to the
other two.
-/

namespace Artform

open Matrix

/-- The triplet `3_r` of the cube group: each rotation acts on the colours by its matrix. -/
noncomputable def cubeTriplet : cubeGroup →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp cubeGroup.subtype

theorem cubeTriplet_mem (g : cubeGroup) :
    cubeTriplet g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  (g : Matrix.specialUnitaryGroup (Fin 3) ℂ).2

namespace CubeGroup

/-- The pairs `(σ, s)` of a permutation of the three axes and three signs with
`sgn(σ) Π_i s_i = 1`. -/
abbrev Pair : Type :=
  {p : Equiv.Perm (Fin 3) × (Fin 3 → ℤˣ) // Equiv.Perm.sign p.1 * ∏ i, p.2 i = 1}

theorem signedPermMatrix_eq (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) :
    signedPermMatrix σ s = Matrix.diagonal (fun i => (((s i : ℤˣ) : ℤ) : ℂ)) * σ.permMatrix ℂ := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [signedPermMatrix, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem det_signedPermMatrix (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) :
    (signedPermMatrix σ s).det = (((Equiv.Perm.sign σ * ∏ i, s i : ℤˣ) : ℤ) : ℂ) := by
  rw [signedPermMatrix_eq, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation,
    Units.val_mul, Units.coe_prod, Int.cast_mul, Int.cast_prod, mul_comm]

theorem star_mul_signedPermMatrix (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤˣ) :
    star (signedPermMatrix σ s) * signedPermMatrix σ s = 1 := by
  rw [star_signedPermMatrix, signedPermMatrix_mul]
  convert signedPermMatrix_one using 2
  · ext i
    simp
  · funext i
    exact Int.units_mul_self _

theorem signedPermMatrix_mem (p : Pair) :
    signedPermMatrix p.1.1 p.1.2 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨star_mul_signedPermMatrix _ _, ?_⟩
  rw [det_signedPermMatrix, p.2]
  simp

/-- The rotation of a pair: the signed permutation matrix with the entry `s_i` in row `i` and
column `σ(i)`. -/
def toGroup (p : Pair) : cubeGroup :=
  ⟨⟨signedPermMatrix p.1.1 p.1.2, signedPermMatrix_mem p⟩, p.1.1, p.1.2, rfl⟩

theorem toGroup_val (p : Pair) :
    ((toGroup p : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      signedPermMatrix p.1.1 p.1.2 := rfl

theorem signedPermMatrix_injective {σ τ : Equiv.Perm (Fin 3)} {s t : Fin 3 → ℤˣ}
    (h : signedPermMatrix σ s = signedPermMatrix τ t) : σ = τ ∧ s = t := by
  have hσ : ∀ i, σ i = τ i := by
    intro i
    have := congrFun (congrFun h i) (σ i)
    simp only [signedPermMatrix, Matrix.of_apply, ite_true] at this
    by_contra hne
    rw [ite_eq_right hne] at this
    exact Units.ne_zero (s i) (by exact_mod_cast this)
  have hστ : σ = τ := Equiv.ext hσ
  subst hστ
  refine ⟨rfl, funext fun i => ?_⟩
  have := congrFun (congrFun h i) (σ i)
  simp only [signedPermMatrix, Matrix.of_apply, ite_true] at this
  exact Units.ext (by exact_mod_cast this)

theorem toGroup_bijective : Function.Bijective toGroup := by
  refine ⟨fun p q h => ?_, fun g => ?_⟩
  · have h' := congrArg (fun g : cubeGroup =>
      ((g : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) h
    simp only [toGroup_val] at h'
    obtain ⟨h1, h2⟩ := signedPermMatrix_injective h'
    exact Subtype.ext (Prod.ext h1 h2)
  · obtain ⟨σ, s, hg⟩ := g.2
    have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp
      (g : Matrix.specialUnitaryGroup (Fin 3) ℂ).2).2
    rw [hg, det_signedPermMatrix] at hdet
    have hdet' : Equiv.Perm.sign σ * ∏ i, s i = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact_mod_cast hdet
    refine ⟨⟨(σ, s), hdet'⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact hg.symm

/-- The rotations of the cube correspond one to one to the pairs `(σ, s)`. -/
noncomputable def equiv : Pair ≃ cubeGroup := Equiv.ofBijective toGroup toGroup_bijective

theorem equiv_apply (p : Pair) : equiv p = toGroup p := rfl

/-- The cube group is finite. -/
@[instance_reducible]
noncomputable def fintype : Fintype cubeGroup := Fintype.ofEquiv Pair equiv

/-- The cube group has twenty-four rotations. -/
theorem card : Nat.card cubeGroup = 24 := by
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card]
  decide +kernel

/-- The trace of the rotation of a pair: the sum of the signs on the axes that `σ` fixes. -/
def trace (p : Pair) : ℤ := ∑ i, if i = p.1.1 i then ((p.1.2 i : ℤˣ) : ℤ) else 0

theorem colourChar_toGroup (p : Pair) : colourChar cubeGroup (toGroup p) = (trace p : ℂ) := by
  simp only [colourChar, toGroup_val, Matrix.trace, Matrix.diag, signedPermMatrix,
    Matrix.of_apply, trace]
  push_cast
  rfl

theorem isDiag_toGroup (p : Pair) :
    Matrix.IsDiag ((toGroup p : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) ↔ p.1.1 = 1 := by
  rw [toGroup_val]
  constructor
  · intro h
    refine Equiv.ext fun i => ?_
    by_contra hne
    have hne' : p.1.1 i ≠ i := fun h' => hne (by rw [h', Equiv.Perm.one_apply])
    have := h hne'.symm
    simp only [signedPermMatrix, Matrix.of_apply, ite_true] at this
    exact Units.ne_zero (p.1.2 i) (by exact_mod_cast this)
  · intro h i j hij
    simp only [signedPermMatrix, Matrix.of_apply, h, Equiv.Perm.coe_one, id_eq]
    rw [ite_eq_right (Ne.symm hij)]

/-- The class of the rotation of a pair, read off its trace: `3` for the identity, `-1` for a
half-turn (about a face axis exactly when `σ` is the identity), `0` for a third-turn, and `1` for
a quarter-turn. -/
def classOf (p : Pair) : CubeClass :=
  if trace p = 3 then .identity
  else if trace p = -1 then (if p.1.1 = 1 then .faceHalfTurn else .edgeHalfTurn)
  else if trace p = 0 then .vertexThirdTurn
  else .faceQuarterTurn

theorem cubeClassOf_toGroup (p : Pair) : cubeClassOf (toGroup p) = classOf p := by
  unfold cubeClassOf classOf
  rw [colourChar_toGroup, isDiag_toGroup]
  have h3 : ((trace p : ℂ) = 3) ↔ trace p = 3 := by exact_mod_cast Iff.rfl
  have hm1 : ((trace p : ℂ) = -1) ↔ trace p = -1 := by exact_mod_cast Iff.rfl
  have h0 : ((trace p : ℂ) = 0) ↔ trace p = 0 := by exact_mod_cast Iff.rfl
  simp only [h3, hm1, h0]
  split_ifs <;> rfl

/-- Counting rotations by a property of their pairs. -/
theorem card_subtype_eq (P : cubeGroup → Prop) (Q : Pair → Prop) [DecidablePred Q]
    (h : ∀ p, P (toGroup p) ↔ Q p) :
    Nat.card {g : cubeGroup // P g} = Fintype.card {p : Pair // Q p} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (equiv.subtypeEquiv fun p => (h p).symm).symm

/-- Every rotation is the rotation of a pair. -/
theorem exists_toGroup (g : cubeGroup) : ∃ p, toGroup p = g := toGroup_bijective.2 g

/-! ### Some rotations -/

/-- The half-turn about the face axis `i`: the sign `+1` on the axis `i` and `-1` on the other
two. -/
def faceHalfTurnPair (i : Fin 3) : Pair :=
  ⟨(1, fun j => if j = i then 1 else -1), by fin_cases i <;> decide⟩

/-- The third-turn `e₀ ↦ e₂ ↦ e₁ ↦ e₀` about a body diagonal: the rotation of the cyclic
permutation of the axes. -/
def thirdTurnPair : Pair := ⟨(finRotate 3, fun _ => 1), by decide⟩

theorem faceHalfTurn_mulVec (i : Fin 3) (v : Fin 3 → ℂ) :
    cubeTriplet (toGroup (faceHalfTurnPair i)) *ᵥ v = fun j => if j = i then v j else -v j := by
  funext j
  rw [show cubeTriplet (toGroup (faceHalfTurnPair i)) =
    signedPermMatrix 1 (fun j => if j = i then 1 else -1) from rfl]
  simp only [Matrix.mulVec, dotProduct, signedPermMatrix, Matrix.of_apply, Equiv.Perm.coe_one,
    id_eq]
  split_ifs with h <;> simp [h]

theorem thirdTurn_mulVec (v : Fin 3 → ℂ) :
    cubeTriplet (toGroup thirdTurnPair) *ᵥ v = fun j => v (finRotate 3 j) := by
  funext j
  rw [show cubeTriplet (toGroup thirdTurnPair) = signedPermMatrix (finRotate 3) (fun _ => 1)
    from rfl]
  simp [Matrix.mulVec, dotProduct, signedPermMatrix]

/-- The triplet of the cube group is irreducible. -/
theorem isIrreducible_tripletRep : (Edge.tripletRep cubeTriplet).IsIrreducible := by
  have hact : ∀ (g : cubeGroup) (v : Fin 3 → ℂ),
      Edge.tripletRep cubeTriplet g v = cubeTriplet g *ᵥ v := fun g v => rfl
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · by_cases hW : ∀ v ∈ W.toSubmodule, v = 0
    · left
      apply Subrepresentation.toSubmodule_injective
      exact (Submodule.eq_bot_iff _).mpr hW
    · right
      push Not at hW
      obtain ⟨v, hv, hv0⟩ := hW
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext h)
      have hsingle : (Pi.single i 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        have h1 := W.apply_mem_toSubmodule (toGroup (faceHalfTurnPair i)) hv
        rw [hact, faceHalfTurn_mulVec] at h1
        have h2 := W.toSubmodule.add_mem hv h1
        have h3 := W.toSubmodule.smul_mem ((2 * v i)⁻¹) h2
        convert h3 using 1
        funext j
        simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs with hj
        · subst hj
          field_simp
          ring
        · ring
      have hrot : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule →
          (Pi.single ((finRotate 3).symm j) 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j hj
        have := W.apply_mem_toSubmodule (toGroup thirdTurnPair) hj
        rw [hact, thirdTurn_mulVec] at this
        convert this using 1
        funext k
        simp only [Pi.single_apply, Equiv.eq_symm_apply]
      have hall : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j
        have h1 := hrot _ hsingle
        have h2 := hrot _ h1
        fin_cases i <;> fin_cases j <;> first | exact hsingle | exact h1 | exact h2
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have hw : w = ∑ j, w j • (Pi.single j 1 : Fin 3 → ℂ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hw]
      exact W.toSubmodule.sum_mem fun j _ => W.toSubmodule.smul_mem _ (hall j)

end CubeGroup

end Artform
