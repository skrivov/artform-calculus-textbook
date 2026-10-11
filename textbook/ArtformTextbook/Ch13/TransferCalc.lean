import ArtformTextbook.Ch12.Models
import ArtformTextbook.Ch13.Defs.Transfer

/-!
# The words of the transfer, computed on lists

`6 L` of Theorem 13.8 applied to a list of masks (`TransferCalc.transfer6`): for each pair of
orderings `(c, c')` of the colours, three hops in turn, combined with the signs. Read in `ℂ` it is
`6 L` applied to the table of the list (`TransferCalc.transfer6_toFock`), so that the kernel can
check the action of `L` on any state written as a list (`TransferCalc.transfer_check`).
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge

namespace TransferCalc

/-- The orderings of the three colours, with their signs. -/
def perms : List ((Fin 3 × Fin 3 × Fin 3) × ℤ) :=
  [((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((0, 2, 1), -1), ((2, 1, 0), -1),
    ((1, 0, 2), -1)]

/-- A sum weighted by the Levi-Civita symbol is a sum over the orderings with their signs. -/
theorem sum_leviCivita_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ c₁, ∑ c₂, ∑ c₃, leviCivita c₁ c₂ c₃ • f c₁ c₂ c₃ =
      (perms.map fun p => ((p.2 : ℤ) : ℂ) • f p.1.1 p.1.2.1 p.1.2.2).sum := by
  simp only [Fin.sum_univ_three, Moments.leviCivita_eq, Moments.lcTab, perms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  simp
  abel

/-- The sixfold sum of Theorem 13.8 over the pairs of orderings. -/
theorem sum6 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (g : Fin 3 × Fin 3 × Fin 3 → Fin 3 × Fin 3 × Fin 3 → M) :
    ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
        (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') • g (c₁, c₂, c₃) (c₁', c₂', c₃') =
      (perms.map fun p => ((p.2 : ℤ) : ℂ) •
        (perms.map fun p' => ((p'.2 : ℤ) : ℂ) • g p.1 p'.1).sum).sum := by
  simp_rw [mul_smul, ← Finset.smul_sum]
  rw [sum_leviCivita_smul fun c₁ c₂ c₃ =>
    ∑ c₁', ∑ c₂', ∑ c₃', leviCivita c₁' c₂' c₃' • g (c₁, c₂, c₃) (c₁', c₂', c₃')]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [sum_leviCivita_smul]

theorem list_sum_mulVec {ι N : Type*} [Fintype N] (l : List ι) (f : ι → Matrix N N ℂ)
    (x : N → ℂ) : (l.map f).sum *ᵥ x = (l.map fun i => f i *ᵥ x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Matrix.add_mulVec, ih]

theorem toFock_list_sum (l : List (ℤ × Vec)) :
    Vec.toFock code (Vec.combo l) = (l.map fun t => (t.1 : ℂ) • Vec.toFock code t.2).sum :=
  Vec.toFock_combo l

/-! ### The words on lists -/

/-- `A_{cc'} + A_{cc'}†` as words. -/
def hopBOp (c c' : Fin 3) : Op EM := hopAOp c c' ++ hopAdOp c c'

theorem hopBOp_toMat (c c' : Fin 3) :
    Op.toMat bookOrd (hopBOp c c') = hopA bookOrd c c' + (hopA bookOrd c c')ᴴ := by
  rw [hopBOp, Op.toMat_append, hopAOp_toMat, hopAdOp_toMat]

/-- Three hops in turn for the pair of orderings `(c, c')`,
`X_{c₃c'₃} (X_{c₂c'₂} (X_{c₁c'₁} v))`. -/
def act3 (X : Fin 3 → Fin 3 → Op EM) (c c' : Fin 3 × Fin 3 × Fin 3) (v : Vec) : Vec :=
  OpC.act parB ((X c.2.2 c'.2.2).compile code) (OpC.act parB ((X c.2.1 c'.2.1).compile code)
    (OpC.act parB ((X c.1 c'.1).compile code) v))

/-- The same three hops in the reverse order, `X_{c₁c'₁} (X_{c₂c'₂} (X_{c₃c'₃} v))`. -/
def act3r (X : Fin 3 → Fin 3 → Op EM) (c c' : Fin 3 × Fin 3 × Fin 3) (v : Vec) : Vec :=
  OpC.act parB ((X c.1 c'.1).compile code) (OpC.act parB ((X c.2.1 c'.2.1).compile code)
    (OpC.act parB ((X c.2.2 c'.2.2).compile code) v))

/-- `6 L` applied to a list: for a real triplet the words in `A + A†`, for a complex one the words
in `A` and their adjoints. -/
def transfer6 (real : Bool) (v : Vec) : Vec :=
  Vec.combo (perms.map fun p => (p.2, Vec.combo (perms.map fun p' => (p'.2,
    if real then act3 hopBOp p.1 p'.1 v
    else act3 hopAOp p.1 p'.1 v ++ act3r hopAdOp p.1 p'.1 v))))

theorem act3_toFock (X : Fin 3 → Fin 3 → Op EM) (c c' : Fin 3 × Fin 3 × Fin 3) (v : Vec) :
    Vec.toFock code (act3 X c c' v) =
      (Op.toMat bookOrd (X c.2.2 c'.2.2) * Op.toMat bookOrd (X c.2.1 c'.2.1) *
        Op.toMat bookOrd (X c.1 c'.1)) *ᵥ Vec.toFock code v := by
  rw [act3, ← Op.toMat_mulVec_compile numbering parB parB_spec,
    ← Op.toMat_mulVec_compile numbering parB parB_spec,
    ← Op.toMat_mulVec_compile numbering parB parB_spec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem act3r_toFock (X : Fin 3 → Fin 3 → Op EM) (c c' : Fin 3 × Fin 3 × Fin 3) (v : Vec) :
    Vec.toFock code (act3r X c c' v) =
      (Op.toMat bookOrd (X c.1 c'.1) * Op.toMat bookOrd (X c.2.1 c'.2.1) *
        Op.toMat bookOrd (X c.2.2 c'.2.2)) *ᵥ Vec.toFock code v := by
  rw [act3r, ← Op.toMat_mulVec_compile numbering parB parB_spec,
    ← Op.toMat_mulVec_compile numbering parB parB_spec,
    ← Op.toMat_mulVec_compile numbering parB parB_spec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem star_leviCivita (i k m : Fin 3) : star (leviCivita i k m) = leviCivita i k m :=
  Moments.leviCivita_real i k m

/-- `6 L` of Theorem 13.8 on the table of a list. -/
theorem transfer6_toFock (real : Bool) (v : Vec) :
    Vec.toFock code (transfer6 real v) =
      ((6 : ℂ) • transferWords bookOrd real) *ᵥ Vec.toFock code v := by
  rw [transfer6, toFock_list_sum, List.map_map]
  cases real with
  | true =>
    have e : (6 : ℂ) • transferWords bookOrd true = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
        (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
          ((hopA bookOrd c₃ c₃' + (hopA bookOrd c₃ c₃')ᴴ) *
            (hopA bookOrd c₂ c₂' + (hopA bookOrd c₂ c₂')ᴴ) *
            (hopA bookOrd c₁ c₁' + (hopA bookOrd c₁ c₁')ᴴ)) := by
      rw [transferWords, transferOf, ite_eq_left rfl, smul_smul]
      norm_num
    rw [e, sum6 (fun c c' => (hopA bookOrd c.2.2 c'.2.2 + (hopA bookOrd c.2.2 c'.2.2)ᴴ) *
        (hopA bookOrd c.2.1 c'.2.1 + (hopA bookOrd c.2.1 c'.2.1)ᴴ) *
        (hopA bookOrd c.1 c'.1 + (hopA bookOrd c.1 c'.1)ᴴ)), list_sum_mulVec]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply, ite_true, toFock_list_sum, List.map_map]
    rw [Matrix.smul_mulVec, list_sum_mulVec]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun p' _ => ?_)
    simp only [Function.comp_apply, act3_toFock, hopBOp_toMat, Matrix.smul_mulVec]
  | false =>
    set S : Matrix (Finset EM) (Finset EM) ℂ := ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
      (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
        (hopA bookOrd c₃ c₃' * hopA bookOrd c₂ c₂' * hopA bookOrd c₁ c₁') with hS
    set T : Matrix (Finset EM) (Finset EM) ℂ := ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
      (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
        ((hopA bookOrd c₁ c₁')ᴴ * (hopA bookOrd c₂ c₂')ᴴ * (hopA bookOrd c₃ c₃')ᴴ) with hT
    have hST : Sᴴ = T := by
      simp only [hS, hT, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_mul',
        star_leviCivita, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have e : (6 : ℂ) • transferWords bookOrd false = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₁', ∑ c₂', ∑ c₃',
        (leviCivita c₁ c₂ c₃ * leviCivita c₁' c₂' c₃') •
          (hopA bookOrd c₃ c₃' * hopA bookOrd c₂ c₂' * hopA bookOrd c₁ c₁' +
            (hopA bookOrd c₁ c₁')ᴴ * (hopA bookOrd c₂ c₂')ᴴ * (hopA bookOrd c₃ c₃')ᴴ) := by
      have e1 : transferWords bookOrd false = (1 / 6 : ℂ) • S + ((1 / 6 : ℂ) • S)ᴴ := by
        rw [transferWords, transferOf, ite_eq_right (by decide)]
      rw [e1, Matrix.conjTranspose_smul, hST, smul_add, smul_smul, smul_smul,
        show star (1 / 6 : ℂ) = 1 / 6 by simp]
      norm_num
      simp only [hS, hT, ← Finset.sum_add_distrib, ← smul_add]
    rw [e, sum6 (fun c c' => hopA bookOrd c.2.2 c'.2.2 * hopA bookOrd c.2.1 c'.2.1 *
        hopA bookOrd c.1 c'.1 + (hopA bookOrd c.1 c'.1)ᴴ * (hopA bookOrd c.2.1 c'.2.1)ᴴ *
          (hopA bookOrd c.2.2 c'.2.2)ᴴ), list_sum_mulVec]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply, Bool.false_eq_true, ite_false, toFock_list_sum,
      List.map_map]
    rw [Matrix.smul_mulVec, list_sum_mulVec]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun p' _ => ?_)
    simp only [Function.comp_apply, Vec.toFock_append, act3_toFock, act3r_toFock, hopAOp_toMat,
      hopAdOp_toMat, Matrix.smul_mulVec, Matrix.add_mulVec]

/-- The kernel checks `6 L v = w` on lists. -/
theorem transfer_check (real : Bool) (v w : Vec)
    (h : (Vec.trie 12 (transfer6 real v) == Vec.trie 12 w) = true) :
    (6 : ℂ) • (transferWords bookOrd real *ᵥ Vec.toFock code v) = Vec.toFock code w := by
  rw [← Matrix.smul_mulVec, ← transfer6_toFock]
  exact toFock_eq_of_check h

end TransferCalc

end Artform
