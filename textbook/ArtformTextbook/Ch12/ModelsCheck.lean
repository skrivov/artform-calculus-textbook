import ArtformTextbook.Ch12.ModelsData
import ArtformTextbook.Ch12.ModelsOps

/-!
# The kernel's checks of the certificate of the models

Each operator of `Ch12/ModelsOps.lean`, applied by the kernel to each product of the basis
(`Edge.basisVec`, `Edge.basisVec36`, `ModelsCheck.blockVec`), gives the combination of products
that the certificate `Ch12/ModelsData.lean` lists in its column (`ModelsCheck.colCheck`); read
back in `ℂ`, the operator carries every combination of products to the combination given by the
matrix of the columns (`ModelsCheck.omega1_lc` and its companions). The eigenvector certificates
are checked by `SpecCert.eigOK` and `SpecCert.invOK`.
-/

namespace Artform.ModelsCheck

open scoped Matrix

open FockCalc ModelsData Edge SpecCert

/-- The parity of the set bits below a position, read from `below`. -/
def parB (k i : ℕ) : Bool := below k i % 2 == 1

/-- The image of the product `j` under a compiled operator is the combination of the column `j`. -/
def colCheck (O : OpC) (cols : List Vec) (bv : ℕ → Vec) (j : ℕ) : Bool :=
  Vec.trie 12 (OpC.act parB O (bv j)) ==
    Vec.trie 12 (Vec.combo ((cols.getD j []).map fun p => (p.2, bv p.1)))

/-- The image of the product `j` under a diagonal operator read off the masks by `f`. -/
def diagCheck (f : ℕ → ℤ) (cols : List Vec) (bv : ℕ → Vec) (j : ℕ) : Bool :=
  Vec.trie 12 ((bv j).map fun p => (p.1, f p.1 * p.2)) ==
    Vec.trie 12 (Vec.combo ((cols.getD j []).map fun p => (p.2, bv p.1)))

/-- `3 Ω` with the pair hop, compiled. -/
def tally1C : OpC := (tally3Op 1).compile code

/-- `3 Ω` without the pair hop, compiled. -/
def tally0C : OpC := (tally3Op 0).compile code

/-- The product of two quartets numbered `4 a + b`, as a list. -/
def blockVec (l : ℕ) : Vec := basisVec (8 * (l / 4 % 4 + 2) + (l % 4 + 2))

/-! ### Checks over ranges -/

theorem all_range_of_chunks (P : ℕ → Bool) (s n : ℕ)
    (h : ∀ a < n, (List.range' (s * a) s).all P = true) :
    ∀ j < s * n, P j = true := by
  intro j hj
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0
      omega
    · exact h0
  have := h (j / s) (Nat.div_lt_of_lt_mul hj)
  rw [List.all_eq_true] at this
  refine this j (List.mem_range'.mpr ⟨j % s, Nat.mod_lt _ hs, ?_⟩)
  rw [one_mul]
  exact (Nat.div_add_mod j s).symm

/-! ### The columns of the tally -/

theorem omega1_cols_0 :
    (List.range' 0 16).all (colCheck tally1C omega1Cols basisVec) = true := by
  decide +kernel

theorem omega1_cols_1 :
    (List.range' 16 16).all (colCheck tally1C omega1Cols basisVec) = true := by
  decide +kernel

theorem omega1_cols_2 :
    (List.range' 32 16).all (colCheck tally1C omega1Cols basisVec) = true := by
  decide +kernel

theorem omega1_cols_3 :
    (List.range' 48 16).all (colCheck tally1C omega1Cols basisVec) = true := by
  decide +kernel

theorem omega1_cols : ∀ j < 64, (colCheck tally1C omega1Cols basisVec) j = true :=
  all_range_of_chunks _ 16 4 fun a ha => by
    interval_cases a
    · exact omega1_cols_0
    · exact omega1_cols_1
    · exact omega1_cols_2
    · exact omega1_cols_3

theorem omega0_cols_0 :
    (List.range' 0 16).all (colCheck tally0C omega0Cols basisVec) = true := by
  decide +kernel

theorem omega0_cols_1 :
    (List.range' 16 16).all (colCheck tally0C omega0Cols basisVec) = true := by
  decide +kernel

theorem omega0_cols_2 :
    (List.range' 32 16).all (colCheck tally0C omega0Cols basisVec) = true := by
  decide +kernel

theorem omega0_cols_3 :
    (List.range' 48 16).all (colCheck tally0C omega0Cols basisVec) = true := by
  decide +kernel

theorem omega0_cols : ∀ j < 64, (colCheck tally0C omega0Cols basisVec) j = true :=
  all_range_of_chunks _ 16 4 fun a ha => by
    interval_cases a
    · exact omega0_cols_0
    · exact omega0_cols_1
    · exact omega0_cols_2
    · exact omega0_cols_3

theorem omega36_cols_0 :
    (List.range' 0 12).all (colCheck tally0C omega36Cols basisVec36) = true := by
  decide +kernel

theorem omega36_cols_1 :
    (List.range' 12 12).all (colCheck tally0C omega36Cols basisVec36) = true := by
  decide +kernel

theorem omega36_cols_2 :
    (List.range' 24 12).all (colCheck tally0C omega36Cols basisVec36) = true := by
  decide +kernel

theorem omega36_cols : ∀ j < 36, (colCheck tally0C omega36Cols basisVec36) j = true :=
  all_range_of_chunks _ 12 3 fun a ha => by
    interval_cases a
    · exact omega36_cols_0
    · exact omega36_cols_1
    · exact omega36_cols_2

/-! ### The eigenvector certificates -/

theorem omega1_eig : eigOK 6 64 omega1Cols omega1Eig = true := by decide +kernel

theorem omega1_inv : invOK 6 64 omega1D omega1Eig omega1Dg = true := by decide +kernel

theorem omega0_eig : eigOK 6 64 omega0Cols omega0Eig = true := by decide +kernel

theorem omega0_inv : invOK 6 64 omega0D omega0Eig omega0Dg = true := by decide +kernel

theorem omega36_eig : eigOK 6 36 omega36Cols omega36Eig = true := by decide +kernel

theorem omega36_inv : invOK 6 36 omega36D omega36Eig omega36Dg = true := by decide +kernel

end Artform.ModelsCheck
