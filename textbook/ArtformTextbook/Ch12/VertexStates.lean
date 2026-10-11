import ArtformTextbook.Ch12.Defs.Models
import ArtformTextbook.Ch12.FockCalc
import ArtformTextbook.Ch11.Moments

/-!
# The eight states of one vertex

* **As lists.** In the book's order of the six modes (`Vertex.bookOrd`, the mode `(c, s)` numbered
  `2 c + s`), each of the eight states of Figure `fig:mm-two-slot-invariants` is a list of masks
  with integer coefficients (`Vertex.eightVec`), computed by the kernel from the creations that
  define it (`Vertex.eight_eq`).
* **Colour rotations.** In any order of the modes, the colour rotation `Γ(g)` transforms the
  creations and annihilations of the states (Proposition 11.12), which gives:
  `Γ(g)|0⟩ = |0⟩`, `Γ(g)|full⟩ = det(g)² |full⟩`, `Γ(g) ε_{s₁s₂s₃} = det(g) ε_{s₁s₂s₃}` for the
  three-quark states built from `ε`, `Γ(g) D = Σ (g gᵀ)_{c'c''} a†_{c'↑} a†_{c''↓} |0⟩` for the pair
  and `Γ(g) H = det(g)² Σ conj((g gᵀ)_{c'c''}) a_{c'↑} a_{c''↓} |full⟩` for the paired holes, `g`
  unitary for the holes. So a rotation (`g gᵀ = 1`, `det g = 1`) fixes all eight, and every matrix
  of `SU(3)` fixes the empty vertex, the quartet and the full vertex.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open FockCalc Spin

namespace Vertex

/-! ### The book's order as a numbering -/

theorem code_lt (m : Fin 3 × Fin 2) : code m < 6 := by
  obtain ⟨c, s⟩ := m
  have := c.2
  have := s.2
  simp only [code]
  omega

theorem numbering : Numbering code 6 bookOrd where
  inj := code_injective
  lt := code_lt
  surj := by
    intro i hi
    refine ⟨(⟨i / 2, by omega⟩, ⟨i % 2, by omega⟩), ?_⟩
    simp only [code]
    omega
  ord_lt _ _ := Iff.rfl

/-- The parity of the set bits below `i`, read from `below`. -/
def par (k i : ℕ) : Bool := below k i % 2 == 1

theorem par_spec (k i : ℕ) : par k i = (below k i % 2 == 1) := rfl

/-! ### The eight states as lists -/

/-- The empty vertex as a list. -/
def emptyVec : Vec := [(0, 1)]

/-- The pair as a list: the masks of `{(c, ↑), (c, ↓)}`. -/
def pairVec : Vec := [(3, 1), (12, 1), (48, 1)]

/-- The four members of the quartet as lists. -/
def quartetVec : Fin 4 → Vec :=
  ![[(21, 1)], [(37, 1), (25, 1), (22, 1)], [(41, 1), (38, 1), (26, 1)], [(42, 1)]]

/-- The paired holes as a list. -/
def holesVec : Vec := [(60, -1), (51, -1), (15, -1)]

/-- The full vertex as a list. -/
def fullVec : Vec := [(63, 1)]

/-- The eight states of Figure `fig:mm-two-slot-invariants` as lists of masks with coefficients,
in the book's order of the modes: the mode `(c, s)` is the bit `2 c + s`. -/
def eightVec : Fin 8 → Vec :=
  ![emptyVec, pairVec, quartetVec 0, quartetVec 1, quartetVec 2, quartetVec 3, holesVec, fullVec]

theorem decode_zero : decode code 0 = (∅ : Finset (Fin 3 × Fin 2)) := by
  ext m
  simp [mem_decode]

theorem decode_63 : decode code 63 = (Finset.univ : Finset (Fin 3 × Fin 2)) := by
  ext m
  simp only [mem_decode, Finset.mem_univ, iff_true]
  obtain ⟨c, s⟩ := m
  fin_cases c <;> fin_cases s <;> decide

theorem ket_empty : Fock.ket ∅ = Vec.toFock code [(0, 1)] := by
  simp [Vec.toFock, decode_zero]

theorem ket_univ : Fock.ket Finset.univ = Vec.toFock code [(63, 1)] := by
  simp [Vec.toFock, decode_63]

theorem sum_fin_three_toFock (f : Fin 3 → Vec) :
    ∑ a : Fin 3, Vec.toFock code (f a) = Vec.toFock code (f 0 ++ f 1 ++ f 2) := by
  rw [Fin.sum_univ_three, Vec.toFock_append, Vec.toFock_append]

theorem two_mulVec (l₁ l₂ : Letter (Fin 3 × Fin 2)) (v : Vec) :
    (l₁.toMat bookOrd * l₂.toMat bookOrd) *ᵥ Vec.toFock code v =
      Vec.toFock code (Vec.wordAct code [l₁, l₂] v) := by
  rw [← wordMat_mulVec numbering]
  simp [wordMat]

theorem three_mulVec (l₁ l₂ l₃ : Letter (Fin 3 × Fin 2)) (v : Vec) :
    (l₁.toMat bookOrd * l₂.toMat bookOrd * l₃.toMat bookOrd) *ᵥ Vec.toFock code v =
      Vec.toFock code (Vec.wordAct code [l₁, l₂, l₃] v) := by
  rw [← wordMat_mulVec numbering]
  simp [wordMat, mul_assoc]

theorem cr_toMat (m : Fin 3 × Fin 2) :
    Fock.creation bookOrd m = (⟨true, m⟩ : Letter (Fin 3 × Fin 2)).toMat bookOrd := rfl

theorem an_toMat (m : Fin 3 × Fin 2) :
    Fock.annihilation bookOrd m = (⟨false, m⟩ : Letter (Fin 3 × Fin 2)).toMat bookOrd := rfl

theorem empty_eq : empty = Vec.toFock code emptyVec := ket_empty

theorem full_eq : full = Vec.toFock code fullVec := ket_univ

theorem pair_eq : pair bookOrd = Vec.toFock code pairVec := by
  simp only [pair, cr_toMat, ket_empty, two_mulVec, sum_fin_three_toFock]
  exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)

theorem holes_eq : holes bookOrd = Vec.toFock code holesVec := by
  simp only [holes, full, an_toMat, ket_univ, two_mulVec, sum_fin_three_toFock]
  exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)

theorem epsState_upupdown :
    epsState bookOrd up up down = Vec.toFock code (Vec.smul 2 (quartetVec 1)) := by
  simp only [epsState, Moments.leviCivita_eq, cr_toMat, ket_empty, three_mulVec,
    ← Vec.toFock_smul, sum_fin_three_toFock]
  exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)

theorem epsState_updowndown :
    epsState bookOrd up down down = Vec.toFock code (Vec.smul 2 (quartetVec 2)) := by
  simp only [epsState, Moments.leviCivita_eq, cr_toMat, ket_empty, three_mulVec,
    ← Vec.toFock_smul, sum_fin_three_toFock]
  exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)

theorem quartet_eq (m : Fin 4) : quartet bookOrd m = Vec.toFock code (quartetVec m) := by
  fin_cases m
  · simp only [quartet, Fin.zero_eta, Matrix.cons_val_zero, cr_toMat, ket_empty, three_mulVec]
    exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)
  · simp only [quartet, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      epsState_upupdown, Vec.toFock_smul, smul_smul]
    norm_num
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val, epsState_updowndown, Vec.toFock_smul,
      smul_smul]
    norm_num
  · simp only [quartet, Fin.reduceFinMk, Matrix.cons_val, cr_toMat, ket_empty, three_mulVec]
    exact Vec.toFock_eq_of_trie_eq numbering (by decide +kernel)

theorem eight_eq (i : Fin 8) : eight bookOrd i = Vec.toFock code (eightVec i) := by
  fin_cases i <;>
    simp [eight, eightVec, empty_eq, pair_eq, quartet_eq, holes_eq, full_eq]

end Vertex

end Artform
