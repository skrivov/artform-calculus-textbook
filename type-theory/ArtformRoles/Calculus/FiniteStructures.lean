import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Finite structural semantics

§12.8 of the paper (finite structural semantics). A finite relational
vocabulary lists the arities of its relations; a finite structure on the
elements `Fin n` gives each relation a Boolean value on every tuple.

* `FinStr.relabel`, `FinStr.Iso`: relabelling along a permutation, and
  isomorphism of finite structures on `Fin n`.
* `FinStr.encode`: a structure read as its table, a list of Booleans, in a
  fixed order of the tuples; reading is injective (`encode_injective`).
* `FinStr.canon`: canonical labelling, the least table over all relabellings.
  Two structures are isomorphic exactly when their canonical tables are equal
  (`iso_iff_canon_eq`), so isomorphism is decidable (`decIso`).

The interpretation `⟦-⟧_L` of erased normal forms as finite structures is
supplied by a signature and is not part of the calculus; with it, different
construction histories may denote isomorphic structures without being
judgmentally equal (`Book.Interp.second_attestation`).
-/

namespace Artform.Roles.Calculus

/-- A finite relational vocabulary: the arity of each relation. -/
abbrev Vocab := List ℕ

/-- A finite structure for the vocabulary `L` on the elements `Fin n`. -/
@[ext]
structure FinStr (L : Vocab) (n : ℕ) where
  /-- The value of each relation on each tuple. -/
  rel : (i : Fin L.length) → (Fin (L.get i) → Fin n) → Bool

namespace FinStr

variable {L : Vocab} {n : ℕ}

instance : DecidableEq (FinStr L n) := fun M N =>
  decidable_of_iff (M.rel = N.rel) ⟨fun h => FinStr.ext h, fun h => h ▸ rfl⟩

/-- Relabelling a structure along a permutation of its elements. -/
def relabel (σ : Equiv.Perm (Fin n)) (M : FinStr L n) : FinStr L n :=
  ⟨fun i v => M.rel i (σ.symm ∘ v)⟩

theorem relabel_one (M : FinStr L n) : M.relabel 1 = M := rfl

theorem relabel_mul (σ τ : Equiv.Perm (Fin n)) (M : FinStr L n) :
    (M.relabel σ).relabel τ = M.relabel (τ * σ) := rfl

/-- Isomorphism: some relabelling of `M` is `N`. -/
def Iso (M N : FinStr L n) : Prop := ∃ σ : Equiv.Perm (Fin n), M.relabel σ = N

/-- The tuples of each relation, indexed by one finite range. -/
def index (L : Vocab) (n : ℕ) :
    (Σ i : Fin L.length, Fin (L.get i) → Fin n) ≃ Fin (∑ i : Fin L.length, n ^ L.get i) :=
  (Equiv.sigmaCongrRight fun _ => finFunctionFinEquiv).trans finSigmaFinEquiv

/-- The table of a structure: its relations read in the order of `index`. -/
def encode (M : FinStr L n) : List Bool :=
  List.ofFn fun p => M.rel ((index L n).symm p).1 ((index L n).symm p).2

theorem encode_injective : Function.Injective (encode : FinStr L n → List Bool) := by
  intro M N h
  have hf := List.ofFn_injective h
  have key : ∀ p : Σ i : Fin L.length, Fin (L.get i) → Fin n,
      M.rel p.1 p.2 = N.rel p.1 p.2 := by
    intro p
    have := congrFun hf (index L n p)
    rwa [Equiv.symm_apply_apply] at this
  ext i v
  exact key ⟨i, v⟩

/-- Canonical labelling: the least table over all relabellings. -/
def canon (M : FinStr L n) : List Bool :=
  (Finset.univ.image fun σ : Equiv.Perm (Fin n) => (M.relabel σ).encode).min'
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 1)⟩

theorem canon_mem (M : FinStr L n) :
    ∃ σ : Equiv.Perm (Fin n), (M.relabel σ).encode = M.canon := by
  have := Finset.min'_mem (Finset.univ.image fun σ : Equiv.Perm (Fin n) => (M.relabel σ).encode)
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 1)⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at this
  exact this

/-- Relabelling does not change the tables a structure can be read as. -/
theorem image_relabel (σ : Equiv.Perm (Fin n)) (M : FinStr L n) :
    (Finset.univ.image fun τ : Equiv.Perm (Fin n) => ((M.relabel σ).relabel τ).encode) =
      Finset.univ.image fun τ : Equiv.Perm (Fin n) => (M.relabel τ).encode := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, relabel_mul]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * σ⁻¹, by rw [mul_assoc, inv_mul_cancel, mul_one]⟩

/-- Two finite structures on `Fin n` are isomorphic exactly when their canonical
tables are equal. -/
theorem iso_iff_canon_eq (M N : FinStr L n) : M.Iso N ↔ M.canon = N.canon := by
  constructor
  · rintro ⟨σ, rfl⟩
    unfold canon
    congr 1
    exact (image_relabel σ M).symm
  · intro h
    obtain ⟨σ, hσ⟩ := canon_mem M
    obtain ⟨τ, hτ⟩ := canon_mem N
    have e : M.relabel σ = N.relabel τ := encode_injective (by rw [hσ, hτ, h])
    refine ⟨τ⁻¹ * σ, ?_⟩
    rw [← relabel_mul, e, relabel_mul, inv_mul_cancel, relabel_one]

/-- Isomorphism of finite structures is decidable. -/
def decIso (M N : FinStr L n) : Decidable (M.Iso N) :=
  decidable_of_iff _ (iso_iff_canon_eq M N).symm

end FinStr

/-! ## Non-vacuity -/

theorem get_two : ∀ i : Fin [2].length, [2].get i = 2
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, h⟩ => absurd h (by simp)

/-- One binary relation on two elements, holding exactly of `(a, b)`. -/
def edge (a b : Fin 2) : FinStr [2] 2 :=
  ⟨fun i v => decide (v (Fin.cast (get_two i).symm 0) = a ∧
    v (Fin.cast (get_two i).symm 1) = b)⟩

/-- The edge `0 → 1` and the edge `1 → 0` are isomorphic, so they have one
canonical table. -/
example : (edge 0 1).canon = (edge 1 0).canon :=
  (FinStr.iso_iff_canon_eq _ _).mp ⟨Equiv.swap 0 1, by decide⟩

end Artform.Roles.Calculus
