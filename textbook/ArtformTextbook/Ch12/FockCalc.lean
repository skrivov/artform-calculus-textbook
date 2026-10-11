import ArtformTextbook.Ch11.Occupation

/-!
# Computing with creations and annihilations on bit masks

The coefficient tables of `Ch11/Defs/Occupation.lean` live over the occupation tables
`Finset M`; the kernel cannot compute with complex numbers, but it computes quickly with natural
numbers. Here a mode `m` gets a number `code m < D`, an occupation table a mask (bit `code m`
set when `m` is occupied), and the order of the modes is the order of their numbers. Then:

* a letter, a creation or an annihilation of one mode, acts on a mask by testing and flipping one
  bit, with the sign `(-1)` to the number of occupied modes below it (`Letter.act`): this is the
  sign rule of Definition 11.10 (`Letter.toMat_mulVec_ket`);
* a word, a product of letters, acts letter by letter, the rightmost first (`wordAct`,
  `wordMat_mulVec_ket`); an operator is an integer combination of words (`Op`), and a vector a list
  of masks with integer coefficients (`Vec`, read in `ℂ` by `Vec.toFock`);
* two vectors are equal when their coefficients, summed mask by mask, agree; the kernel checks
  that by building a binary trie of each, keyed by the bits of the masks (`Trie`, `Vec.trie`),
  and comparing the tries (`Vec.toFock_eq_of_trie_eq`).

So an identity `X v = w` between an operator built from creations and annihilations and explicit
vectors is proved by `decide +kernel` on the masks, and read back in `ℂ`.
-/

namespace Artform.FockCalc

open scoped Matrix

/-! ### Masks -/

/-- The number of set bits of `k` below the position `i`. -/
def below (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => below k i + (k.testBit i).toNat

theorem below_eq (k i : ℕ) :
    below k i = ((Finset.range i).filter fun j => k.testBit j = true).card := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [below, ih, Finset.range_add_one, Finset.filter_insert]
    cases h : k.testBit i
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]
      simp

theorem below_mod (k i : ℕ) : below (k % 2 ^ i) i = below k i := by
  rw [below_eq, below_eq]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_mod_two_pow]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa [h1] using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simp [h1, h2]⟩

theorem below_of_lt_two_pow {r i : ℕ} (hr : r < 2 ^ i) : ∀ j, i ≤ j → below r j = below r i
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · rw [below, below_of_lt_two_pow hr j (by omega),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      rfl
    · rw [show i = j + 1 by omega]

/-- A letter of a word: the creation (`cr = true`) or the annihilation (`cr = false`) of a mode. -/
structure Letter (M : Type*) where
  /-- Whether the letter is a creation. -/
  cr : Bool
  /-- The mode it creates or annihilates. -/
  m : M

/-- A letter acting on a mask: `none` when the result is zero, else whether the sign is
negative, and the new mask. The sign is `(-1)` to the number of occupied modes below. -/
def Letter.act {M : Type*} (code : M → ℕ) (l : Letter M) (k : ℕ) : Option (Bool × ℕ) :=
  if k.testBit (code l.m) = l.cr then none
  else some (below k (code l.m) % 2 == 1, k ^^^ 2 ^ code l.m)

/-- A word, a product of letters, acting on a mask; the rightmost letter acts first. -/
def wordAct {M : Type*} (code : M → ℕ) : List (Letter M) → ℕ → Option (Bool × ℕ)
  | [], k => some (false, k)
  | l :: w, k =>
    match wordAct code w k with
    | none => none
    | some (s, k') =>
      match l.act code k' with
      | none => none
      | some (s', k'') => some (xor s s', k'')

/-- A vector: a list of masks with integer coefficients. -/
abbrev Vec : Type := List (ℕ × ℤ)

/-- An operator: a list of words with integer coefficients. -/
abbrev Op (M : Type*) : Type _ := List (ℤ × List (Letter M))

/-- A word acting on a vector. -/
def Vec.wordAct {M : Type*} (code : M → ℕ) (w : List (Letter M)) (v : Vec) : Vec :=
  v.filterMap fun p => (FockCalc.wordAct code w p.1).map fun r => (r.2, if r.1 then -p.2 else p.2)

/-- An operator acting on a vector. -/
def Op.act {M : Type*} (code : M → ℕ) (O : Op M) (v : Vec) : Vec :=
  O.flatMap fun t => (Vec.wordAct code t.2 v).map fun p => (p.1, t.1 * p.2)

/-- The vector `a v`. -/
def Vec.smul (a : ℤ) (v : Vec) : Vec := v.map fun p => (p.1, a * p.2)

/-- The combination `Σ_i a_i v_i` of vectors. -/
def Vec.combo (l : List (ℤ × Vec)) : Vec := l.flatMap fun t => Vec.smul t.1 t.2

/-- The product of two operators. -/
def Op.mul {M : Type*} (O O' : Op M) : Op M :=
  O.flatMap fun t => O'.map fun t' => (t.1 * t'.1, t.2 ++ t'.2)

/-! ### Compiled operators

For the kernel the letters are compiled once to pairs `(cr, i)` of a flag and the number of the
mode, and the parity of the occupied modes below `i` is read from a function `par`, which may be
a table (`below` is its specification). -/

/-- A compiled letter: whether it creates, and the number of its mode. -/
abbrev CLetter : Type := Bool × ℕ

/-- An operator with compiled letters. -/
abbrev OpC : Type := List (ℤ × List CLetter)

/-- Compile a word. -/
def compileWord {M : Type*} (code : M → ℕ) (w : List (Letter M)) : List CLetter :=
  w.map fun l => (l.cr, code l.m)

/-- Compile an operator. -/
def Op.compile {M : Type*} (code : M → ℕ) (O : Op M) : OpC :=
  O.map fun t => (t.1, compileWord code t.2)

/-- A compiled letter acting on a mask. -/
def actC (par : ℕ → ℕ → Bool) (l : CLetter) (k : ℕ) : Option (Bool × ℕ) :=
  if k.testBit l.2 = l.1 then none else some (par k l.2, k ^^^ 2 ^ l.2)

/-- A compiled word acting on a mask, the rightmost letter first. -/
def wordActC (par : ℕ → ℕ → Bool) : List CLetter → ℕ → Option (Bool × ℕ)
  | [], k => some (false, k)
  | l :: w, k =>
    match wordActC par w k with
    | none => none
    | some (s, k') =>
      match actC par l k' with
      | none => none
      | some (s', k'') => some (xor s s', k'')

/-- A compiled word acting on a vector. -/
def Vec.wordActC (par : ℕ → ℕ → Bool) (w : List CLetter) (v : Vec) : Vec :=
  v.filterMap fun p =>
    (FockCalc.wordActC par w p.1).map fun r => (r.2, if r.1 then -p.2 else p.2)

/-- A compiled operator acting on a vector. -/
def OpC.act (par : ℕ → ℕ → Bool) (O : OpC) (v : Vec) : Vec :=
  O.flatMap fun t => (Vec.wordActC par t.2 v).map fun p => (p.1, t.1 * p.2)

theorem wordActC_compile {M : Type*} (code : M → ℕ) (par : ℕ → ℕ → Bool)
    (hpar : ∀ k i, par k i = (below k i % 2 == 1)) (w : List (Letter M)) (k : ℕ) :
    wordActC par (compileWord code w) k = wordAct code w k := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [compileWord, List.map_cons] at ih ⊢
    rw [wordActC, wordAct, ih]
    rcases wordAct code w k with _ | ⟨s, k'⟩
    · rfl
    · simp only [actC, Letter.act, hpar]

theorem OpC.act_compile {M : Type*} (code : M → ℕ) (par : ℕ → ℕ → Bool)
    (hpar : ∀ k i, par k i = (below k i % 2 == 1)) (O : Op M) (v : Vec) :
    OpC.act par (O.compile code) v = Op.act code O v := by
  simp only [OpC.act, Op.act, Op.compile, List.flatMap_map, Vec.wordActC, Vec.wordAct,
    wordActC_compile code par hpar]

/-! ### Tries -/

/-- A binary trie of integers keyed by masks, read bit by bit from the lowest. -/
inductive Trie
  | nil
  | leaf (z : ℤ)
  | node (l r : Trie)
  deriving DecidableEq

namespace Trie

/-- The value at a leaf (zero elsewhere). -/
def leafVal : Trie → ℤ
  | leaf z => z
  | _ => 0

/-- The two subtries of a node (empty elsewhere). -/
def left : Trie → Trie
  | node l _ => l
  | _ => nil

/-- The two subtries of a node (empty elsewhere). -/
def right : Trie → Trie
  | node _ r => r
  | _ => nil

/-- A node, collapsed to `nil` when both subtries are empty. -/
def mkNode : Trie → Trie → Trie
  | nil, nil => nil
  | l, r => node l r

/-- A leaf, collapsed to `nil` when its value is zero. -/
def mkLeaf (z : ℤ) : Trie := if z = 0 then nil else leaf z

/-- Add `z` at the key `k`, in a trie of depth `d`. -/
def add : ℕ → ℕ → ℤ → Trie → Trie
  | 0, _, z, t => mkLeaf (t.leafVal + z)
  | d + 1, k, z, t =>
    if k % 2 = 0 then mkNode (add d (k / 2) z t.left) t.right
    else mkNode t.left (add d (k / 2) z t.right)

/-- The value at the key `k`, in a trie of depth `d`. -/
def get : ℕ → ℕ → Trie → ℤ
  | 0, _, t => t.leafVal
  | d + 1, k, t => if k % 2 = 0 then get d (k / 2) t.left else get d (k / 2) t.right

theorem get_nil : ∀ d k, get d k nil = 0
  | 0, _ => rfl
  | d + 1, k => by
    simp only [get, left, right]
    split_ifs <;> exact get_nil d _

theorem mkNode_left (l r : Trie) : (mkNode l r).left = l := by
  cases l <;> cases r <;> rfl

theorem mkNode_right (l r : Trie) : (mkNode l r).right = r := by
  cases l <;> cases r <;> rfl

theorem leafVal_mkLeaf (z : ℤ) : (mkLeaf z).leafVal = z := by
  unfold mkLeaf
  split_ifs with h
  · simp [leafVal, h]
  · rfl

theorem mod_two_pow_succ_eq_iff (k k' d : ℕ) :
    k % 2 ^ (d + 1) = k' % 2 ^ (d + 1) ↔ k % 2 = k' % 2 ∧ k / 2 % 2 ^ d = k' / 2 % 2 ^ d := by
  have h1 : ∀ x : ℕ, x % 2 ^ (d + 1) = x % 2 + 2 * (x / 2 % 2 ^ d) := by
    intro x
    rw [pow_succ, mul_comm, Nat.mod_mul]
  rw [h1 k, h1 k']
  omega

theorem get_add : ∀ (d k k' : ℕ) (z : ℤ) (t : Trie),
    get d k (add d k' z t) = get d k t + if k % 2 ^ d = k' % 2 ^ d then z else 0
  | 0, k, k', z, t => by
    simp [get, add, leafVal_mkLeaf, Nat.mod_one]
  | d + 1, k, k', z, t => by
    have key := mod_two_pow_succ_eq_iff k k' d
    unfold add get
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      rcases Nat.mod_two_eq_zero_or_one k' with hk' | hk'
    · have h : k % 2 ^ (d + 1) = k' % 2 ^ (d + 1) ↔ k / 2 % 2 ^ d = k' / 2 % 2 ^ d := by
        rw [key, hk, hk']
        simp
      simp only [hk, hk', ite_true, mkNode_left, get_add d, h]
    · have h : ¬ (k % 2 ^ (d + 1) = k' % 2 ^ (d + 1)) := by
        rw [key, hk, hk']
        simp
      simp only [hk, hk', ite_true, one_ne_zero, ite_false, mkNode_left, h, add_zero]
    · have h : ¬ (k % 2 ^ (d + 1) = k' % 2 ^ (d + 1)) := by
        rw [key, hk, hk']
        simp
      simp only [hk, hk', ite_true, one_ne_zero, ite_false, mkNode_right, h, add_zero]
    · have h : k % 2 ^ (d + 1) = k' % 2 ^ (d + 1) ↔ k / 2 % 2 ^ d = k' / 2 % 2 ^ d := by
        rw [key, hk, hk']
        simp
      simp only [hk, hk', one_ne_zero, ite_false, mkNode_right, get_add d, h]

end Trie

/-- The trie of a vector, of depth `d`: its coefficients summed mask by mask. -/
def Vec.trie (d : ℕ) (v : Vec) : Trie := v.foldl (fun t p => t.add d p.1 p.2) .nil

/-- The coefficients of a vector at the masks equal to `k` modulo `2^d`, summed. -/
def Vec.sumAt (d k : ℕ) (v : Vec) : ℤ :=
  ((v.filter fun p => p.1 % 2 ^ d = k % 2 ^ d).map Prod.snd).sum

theorem Vec.get_foldl (d k : ℕ) (v : Vec) (t : Trie) :
    Trie.get d k (v.foldl (fun t p => t.add d p.1 p.2) t) = Trie.get d k t + Vec.sumAt d k v := by
  induction v generalizing t with
  | nil => simp [Vec.sumAt]
  | cons p v ih =>
    rw [List.foldl_cons, ih, Trie.get_add, Vec.sumAt, Vec.sumAt, List.filter_cons]
    by_cases h : p.1 % 2 ^ d = k % 2 ^ d
    · rw [ite_eq_left h.symm, ite_eq_left (by simpa using h), List.map_cons, List.sum_cons]
      ring
    · rw [ite_eq_right (Ne.symm h), ite_eq_right (by simpa using h)]
      ring

theorem Vec.get_trie (d k : ℕ) (v : Vec) : Trie.get d k (Vec.trie d v) = Vec.sumAt d k v := by
  rw [Vec.trie, Vec.get_foldl, Trie.get_nil, zero_add]

/-! ### Reading masks and vectors in `ℂ` -/

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The occupation table of a mask: the modes whose bit is set. -/
def decode (code : M → ℕ) (k : ℕ) : Finset M := Finset.univ.filter fun m => k.testBit (code m)

/-- A vector read as a coefficient table, `Σ_{(k, z)} z |decode k⟩`. -/
noncomputable def Vec.toFock (code : M → ℕ) (v : Vec) : Finset M → ℂ :=
  (v.map fun p => (p.2 : ℂ) • Fock.ket (decode code p.1)).sum

/-- A letter as a matrix. -/
noncomputable def Letter.toMat (ord : LinearOrder M) (l : Letter M) :
    Matrix (Finset M) (Finset M) ℂ :=
  if l.cr then Fock.creation ord l.m else Fock.annihilation ord l.m

/-- A word as a matrix: the product of its letters. -/
noncomputable def wordMat (ord : LinearOrder M) (w : List (Letter M)) :
    Matrix (Finset M) (Finset M) ℂ :=
  (w.map (Letter.toMat ord)).prod

/-- An operator as a matrix: `Σ z w`. -/
noncomputable def Op.toMat (ord : LinearOrder M) (O : Op M) : Matrix (Finset M) (Finset M) ℂ :=
  (O.map fun t => (t.1 : ℂ) • wordMat ord t.2).sum

/-- The sign `(-1)` or `1` of a flag. -/
def sgn (s : Bool) : ℂ := if s then -1 else 1

/-- The hypotheses on a numbering of the modes: injective, with values below `D`, and every
number below `D` used; and an order that is the order of the numbers. -/
structure Numbering (code : M → ℕ) (D : ℕ) (ord : LinearOrder M) : Prop where
  inj : Function.Injective code
  lt : ∀ m, code m < D
  surj : ∀ i < D, ∃ m, code m = i
  ord_lt : ∀ a b, ord.lt a b ↔ code a < code b

section Numbering

variable {code : M → ℕ} {D : ℕ} {ord : LinearOrder M}

omit [DecidableEq M] in
theorem mem_decode {k : ℕ} {m : M} : m ∈ decode code k ↔ k.testBit (code m) = true := by
  simp [decode]

theorem decode_xor (hN : Numbering code D ord) (k : ℕ) (m : M) :
    decode code (k ^^^ 2 ^ code m) =
      if k.testBit (code m) then (decode code k).erase m else insert m (decode code k) := by
  ext m'
  rw [mem_decode, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hm : m' = m
  · subst hm
    split_ifs with h <;> simp [h, mem_decode]
  · have hc : code m ≠ code m' := fun h => hm (hN.inj h).symm
    rw [decide_eq_false hc, Bool.xor_false]
    split_ifs <;> simp [hm, mem_decode]

omit [DecidableEq M] in
theorem precCount_decode (hN : Numbering code D ord) (k : ℕ) (m : M) :
    Fock.precCount ord (decode code k) m = below k (code m) := by
  rw [below_eq, Fock.precCount]
  refine Finset.card_bij (fun m' _ => code m') ?_ ?_ ?_
  · intro m' hm'
    rw [Finset.mem_filter] at hm' ⊢
    refine ⟨Finset.mem_range.mpr ((hN.ord_lt m' m).mp hm'.2), mem_decode.mp hm'.1⟩
  · intro a _ b _ h
    exact hN.inj h
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨m', rfl⟩ := hN.surj j (lt_trans hj.1 (hN.lt m))
    exact ⟨m', Finset.mem_filter.mpr ⟨mem_decode.mpr hj.2, (hN.ord_lt m' m).mpr hj.1⟩, rfl⟩

theorem neg_one_pow_eq_sgn (n : ℕ) : (-1 : ℂ) ^ n = sgn (n % 2 == 1) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, Nat.even_iff.mp h]
    rfl
  · rw [h.neg_one_pow, Nat.odd_iff.mp h]
    rfl

theorem Letter.toMat_mulVec_ket (hN : Numbering code D ord) (l : Letter M) (k : ℕ) :
    l.toMat ord *ᵥ Fock.ket (decode code k) =
      match l.act code k with
      | none => 0
      | some (s, k') => sgn s • Fock.ket (decode code k') := by
  obtain ⟨cr, m⟩ := l
  simp only [Letter.toMat, Letter.act]
  cases cr <;> cases h : k.testBit (code m)
  · -- annihilation of an empty mode
    simp only [Bool.false_eq_true, ite_false, ite_true]
    exact Fock.annihilation_mulVec_ket_of_notMem (by simp [mem_decode, h])
  · -- annihilation of an occupied mode
    simp only [Bool.false_eq_true, ite_false, Bool.true_eq_false]
    rw [Fock.annihilation_mulVec_ket_of_mem (mem_decode.mpr h), precCount_decode hN,
      neg_one_pow_eq_sgn, decode_xor hN, ite_eq_left h]
  · -- creation in an empty mode
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rw [Fock.creation_mulVec_ket_of_notMem (by simp [mem_decode, h]), precCount_decode hN,
      neg_one_pow_eq_sgn, decode_xor hN, ite_eq_right (by simp [h])]
  · -- creation in an occupied mode
    simp only [ite_true]
    exact Fock.creation_mulVec_ket_of_mem (mem_decode.mpr h)

theorem sgn_xor (s s' : Bool) : sgn (xor s s') = sgn s * sgn s' := by
  cases s <;> cases s' <;> simp [sgn]

theorem wordMat_mulVec_ket (hN : Numbering code D ord) (w : List (Letter M)) (k : ℕ) :
    wordMat ord w *ᵥ Fock.ket (decode code k) =
      match wordAct code w k with
      | none => 0
      | some (s, k') => sgn s • Fock.ket (decode code k') := by
  induction w with
  | nil => simp [wordMat, wordAct, sgn]
  | cons l w ih =>
    rw [wordMat, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ← wordMat, ih,
      wordAct]
    rcases wordAct code w k with _ | ⟨s, k'⟩
    · simp
    · simp only [Matrix.mulVec_smul]
      rw [Letter.toMat_mulVec_ket hN]
      rcases l.act code k' with _ | ⟨s', k''⟩
      · simp
      · simp only [smul_smul, sgn_xor]

theorem Vec.toFock_nil : Vec.toFock code [] = 0 := rfl

theorem Vec.toFock_cons (p : ℕ × ℤ) (v : Vec) :
    Vec.toFock code (p :: v) = (p.2 : ℂ) • Fock.ket (decode code p.1) + Vec.toFock code v := by
  simp [Vec.toFock]

theorem Vec.toFock_append (v v' : Vec) :
    Vec.toFock code (v ++ v') = Vec.toFock code v + Vec.toFock code v' := by
  simp [Vec.toFock]

theorem Vec.toFock_smul (a : ℤ) (v : Vec) :
    Vec.toFock code (Vec.smul a v) = (a : ℂ) • Vec.toFock code v := by
  induction v with
  | nil => simp [Vec.smul, Vec.toFock]
  | cons p v ih =>
    rw [Vec.smul, List.map_cons, ← Vec.smul, Vec.toFock_cons, ih, Vec.toFock_cons, smul_add,
      smul_smul]
    push_cast
    rfl

theorem Vec.toFock_combo (l : List (ℤ × Vec)) :
    Vec.toFock code (Vec.combo l) = (l.map fun t => (t.1 : ℂ) • Vec.toFock code t.2).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [Vec.combo, List.flatMap_cons, ← Vec.combo, Vec.toFock_append, Vec.toFock_smul, ih,
      List.map_cons, List.sum_cons]

theorem wordMat_mulVec (hN : Numbering code D ord) (w : List (Letter M)) (v : Vec) :
    wordMat ord w *ᵥ Vec.toFock code v = Vec.toFock code (Vec.wordAct code w v) := by
  induction v with
  | nil => simp [Vec.toFock, Vec.wordAct]
  | cons p v ih =>
    rw [Vec.toFock_cons, Matrix.mulVec_add, Matrix.mulVec_smul, ih, wordMat_mulVec_ket hN]
    rcases h : FockCalc.wordAct code w p.1 with _ | ⟨s, k'⟩
    · simp only [smul_zero, zero_add, Vec.wordAct, List.filterMap_cons, h, Option.map_none]
    · simp only [Vec.wordAct, List.filterMap_cons, h, Option.map_some, Vec.toFock_cons,
        smul_smul]
      congr 2
      cases s <;> simp [sgn]

theorem wordMat_append (w w' : List (Letter M)) :
    wordMat ord (w ++ w') = wordMat ord w * wordMat ord w' := by
  simp [wordMat]

theorem Op.toMat_cons (t : ℤ × List (Letter M)) (O : Op M) :
    Op.toMat ord (t :: O) = (t.1 : ℂ) • wordMat ord t.2 + Op.toMat ord O := by
  simp only [Op.toMat, List.map_cons, List.sum_cons]

theorem Op.toMat_mulVec (hN : Numbering code D ord) (O : Op M) (v : Vec) :
    Op.toMat ord O *ᵥ Vec.toFock code v = Vec.toFock code (Op.act code O v) := by
  induction O with
  | nil => simp [Op.toMat, Op.act, Vec.toFock]
  | cons t O ih =>
    have e : Op.act code (t :: O) v = Vec.smul t.1 (Vec.wordAct code t.2 v) ++ Op.act code O v :=
      by simp only [Op.act, Vec.smul, List.flatMap_cons]
    rw [e, Op.toMat_cons, Vec.toFock_append, Vec.toFock_smul, Matrix.add_mulVec,
      Matrix.smul_mulVec, wordMat_mulVec hN, ih]

theorem Op.toMat_append (O O' : Op M) :
    Op.toMat ord (O ++ O') = Op.toMat ord O + Op.toMat ord O' := by
  simp [Op.toMat]

theorem Op.toMat_map_prefix (a : ℤ) (w : List (Letter M)) (O' : Op M) :
    Op.toMat ord (O'.map fun t' => (a * t'.1, w ++ t'.2)) =
      (a : ℂ) • (wordMat ord w * Op.toMat ord O') := by
  induction O' with
  | nil => simp [Op.toMat]
  | cons t' O' ih =>
    rw [List.map_cons, Op.toMat_cons, Op.toMat_cons, ih, wordMat_append, Matrix.mul_add,
      Matrix.mul_smul, smul_add, smul_smul, Int.cast_mul]

theorem Op.toMat_mul (O O' : Op M) :
    Op.toMat ord (Op.mul O O') = Op.toMat ord O * Op.toMat ord O' := by
  induction O with
  | nil => simp [Op.mul, Op.toMat]
  | cons t O ih =>
    have e1 : Op.mul (t :: O) O' =
        (O'.map fun t' => (t.1 * t'.1, t.2 ++ t'.2)) ++ Op.mul O O' := by
      simp only [Op.mul, List.flatMap_cons]
    rw [e1, Op.toMat_append, Op.toMat_map_prefix, ih, Op.toMat_cons, add_mul, Matrix.smul_mul]

/-- An operator acting on a vector, computed with compiled letters. -/
theorem Op.toMat_mulVec_compile (hN : Numbering code D ord) (par : ℕ → ℕ → Bool)
    (hpar : ∀ k i, par k i = (below k i % 2 == 1)) (O : Op M) (v : Vec) :
    Op.toMat ord O *ᵥ Vec.toFock code v = Vec.toFock code (OpC.act par (O.compile code) v) := by
  rw [Op.toMat_mulVec hN, OpC.act_compile code par hpar]

/-- The coefficient table of a vector is the sum, over the masks below `2^D`, of the summed
coefficients at that mask. -/
theorem Vec.toFock_eq_sum (hN : Numbering code D ord) (v : Vec) :
    Vec.toFock code v =
      ∑ r ∈ Finset.range (2 ^ D), (Vec.sumAt D r v : ℂ) • Fock.ket (decode code r) := by
  have hdec : ∀ k, decode code (k % 2 ^ D) = decode code k := by
    intro k
    ext m
    simp [mem_decode, Nat.testBit_mod_two_pow, hN.lt m]
  induction v with
  | nil => simp [Vec.toFock, Vec.sumAt]
  | cons p v ih =>
    rw [Vec.toFock_cons, ih]
    have hsplit : ∀ r, Vec.sumAt D r (p :: v) =
        (if r % 2 ^ D = p.1 % 2 ^ D then p.2 else 0) + Vec.sumAt D r v := by
      intro r
      simp only [Vec.sumAt, List.filter_cons]
      split_ifs with h1 h2 h2 <;> simp_all
    simp only [hsplit, Int.cast_add, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (p.1 % 2 ^ D)]
    · rw [ite_eq_left (Nat.mod_mod_of_dvd _ (dvd_refl _)), hdec]
    · intro r hr hne
      rw [ite_eq_right]
      · simp
      · intro h
        apply hne
        rw [← Nat.mod_eq_of_lt (Finset.mem_range.mp hr), h]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))) h

/-- Two vectors whose tries agree have the same coefficient table. -/
theorem Vec.toFock_eq_of_trie_eq (hN : Numbering code D ord) {v v' : Vec}
    (h : Vec.trie D v = Vec.trie D v') : Vec.toFock code v = Vec.toFock code v' := by
  rw [Vec.toFock_eq_sum hN, Vec.toFock_eq_sum hN]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Vec.get_trie, ← Vec.get_trie, h]

omit [DecidableEq M] in
/-- Two masks below `2^D` with the same occupation table are equal. -/
theorem decode_injOn (hN : Numbering code D ord) {k k' : ℕ} (hk : k < 2 ^ D) (hk' : k' < 2 ^ D)
    (h : decode code k = decode code k') : k = k' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < D
  · obtain ⟨m, rfl⟩ := hN.surj j hj
    have := congrArg (fun s => m ∈ s) h
    simp only [mem_decode, eq_iff_iff] at this
    cases h1 : k.testBit (code m) <;> cases h2 : k'.testBit (code m) <;> simp_all
  · push Not at hj
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hj)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hk' (Nat.pow_le_pow_right (by norm_num) hj))]

/-- The coefficient of a vector at the table of a mask below `2^D`. -/
theorem Vec.toFock_apply (hN : Numbering code D ord) (v : Vec) {k : ℕ} (hk : k < 2 ^ D) :
    Vec.toFock code v (decode code k) = (Vec.sumAt D k v : ℂ) := by
  rw [Vec.toFock_eq_sum hN, Finset.sum_apply, Finset.sum_eq_single k]
  · simp [Fock.ket]
  · intro r hr hne
    rw [Pi.smul_apply, Fock.ket, Pi.single_apply, ite_eq_right, smul_zero]
    intro h
    exact hne (decode_injOn hN (Finset.mem_range.mp hr) hk h.symm)
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

/-- A family of vectors with pivots: vector `i` has a nonzero coefficient at the mask `p i` and
every other vector has coefficient zero there. Such a family is linearly independent. -/
theorem Vec.linearIndependent (hN : Numbering code D ord) {ι : Type*} [Finite ι]
    (v : ι → Vec) (p : ι → ℕ) (hp : ∀ i, p i < 2 ^ D)
    (hpiv : ∀ i j, Vec.sumAt D (p j) (v i) = 0 ↔ i ≠ j) :
    LinearIndependent ℂ fun i => Vec.toFock code (v i) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrFun hg (decode code (p j))
  rw [Finset.sum_apply, Pi.zero_apply, Finset.sum_eq_single j] at this
  · rw [Pi.smul_apply, Vec.toFock_apply hN _ (hp j), smul_eq_mul] at this
    have hne : (Vec.sumAt D (p j) (v j) : ℂ) ≠ 0 := by
      exact_mod_cast fun h => ((hpiv j j).mp h) rfl
    exact (mul_eq_zero.mp this).resolve_right hne
  · intro i _ hij
    rw [Pi.smul_apply, Vec.toFock_apply hN _ (hp j), (hpiv i j).mpr hij]
    simp
  · simp

end Numbering

end Artform.FockCalc
