import ArtformScores.Basic

/-!
# The statements

Each statement of the algebra of scores that the library proves, as a
`def … : Prop` tagged with its ledger label. The proofs are in the files that
follow, each a theorem whose type is exactly its statement.
-/

namespace Artform.Scores.Statement

open Matrix (SpecialLinearGroup)
open Artform.Scores
open scoped Pointwise

/-- **R1** (merging). Two kicks in a row are one kick with the summed stencil, and
two moves in a row are one move. -/
@[ledger "R1"]
def merging : Prop :=
  ∀ (S : Type) [CommRing S] (f g : S),
    realize [Step.kick f, Step.kick g] = realize [Step.kick (f + g)] ∧
    realize [Step.move f, Step.move g] = realize [Step.move (f + g)]

/-- **R3** (Whitehead's rule). For a unit `u`, the Whitehead word `w(u)` has the
law `[[0, u], [-u⁻¹, 0]]`, and conjugating by it turns a move `M(f)` into the
kick `K(-u⁻² f)` and a kick `K(f)` into the move `M(-u² f)`. -/
@[ledger "R3"]
def whiteheadRule : Prop :=
  ∀ (S : Type) [CommRing S] (u : Sˣ) (f : S),
    (realize (whitehead u) : Matrix (Fin 2) (Fin 2) S) = !![0, ↑u; -↑u⁻¹, 0] ∧
    realize (whitehead u) * (Step.move f).sl * (realize (whitehead u))⁻¹ =
      (Step.kick (-(↑u⁻¹ * ↑u⁻¹ * f))).sl ∧
    realize (whitehead u) * (Step.kick f).sl * (realize (whitehead u))⁻¹ =
      (Step.move (-(↑u * ↑u * f))).sl

/-- **R4** (balanced movers). The balanced pair `h(u) = w(u) w(1)⁻¹` is the law
`diag(u, u⁻¹)`, and `h(u) h(v) = h(uv)`. -/
@[ledger "R4"]
def balancedRule : Prop :=
  ∀ (S : Type) [CommRing S] (u v : Sˣ),
    (balanced u : Matrix (Fin 2) (Fin 2) S) = !![↑u, 0; 0, ↑u⁻¹] ∧
    balanced u * balanced v = balanced (u * v)

/-- **R5** (time reversal). The reversed score, its steps in the opposite order and
each inverted, realizes the inverse law. -/
@[ledger "R5"]
def timeReversal : Prop :=
  ∀ (S : Type) [CommRing S] (w : Score S), realize w.reverse = (realize w)⁻¹

/-- **R6** (blocking). Blocking commutes with the realizer, `⟦B(w)⟧ = B(⟦w⟧)`: when the
stencil ring `S` is free over `S′` on `m` places, the blocking of the law of a score is the
law of its blocked score. -/
@[ledger "R6"]
def blocking : Prop :=
  ∀ (S' S : Type) [CommRing S'] [CommRing S] [Algebra S' S] (m : ℕ)
    (bs : Module.Basis (Fin m) S' S) (w : Score S),
    block bs (realize w : Matrix (Fin 2) (Fin 2) S) = realizePlaced (blockScore bs w)

/-- **R6** (red-black on the blocked artform). On an index-2 blocking, with the places red
(the basis vector `1`) and black (`x`, with `x² = d` a unit), the red and black kicks
together are the blocked kick. The blocked shift by `x` turns the red-black tick into the
black-red tick, and the red-black tick is the blocking of a law of the artform only if
`κ² β = 0`, `β` the black part of the move's stencil `h`. -/
@[ledger "R6"]
def redBlack : Prop :=
  ∀ (S' S : Type) [CommRing S'] [CommRing S] [Algebra S' S] (bs : Module.Basis (Fin 2) S' S)
    (x : S) (d : S'ˣ), bs 0 = 1 → bs 1 = x → x * x = algebraMap S' S ↑d → ∀ (κ : S') (h : S),
    realizePlaced [redKick κ, blackKick κ] = block bs (Step.kick (algebraMap S' S κ)).mat ∧
    block bs (x • 1) * redBlackTick bs κ h = blackRedTick bs κ h * block bs (x • 1) ∧
    ((∃ T : Matrix (Fin 2) (Fin 2) S, block bs T = redBlackTick bs κ h) →
      κ * κ * bs.repr h 1 = 0)

/-- **R6** (the cosets; the ledger's Definition 3). Blocking by a sublattice `Λ′ ⊂ Λ` reads the
stencils as a free module over the sublattice's stencils. When `t₀, …, t_(m-1)` are coset
representatives, each cell being `λ′ + t_i` for exactly one `i`, the shifts by the `t_i` are a
basis of `R[Λ]` over `R[Λ′]`, one place for each coset. So the blocking (R6) and red-black
apply to every sublattice blocking. -/
@[ledger "R6"]
def cosets : Prop :=
  ∀ (R Λ : Type) [CommRing R] [AddCommGroup Λ] (Λ' : AddSubgroup Λ) (m : ℕ) (t : Fin m → Λ),
    (∀ a : Λ, ∃! i, a - t i ∈ Λ') →
    ∃ bs : Module.Basis (Fin m) (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ),
      ∀ i, bs i = AddMonoidAlgebra.single (t i) 1

/-- **R6** (red-black on the checkerboard; Definition 3 and finding 044). On `ℤ²` the
checkerboard `Λ′`, the cells `(a, b)` with `a + b` even, has the coset representatives `0` and
`e₁`. So the stencils `R[x^±1, y^±1]` have the basis `1, x` over the checkerboard's stencils
`R[Λ′] = R[u^±1, v^±1]`, with `u = x y` and `v = x/y`, and `x² = u v` is a unit of `R[Λ′]`:
red-black's hypotheses hold. The book's face form `g = 4 - x - 1/x - y - 1/y` has the red part
`4` and the black part `-(1 + 1/u + 1/v + 1/(u v))`. So when `κ² λ ≠ 0`, the red-black tick
`K_red(κ) M½ K_black(κ) M½`, with the half move `M½ = M(-λg/2)`, is the blocking of no law of
the artform. -/
@[ledger "R6"]
def checkerboardRedBlack : Prop :=
  ∀ (R : Type) [CommRing R] [Invertible (2 : R)],
    ∃ bs : Module.Basis (Fin 2) (AddMonoidAlgebra R checkerboard) (AddMonoidAlgebra R (ℤ × ℤ)),
      bs 0 = 1 ∧ bs 1 = shiftX R ∧
      shiftX R * shiftX R = algebraMap (AddMonoidAlgebra R checkerboard)
        (AddMonoidAlgebra R (ℤ × ℤ)) (AddMonoidAlgebra.single (cellU + cellV) 1) ∧
      IsUnit (AddMonoidAlgebra.single (cellU + cellV) (1 : R)) ∧
      bs.repr (faceStencil R) 0 = 4 ∧
      bs.repr (faceStencil R) 1 = -(1 + AddMonoidAlgebra.single (-cellU) 1 +
        AddMonoidAlgebra.single (-cellV) 1 + AddMonoidAlgebra.single (-(cellU + cellV)) 1) ∧
      ∀ κ ℓ : R, κ * κ * ℓ ≠ 0 →
        ¬ ∃ T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra R (ℤ × ℤ)),
          block bs T = redBlackTick bs (algebraMap R (AddMonoidAlgebra R checkerboard) κ)
            ((-(ℓ * ⅟2)) • faceStencil R)

/-- **T1** (one dimension, every dial). Over a field `F`, every law of determinant 1
on a dial, `A ∈ SL(2, F[x, 1/x])`, is the law of a score: `E₂ = SL₂` there. -/
@[ledger "T1"]
def everyLawIsAScore : Prop :=
  ∀ (F : Type) [Field F] (A : SpecialLinearGroup (Fin 2) (LaurentPolynomial F)),
    ∃ w : Score (LaurentPolynomial F), realize w = A

/-- **T1** for the dials `Z/p^k`, `p` prime: every law of determinant 1 in
`SL(2, (Z/p^k)[x, 1/x])` is the law of a score. -/
@[ledger "T1"]
def everyLawIsAScorePrimePower : Prop :=
  ∀ (p k : ℕ), p.Prime → ∀ A : SpecialLinearGroup (Fin 2) (LaurentPolynomial (ZMod (p ^ k))),
    ∃ w : Score (LaurentPolynomial (ZMod (p ^ k))), realize w = A

/-- **T1** for every dial `Z/n`, `n ≥ 1`: every law of determinant 1 in
`SL(2, (Z/n)[x, 1/x])` is the law of a score. (Mathlib's `ZMod 0` is `ℤ`, which is
no dial.) -/
@[ledger "T1"]
def everyLawIsAScoreModulus : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ A : SpecialLinearGroup (Fin 2) (LaurentPolynomial (ZMod n)),
    ∃ w : Score (LaurentPolynomial (ZMod n)), realize w = A

/-- **T2** (the index). No score realizes a chiral mover `diag(a, 1)` with
`a ≠ 1`: every law of a score has determinant 1. -/
@[ledger "T2"]
def index : Prop :=
  ∀ (S : Type) [CommRing S] (a : S), a ≠ 1 →
    ∀ w : Score S, (realize w : Matrix (Fin 2) (Fin 2) S) ≠ !![a, 0; 0, 1]

/-- **T4** (one mode on a prime dial). For `p = 5, 7, 11, 13`, merging (R1) and
Whitehead's rule (R3) present `SL(2, F_p)` on `X = M(1)` and `Y = K(1)`. Every law is
the law of a word in `X` and `Y`, and two words have the same law exactly when they
are equal in the group presented by the rules. -/
@[ledger "T4"]
def oneModeComplete : Prop :=
  ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
    (∀ A : SpecialLinearGroup (Fin 2) (ZMod p), ∃ v : FreeGroup OneMode.Gen,
      OneMode.law p v = A) ∧
    ∀ v₁ v₂ : FreeGroup OneMode.Gen, OneMode.law p v₁ = OneMode.law p v₂ ↔
      PresentedGroup.mk (OneMode.relators p) v₁ = PresentedGroup.mk (OneMode.relators p) v₂

/-- **T7** (Latimer–MacDuffee: the class of a law). On the curve of the phase `t`,
`A_t = S[λ]/(λ² - tλ + 1)`, a law `[[a, b], [c, d]]` of phase `t` has the left eigenvector
`u = (c, λ - a)`, `u T = λ u`, and so the ideal `(c, λ - a)`. When `t² - 4` is not a
square in the fraction field, processing keeps the ideal's class: if `T′ = P T P⁻¹` with
`P` invertible, then `(c′, λ - a′)` and `(c, λ - a)` are in the same class. -/
@[ledger "T7"]
def classInvariance : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] (t : S), NonSquareDisc t →
    ∀ (T T' : SpecialLinearGroup (Fin 2) S) (P : GL (Fin 2) S), phase T = t →
      (T' : Matrix (Fin 2) (Fin 2) S) = (P : Matrix (Fin 2) (Fin 2) S) * T *
        ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) →
      Matrix.vecMul (eigenRow t T)
          ((T : Matrix (Fin 2) (Fin 2) S).map (algebraMap S (curveRing t))) =
        eig t • eigenRow t T ∧
      SameClass (lawIdeal t T') (lawIdeal t T)

/-- **T7** (the trivial class). A law `T` of phase `t` is in the trivial class, the class of
`A_t` itself, exactly when it has a cyclic vector `v`, one with `det[v | T v]` a unit. That
determinant is the law's quadratic form `Q_T(v)`, so the class is trivial exactly when `Q_T`
represents a unit. A cyclic vector conjugates `T` to the companion tick
`C_t = [[0, -1], [1, t]]`: `T [v | T v] = [v | T v] C_t`. -/
@[ledger "T7"]
def trivialClass : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] (t : S), NonSquareDisc t →
    ∀ T : SpecialLinearGroup (Fin 2) S, phase T = t →
      (∀ v : Fin 2 → S, IsUnit (cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) v).det →
        (T : Matrix (Fin 2) (Fin 2) S) * cyclicMatrix T v = cyclicMatrix T v * companion t) ∧
      (SameClass (lawIdeal t T) ⊤ ↔
        ∃ v : Fin 2 → S, IsUnit (cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) v).det)

/-- **T7** (Latimer–MacDuffee: one class, one law up to processing). When `t² - 4` is not a
square in the fraction field, the ideal `(c, λ - a)` of a law of phase `t` is nonzero, and two
laws of phase `t` have their ideals in the same class exactly when processing turns one into
the other: `T′ = P T P⁻¹` with `P` invertible. -/
@[ledger "T7"]
def classesOneToOne : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] (t : S), NonSquareDisc t →
    ∀ T T' : SpecialLinearGroup (Fin 2) S, phase T = t → phase T' = t →
      lawIdeal t T ≠ ⊥ ∧
      (SameClass (lawIdeal t T') (lawIdeal t T) ↔
        ∃ P : GL (Fin 2) S, (T' : Matrix (Fin 2) (Fin 2) S) =
          (P : Matrix (Fin 2) (Fin 2) S) * T * ((P⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S))

/-- **T7** (Latimer–MacDuffee: every class is a law's). Over a principal ideal domain `S`, as
the ledger's `F[x, 1/x]`, with `t² - 4` not a square in the fraction field, every nonzero ideal
of `A_t` is in the class of the ideal `(c, λ - a)` of some law of phase `t`. -/
@[ledger "T7"]
def classesOnto : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] (t : S), NonSquareDisc t →
    ∀ I : Ideal (curveRing t), I ≠ ⊥ →
      ∃ T : SpecialLinearGroup (Fin 2) S, phase T = t ∧ SameClass (lawIdeal t T) I

/-- **T12** (the reading). Two laws with the same phase and the same reading give
the same output from rest: from `(b, e) = (b₀, 0)`, the flux `b` after `n`
ticks is the same for both. -/
@[ledger "T12"]
def readingDetermines : Prop :=
  ∀ (S : Type) [CommRing S] (T T' : SpecialLinearGroup (Fin 2) S),
    phase T = phase T' → reading T = reading T' → ∀ (n : ℕ) (b₀ : S),
      Matrix.mulVec ((T ^ n : SpecialLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
          ![b₀, 0] 0 =
        Matrix.mulVec ((T' ^ n : SpecialLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
          ![b₀, 0] 0

/-- **T12** (palindromes). A law with no cut (`a = d`) is reversed by the
reflection `P₀ = diag(1, -1)`: `P₀ T P₀ = T⁻¹`. -/
@[ledger "T12"]
def palindrome : Prop :=
  ∀ (S : Type) [CommRing S] (T : SpecialLinearGroup (Fin 2) S),
    (T : Matrix (Fin 2) (Fin 2) S) 0 0 = (T : Matrix (Fin 2) (Fin 2) S) 1 1 →
      !![1, 0; 0, -1] * (T : Matrix (Fin 2) (Fin 2) S) * !![1, 0; 0, -1] =
        ((T⁻¹ : SpecialLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)

/-- **T13** (the crystallographic pulls). The one-mode tick of the leapfrog has
order 6, 4 and 3 at the pulls `μ = 1, 2, 3`, and infinite order at `μ = 4`. -/
@[ledger "T13"]
def stepOrders : Prop :=
  (tick 1 ^ 6 = 1 ∧ ∀ k : ℕ, 0 < k → k < 6 → tick 1 ^ k ≠ 1) ∧
  (tick 2 ^ 4 = 1 ∧ ∀ k : ℕ, 0 < k → k < 4 → tick 2 ^ k ≠ 1) ∧
  (tick 3 ^ 3 = 1 ∧ ∀ k : ℕ, 0 < k → k < 3 → tick 3 ^ k ≠ 1) ∧
  (∀ k : ℕ, 0 < k → tick 4 ^ k ≠ 1)

/-- **T14** (the caller's cut). The two orders of the dimension split have the same
phase and the cuts `±h²(gx - gy)/2`. A caller that calls `xy` with weight `q`
and `yx` with weight `1 - q` has a mean tick with the cut
`(2q - 1) h²(gx - gy)/2`, which vanishes for every pull exactly when
`q = 1/2`. -/
@[ledger "T14"]
def callerCut : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h gx gy q : K),
    cut (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) = h ^ 2 * (gx - gy) / 2 ∧
    cut (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K) = -(h ^ 2 * (gx - gy) / 2) ∧
    (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K).trace =
      (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K).trace ∧
    cut (q • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
        (1 - q) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) =
      (2 * q - 1) * (h ^ 2 * (gx - gy) / 2)

/-- **T15** (every method is light in the boxes its score cuts; the ledger's finding 042,
Theorem S5.2). Paint a number on each bell and read each row as a field. For every sequence
of changes, `u(t + 1) = P_t u(t)`, and the rows obey the book's tick
`u(t + 1) + u(t - 1) = S_t u(t)` with `S_t = P_t + P_(t-1)`. Two changes `A` and `B` cut the
row into dodges and mirror boxes. On a dodge, a pair that both swap, `S` is the doubled bond.
Elsewhere `S` is the neighbour sum of the box, with a wall where neither change swaps, and at
a wall a place is made. -/
@[ledger "T15"]
def methodsAreLight : Prop :=
  ∀ (R : Type) [AddCommMonoid R] (N : ℕ),
    (∀ (π : ℕ → Equiv.Perm (Fin N)), (∀ t, Bells.IsChange (π t)) → ∀ (f : Fin N → R) (t : ℕ),
      Bells.paint f (Bells.row π (t + 1)) = Bells.act (π t) (Bells.paint f (Bells.row π t)) ∧
      Bells.paint f (Bells.row π (t + 2)) + Bells.paint f (Bells.row π t) =
        Bells.act (π (t + 1)) (Bells.paint f (Bells.row π (t + 1))) +
          Bells.act (π t) (Bells.paint f (Bells.row π (t + 1)))) ∧
    ∀ (A B : Equiv.Perm (Fin N)), Bells.IsChange A → Bells.IsChange B →
      ∀ (u : Fin N → R) (i : Fin N),
        (Bells.IsDodge A B i →
          Bells.act A u i + Bells.act B u i = u (A i) + u (A i) ∧ B (A i) = i) ∧
        (¬ Bells.IsDodge A B i →
          Bells.act A u i + Bells.act B u i = Bells.boxSum A B u i ∧
          (Bells.boxLeft A B i = i ∨ Bells.boxRight A B i = i → A i = i ∨ B i = i))

/-- **T15** (plain hunt is light in a mirror box; finding 042, Theorem S5.1). Plain hunt rings
the changes `X = (12)(34)…` and `Y = (23)(45)…` in turn, `X` first. On `N` bells:
1. `P_X + P_Y = S_mirror`, the neighbour sum of a box with mirror walls;
2. the painted rows obey the book's tick `u(t + 1) + u(t - 1) = S_mirror u(t)`;
3. every bell is a light ray: after `t` changes the bell from the position `b` is at
   `fold (start b + t)`, the point `start b + t` of a circle of `2N` places folded onto the box.
   It moves one place per change or lies at a wall, and for `N ≥ 2` it never lies twice
   running;
4. for `N ≥ 3` the plain course has `2N` rows: two rows are equal exactly when their times
   agree mod `2N`. -/
@[ledger "T15"]
def plainHuntIsLight : Prop :=
  ∀ N : ℕ,
    (∀ (R : Type) [AddCommMonoid R] (u : Fin N → R),
      Bells.act (Bells.huntX N) u + Bells.act (Bells.huntY N) u = Bells.mirror u) ∧
    (∀ (R : Type) [AddCommMonoid R] (f : Fin N → R) (t : ℕ),
      Bells.paint f (Bells.hunt N (t + 2)) + Bells.paint f (Bells.hunt N t) =
        Bells.mirror (Bells.paint f (Bells.hunt N (t + 1)))) ∧
    (∀ (t : ℕ) (b : Fin N),
      (Bells.hunt N t b : ℕ) = Bells.fold N (Bells.start N b + t) ∧
      ((Bells.hunt N (t + 1) b : ℕ) + 1 = Bells.hunt N t b ∨
        (Bells.hunt N t b : ℕ) + 1 = Bells.hunt N (t + 1) b ∨
        (Bells.hunt N (t + 1) b = Bells.hunt N t b ∧
          ((Bells.hunt N t b : ℕ) = 0 ∨ (Bells.hunt N t b : ℕ) + 1 = N))) ∧
      (2 ≤ N → Bells.hunt N (t + 1) b = Bells.hunt N t b →
        Bells.hunt N (t + 2) b ≠ Bells.hunt N (t + 1) b)) ∧
    (3 ≤ N → ∀ s t : ℕ, Bells.hunt N s = Bells.hunt N t ↔ s % (2 * N) = t % (2 * N))

/-- **T15** (the modes of the mirror box; finding 042, Theorem S5.1, part 4). The mode
`v_k(i) = cos(πk(2i + 1)/(2N))` has `S_mirror v_k = 2 cos(πk/N) v_k`. The `N` modes
`0 ≤ k < N` are independent, and `S_mirror` has no other eigenvalue. The tick turns the mode
`k` by `πk/N` per change: `u(t) = (A cos(πkt/N) + B sin(πkt/N)) v_k` obeys
`u(t + 1) + u(t - 1) = S_mirror u(t)`, and `2N` changes, the plain course, are a period of
every mode. -/
@[ledger "T15"]
def mirrorModes : Prop :=
  ∀ N : ℕ,
    (∀ k : ℕ, Bells.mirror (Bells.mode N k) =
      (2 * Real.cos (Real.pi * k / N)) • Bells.mode N k) ∧
    LinearIndependent ℝ (fun k : Fin N => Bells.mode N k) ∧
    (∀ (μ : ℝ) (v : Fin N → ℝ), v ≠ 0 → Bells.mirror v = μ • v →
      ∃ k < N, μ = 2 * Real.cos (Real.pi * k / N)) ∧
    ∀ (k : ℕ) (A B : ℝ) (t : ℕ),
      Bells.turn N k A B (t + 2) + Bells.turn N k A B t =
        Bells.mirror (Bells.turn N k A B (t + 1)) ∧
      Bells.turn N k A B (t + 2 * N) = Bells.turn N k A B t

/-- **T15** (the presentation of the bells; Moore 1897). On `n + 1` positions the steps are the
swaps `s_i` of the neighbours `i` and `i + 1`, and the rules are Coxeter's: `s_i² = 1`,
`(s_i s_(i+1))³ = 1`, and `(s_i s_j)² = 1` for `|i - j| ≥ 2`, the relations of Mathlib's
Coxeter matrix `A_n`. Every permutation is the law of a word in the `s_i`, and two words have
the same law exactly when they are equal in the group that the rules present. -/
@[ledger "T15"]
def bellsPresentation : Prop :=
  ∀ n : ℕ,
    (∀ σ : Equiv.Perm (Fin (n + 1)), ∃ v : FreeGroup (Fin n), Bells.law n v = σ) ∧
    ∀ v₁ v₂ : FreeGroup (Fin n), Bells.law n v₁ = Bells.law n v₂ ↔
      PresentedGroup.mk (CoxeterMatrix.A n).relationsSet v₁ =
        PresentedGroup.mk (CoxeterMatrix.A n).relationsSet v₂

/-- **T15** (Rankin's parity; the ledger's finding 043, Lemma 1). Let `σ` be a permutation of a
finite group `G` whose every step is `x → A x` or `x → B x`, and let `c = A⁻¹ B`.
1. The step chosen at `c⁻¹ w` is the one chosen at `w`, so the choice is constant on each
   coset `⟨c⟩ x`.
2. So `σ = L_A ∘ ∏ ρ_C`, with one cycle `ρ_C` of length `ord c` for each of the `m` cosets `C`
   that take `B`: `m · ord c` elements take `B`, and `sign σ = sign L_A · ((-1)^(ord c + 1))^m`.
3. An extent is one cycle through all of `G`, so its sign is `(-1)^(|G| + 1)`, that of a
   `|G|`-cycle. -/
@[ledger "T15"]
def rankinParity : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : G) (σ : Equiv.Perm G),
    (∀ x, σ x = A * x ∨ σ x = B * x) →
      (∀ w, σ ((A⁻¹ * B)⁻¹ * w) = A * ((A⁻¹ * B)⁻¹ * w) ↔ σ w = A * w) ∧
      (∃ m : ℕ, m * orderOf (A⁻¹ * B) = (Finset.univ.filter fun x => σ x ≠ A * x).card ∧
        Equiv.Perm.sign σ =
          Equiv.Perm.sign (Equiv.mulLeft A) * ((-1) ^ (orderOf (A⁻¹ * B) + 1)) ^ m) ∧
      (Bells.IsExtent A B σ → Equiv.Perm.sign σ = (-1) ^ (Fintype.card G + 1))

/-- **T15** (the lifting lemma; finding 043, Lemma 2). If a normal subgroup `N` of a finite
group `G` lies in `⟨c⟩`, `c = A⁻¹ B`, every extent `σ` of `G` under `A` and `B` maps to an extent
of `G/N` under the images of `A` and `B`: `x N ↦ σ(x) N` is well defined, and an extent. -/
@[ledger "T15"]
def extentLifting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : G) (N : Subgroup G) [N.Normal],
    N ≤ Subgroup.zpowers (A⁻¹ * B) → ∀ σ : Equiv.Perm G, Bells.IsExtent A B σ →
      ∃ σ' : Equiv.Perm (G ⧸ N), Bells.IsExtent (A : G ⧸ N) (B : G ⧸ N) σ' ∧
        ∀ x : G, σ' (x : G ⧸ N) = (σ x : G ⧸ N)

/-- **T15** (the Fibonacci rule; finding 043, Theorem S5.3, part 2). On one mode over `ZMod p`,
`p` an odd prime, the leapfrog's steps are the kick `K = K(1) = [[1, 0], [1, 1]]` and the move
`M = M(-1) = [[1, -1], [0, 1]]`. A forward extent of `SL(2, p)` or of `PSL(2, p)` under `K` and
`M` needs `4 ∣ α(p)`, with `α(p)` the Fibonacci rank of apparition, the least `k ≥ 1` with
`p ∣ F_k`. -/
@[ledger "T15"]
def fibonacciRule : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod p)),
      Bells.IsExtent (Step.kick (1 : ZMod p)).sl (Step.move (-1 : ZMod p)).sl σ →
        4 ∣ Bells.fibRank p) ∧
    ∀ σ : Equiv.Perm (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
      Bells.IsExtent
        ((Step.kick (1 : ZMod p)).sl : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
        ((Step.move (-1 : ZMod p)).sl : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) σ →
        4 ∣ Bells.fibRank p

/-- **T15** (one back-step; the ledger's finding 043, Lemma 3). Let `σ` be a permutation of a
finite group `G` that steps forward, `x → A x` or `x → B x`, at every element but one, `x₀`, where
it steps back by `A⁻¹` or by `B⁻¹`; a Hamiltonian cycle with one back-step is one. Then `A B` lies
in `⟨c⟩`, `c = A⁻¹ B`, when the back-step is `A⁻¹`, and `B A` does when it is `B⁻¹`. -/
@[ledger "T15"]
def oneBackStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : G) (σ : Equiv.Perm G) (x₀ : G),
    (∀ x, x ≠ x₀ → σ x = A * x ∨ σ x = B * x) →
      (σ x₀ = A⁻¹ * x₀ → A * B ∈ Subgroup.zpowers (A⁻¹ * B)) ∧
      (σ x₀ = B⁻¹ * x₀ → B * A ∈ Subgroup.zpowers (A⁻¹ * B))

/-- **T15** (kicks with back-moves never ring; finding 043, Theorem S5.3, part 1). On one mode
over `ZMod n`, `n ≥ 3`, take the forward kick `K = K(1)` and the backward move `M⁻¹ = M(1)`, the
inverse of the leapfrog's move `M = M(-1)`. Their staggered tick `M⁻¹ K = [[2, 1], [1, 1]]` is
Arnold's cat map, and the score of `K` and `M⁻¹` has no extent of `SL(2, Z/n)` or of
`PSL(2, Z/n) = SL(2, Z/n)/{±1}`. -/
@[ledger "T15"]
def catMapNeverRings : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (((Step.move (1 : ZMod n)).sl * (Step.kick (1 : ZMod n)).sl :
        SpecialLinearGroup (Fin 2) (ZMod n)) : Matrix (Fin 2) (Fin 2) (ZMod n)) =
      !![2, 1; 1, 1] ∧
    (∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod n)),
      ¬ Bells.IsExtent (Step.kick (1 : ZMod n)).sl (Step.move (1 : ZMod n)).sl σ) ∧
    ∀ σ : Equiv.Perm (SpecialLinearGroup (Fin 2) (ZMod n) ⧸ Bells.pmOne n),
      ¬ Bells.IsExtent
        ((Step.kick (1 : ZMod n)).sl : SpecialLinearGroup (Fin 2) (ZMod n) ⧸ Bells.pmOne n)
        ((Step.move (1 : ZMod n)).sl : SpecialLinearGroup (Fin 2) (ZMod n) ⧸ Bells.pmOne n) σ

/-- **T15** (the balance of back-steps; it generalizes the ledger's finding 043, Lemma 3). For any
permutation `σ` of a finite group, `A ≠ B` and any union `O` of the cosets `⟨c⟩ x`, `c = A⁻¹ B`: the
back-steps of `σ` in `O` are as many as the `v ∈ O` such that `B v` is the target of a back-step. -/
@[ledger "T15"]
def backStepBalance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : G) (σ : Equiv.Perm G) (O : Set G), A ≠ B →
    (∀ v, A⁻¹ * B * v ∈ O ↔ v ∈ O) →
      (O ∩ Bells.backSteps A B σ).ncard = (O ∩ {v | σ⁻¹ (B * v) ∈ Bells.backSteps A B σ}).ncard

/-- **T15** (the two squares; finding 043, Theorem S5.4, part 1). Their extents need exactly two
back-turns: `L⁻¹ R` has order 3, `L R` and `R L` have order 5, and the fewest back-turns of a run of
the group of the two squares is two. -/
@[ledger "T15"]
def twoSquaresBackTurns : Prop :=
  orderOf (Bells.turnL⁻¹ * Bells.turnR) = 3 ∧ orderOf (Bells.turnL * Bells.turnR) = 5 ∧
    orderOf (Bells.turnR * Bells.turnL) = 5 ∧ Bells.FewestBack Bells.turnL Bells.turnR 2

/-- **T15** (the fewest back-steps; finding 043, Theorem S5.4, parts 2 and 3), under the leapfrog's
`K` and `M`, on `SL(2, Z/n)` and `PSL(2, Z/n)`: none for `n = 3, 6, 7, 9, 12`; exactly two for
`n = 4, 5, 10, 13`, among them the octahedron's and the icosahedron's groups `PSL(2, Z/4)` and
`PSL(2, 5)`; neither one nor two for `n = 8` and `n = 11`, so at least three for `n = 11`, which has
no extent; and `PSL(2, Z/8)` has a run with three. -/
@[ledger "T15"]
def fewestBackSteps : Prop :=
  (∀ n ∈ [3, 6, 7, 9, 12], Bells.FewestBack (Bells.leapK n) (Bells.leapM n) 0 ∧
    Bells.FewestBack (Bells.barK n) (Bells.barM n) 0) ∧
  (∀ n ∈ [4, 5, 10, 13], Bells.FewestBack (Bells.leapK n) (Bells.leapM n) 2 ∧
    Bells.FewestBack (Bells.barK n) (Bells.barM n) 2) ∧
  (∀ n ∈ [8, 11],
    (∀ σ, Bells.IsRun (Bells.leapK n) (Bells.leapM n) σ →
      (Bells.backSteps (Bells.leapK n) (Bells.leapM n) σ).ncard ≠ 1 ∧
      (Bells.backSteps (Bells.leapK n) (Bells.leapM n) σ).ncard ≠ 2) ∧
    ∀ σ, Bells.IsRun (Bells.barK n) (Bells.barM n) σ →
      (Bells.backSteps (Bells.barK n) (Bells.barM n) σ).ncard ≠ 1 ∧
      (Bells.backSteps (Bells.barK n) (Bells.barM n) σ).ncard ≠ 2) ∧
  (∀ σ, Bells.IsRun (Bells.leapK 11) (Bells.leapM 11) σ →
    3 ≤ (Bells.backSteps (Bells.leapK 11) (Bells.leapM 11) σ).ncard) ∧
  (∀ σ, Bells.IsRun (Bells.barK 11) (Bells.barM 11) σ →
    3 ≤ (Bells.backSteps (Bells.barK 11) (Bells.barM 11) σ).ncard) ∧
  ∃ σ, Bells.IsRun (Bells.barK 8) (Bells.barM 8) σ ∧
    (Bells.backSteps (Bells.barK 8) (Bells.barM 8) σ).ncard = 3

/-- **T15** (the table of forward extents; finding 043, Theorem S5.3, part 3), under the leapfrog's
`K` and `M`: `2` extents for `n = 2`, `16` for `n = 3` and `768` for `n = 6`, of `SL(2, Z/n)` and of
`PSL(2, Z/n)` alike; none for `n = 4, 5, 10, 11, 13`; and some for `n = 7, 9, 12`. For `n = 8` the
question is open. -/
@[ledger "T15"]
def forwardExtentTable : Prop :=
  (Bells.extentsSL 2).ncard = 2 ∧ (Bells.extentsPSL 2).ncard = 2 ∧
  (Bells.extentsSL 3).ncard = 16 ∧ (Bells.extentsPSL 3).ncard = 16 ∧
  (Bells.extentsSL 6).ncard = 768 ∧ (Bells.extentsPSL 6).ncard = 768 ∧
  (∀ n ∈ [4, 5, 10, 11, 13], Bells.extentsSL n = ∅ ∧ Bells.extentsPSL n = ∅) ∧
  ∀ n ∈ [7, 9, 12], (Bells.extentsSL n).Nonempty ∧ (Bells.extentsPSL n).Nonempty

/-- **T15** (ringing on a lattice only transports; finding 082, the permutation case of finding
016's Theorem K, here without that theorem). A linear permutation law moves the values of `c`
channels on the cells `Λ`: it is a permutation `σ` of `Λ × Fin c` that commutes with the shifts of
`Λ`. In any dimension, and for one tick of any periodic score (blocked by Definition 3 if its place
needs it), some `q ≥ 1` makes `σ^q` a shift of each channel by its own lattice vector `v i`. So
every painted field moves rigidly: its value at `(z, i)` is at `(z + v i, i)` after `q` ticks. -/
@[ledger "T15"]
def permutationLawsTransport : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (c : ℕ) (σ : Equiv.Perm (Λ × Fin c)),
    (∀ w z i, σ (z + w, i) = ((σ (z, i)).1 + w, (σ (z, i)).2)) →
    ∃ (q : ℕ) (v : Fin c → Λ), 0 < q ∧
      (∀ z i, (σ ^ q) (z, i) = (z + v i, i)) ∧
      ∀ (R : Type) (u : Λ × Fin c → R) z i, u ((σ ^ q)⁻¹ (z + v i, i)) = u (z, i)

/-- **T13** (Theorem Q, part 1; finding 037). The one-mode tick `T = M(-μ) K(1)` has finite order
exactly at the pulls `μ = 1, 2, 3` (`stepOrders` gives the orders `6, 4, 3`). At `μ = 0` and `μ = 4`
it grows linearly, by the powers written here. For `μ ≥ 5` it grows by `ρ = (μ - 2 + √(μ² - 4μ))/2`
per tick: `ρ > 1`, and the trace of `Tⁿ` is `(-ρ)ⁿ + (-ρ)⁻ⁿ`. -/
@[ledger "T13"]
def tickGrowth : Prop :=
  (∀ μ : ℕ, IsOfFinOrder (tick μ) ↔ μ = 1 ∨ μ = 2 ∨ μ = 3) ∧
  (∀ n : ℕ, ((tick 0 ^ n : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![1, 0; (n : ℤ), 1]) ∧
  (∀ n : ℕ, ((tick 4 ^ n : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (-1 : ℤ) ^ n • !![1 + 2 * (n : ℤ), 4 * n; -n, 1 - 2 * n]) ∧
  ∀ μ : ℕ, 5 ≤ μ → 1 < StepGroup.growth μ ∧ ∀ n : ℕ,
    ((Matrix.trace ((tick μ ^ n : SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) : ℤ) : ℝ) =
      (-StepGroup.growth μ) ^ n + ((-StepGroup.growth μ)⁻¹) ^ n

/-- **T13** (Theorem Q, part 2; finding 037). The step group `Σ_μ = ⟨K, M(-μ)⟩` lies in `Γ¹(μ)` for
every `μ ≥ 1`, with equality exactly when `μ ≤ 4`. Its index in `SL(2, ℤ)` is `1, 3, 8, 12` at
`μ = 1, 2, 3, 4`, and infinite (`Subgroup.index = 0`) for `μ ≥ 5`. The relations of the ledger's
table hold: `K M K = M K M` and `(K M K)⁴ = 1` at `μ = 1`; `(M K)⁴ = 1` and `(M K)² K = K (M K)²` at
`μ = 2`; `(M K)³ = 1` at `μ = 3`. -/
@[ledger "T13"]
def stepGroups : Prop :=
  (∀ μ : ℕ, 1 ≤ μ → StepGroup.stepGroup μ ≤ StepGroup.gammaUpper μ ∧
    (StepGroup.stepGroup μ = StepGroup.gammaUpper μ ↔ μ ≤ 4)) ∧
  (StepGroup.stepGroup 1).index = 1 ∧ (StepGroup.stepGroup 2).index = 3 ∧
  (StepGroup.stepGroup 3).index = 8 ∧ (StepGroup.stepGroup 4).index = 12 ∧
  (∀ μ : ℤ, 5 ≤ μ → (StepGroup.stepGroup μ).index = 0) ∧
  StepGroup.Kz * StepGroup.Mz 1 * StepGroup.Kz = StepGroup.Mz 1 * StepGroup.Kz * StepGroup.Mz 1 ∧
  (StepGroup.Kz * StepGroup.Mz 1 * StepGroup.Kz) ^ 4 = 1 ∧
  (StepGroup.Mz 2 * StepGroup.Kz) ^ 4 = 1 ∧
  (StepGroup.Mz 2 * StepGroup.Kz) ^ 2 * StepGroup.Kz =
    StepGroup.Kz * (StepGroup.Mz 2 * StepGroup.Kz) ^ 2 ∧
  (StepGroup.Mz 3 * StepGroup.Kz) ^ 3 = 1

/-- **T13** (Theorem Q, part 3; finding 037). For every real `μ ≥ 4` the kick and the move generate
a free group. For a positive integer `μ`, they do exactly when `μ ≥ 4`. -/
@[ledger "T13"]
def stepGroupsFree : Prop :=
  (∀ μ : ℝ, 4 ≤ μ → Function.Injective
    (FreeGroup.lift ![(Step.kick (1 : ℝ)).sl, (Step.move (-μ)).sl])) ∧
  ∀ μ : ℕ, 1 ≤ μ →
    (Function.Injective (FreeGroup.lift ![StepGroup.Kz, StepGroup.Mz μ]) ↔ 4 ≤ μ)

/-- **T13** (Theorem U, part 1; finding 038, after Klein). For `n ≥ 3` the map of the dial `Z/n` is
a regular map of type `{3, n}`. `PSL(2, Z/n)` acts simply transitively on the directed edges: each
law gives the directed edge of its columns, every directed edge is one law's, and two laws have one
directed edge exactly when they are one element of `PSL(2, Z/n)`. The counts: one directed edge per
element, `|PSL| = V n = 2 E = 3 F`, so `(V - E + F) · 6 n = |PSL| (6 - n)`. `E` has `n` neighbours.
The triangles of the graph are the faces, the two faces `{u, v, u ± v}` on an edge differ, and the
action keeps the edges and the faces. -/
@[ledger "T13"]
def regularMap : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∀ g : SpecialLinearGroup (Fin 2) (ZMod n), Klein.toDir g ∈ Klein.dirEdges n) ∧
    (∀ p ∈ Klein.dirEdges n, ∃ g : SpecialLinearGroup (Fin 2) (ZMod n), Klein.toDir g = p) ∧
    (∀ g h : SpecialLinearGroup (Fin 2) (ZMod n),
      Klein.toDir g = Klein.toDir h ↔ (g : Bells.PSLZ n) = (h : Bells.PSLZ n)) ∧
    Nat.card (Bells.PSLZ n) = (Klein.dirEdges n).ncard ∧
    Nat.card (Bells.PSLZ n) = (Klein.vertices n).ncard * n ∧
    Nat.card (Bells.PSLZ n) = (Klein.edges n).ncard * 2 ∧
    Nat.card (Bells.PSLZ n) = (Klein.faces n).ncard * 3 ∧
    (((Klein.vertices n).ncard : ℤ) - (Klein.edges n).ncard + (Klein.faces n).ncard) * (6 * n) =
      Nat.card (Bells.PSLZ n) * (6 - n) ∧
    (Klein.neighbours (Klein.cls (Klein.eE : Klein.State n))).ncard = n ∧
    (∀ u v w : Klein.State n, Klein.det2 u v = 1 →
      (Klein.det2 u w = 1 ∨ Klein.det2 u w = -1) → (Klein.det2 v w = 1 ∨ Klein.det2 v w = -1) →
        ({Klein.cls u, Klein.cls v, Klein.cls w} : Set (Klein.Cls n)) ∈ Klein.faces n) ∧
    (∀ u v : Klein.State n, Klein.det2 u v = 1 → Klein.cls (u + v) ≠ Klein.cls (u - v)) ∧
    (∀ (g : SpecialLinearGroup (Fin 2) (ZMod n)), ∀ S ∈ Klein.edges n, g • S ∈ Klein.edges n) ∧
    ∀ (g : SpecialLinearGroup (Fin 2) (ZMod n)), ∀ S ∈ Klein.faces n, g • S ∈ Klein.faces n

/-- **T13** (Theorem U, part 1; finding 038). The dials `n = 3, 4, 5` give the tetrahedron, the
octahedron and the icosahedron: `|PSL| = 12, 24, 60`, with `(V, E, F) = (4, 6, 4)`, `(6, 12, 8)` and
`(12, 30, 20)`. -/
@[ledger "T13"]
def platonicSolids : Prop :=
  (Nat.card (Bells.PSLZ 3) = 12 ∧ (Klein.vertices 3).ncard = 4 ∧ (Klein.edges 3).ncard = 6 ∧
    (Klein.faces 3).ncard = 4) ∧
  (Nat.card (Bells.PSLZ 4) = 24 ∧ (Klein.vertices 4).ncard = 6 ∧ (Klein.edges 4).ncard = 12 ∧
    (Klein.faces 4).ncard = 8) ∧
  (Nat.card (Bells.PSLZ 5) = 60 ∧ (Klein.vertices 5).ncard = 12 ∧ (Klein.edges 5).ncard = 30 ∧
    (Klein.faces 5).ncard = 20)

/-- **T13** (Theorem U, parts 2 and 3; finding 038). The kick fixes `E` and turns its link
`[1 : e] ↦ [1 : e + κ]`; the move fixes `B` and turns its link `[b : 1] ↦ [b - ℓ : 1]`; `E` and `B`
are adjacent. A kick moves a state `(b, e)` along an edge exactly when `κ b² = ±1`, and a move when
`ℓ e² = ±1`, since `det(v, K v) = κ b²` and `det(v, M v) = ℓ e²`. Every unit squares to `±1` exactly
on the dials `1, 2, 3, 4, 5, 6, 8, 10, 12` and `24`. -/
@[ledger "T13"]
def stepsAreTurns : Prop :=
  (∀ (n : ℕ) (κ ℓ : ZMod n),
    Klein.act (Step.kick κ).sl Klein.eE = Klein.eE ∧
    (∀ e : ZMod n, Klein.act (Step.kick κ).sl (1, e) = (1, e + κ)) ∧
    Klein.act (Step.move (-ℓ)).sl Klein.eB = Klein.eB ∧
    (∀ b : ZMod n, Klein.act (Step.move (-ℓ)).sl (b, 1) = (b - ℓ, 1)) ∧
    Klein.det2 (Klein.eE : Klein.State n) Klein.eB = -1 ∧
    (∀ u : Klein.State n, Klein.det2 u (Klein.act (Step.kick κ).sl u) = κ * u.1 ^ 2) ∧
    ∀ u : Klein.State n, Klein.det2 u (Klein.act (Step.move (-ℓ)).sl u) = ℓ * u.2 ^ 2) ∧
  ∀ n : ℕ, n ≠ 0 → ((∀ u : (ZMod n)ˣ, (u : ZMod n) ^ 2 = 1 ∨ (u : ZMod n) ^ 2 = -1) ↔
    n ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12, 24])

/-- **T13** (Theorem U, parts 4 and 5; finding 038). A law that fixes a vertex has the trace `±2`,
one that fixes an edge `0` or `±2`, and one that fixes a face `±1` or `±2`; the tick `T_μ` has the
trace `2 - μ`. So a fixed cell needs `μ ≡ 0, 1, 2, 3, 4` modulo `n`, and each of these fixes a cell
on every dial: `E`; the face `{B, E, [1 : -1]}`; the edge `{B, [1 : -1]}`; the face
`{B, [-2 : 1], [1 : -1]}`; and the vertex `[-2 : 1]`. The exploding mode `μ = 8` fixes no cell for
`n ≥ 9`. It is an edge flip on `C₃`, the turn about `E` on `C₄`, and a face turn on `C₅`, and its
orders on `C₃₆`, `C₁₂₀`, `C₃₆₀` and `C₃₆₀₀` are `12, 24, 24` and `240`. -/
@[ledger "T13"]
def tickCells : Prop :=
  (∀ (n : ℕ) (g : SpecialLinearGroup (Fin 2) (ZMod n)), ∀ x ∈ Klein.vertices n, g • x = x →
    Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2) ∧
  (∀ (n : ℕ) (g : SpecialLinearGroup (Fin 2) (ZMod n)), ∀ S ∈ Klein.edges n, g • S = S →
    Matrix.trace g.1 = 0 ∨ Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ (g : SpecialLinearGroup (Fin 2) (ZMod n)), ∀ S ∈ Klein.faces n, g • S = S →
    Matrix.trace g.1 = 1 ∨ Matrix.trace g.1 = -1 ∨ Matrix.trace g.1 = 2 ∨ Matrix.trace g.1 = -2) ∧
  (∀ (n : ℕ) (μ : ZMod n), Matrix.trace (Klein.tickN μ).1 = 2 - μ) ∧
  (∀ n : ℕ,
    Klein.tickN (0 : ZMod n) • Klein.cls (Klein.eE : Klein.State n) = Klein.cls Klein.eE ∧
    Klein.tickN (1 : ZMod n) •
      ({Klein.cls Klein.eB, Klein.cls Klein.eE, Klein.cls ((1, -1) : Klein.State n)} :
        Set (Klein.Cls n)) =
      {Klein.cls Klein.eB, Klein.cls Klein.eE, Klein.cls ((1, -1) : Klein.State n)} ∧
    Klein.tickN (2 : ZMod n) •
      ({Klein.cls Klein.eB, Klein.cls ((1, -1) : Klein.State n)} : Set (Klein.Cls n)) =
      {Klein.cls Klein.eB, Klein.cls ((1, -1) : Klein.State n)} ∧
    Klein.tickN (3 : ZMod n) •
      ({Klein.cls Klein.eB, Klein.cls ((-2, 1) : Klein.State n),
        Klein.cls ((1, -1) : Klein.State n)} : Set (Klein.Cls n)) =
      {Klein.cls Klein.eB, Klein.cls ((-2, 1) : Klein.State n),
        Klein.cls ((1, -1) : Klein.State n)} ∧
    Klein.tickN (4 : ZMod n) • Klein.cls ((-2, 1) : Klein.State n) =
      Klein.cls ((-2, 1) : Klein.State n)) ∧
  (∀ n : ℕ, 9 ≤ n →
    (∀ x ∈ Klein.vertices n, Klein.tickN (8 : ZMod n) • x ≠ x) ∧
    (∀ S ∈ Klein.edges n, Klein.tickN (8 : ZMod n) • S ≠ S) ∧
    ∀ S ∈ Klein.faces n, Klein.tickN (8 : ZMod n) • S ≠ S) ∧
  (Klein.tickN (8 : ZMod 3) •
      ({Klein.cls Klein.eB, Klein.cls ((1, -1) : Klein.State 3)} : Set (Klein.Cls 3)) =
      {Klein.cls Klein.eB, Klein.cls ((1, -1) : Klein.State 3)} ∧
    Klein.tickN (8 : ZMod 4) • Klein.cls (Klein.eE : Klein.State 4) = Klein.cls Klein.eE ∧
    Klein.tickN (8 : ZMod 5) •
      ({Klein.cls Klein.eB, Klein.cls ((-2, 1) : Klein.State 5),
        Klein.cls ((1, -1) : Klein.State 5)} : Set (Klein.Cls 5)) =
      {Klein.cls Klein.eB, Klein.cls ((-2, 1) : Klein.State 5),
        Klein.cls ((1, -1) : Klein.State 5)}) ∧
  orderOf (Klein.tickN (8 : ZMod 36)) = 12 ∧ orderOf (Klein.tickN (8 : ZMod 120)) = 24 ∧
    orderOf (Klein.tickN (8 : ZMod 360)) = 24 ∧ orderOf (Klein.tickN (8 : ZMod 3600)) = 240

/-- **T13** (Theorem Y; finding 038). The two squares are the projective line over `F₅`.
1. With the labelling `v₀ ↦ ∞`, `v_k ↦ k - 1`, `L` is `x ↦ 1 / (2 x + 1)` and `R` is `x ↦ 2 x + 3`.
   They generate `PGL(2, 5)`, the image of `GL(2, 5)` on the projective line: `120` elements, and
   isomorphic to `S₅`.
2. The labellings that make `L` and `R` Möbius maps are the book's labelling followed by an element
   of `PGL(2, 5)`: `120` of them, and only the book's has `v₀, v₁, v₂` at `∞, 0, 1`.
3. `R ∘ L` is the kick of strength `2`, `x ↦ x / (2 x + 1)`. It moves the ring
   `v₀ → v₄ → v₅ → v₂ → v₃ → v₀` and fixes `v₁`, and its order is `5`.
4. `det L = 3` and `det R = 2` are not squares mod `5`. Each turn carries the pairs of determinant
   `±1` onto those of determinant `±2`, and back. A law of square determinant acts as an element of
   `SL(2, 5)`, and each product of two turns has a square determinant. -/
@[ledger "T13"]
def twoSquaresProjective : Prop :=
  (∀ i, Bells.corner (Bells.squareL i) = Bells.matL • Bells.corner i) ∧
  (∀ i, Bells.corner (Bells.squareR i) = Bells.matR • Bells.corner i) ∧
  Bells.twoSquares.map Bells.toLine.toMonoidHom = Bells.rho.range ∧
  Nat.card Bells.twoSquares = 120 ∧
  Nonempty (Bells.twoSquares ≃* Equiv.Perm (Fin 5)) ∧
  (∀ c, Bells.IsMobiusLabelling c ↔ ∃ g, ∀ i, c i = Bells.rho g (Bells.corner i)) ∧
  {c | Bells.IsMobiusLabelling c}.ncard = 120 ∧
  (∀ c, Bells.IsMobiusLabelling c → c 0 = Bells.corner 0 → c 1 = Bells.corner 1 →
    c 2 = Bells.corner 2 → c = Bells.corner) ∧
  Bells.corner.permCongr (Bells.squareR * Bells.squareL) = Bells.rho Bells.matK2 ∧
  ((Bells.squareR * Bells.squareL) 0 = 4 ∧ (Bells.squareR * Bells.squareL) 4 = 5 ∧
    (Bells.squareR * Bells.squareL) 5 = 2 ∧ (Bells.squareR * Bells.squareL) 2 = 3 ∧
    (Bells.squareR * Bells.squareL) 3 = 0 ∧ (Bells.squareR * Bells.squareL) 1 = 1) ∧
  orderOf (Bells.squareR * Bells.squareL) = 5 ∧
  (Bells.matL.det = (3 : Bells.K5) ∧ ¬ IsSquare (3 : Bells.K5) ∧ Bells.matR.det = (2 : Bells.K5) ∧
    ¬ IsSquare (2 : Bells.K5)) ∧
  (∀ u v : Bells.K5 × Bells.K5,
    ((Bells.detK5 u v = 1 ∨ Bells.detK5 u v = -1) →
      (Bells.detK5 (Bells.stateL u) (Bells.stateL v) = 2 ∨
        Bells.detK5 (Bells.stateL u) (Bells.stateL v) = -2) ∧
      (Bells.detK5 (Bells.stateR u) (Bells.stateR v) = 2 ∨
        Bells.detK5 (Bells.stateR u) (Bells.stateR v) = -2)) ∧
    ((Bells.detK5 u v = 2 ∨ Bells.detK5 u v = -2) →
      (Bells.detK5 (Bells.stateL u) (Bells.stateL v) = 1 ∨
        Bells.detK5 (Bells.stateL u) (Bells.stateL v) = -1) ∧
      (Bells.detK5 (Bells.stateR u) (Bells.stateR v) = 1 ∨
        Bells.detK5 (Bells.stateR u) (Bells.stateR v) = -1))) ∧
  (∀ g : Matrix.GeneralLinearGroup (Fin 2) Bells.K5, IsSquare (g.1.det) →
    ∃ s : SpecialLinearGroup (Fin 2) Bells.K5,
      Bells.rho g = Bells.rho (s : Matrix.GeneralLinearGroup (Fin 2) Bells.K5)) ∧
  (IsSquare (Bells.matL * Bells.matL).1.det ∧ IsSquare (Bells.matL * Bells.matR).1.det ∧
    IsSquare (Bells.matR * Bells.matL).1.det ∧ IsSquare (Bells.matR * Bells.matR).1.det)

/-- **R2** (commutation; Steinberg's relations). On `c` channels: merging; `e_ij(0) = 1`; steps
`e_ij(f)` and `e_kl(g)` with `j ≠ k` and `i ≠ l` commute; and for distinct `i, j, k` the commutator
of the laws, `e_ij(f) e_jk(g) e_ij(-f) e_jk(-g)` as matrices, is `e_ik(f g)`. A score runs in time
order, so that law is the score `e_jk(-g), e_ij(-f), e_jk(g), e_ij(f)`, and the score
`e_ij(f), e_jk(g), e_ij(-f), e_jk(-g)` has the law `e_ik(-f g)`. -/
@[ledger "R2"]
def steinbergRules : Prop :=
  ∀ (S : Type) [CommRing S] (c : ℕ) (i j k l : Fin c) (f g : S),
    (i ≠ j → realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨i, j, g⟩] = realizeC [⟨i, j, f + g⟩]) ∧
    realizeC [(⟨i, j, 0⟩ : ChanStep c S)] = 1 ∧
    (j ≠ k → i ≠ l → realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨k, l, g⟩] =
      realizeC [⟨k, l, g⟩, ⟨i, j, f⟩]) ∧
    (i ≠ j → j ≠ k → i ≠ k →
      Matrix.transvection i j f * Matrix.transvection j k g * Matrix.transvection i j (-f) *
        Matrix.transvection j k (-g) = Matrix.transvection i k (f * g) ∧
      realizeC [(⟨j, k, -g⟩ : ChanStep c S), ⟨i, j, -f⟩, ⟨j, k, g⟩, ⟨i, j, f⟩] =
        (⟨i, k, f * g⟩ : ChanStep c S).mat ∧
      realizeC [(⟨i, j, f⟩ : ChanStep c S), ⟨j, k, g⟩, ⟨i, j, -f⟩, ⟨j, k, -g⟩] =
        (⟨i, k, -(f * g)⟩ : ChanStep c S).mat)

/-- **T1** (the fewest steps). A law is one step exactly when it is a shear, and a score of at most
two steps exactly when `a = 1` or `d = 1`. So every other law needs three or more, and Strang's
`K(k), M(m), K(k)` with `k m ≠ 0` needs three. -/
@[ledger "T1"]
def fewestSteps : Prop :=
  ∀ (S : Type) [CommRing S],
    (∀ T : SpecialLinearGroup (Fin 2) S, (∃ s : Step S, s.sl = T) ↔
      T.1 0 0 = 1 ∧ T.1 1 1 = 1 ∧ (T.1 0 1 = 0 ∨ T.1 1 0 = 0)) ∧
    (∀ T : SpecialLinearGroup (Fin 2) S, (∃ w : Score S, w.length ≤ 2 ∧ realize w = T) ↔
      T.1 0 0 = 1 ∨ T.1 1 1 = 1) ∧
    ∀ k m : S, k * m ≠ 0 → ∀ w : Score S,
      realize w = realize [Step.kick k, Step.move m, Step.kick k] → 3 ≤ w.length

/-- **T2** (the index as a group). Over a field `F`, with `S = F[x, 1/x]`: `E₂(S)` is the kernel of
the determinant on `GL₂(S)`, and the determinant is onto, so `GL₂(S)/E₂(S) ≅ S*`. The units of `S`
are the monomials `r xᵏ`. The balanced pair `diag(x, 1/x)` is a score of six shears. -/
@[ledger "T2"]
def indexGroup : Prop :=
  ∀ (F : Type) [Field F],
    elementary (LaurentPolynomial F) = (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial F) →* (LaurentPolynomial F)ˣ).ker ∧
    Function.Surjective (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial F) →* (LaurentPolynomial F)ˣ) ∧
    (∀ u : (LaurentPolynomial F)ˣ, ∃ (r : Fˣ) (k : ℤ),
      (u : LaurentPolynomial F) = LaurentPolynomial.C (r : F) * LaurentPolynomial.T k) ∧
    (∀ (r : Fˣ) (k : ℤ), IsUnit (LaurentPolynomial.C (r : F) * LaurentPolynomial.T k)) ∧
    ∃ w : Score (LaurentPolynomial F), w.length = 6 ∧
      (realize w : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
        !![LaurentPolynomial.T 1, 0; 0, LaurentPolynomial.T (-1)]

/-- **T11** (face and link; finding 064, Theorem S3.10). Take any score of constant kicks `K(w κ)`
and moves `M(-w ℓ g)`, `g = D D*`, and its link form, with the kicks `K(w κ D*)` and the moves
`M(-w ℓ D)`. Then `T_link Λ = Λ T_face` with `Λ = diag(1, D*)`, so `a` is the same, and `c_link =
D* c` and `b = D* b_link`. At the zero mode `x = 1` the link form is the identity (unglued), and
the face form is the kick of the total weight, glued when that is not zero. Over a domain, the two
have one phase, and the link ideal lies between `D*` times the face ideal and the face ideal. -/
@[ledger "T11"]
def faceAndLink : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (κ ℓ : R) (w : List (Step R)),
    let Tf := realize (w.map (faceStep κ ℓ))
    let Tl := realize (w.map (linkStep κ ℓ))
    Tl.1 * lambdaMat R = lambdaMat R * Tf.1 ∧
    Tl.1 0 0 = Tf.1 0 0 ∧ Tl.1 1 0 = diffDs R * Tf.1 1 0 ∧ Tf.1 0 1 = Tl.1 0 1 * diffDs R ∧
    Tl.1 1 1 = Tf.1 1 1 ∧
    Matrix.SpecialLinearGroup.map (atZero R) Tl = 1 ∧
    (Matrix.SpecialLinearGroup.map (atZero R) Tf).1 = !![1, 0; totalKick w * κ, 1] ∧
    ∀ t : LaurentPolynomial R, lawIdeal t Tl.1 ≤ lawIdeal t Tf.1 ∧
      Ideal.span {algebraMap _ (curveRing t) (diffDs R)} * lawIdeal t Tf.1 ≤ lawIdeal t Tl.1

/-- **T12** (the criterion for palindromes). Over a principal ideal domain in which `2` is
invertible, a law is processing-equivalent to a palindrome exactly when some invertible `P`
reverses it, `P T P⁻¹ = T⁻¹`, with `-det P` a square. So a palindrome's class is fixed by time
reversal. The converse needs the square: on some dials a class that time reversal fixes holds no
palindrome. -/
@[ledger "T12"]
def palindromeCriterion : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Invertible (2 : S)]
    (T : SpecialLinearGroup (Fin 2) S),
    (∃ Q : Matrix.GeneralLinearGroup (Fin 2) S,
      (Q.1 * T.1 * (Q⁻¹ : Matrix.GeneralLinearGroup (Fin 2) S).1) 0 0 =
        (Q.1 * T.1 * (Q⁻¹ : Matrix.GeneralLinearGroup (Fin 2) S).1) 1 1) ↔
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) S,
      P.1 * T.1 = ((T⁻¹ : SpecialLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) * P.1 ∧
      IsSquare (-(P.1.det))

/-- **T14** (the caller's rule; finding 080, Theorem S8.5). A caller that reads two equally
prepared response cells calls `xy` with the share of the patterns that its rule sends there. The
book's rule, turn on `11`, has the share `1/4`, and leaves the cut `-h²(g_x - g_y)/4`. The rules
"turn on `a = 1`" and "turn on `a ≠ b`" have the share `1/2`, and leave no cut. -/
@[ledger "T14"]
def callerRules : Prop :=
  share turnOn11 = 1 / 4 ∧ share turnOnA = 1 / 2 ∧ share turnOnNe = 1 / 2 ∧
  ∀ (K : Type) [Field K] [CharZero K] (h gx gy : K),
    cut (((share turnOn11 : ℚ) : K) • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
      (1 - ((share turnOn11 : ℚ) : K)) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) =
        -(h ^ 2 * (gx - gy) / 4) ∧
    cut (((share turnOnA : ℚ) : K) • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
      (1 - ((share turnOnA : ℚ) : K)) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) = 0 ∧
    cut (((share turnOnNe : ℚ) : K) • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
      (1 - ((share turnOnNe : ℚ) : K)) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) = 0

/-- **T14** (one cue; finding 080, Theorem S8.6). Multiplication by the indicator of a set `X` of
cells commutes with the shift by `w` exactly when `X` is invariant under `w`, and with all the
shifts exactly when `X` is empty or everything. So a kick placed by one cue for all the faces of a
colour is a stencil on the blocked artform, and a kick placed by a coin per face is none. -/
@[ledger "T14"]
def oneCue : Prop :=
  ∀ (Λ R : Type) [AddCommGroup Λ] [CommRing R] [Nontrivial R] (X : Set Λ),
    (∀ w : Λ, (∀ u : Λ → R, shiftField w (maskField X u) = maskField X (shiftField w u)) ↔
      ∀ z, z + w ∈ X ↔ z ∈ X) ∧
    ((∀ (w : Λ) (u : Λ → R), shiftField w (maskField X u) = maskField X (shiftField w u)) ↔
      X = ∅ ∨ X = Set.univ)

/-- **T16** (the duet; the book's `06-controller`). The cue is read from two equally prepared cells,
`orbit` on `11`. Read by both dancers, they never disagree, and both orbit on one pattern of four.
With a coin each, they disagree on `6` of `16` patterns, and both orbit on one of `16`. Two choices
from independent sources that agree every time are fixed: they can agree and vary only through a
cause they share. -/
@[ledger "T16"]
def duet : Prop :=
  (Finset.univ.filter fun p : Bool × Bool => turnOn11 p ≠ turnOn11 p).card = 0 ∧
  (Finset.univ.filter fun p : Bool × Bool => turnOn11 p = true ∧ turnOn11 p = true).card = 1 ∧
  (Finset.univ.filter fun p : (Bool × Bool) × (Bool × Bool) =>
    turnOn11 p.1 ≠ turnOn11 p.2).card = 6 ∧
  (Finset.univ.filter fun p : (Bool × Bool) × (Bool × Bool) =>
    turnOn11 p.1 = true ∧ turnOn11 p.2 = true).card = 1 ∧
  ∀ (Ω₁ Ω₂ α : Type) [Nonempty Ω₁] [Nonempty Ω₂] (f : Ω₁ → α) (g : Ω₂ → α),
    (∀ ω₁ ω₂, f ω₁ = g ω₂) → ∃ a, (∀ ω, f ω = a) ∧ ∀ ω, g ω = a

/-- **T8** (the curve of the leapfrog phase; finding 057, Theorem S3.4, part 1). With `q = κ ℓ`
different from `0` and `1`, the curve `λ + 1/λ = 2 - q (2 - x - 1/x)` is rational. The point `s` of
the line, other than `0`, `1` and `q`, goes to `x = q (1 - s) / (s (s - q))` and
`λ = s (1 - s) / (s - q)`, a point of the curve. Conversely `s = (λ - 1) / (x - 1)` is the inverse,
at every point of the curve with `x ≠ 1`. Over `x = 1` the curve has the one point `λ = 1`, the
node, and the line has the two points `s² = q`, its two branches. -/
@[ledger "T8"]
def leapfrogCurve : Prop :=
  ∀ (K : Type) [Field K] (q : K), q ≠ 0 → q ≠ 1 →
    (∀ s : K, s ≠ 0 → s ≠ 1 → s ≠ q →
      let x := q * (1 - s) / (s * (s - q))
      let l := s * (1 - s) / (s - q)
      x ≠ 0 ∧ l ≠ 0 ∧ l + l⁻¹ = 2 - q * (2 - x - x⁻¹) ∧ (x = 1 ↔ s * s = q)) ∧
    (∀ x l : K, x ≠ 0 → l ≠ 0 → l + l⁻¹ = 2 - q * (2 - x - x⁻¹) → x ≠ 1 →
      let s := (l - 1) / (x - 1)
      s ≠ 0 ∧ s ≠ 1 ∧ s ≠ q ∧ x = q * (1 - s) / (s * (s - q)) ∧ l = s * (1 - s) / (s - q)) ∧
    (∀ l : K, l ≠ 0 → l + l⁻¹ = 2 - q * (2 - 1 - 1⁻¹) → l = 1)

/-- **T8** (the classes of the leapfrog phase; finding 057, Theorem S3.4). Over a field of
characteristic not `2`, with `q = κ ℓ` different from `0` and `1`, the discriminant of the phase
`t = 2 - q g` is not a square, so T7 applies, and the laws of the phase, up to processing, are one
to one with `U/⟨-1, ρ⟩` and one more class: the glued classes and the unglued one. The law `L` is
unglued exactly when it is the identity at the zero mode. It has the trivial class exactly when it
has a cyclic vector. Time reversal inverts the class. The law `gluedLaw q y` has the class of
`z / z̄`, with `z = y + r`, and `ungluedLaw q` the unglued one, which pins the map on every
class. -/
@[ledger "T8"]
def leapfrogClasses : Prop :=
  ∀ (F : Type) [Field F] (q : F), (2 : F) ≠ 0 → q ≠ 0 → q ≠ 1 →
    NonSquareDisc (Leapfrog.phaseT q) ∧
    (∀ y, phase (Leapfrog.gluedLaw q y) = Leapfrog.phaseT q) ∧
    phase (Leapfrog.ungluedLaw q) = Leapfrog.phaseT q ∧
    ∃ Φ : SpecialLinearGroup (Fin 2) (LaurentPolynomial F) →
        Option (Leapfrog.U q ⧸ Leapfrog.gluing q),
      (∀ L L', phase L = Leapfrog.phaseT q → phase L' = Leapfrog.phaseT q →
        (Φ L = Φ L' ↔ Processed L L')) ∧
      (∀ w, ∃ L, phase L = Leapfrog.phaseT q ∧ Φ L = w) ∧
      (∀ L, phase L = Leapfrog.phaseT q →
        (Φ L = none ↔ Matrix.SpecialLinearGroup.map (atZero F) L = 1)) ∧
      (∀ L, phase L = Leapfrog.phaseT q → (Φ L = some 1 ↔ ∃ v,
        IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det)) ∧
      (∀ L, phase L = Leapfrog.phaseT q → Φ L⁻¹ = (Φ L).map (·⁻¹)) ∧
      (∀ (y : F) (z : (Leapfrog.Fib q)ˣ), (z : Leapfrog.Fib q) =
          algebraMap F (Leapfrog.Fib q) y + Leapfrog.rE →
        Φ (Leapfrog.gluedLaw q y) = some (Leapfrog.theta z : Leapfrog.U q)) ∧
      Φ (Leapfrog.ungluedLaw q) = none

/-- **T8** (the count; finding 057, Theorem S3.4). Over a finite field of characteristic not `2`,
with `q` different from `0` and `1`, there are `|U| / |⟨-1, ρ⟩|` glued classes and one unglued, and
`|U|` is `|F| - 1` when `q` is a square and `|F| + 1` when it is not. The subgroup `⟨-1, ρ⟩` has at
least four elements, so at most `|U| / 4` classes are glued, and exactly four when `q = -1`. -/
@[ledger "T8"]
def leapfrogCount : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : F), (2 : F) ≠ 0 → q ≠ 0 → q ≠ 1 →
    Nat.card (Quotient (processingSetoid (Leapfrog.phaseT q))) =
      Nat.card (Leapfrog.U q) / Nat.card (Leapfrog.gluing q) + 1 ∧
    (IsSquare q → Nat.card (Leapfrog.U q) = Nat.card F - 1) ∧
    (¬ IsSquare q → Nat.card (Leapfrog.U q) = Nat.card F + 1) ∧
    4 ≤ Nat.card (Leapfrog.gluing q) ∧ (Nat.card (Leapfrog.gluing q) = 4 ↔ q = -1)

/-- **T8** (the split node; finding 057, Theorem S3.4). When `q = h²` in `F`, evaluation at `h`
identifies `U` with the units of `F` and `⟨-1, ρ⟩` with `⟨-1, (1 - h)/(1 + h)⟩`. -/
@[ledger "T8"]
def leapfrogSplit : Prop :=
  ∀ (F : Type) [Field F] (q h : F), (2 : F) ≠ 0 → q ≠ 0 → q ≠ 1 → h * h = q →
    ∃ e : Leapfrog.U q ≃* Fˣ,
      (∀ u : Leapfrog.U q, ((e u : Fˣ) : F) =
        ((u : (Leapfrog.Fib q)ˣ) : Leapfrog.Fib q).re +
          ((u : (Leapfrog.Fib q)ˣ) : Leapfrog.Fib q).im * h) ∧
      (Leapfrog.gluing q).map e.toMonoidHom =
        Subgroup.closure {x : Fˣ | (x : F) = -1 ∨ (x : F) * (1 + h) = 1 - h}

/-- **T8** (the schemes; finding 057, Theorem S3.4, part 4). With `κ ℓ` different from `0` and `1`,
the face form of the book's tick, of `M K`, of Strang and of position Verlet has the leapfrog phase
and is processed from the companion tick, the trivial class. The link form of each has the same
phase and is processed from `ungluedLaw`, the unglued class. -/
@[ledger "T8"]
def leapfrogSchemes : Prop :=
  ∀ (F : Type) [Field F] (κ ℓ : F), (2 : F) ≠ 0 → κ * ℓ ≠ 0 → κ * ℓ ≠ 1 →
    ∀ w ∈ Leapfrog.schemes F,
      phase (realize (w.map (faceStep κ ℓ))) = Leapfrog.phaseT (κ * ℓ) ∧
      Processed (Leapfrog.companionLaw (κ * ℓ)) (realize (w.map (faceStep κ ℓ))) ∧
      phase (realize (w.map (linkStep κ ℓ))) = Leapfrog.phaseT (κ * ℓ) ∧
      Processed (Leapfrog.ungluedLaw (κ * ℓ)) (realize (w.map (linkStep κ ℓ)))

/-- **T8** (the magic step; finding 057, Theorem S3.5). At `κ ℓ = 1` the phase is `x + 1/x`, and
every law is processed from a normal form `[[x, 0], [w, 1/x]]`, whose class is read from the values
of `w` at the two crossings `x = 1` and `x = -1`. The classes are those glued at both crossings,
`F^×/{±1}`, by the ratio of the values, and one each glued at `x = 1` only, at `x = -1` only and at
neither. A law is the identity at `x = 1` exactly when `w` vanishes there, and `-1` at `x = -1`
exactly when `w` vanishes there. The trivial class, glued at both with the ratio `1`, is the class
of the laws with a cyclic vector. -/
@[ledger "T8"]
def magicClasses : Prop :=
  ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    ∃ Φ : SpecialLinearGroup (Fin 2) (LaurentPolynomial F) →
        (Fˣ ⧸ Leapfrog.signs F) ⊕ Fin 3,
      (∀ L L', phase L = Leapfrog.phaseT (1 : F) → phase L' = Leapfrog.phaseT (1 : F) →
        (Φ L = Φ L' ↔ Processed L L')) ∧
      (∀ w, phase (Leapfrog.magicLaw w) = Leapfrog.phaseT (1 : F) ∧
        Φ (Leapfrog.magicLaw w) = Leapfrog.ofPair (atZero F w) (Leapfrog.atPi F w)) ∧
      (∀ c, ∃ w, Leapfrog.ofPair (atZero F w) (Leapfrog.atPi F w) = c) ∧
      (∀ L, phase L = Leapfrog.phaseT (1 : F) → ∃ w, Processed (Leapfrog.magicLaw w) L) ∧
      (∀ L w, Processed (Leapfrog.magicLaw w) L →
        ((L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map (atZero F) = 1 ↔
          atZero F w = 0) ∧
        ((L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map (Leapfrog.atPi F) = -1 ↔
          Leapfrog.atPi F w = 0)) ∧
      (∀ L, phase L = Leapfrog.phaseT (1 : F) → (Φ L = Sum.inl 1 ↔ ∃ v,
        IsUnit (cyclicMatrix (L : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det))

/-- **T8** (the count at the magic step; finding 057, Theorem S3.5). On a dial `C_p` there are
`(p - 1)/2 + 3` classes: over a finite field `F` of characteristic not `2`, `(|F| - 1)/2 + 3`. -/
@[ledger "T8"]
def magicCount : Prop :=
  ∀ (F : Type) [Field F] [Finite F], (2 : F) ≠ 0 →
    Nat.card (Quotient (processingSetoid (Leapfrog.phaseT (1 : F)))) = (Nat.card F - 1) / 2 + 3

/-- **T8** (the schemes at the magic step; finding 057, Theorem S3.5). With `κ ℓ = 1`, each face
form of the book's schemes has a cyclic vector, so the trivial class. The link form of each is the
identity at `x = 1` and not `-1` at `x = -1`: glued at `x = -1` only. The split movers
`diag(x, 1/x)` are the normal form of `w = 0`, glued at neither. -/
@[ledger "T8"]
def magicSchemes : Prop :=
  ∀ (F : Type) [Field F] (κ ℓ : F), (2 : F) ≠ 0 → κ * ℓ = 1 →
    (∀ w ∈ Leapfrog.schemes F,
      phase (realize (w.map (faceStep κ ℓ))) = Leapfrog.phaseT (1 : F) ∧
      (∃ v, IsUnit (cyclicMatrix (realize (w.map (faceStep κ ℓ)) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) v).det) ∧
      phase (realize (w.map (linkStep κ ℓ))) = Leapfrog.phaseT (1 : F) ∧
      (realize (w.map (linkStep κ ℓ)) : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map
        (atZero F) = 1 ∧
      (realize (w.map (linkStep κ ℓ)) : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)).map
        (Leapfrog.atPi F) ≠ -1) ∧
    (Leapfrog.magicLaw (0 : LaurentPolynomial F) : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) =
      !![LaurentPolynomial.T 1, 0; 0, LaurentPolynomial.T (-1)] ∧
    Leapfrog.ofPair (atZero F 0) (Leapfrog.atPi F 0) = Sum.inr 2

/-- **T12** (the palindromes of the leapfrog phase; the correction of 2026-10-30). Over a field of
characteristic not `2`, with `q` different from `0` and `1`, a law of the phase is processed from a
palindrome exactly when it lies in the unglued class, in the trivial class, or, when `1 - q = w²`,
in the class of `r - (1 + w)`, whose `z / z̄` is `κ = (1 - r) / w`, with `κ² = ρ`. -/
@[ledger "T12"]
def leapfrogPalindromes : Prop :=
  ∀ (F : Type) [Field F] (q : F), (2 : F) ≠ 0 → q ≠ 0 → q ≠ 1 →
    ∀ L : SpecialLinearGroup (Fin 2) (LaurentPolynomial F), phase L = Leapfrog.phaseT q →
      ((∃ L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial F),
          (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 0 0 =
            (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial F)) 1 1 ∧ Processed L' L) ↔
        (Processed (Leapfrog.ungluedLaw q) L ∨ Processed (Leapfrog.companionLaw q) L ∨
          ∃ w : F, w * w = 1 - q ∧ Processed (Leapfrog.gluedLaw q (-(1 + w))) L))

/-- **T12** (a fixed class without a palindrome; the correction of 2026-10-30). On the dial `C₁₁` at
`κλ = 8`, the law `gluedLaw 8 5` is processed into its own inverse, and no palindrome is processed
into it: a class that time reversal fixes need not hold a palindrome. -/
@[ledger "T12"]
def palindromeGap : Prop :=
  phase (Leapfrog.gluedLaw (8 : ZMod 11) 5) = Leapfrog.phaseT (8 : ZMod 11) ∧
  Processed (Leapfrog.gluedLaw (8 : ZMod 11) 5) (Leapfrog.gluedLaw (8 : ZMod 11) 5)⁻¹ ∧
  ¬ ∃ L' : SpecialLinearGroup (Fin 2) (LaurentPolynomial (ZMod 11)),
    (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 11))) 0 0 =
      (L' : Matrix (Fin 2) (Fin 2) (LaurentPolynomial (ZMod 11))) 1 1 ∧
    Processed L' (Leapfrog.gluedLaw (8 : ZMod 11) 5)

end Artform.Scores.Statement
