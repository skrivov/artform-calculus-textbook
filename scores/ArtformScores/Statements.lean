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

end Artform.Scores.Statement
