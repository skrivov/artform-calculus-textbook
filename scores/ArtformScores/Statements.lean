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

end Artform.Scores.Statement
