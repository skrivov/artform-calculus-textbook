import ArtformScores.Caller
import ArtformScores.CRT
import ArtformScores.Readings
import ArtformScores.Steinberg
import ArtformScores.KleinMap
import ArtformScores.LeapfrogClasses

/-! # Strengthened statements closing the independent review returns -/
namespace Artform.Scores
open Matrix (SpecialLinearGroup)

/-- An explicit graph identification on primitive states modulo sign. -/
def PrimitiveGraphModel (n N : ℕ) (adj : Fin N → Fin N → Prop) : Prop :=
  ∃ v : Fin N → Klein.State n,
    (∀ i, Klein.IsPrim (v i)) ∧
    (∀ u : Klein.State n, Klein.IsPrim u → ∃! i, u = v i ∨ u = -v i) ∧
    ∀ i j, adj i j ↔ Klein.det2 (v i) (v j) = 1 ∨ Klein.det2 (v i) (v j) = -1

/-- The standard octahedron: three pairs of opposite vertices. -/
def octahedronAdj (i j : Fin 6) : Prop := i.val / 2 ≠ j.val / 2

/-- Edges of the standard icosahedron: two pentagonal rings between the poles. -/
def icosahedronEdge (i j : Fin 12) : Prop :=
  (i = 0 ∧ 2 ≤ j.val ∧ j.val < 7) ∨ (i = 1 ∧ 7 ≤ j.val) ∨
  (2 ≤ i.val ∧ i.val < 7 ∧ 2 ≤ j.val ∧ j.val < 7 ∧ j.val - 2 = (i.val - 2 + 1) % 5) ∨
  (7 ≤ i.val ∧ 7 ≤ j.val ∧ j.val - 7 = (i.val - 7 + 1) % 5) ∨
  (2 ≤ i.val ∧ i.val < 7 ∧ 7 ≤ j.val ∧
    (j.val - 7 = i.val - 2 ∨ j.val - 7 = (i.val - 2 + 4) % 5))

def icosahedronAdj (i j : Fin 12) : Prop := icosahedronEdge i j ∨ icosahedronEdge j i

namespace Statement

/-- **T12** (the complete reading, with the real closed form and repeated-root limits). -/
@[ledger "T12"]
def readingComplete : Prop :=
  readingDetermines ∧
  (∀ (S : Type) [CommRing S] (A B : SpecialLinearGroup (Fin 2) S),
    (phase A = phase B ∧ reading A = reading B) ↔
      ∀ n : ℕ, (A ^ n).1 0 0 = (B ^ n).1 0 0) ∧
  (∀ (A : SpecialLinearGroup (Fin 2) ℝ) (θ : ℝ), phase A = 2 * Real.cos θ →
    Real.sin θ ≠ 0 → ∀ n : ℕ,
    (A ^ n).1 0 0 = Real.cos (n * θ) +
      ((A.1 0 0 - A.1 1 1) / 2) * Real.sin (n * θ) / Real.sin θ) ∧
  (∀ (S : Type) [CommRing S] (A : SpecialLinearGroup (Fin 2) S) (ε : S),
    ε * ε = 1 → phase A = 2 * ε → ∀ n : ℕ,
      (A ^ n).1 0 0 = ε ^ n * (1 + (n : S) * (ε * reading A - 1)))

/-- **T14** (the mean cut and all its zero cases). -/
@[ledger "T14"]
def callerCutComplete : Prop := callerCut ∧
  ∀ (K : Type) [Field K] [CharZero K] (h gx gy q : K),
    (cut (q • (splitTick true h gx gy : Matrix (Fin 2) (Fin 2) K) +
      (1 - q) • (splitTick false h gx gy : Matrix (Fin 2) (Fin 2) K)) = 0 ↔
      q = 1 / 2 ∨ h = 0 ∨ gx = gy)

/-- **T2** (the index over fields and every positive dial). -/
@[ledger "T2"]
def indexGroupComplete : Prop := indexGroup ∧
  ∀ n : ℕ, n ≠ 0 →
    elementary (LaurentPolynomial (ZMod n)) = (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial (ZMod n)) →*
        (LaurentPolynomial (ZMod n))ˣ).ker ∧
    Function.Surjective (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) (LaurentPolynomial (ZMod n)) →*
        (LaurentPolynomial (ZMod n))ˣ)

/-- **T13** (the named Platonic incidence structures, beyond their counts).
The tetrahedron is the complete graph on four vertices; the octahedron has
three opposite pairs; the icosahedron consists of two joined pentagonal rings
and their poles. Faces are their triangles, as in `regularMap`. -/
@[ledger "T13"]
def platonicIncidence : Prop := platonicSolids ∧
  PrimitiveGraphModel 3 4 (fun i j => i ≠ j) ∧
  PrimitiveGraphModel 4 6 octahedronAdj ∧ PrimitiveGraphModel 5 12 icosahedronAdj

/-- **T11** (the normalization comparison). Every score satisfies the original
intertwining theorem. For nonzero total kick, in every normal domain containing
the stencil ring and an eigenvalue, the extended link ideal is exactly `D*`
times the extended face ideal. This is equality up to a principal divisor,
including the normalization of each irreducible component of the phase curve. -/
@[ledger "T11"]
def faceAndLinkNormalization : Prop := faceAndLink ∧
  ∀ (F : Type) [Field F] (κ ℓ : F) (w : Score F), totalKick w * κ ≠ 0 →
    let Tf := realize (w.map (faceStep κ ℓ))
    let Tl := realize (w.map (linkStep κ ℓ))
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
      (ι : LaurentPolynomial F →+* B), Function.Injective ι → ∀ lam : B,
      lam * lam - ι (phase Tf) * lam + 1 = 0 →
      Ideal.span {ι (Tl.1 1 0), lam - ι (Tl.1 0 0)} =
        Ideal.span {ι (diffDs F)} * Ideal.span {ι (Tf.1 1 0), lam - ι (Tf.1 0 0)}

/-- **T8** (normalization, unique singularity and the ordinary node).
An injective integral map into a normal domain, with every target element a
fraction of source elements, is a normalization in the common fraction field.
The tangent polynomial is separable and its split branches are distinct. -/
@[ledger "T8"]
def leapfrogNormalization : Prop := leapfrogCurve ∧
  ∀ (F : Type) [Field F] (q : F), (2 : F) ≠ 0 → q ≠ 0 → q ≠ 1 →
    IsIntegrallyClosed (Leapfrog.Norm q) ∧
    (∃ ι : curveRing (Leapfrog.phaseT q) →+* Leapfrog.Norm q,
      Function.Injective ι ∧
      (∀ z : Leapfrog.Norm q, ∃ p : Polynomial (curveRing (Leapfrog.phaseT q)),
        p.Monic ∧ Polynomial.eval₂ ι z p = 0) ∧
      (∀ z : Leapfrog.Norm q, ∃ a d : curveRing (Leapfrog.phaseT q),
        d ≠ 0 ∧ ι d * z = ι a) ∧
      ι (eig (Leapfrog.phaseT q)) = 1 +
        (ι (algebraMap (LaurentPolynomial F) (curveRing (Leapfrog.phaseT q))
          (LaurentPolynomial.T 1)) - 1) * Leapfrog.sN q) ∧
    (∀ x lam : F, x ≠ 0 → lam ≠ 0 →
      ((x * (lam - 1)^2 - q * (x - 1)^2 * lam = 0 ∧
       (lam - 1)^2 - 2 * q * (x - 1) * lam = 0 ∧
       2 * x * (lam - 1) - q * (x - 1)^2 = 0) ↔ x = 1 ∧ lam = 1)) ∧
    (∀ u v : F,
      (1 + u) * ((1 + v) - 1)^2 - q * ((1 + u) - 1)^2 * (1 + v) =
        v^2 - q * u^2 + u * v^2 - q * u^2 * v) ∧
    (Polynomial.X ^ 2 - Polynomial.C q : Polynomial F).Separable ∧
    ∀ h : F, h * h = q → h ≠ -h ∧ ∀ u v : F,
      v ^ 2 - q * u ^ 2 = (v - h * u) * (v + h * u)

end Statement
end Artform.Scores
