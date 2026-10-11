import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import ArtformTextbook.Ch05.Defs.Affine
import ArtformTextbook.Ch05.Defs.Calculus

/-!
# The canonical pairing of the Maxwell fields (Section 6.4)

A pair `(A, E)` of link tables is written as one table on two copies of the
edges, `K.E ⊕ K.E`: `A` on the left copy and `E` on the right. On these tables
the source-free kick and the Faraday move are additive bijections, and the
tick with a source `J` is an affine law in the sense of Definition 5.5.
-/

namespace Artform

open scoped BigOperators

variable (K : Canvas)

/-- `⟨a, b⟩` on link tables: multiply link by link, each link once in its
stored orientation, and add. -/
def Canvas.linkDot (a b : K.E → ZMod 8) : ZMod 8 := ∑ e, a e * b e

/-- `⟨g, φ⟩` on site functions: multiply site by site and add. -/
def Canvas.siteDot (g φ : K.V → ZMod 8) : ZMod 8 := ∑ v, g v * φ v

/-- The state `(A, E)` as one table on `K.E ⊕ K.E`: `A` on the left copy of
the edges, `E` on the right one. -/
def fieldPair {K : Canvas} (A E : K.E → ZMod 8) : K.E ⊕ K.E → ZMod 8 := Sum.elim A E

/-- The canonical pairing of Lemma 6.5,
`Ω((A, E), (a, e)) = ⟨A, e⟩ − ⟨E, a⟩`, on tables of `K.E ⊕ K.E`. -/
def maxwellOmega : Pairing (K.E ⊕ K.E) 8 :=
  AddMonoidHom.mk'
    (fun p => AddMonoidHom.mk'
      (fun q => K.linkDot (p ∘ Sum.inl) (q ∘ Sum.inr) - K.linkDot (p ∘ Sum.inr) (q ∘ Sum.inl))
      (fun q q' => by
        simp only [Canvas.linkDot, Function.comp_apply, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
        abel))
    (fun p p' => by
      ext q
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Canvas.linkDot,
        Function.comp_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      abel)

/-- `curl*(curl A)` adds up. -/
theorem Canvas.curlStar_curl_add (a b : K.E → ZMod 8) :
    K.curlStar (K.curl (a + b)) = K.curlStar (K.curl a) + K.curlStar (K.curl b) := by
  funext e
  simp only [Canvas.curlStar, Canvas.curl, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The source-free kick `E ↦ E + curl*(curl A)`, which leaves `A` alone, as an
additive bijection of the tables of `(A, E)`. -/
def maxwellKick : (K.E ⊕ K.E → ZMod 8) ≃+ (K.E ⊕ K.E → ZMod 8) where
  toFun p := fieldPair (p ∘ Sum.inl) (p ∘ Sum.inr + K.curlStar (K.curl (p ∘ Sum.inl)))
  invFun p := fieldPair (p ∘ Sum.inl) (p ∘ Sum.inr - K.curlStar (K.curl (p ∘ Sum.inl)))
  left_inv p := by
    funext c
    cases c <;> simp [fieldPair]
  right_inv p := by
    funext c
    cases c <;> simp [fieldPair]
  map_add' p q := by
    funext c
    cases c with
    | inl e => rfl
    | inr e =>
      simp only [fieldPair, Sum.elim_inr, Pi.add_apply]
      have h := congrFun (K.curlStar_curl_add (p ∘ Sum.inl) (q ∘ Sum.inl)) e
      simp only [Pi.add_apply] at h
      rw [show (p + q) ∘ Sum.inl = p ∘ Sum.inl + q ∘ Sum.inl from rfl, h]
      simp only [Function.comp_apply, Pi.add_apply]
      abel

/-- The Faraday move `A ↦ A − E`, which leaves `E` alone, as an additive
bijection of the tables of `(A, E)`. -/
def maxwellMove : (K.E ⊕ K.E → ZMod 8) ≃+ (K.E ⊕ K.E → ZMod 8) where
  toFun p := fieldPair (p ∘ Sum.inl - p ∘ Sum.inr) (p ∘ Sum.inr)
  invFun p := fieldPair (p ∘ Sum.inl + p ∘ Sum.inr) (p ∘ Sum.inr)
  left_inv p := by
    funext c
    cases c <;> simp [fieldPair]
  right_inv p := by
    funext c
    cases c <;> simp [fieldPair]
  map_add' p q := by
    funext c
    cases c with
    | inl e =>
      simp only [fieldPair, Sum.elim_inl, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
      abel
    | inr e => rfl

/-- The source-free Maxwell tick on the tables of `(A, E)`: the kick, then the
move. -/
def maxwellLinear : (K.E ⊕ K.E → ZMod 8) ≃+ (K.E ⊕ K.E → ZMod 8) :=
  (maxwellKick K).trans (maxwellMove K)

/-- The Maxwell tick with source `J` on the tables of `(A, E)`, as an affine
law (Definition 5.5): its additive part is the source-free tick, and its
source is `b = (J, −J)`. -/
def maxwellAffine (J : K.E → ZMod 8) : AffineLaw (K.E ⊕ K.E) 8 :=
  ⟨maxwellLinear K, fieldPair J (-J)⟩

/-- The gauge direction of a site function `g`: the table `w_g = (Dg, 0)`. -/
def gaugeDirection (g : K.V → ZMod 8) : K.E ⊕ K.E → ZMod 8 := fieldPair (K.diff g) 0

end Artform
