import Mathlib.SetTheory.Cardinal.Finite
import ArtformTextbook.Ch05.Statements.Gauge

/-!
# The pose orbit is a torsor (Lemma 5.16)

The proof is the book's. If `g · m = h · m`, then `h⁻¹ g` fixes `m`, so it is
`1` by rigidity and `g = h`: each pose is `g · m` for exactly one `g`. So
`(g · m) · k := (gk) · m` is well defined; it is a right action, transitive
because `(g · m) · (g⁻¹ h) = h · m`, and free because `(gk) · m = g · m` forces
`gk = g`.
-/

namespace Artform

/-- On a rigid mark, `g · m = h · m` forces `g = h`. -/
private theorem eq_of_smul_eq {G M : Type} [Group G] [MulAction G M] {m : M}
    (hm : MulAction.stabilizer G m = ⊥) {g h : G} (hgh : g • m = h • m) : g = h := by
  have h1 : h⁻¹ * g ∈ MulAction.stabilizer G m := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hgh, inv_smul_smul]
  rw [hm, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

/-- **Lemma 5.16** (pose orbit). The orbit of a rigid mark is a right torsor
under `(g · m) · k := (gk) · m`, and the marked corner of an octagon is rigid
under `C₈` with eight poses in its orbit. -/
@[book "lem:pose-torsor"]
theorem poseTorsor : Statement.poseTorsor := by
  refine ⟨fun G M _ _ m hm => ?_, ?_⟩
  · -- each pose `x` is `g · m` for the element `rep x`, and for no other
    let rep : MulAction.orbit G m → G := fun x => Classical.choose x.2
    have hrep : ∀ x : MulAction.orbit G m, rep x • m = x.1 := fun x => Classical.choose_spec x.2
    let act : MulAction.orbit G m → G → MulAction.orbit G m :=
      fun x k => ⟨(rep x * k) • m, MulAction.mem_orbit m _⟩
    have hrep_mk : ∀ g : G, rep ⟨g • m, MulAction.mem_orbit m g⟩ = g :=
      fun g => eq_of_smul_eq hm (hrep ⟨g • m, MulAction.mem_orbit m g⟩)
    have hrep_act : ∀ x k, rep (act x k) = rep x * k := fun x k =>
      eq_of_smul_eq hm (hrep (act x k))
    refine ⟨act, fun g k => ?_, ⟨fun x => ?_, fun x g k => ?_, ⟨⟨m, MulAction.mem_orbit_self m⟩⟩,
      fun x g hx => ?_, fun x y => ⟨(rep x)⁻¹ * rep y, ?_⟩⟩⟩
    · exact Subtype.ext (by simp only [act, hrep_mk])
    · exact Subtype.ext (by simp only [act, mul_one, hrep x])
    · exact Subtype.ext (by simp only [act, hrep_act, mul_assoc])
    · have h1 : (rep x * g) • m = rep x • m := by
        rw [hrep x]
        exact congrArg Subtype.val hx
      exact mul_eq_left.mp (eq_of_smul_eq hm h1)
    · exact Subtype.ext (by simp only [act, mul_inv_cancel_left, hrep y])
  · -- the octagon: `C₈` turns the corners, and only the identity fixes corner `0`
    have hstab : MulAction.stabilizer (Multiplicative (ZMod 8)) (0 : ZMod 8) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg
      have h : Multiplicative.toAdd g + 0 = 0 := hg
      rw [add_zero] at h
      exact congrArg Multiplicative.ofAdd h
    refine ⟨hstab, ?_⟩
    have huniv : MulAction.orbit (Multiplicative (ZMod 8)) (0 : ZMod 8) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨Multiplicative.ofAdd y, ?_⟩
      change y + 0 = y
      rw [add_zero]
    rw [huniv, Nat.card_univ, Nat.card_zmod]

/-! ## Non-vacuity

The book's example: the marked octagon and its rotations. The mark is rigid, so
Lemma 5.16 makes the eight poses a right `C₈`-torsor. -/

/-- The hypothesis of Lemma 5.16 is met by the marked corner of the octagon. -/
example : MulAction.stabilizer (Multiplicative (ZMod 8)) (0 : ZMod 8) = ⊥ :=
  poseTorsor.2.1

/-- So the eight poses of the marked octagon form a right `C₈`-torsor. -/
example : ∃ act : MulAction.orbit (Multiplicative (ZMod 8)) (0 : ZMod 8) →
      Multiplicative (ZMod 8) → MulAction.orbit (Multiplicative (ZMod 8)) (0 : ZMod 8),
    IsRightTorsor (Multiplicative (ZMod 8)) (MulAction.orbit (Multiplicative (ZMod 8))
      (0 : ZMod 8)) act :=
  let ⟨act, _, h⟩ := poseTorsor.1 _ _ (0 : ZMod 8) poseTorsor.2.1
  ⟨act, h⟩

end Artform
