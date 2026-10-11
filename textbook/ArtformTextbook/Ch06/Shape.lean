import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import ArtformTextbook.Ch06.Linear
import ArtformTextbook.Ch06.Statements.Maxwell

/-!
# What the two steps force (Proposition 6.11)

The kick is built face by face from one rule `r`, which reads the four links of
a face and adds a value at each of them. At a position `p` where some face has
an edge on no other face, the kick there is `r(·)(p)` of that face alone. So
`r(·)(p)` is additive, and blindness to gauge changes makes it vanish on every
table `Dg` of the face, which are the tables of boundary sum `0`; it is
therefore the boundary sum times one number `w_p`. Every position has such an
edge on the rim of the window: the lower and left edges of the lower left face,
the right and upper edges of the upper right one. Gauss's law, tried on the
potential `1` on one rim edge, whose kick is `w` round its face, forces
`w = (κ, κ, −κ, −κ)`: the face adds `κ` times its curvature round its
boundary, and the kick is `κ curl*(curl A)`. The move adds `μ(E') = μ(1) E'`.
-/

namespace Artform

open scoped BigOperators

variable {m n : ℕ}

/-- How the boundary of a face reads an edge, as a sum over its four edges. -/
theorem squareGrid_inc (e : GridEdge m n) (f : GridFace m n) :
    ((squareGrid m n).inc e f : ZMod 8) =
      (if gridFaceEdge f 0 = e then 1 else 0) + (if gridFaceEdge f 1 = e then 1 else 0) -
      (if gridFaceEdge f 2 = e then 1 else 0) - (if gridFaceEdge f 3 = e then 1 else 0) := by
  simp only [Canvas.inc, squareGrid, List.finRange_succ, List.finRange_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, gridFaceDir]
  simp
  split_ifs <;> ring

/-- The curl of a face of the window: `A` along its lower and right edges, less
`A` along its upper and left ones. -/
theorem squareGrid_curl (A : GridEdge m n → ZMod 8) (f : GridFace m n) :
    (squareGrid m n).curl A f = A (gridFaceEdge f 0) + A (gridFaceEdge f 1) -
      A (gridFaceEdge f 2) - A (gridFaceEdge f 3) := by
  simp only [Canvas.curl, squareGrid_inc, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- The boundary sum of four link values, read round a face: the lower and the
right edge along, the upper and the left edge against. -/
def faceCurl (x : Fin 4 → ZMod 8) : ZMod 8 := x 0 + x 1 - x 2 - x 3

/-- Every table on the four edges of a face whose boundary sum is `0` is the
difference of a site function. -/
theorem squareGrid_exists_diff_eq (f : GridFace m n) (y : Fin 4 → ZMod 8)
    (hy : faceCurl y = 0) :
    ∃ g : GridVertex m n → ZMod 8, ∀ k, (squareGrid m n).diff g (gridFaceEdge f k) = y k := by
  obtain ⟨i, j⟩ := f
  refine ⟨fun v => if v = (i.succ, j.castSucc) then y 0
    else if v = (i.succ, j.succ) then y 0 + y 1
    else if v = (i.castSucc, j.succ) then y 3 else 0, fun k => ?_⟩
  have hi : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne
  have hj : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  unfold faceCurl at hy
  fin_cases k <;> simp [Canvas.diff, gridSrc, gridTgt, gridFaceEdge, hi, hj, hj.symm]
  · linear_combination hy

/-- The four edges of a face are four different edges. -/
theorem gridFaceEdge_injective (f : GridFace m n) : Function.Injective (gridFaceEdge f) := by
  obtain ⟨i, j⟩ := f
  have hi : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne
  have hj : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  intro k k' h
  fin_cases k <;> fin_cases k' <;> simp_all [gridFaceEdge]

/-- The kick at an edge that lies on one face alone, at one position, is what
that face adds there. -/
theorem faceKick_of_unique (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8) (A : GridEdge m n → ZMod 8)
    (f : GridFace m n) (p : Fin 4)
    (h : ∀ f' k, gridFaceEdge f' k = gridFaceEdge f p → f' = f ∧ k = p) :
    faceKick r A (gridFaceEdge f p) = r (fun j => A (gridFaceEdge f j)) p := by
  unfold faceKick
  rw [Finset.sum_eq_single f, Finset.sum_eq_single p]
  · simp
  · intro k _ hk
    rw [ite_eq_right_iff]
    intro he
    exact absurd (h f k he).2 hk
  · intro hp
    exact absurd (Finset.mem_univ p) hp
  · intro f' _ hf'
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right_iff]
    intro he
    exact absurd (h f' k he).1 hf'
  · intro hf
    exact absurd (Finset.mem_univ f) hf

/-- The lower edge of the lower left face lies on that face alone. -/
theorem rim_bottom (hm : 0 < m) (hn : 0 < n) (f' : GridFace m n) (k : Fin 4)
    (h : gridFaceEdge f' k = gridFaceEdge (⟨0, hm⟩, ⟨0, hn⟩) 0) :
    f' = (⟨0, hm⟩, ⟨0, hn⟩) ∧ k = 0 := by
  obtain ⟨i, j⟩ := f'
  fin_cases k <;> simp [gridFaceEdge, Fin.ext_iff] at h ⊢
  omega

/-- The left edge of the lower left face lies on that face alone. -/
theorem rim_left (hm : 0 < m) (hn : 0 < n) (f' : GridFace m n) (k : Fin 4)
    (h : gridFaceEdge f' k = gridFaceEdge (⟨0, hm⟩, ⟨0, hn⟩) 3) :
    f' = (⟨0, hm⟩, ⟨0, hn⟩) ∧ k = 3 := by
  obtain ⟨i, j⟩ := f'
  fin_cases k <;> simp [gridFaceEdge, Fin.ext_iff] at h ⊢
  omega

/-- The right edge of the upper right face lies on that face alone. -/
theorem rim_right (hm : 0 < m) (hn : 0 < n) (f' : GridFace m n) (k : Fin 4)
    (h : gridFaceEdge f' k = gridFaceEdge (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩) 1) :
    f' = (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩) ∧ k = 1 := by
  obtain ⟨i, j⟩ := f'
  fin_cases k <;> simp [gridFaceEdge, Fin.ext_iff] at h ⊢ <;> omega

/-- The upper edge of the upper right face lies on that face alone. -/
theorem rim_top (hm : 0 < m) (hn : 0 < n) (f' : GridFace m n) (k : Fin 4)
    (h : gridFaceEdge f' k = gridFaceEdge (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩) 2) :
    f' = (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩) ∧ k = 2 := by
  obtain ⟨i, j⟩ := f'
  fin_cases k <;> simp [gridFaceEdge, Fin.ext_iff] at h ⊢ <;> omega

/-- Where an edge at position `p` of a face lies on no other face, an additive
kick that is blind to gauge changes adds there the boundary sum of the face
times one number: `r(x)(p) = (x₀ + x₁ − x₂ − x₃) r(δ₀)(p)`. -/
theorem rule_eq_of_unique (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8)
    (hφ : ∀ A A' : GridEdge m n → ZMod 8, faceKick r (A + A') = faceKick r A + faceKick r A')
    (hgauge : ∀ (A : GridEdge m n → ZMod 8) (g : GridVertex m n → ZMod 8),
      faceKick r (A + (squareGrid m n).diff g) = faceKick r A)
    (f : GridFace m n) (p : Fin 4)
    (hrim : ∀ f' k, gridFaceEdge f' k = gridFaceEdge f p → f' = f ∧ k = p)
    (x : Fin 4 → ZMod 8) : r x p = faceCurl x * r (Pi.single 0 1) p := by
  -- a table on the edges of `f` alone, extended by `0`
  let ext : (Fin 4 → ZMod 8) → GridEdge m n → ZMod 8 := fun y e =>
    ∑ k, if gridFaceEdge f k = e then y k else 0
  have hext : ∀ y j, ext y (gridFaceEdge f j) = y j := fun y j => by
    simp only [ext, (gridFaceEdge_injective f).eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  have hR : ∀ y, r y p = faceKick r (ext y) (gridFaceEdge f p) := fun y => by
    rw [faceKick_of_unique r _ f p hrim]
    exact congrArg (fun z => r z p) (funext fun j => (hext y j).symm)
  have hext_add : ∀ y y', ext (y + y') = ext y + ext y' := fun y y' => by
    funext e
    simp only [ext, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hadd : ∀ y y', r (y + y') p = r y p + r y' p := fun y y' => by
    rw [hR, hR y, hR y', hext_add, hφ]
    rfl
  have h0 : faceKick r (0 : GridEdge m n → ZMod 8) = 0 := by
    have h := hφ 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hblind : ∀ g : GridVertex m n → ZMod 8,
      r (fun j => (squareGrid m n).diff g (gridFaceEdge f j)) p = 0 := fun g => by
    rw [← faceKick_of_unique r _ f p hrim]
    have h := hgauge 0 g
    rw [zero_add, h0] at h
    rw [h]
    rfl
  let R : (Fin 4 → ZMod 8) →+ ZMod 8 := AddMonoidHom.mk' (fun y => r y p) hadd
  have hy : faceCurl (x - faceCurl x • Pi.single 0 1) = 0 := by
    simp [faceCurl]
    ring
  obtain ⟨g, hg⟩ := squareGrid_exists_diff_eq f _ hy
  have hsplit : x = (x - faceCurl x • Pi.single 0 1) + faceCurl x • Pi.single 0 1 := by abel
  have hRx : R x = R (x - faceCurl x • Pi.single 0 1) + faceCurl x • R (Pi.single 0 1) := by
    rw [← ZMod.map_smul, ← map_add, ← hsplit]
  have hzero : R (x - faceCurl x • Pi.single 0 1) = 0 := by
    rw [← funext hg]
    exact hblind g
  simpa [R, hzero, smul_eq_mul] using hRx

/-- On a window with a face, an additive kick built face by face by one rule,
blind to gauge changes and keeping Gauss's law, is `κ curl*(curl A)`. -/
theorem faceKick_eq_curlStar_curl (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8)
    (hφ : ∀ A A' : GridEdge m n → ZMod 8, faceKick r (A + A') = faceKick r A + faceKick r A')
    (hgauge : ∀ (A : GridEdge m n → ZMod 8) (g : GridVertex m n → ZMod 8),
      faceKick r (A + (squareGrid m n).diff g) = faceKick r A)
    (hgauss : ∀ A : GridEdge m n → ZMod 8, (squareGrid m n).div (faceKick r A) = 0)
    (hm : 0 < m) (hn : 0 < n) :
    ∃ κ : ZMod 8, ∀ (A : GridEdge m n → ZMod 8) (e : GridEdge m n),
      faceKick r A e = κ * (squareGrid m n).curlStar ((squareGrid m n).curl A) e := by
  let f₀ : GridFace m n := (⟨0, hm⟩, ⟨0, hn⟩)
  let f₁ : GridFace m n := (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩)
  let w : Fin 4 → ZMod 8 := r (Pi.single 0 1)
  -- the rule adds the boundary sum times `w p` at the position `p`
  have hr : ∀ x p, r x p = faceCurl x * w p := by
    intro x p
    fin_cases p
    · exact rule_eq_of_unique r hφ hgauge f₀ 0 (rim_bottom hm hn) x
    · exact rule_eq_of_unique r hφ hgauge f₁ 1 (rim_right hm hn) x
    · exact rule_eq_of_unique r hφ hgauge f₁ 2 (rim_top hm hn) x
    · exact rule_eq_of_unique r hφ hgauge f₀ 3 (rim_left hm hn) x
  -- the kick in general: each face adds its curvature times `w`
  have hkick : ∀ (A : GridEdge m n → ZMod 8) e,
      faceKick r A e = ∑ f, ∑ k, if gridFaceEdge f k = e then
        (squareGrid m n).curl A f * w k else 0 := by
    intro A e
    unfold faceKick
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hr, squareGrid_curl]
    rfl
  -- Gauss's law, for the potential `1` on the lower edge of `f₀` alone
  let A₀ : GridEdge m n → ZMod 8 := fun e => if e = gridFaceEdge f₀ 0 then 1 else 0
  have hcurl₀ : ∀ f, (squareGrid m n).curl A₀ f = if f = f₀ then 1 else 0 := by
    intro f
    rw [squareGrid_curl]
    by_cases hf : f = f₀
    · subst hf
      have h1 : gridFaceEdge f₀ 1 ≠ gridFaceEdge f₀ 0 :=
        (gridFaceEdge_injective f₀).ne (by decide)
      have h2 : gridFaceEdge f₀ 2 ≠ gridFaceEdge f₀ 0 :=
        (gridFaceEdge_injective f₀).ne (by decide)
      have h3 : gridFaceEdge f₀ 3 ≠ gridFaceEdge f₀ 0 :=
        (gridFaceEdge_injective f₀).ne (by decide)
      simp [A₀, h1, h2, h3]
    · have hk : ∀ k, gridFaceEdge f k ≠ gridFaceEdge f₀ 0 := fun k he =>
        hf (rim_bottom hm hn f k he).1
      simp [A₀, hk, hf]
  have hkick₀ : ∀ e, faceKick r A₀ e = ∑ k, if gridFaceEdge f₀ k = e then w k else 0 := by
    intro e
    rw [hkick, Finset.sum_eq_single f₀]
    · simp [hcurl₀]
    · intro f _ hf
      simp [hcurl₀, hf]
    · intro h
      exact absurd (Finset.mem_univ f₀) h
  have hpair : ∀ g : GridVertex m n → ZMod 8,
      ∑ k, (squareGrid m n).diff g (gridFaceEdge f₀ k) * w k = 0 := by
    intro g
    have h := (squareGrid m n).sum_diff_mul g (faceKick r A₀)
    rw [hgauss A₀] at h
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero] at h
    rw [← h]
    simp only [hkick₀, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hw : ∀ y, faceCurl y = 0 → ∑ k, y k * w k = 0 := by
    intro y hy
    obtain ⟨g, hg⟩ := squareGrid_exists_diff_eq f₀ y hy
    simpa [hg] using hpair g
  have h1 : w 0 - w 1 = 0 := by
    have h := hw ![1, -1, 0, 0] (by simp [faceCurl])
    rwa [Fin.sum_univ_four, show (![1, -1, 0, 0] : Fin 4 → ZMod 8) 0 = 1 from rfl,
      show (![1, -1, 0, 0] : Fin 4 → ZMod 8) 1 = -1 from rfl,
      show (![1, -1, 0, 0] : Fin 4 → ZMod 8) 2 = 0 from rfl,
      show (![1, -1, 0, 0] : Fin 4 → ZMod 8) 3 = 0 from rfl, one_mul, neg_one_mul, zero_mul,
      zero_mul, add_zero, add_zero, ← sub_eq_add_neg] at h
  have h2 : w 1 + w 2 = 0 := by
    have h := hw ![0, 1, 1, 0] (by simp [faceCurl])
    rwa [Fin.sum_univ_four, show (![0, 1, 1, 0] : Fin 4 → ZMod 8) 0 = 0 from rfl,
      show (![0, 1, 1, 0] : Fin 4 → ZMod 8) 1 = 1 from rfl,
      show (![0, 1, 1, 0] : Fin 4 → ZMod 8) 2 = 1 from rfl,
      show (![0, 1, 1, 0] : Fin 4 → ZMod 8) 3 = 0 from rfl, one_mul, one_mul, zero_mul,
      zero_mul, zero_add, add_zero] at h
  have h3 : w 3 - w 2 = 0 := by
    have h := hw ![0, 0, -1, 1] (by simp [faceCurl])
    rwa [Fin.sum_univ_four, show (![0, 0, -1, 1] : Fin 4 → ZMod 8) 0 = 0 from rfl,
      show (![0, 0, -1, 1] : Fin 4 → ZMod 8) 1 = 0 from rfl,
      show (![0, 0, -1, 1] : Fin 4 → ZMod 8) 2 = -1 from rfl,
      show (![0, 0, -1, 1] : Fin 4 → ZMod 8) 3 = 1 from rfl, one_mul, neg_one_mul, zero_mul,
      zero_mul, zero_add, zero_add, neg_add_eq_sub] at h
  have hw1 : w 1 = w 0 := by linear_combination -h1
  have hw2 : w 2 = -w 0 := by linear_combination h2 + h1
  have hw3 : w 3 = -w 0 := by linear_combination h3 + h2 + h1
  refine ⟨w 0, fun A e => ?_⟩
  rw [hkick, Canvas.curlStar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [squareGrid_inc, Fin.sum_univ_four, hw1, hw2, hw3]
  split_ifs <;> ring

/-- **Proposition 6.11** (what the two steps force). On a square window, two
steps of the given shape that are additive, the same at every face and every
link, blind to gauge changes and keeping Gauss's law are
`E' = E + κ curl*(curl A)` and `A' = A − λ E'`; conversely, every such pair of
steps is reversible and gauge covariant, and keeps Gauss's law. -/
@[book "prop:maxwell-shape"]
theorem maxwellShape : Statement.maxwellShape := by
  refine ⟨fun m n r μ hφ hμ hgauge hgauss => ?_, fun K κ lam => ?_⟩
  · -- the move adds `μ(E') = μ(1) E'`
    have hμx : ∀ x : ZMod 8, μ x = x * μ 1 := fun x => by
      have h := map_nsmul (AddMonoidHom.mk' μ hμ) x.val 1
      simp only [AddMonoidHom.mk'_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h
      exact h
    -- the kick adds `κ curl*(curl A)`
    obtain ⟨κ, hκ⟩ : ∃ κ : ZMod 8, ∀ (A : GridEdge m n → ZMod 8) (e : GridEdge m n),
        faceKick r A e = κ * (squareGrid m n).curlStar ((squareGrid m n).curl A) e := by
      by_cases hmn : 0 < m ∧ 0 < n
      · exact faceKick_eq_curlStar_curl r hφ hgauge hgauss hmn.1 hmn.2
      · -- a window with no face: the kick adds nothing, and neither does `curl*`
        refine ⟨0, fun A e => ?_⟩
        rw [zero_mul]
        exact Finset.sum_eq_zero fun f _ => absurd ⟨f.1.pos, f.2.pos⟩ hmn
    refine ⟨κ, -μ 1, fun A E => ?_⟩
    simp only [twoStepTick, Prod.mk.injEq]
    refine ⟨funext fun e => ?_, funext fun e => ?_⟩
    · simp only [Pi.add_apply, hκ]
      rw [hμx]
      ring
    · simp only [Pi.add_apply, hκ]
  · intro kick move
    have hkick : Function.Bijective kick := by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨fun s => (s.1, fun e => s.2 e - κ * K.curlStar (K.curl s.1) e), fun s => ?_,
          fun s => ?_⟩
      · exact Prod.ext rfl (funext fun e => add_sub_cancel_right (s.2 e) _)
      · exact Prod.ext rfl (funext fun e => sub_add_cancel (s.2 e) _)
    have hmove : Function.Bijective move := by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨fun s => (fun e => s.1 e + lam * s.2 e, s.2), fun s => ?_, fun s => ?_⟩
      · exact Prod.ext (funext fun e => sub_add_cancel (s.1 e) _) rfl
      · exact Prod.ext (funext fun e => add_sub_cancel_right (s.1 e) _) rfl
    refine ⟨hkick, hmove, hmove.comp hkick, fun A E g => ?_, fun A E g => ?_,
      fun A E ρ hG => ?_⟩
    · -- `curl (A + Dg) = curl A`
      change (A + K.diff g, fun e => E e + κ * K.curlStar (K.curl (A + K.diff g)) e) =
        (A + K.diff g, fun e => E e + κ * K.curlStar (K.curl A) e)
      rw [Canvas.curl_add, Canvas.curl_diff, add_zero]
    · change (fun e => (A + K.diff g) e - lam * E e, E) =
        (fun e => A e - lam * E e + K.diff g e, E)
      refine Prod.ext (funext fun e => ?_) rfl
      simp only [Pi.add_apply]
      ring
    · -- `div curl* = 0`
      change K.div (fun e => E e + κ * K.curlStar (K.curl A) e) = ρ
      have h : (fun e => E e + κ * K.curlStar (K.curl A) e) =
          E + K.curlStar (κ • K.curl A) := by
        funext e
        simp [Canvas.curlStar, Finset.mul_sum, mul_left_comm]
      rw [h, Canvas.div_add, Canvas.div_curlStar, add_zero, hG]

/-! ## Non-vacuity -/

/-- The rule of the chapter's tick, `κ = 1`: each face adds its curvature round
its boundary, read anticlockwise. -/
def curlRule (x : Fin 4 → ZMod 8) : Fin 4 → ZMod 8 :=
  ![faceCurl x, faceCurl x, -faceCurl x, -faceCurl x]

/-- On every square window the chapter's kick is the face kick of `curlRule`. -/
theorem faceKick_curlRule (A : GridEdge m n → ZMod 8) :
    faceKick curlRule A = (squareGrid m n).curlStar ((squareGrid m n).curl A) := by
  funext e
  unfold faceKick
  rw [Canvas.curlStar]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [squareGrid_inc, squareGrid_curl, Fin.sum_univ_four]
  simp only [curlRule, faceCurl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  split_ifs <;> ring

/-- The chapter's two steps meet the hypotheses of Proposition 6.11 on every
square window: the face rule `curlRule` is additive, blind to gauge changes,
and keeps Gauss's law, and the move `μ(x) = −x` is additive. -/
theorem curlRule_hypotheses (m n : ℕ) :
    (∀ A A' : GridEdge m n → ZMod 8,
      faceKick curlRule (A + A') = faceKick curlRule A + faceKick curlRule A') ∧
    (∀ x y : ZMod 8, -(x + y) = -x + -y) ∧
    (∀ (A : GridEdge m n → ZMod 8) (g : GridVertex m n → ZMod 8),
      faceKick curlRule (A + (squareGrid m n).diff g) = faceKick curlRule A) ∧
    (∀ A : GridEdge m n → ZMod 8, (squareGrid m n).div (faceKick curlRule A) = 0) := by
  refine ⟨fun A A' => ?_, fun x y => neg_add x y, fun A g => ?_, fun A => ?_⟩
  · rw [faceKick_curlRule, faceKick_curlRule, faceKick_curlRule, Canvas.curl_add,
      Canvas.curlStar_add]
  · rw [faceKick_curlRule, faceKick_curlRule, Canvas.curl_add, Canvas.curl_diff, add_zero]
  · rw [faceKick_curlRule, Canvas.div_curlStar]

/-- The hypotheses of Proposition 6.11 met on the chapter's window
`W = SquareGrid(3, 3)` by the chapter's own two steps: the face rule
`curlRule` and the move `μ(x) = −x`. -/
example : (∀ A A' : GridEdge 3 3 → ZMod 8,
      faceKick curlRule (A + A') = faceKick curlRule A + faceKick curlRule A') ∧
    (∀ x y : ZMod 8, -(x + y) = -x + -y) ∧
    (∀ (A : GridEdge 3 3 → ZMod 8) (g : GridVertex 3 3 → ZMod 8),
      faceKick curlRule (A + (squareGrid 3 3).diff g) = faceKick curlRule A) ∧
    (∀ A : GridEdge 3 3 → ZMod 8, (squareGrid 3 3).div (faceKick curlRule A) = 0) :=
  curlRule_hypotheses 3 3

end Artform
