import ArtformTextbook.Ch05.Defs.Laws
import ArtformTextbook.Ch05.Holonomy

/-!
# The pose law on the two squares (Section 5.15, `sec:gauge-law`)

The two squares `K = SquareGrid(2,1)` of `Skeleton.TwoSquares`, with a pose at
every corner, written in link coordinates as an element `g_v` of the group. The
pose law is the law of two squares that turn (Section 5.5), carrying poses: at
every tick the left square turns and then the right, and each turn carries
every pose of its square one corner on, across the edge between,
`g'_v = U_e g_u`. The right turn crosses `e₂` against its arrow, from `v₂` to
`v₁`, with `U_{ē₂} = U_{e₂}⁻¹`. The links stay as they are.
-/

namespace Artform

namespace Skeleton.TwoSquares

open Vertex Edge

variable {G : Type*} [Group G]

/-- The left turn of the pose law, corner by corner: every corner of the left
square takes the pose of the corner behind it, carried across the edge between
(`g'_{v₁} = U_{e₁} g_{v₀}`, `g'_{v₂} = U_{e₂} g_{v₁}`, `g'_{v₃} = U_{e₃} g_{v₂}`,
`g'_{v₀} = U_{e₄} g_{v₃}`), and `v₄`, `v₅` keep theirs. -/
def poseLeft (U : skeleton.LinkTable G) (g : Vertex → G) : Vertex → G
  | v₀ => U (along e₄) * g v₃
  | v₁ => U (along e₁) * g v₀
  | v₂ => U (along e₂) * g v₁
  | v₃ => U (along e₃) * g v₂
  | v₄ => g v₄
  | v₅ => g v₅

/-- The right turn of the pose law, corner by corner: every corner of the right
square takes the pose of the corner behind it, carried across the edge between
(`g'_{v₄} = U_{e₅} g_{v₁}`, `g'_{v₅} = U_{e₆} g_{v₄}`, `g'_{v₂} = U_{e₇} g_{v₅}`,
and `g'_{v₁} = U_{ē₂} g_{v₂}`, across `e₂` against its arrow), and `v₀`, `v₃`
keep theirs. -/
def poseRight (U : skeleton.LinkTable G) (g : Vertex → G) : Vertex → G
  | v₀ => g v₀
  | v₁ => U (against e₂) * g v₂
  | v₂ => U (along e₇) * g v₅
  | v₃ => g v₃
  | v₄ => U (along e₅) * g v₁
  | v₅ => U (along e₆) * g v₄

/-- The pose law (Section 5.15). A state is a link table `U`, in the
coordinates of a trivialization, and a pose `g_v` at every corner. At every
tick the left square turns and then the right, carrying poses; the links stay
as they are. -/
def poseLaw : DetLaw (skeleton.LinkTable G × (Vertex → G)) where
  tick x := (x.1, poseRight x.1 (poseLeft x.1 x.2))

/-- The outside of `K`, crossed anticlockwise as a loop based at `v`: from `v₀`
it is `e₄ e₃ e₇ e₆ e₅ e₁`, along `e₁`, `e₅`, `e₆`, `e₇`, `e₃`, `e₄` in turn,
written with the edge crossed first on the right; from another corner it is the
same cycle, started there. -/
def outside : (v : Vertex) → skeleton.Path v v
  | v₀ => .cons (along e₄) (.cons (along e₃) (.cons (along e₇) (.cons (along e₆)
      (.cons (along e₅) (.cons (along e₁) (.nil _))))))
  | v₁ => .cons (along e₁) (.cons (along e₄) (.cons (along e₃) (.cons (along e₇)
      (.cons (along e₆) (.cons (along e₅) (.nil _))))))
  | v₂ => .cons (along e₇) (.cons (along e₆) (.cons (along e₅) (.cons (along e₁)
      (.cons (along e₄) (.cons (along e₃) (.nil _))))))
  | v₃ => .cons (along e₃) (.cons (along e₇) (.cons (along e₆) (.cons (along e₅)
      (.cons (along e₁) (.cons (along e₄) (.nil _))))))
  | v₄ => .cons (along e₅) (.cons (along e₁) (.cons (along e₄) (.cons (along e₃)
      (.cons (along e₇) (.cons (along e₆) (.nil _))))))
  | v₅ => .cons (along e₆) (.cons (along e₅) (.cons (along e₁) (.cons (along e₄)
      (.cons (along e₃) (.cons (along e₇) (.nil _))))))

end Skeleton.TwoSquares

end Artform
