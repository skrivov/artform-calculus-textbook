import ArtformScores.GravityBridge.Native.CurvedSubdivision.WordsDefs

/-! # All six original based words and guarded reverse loops -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-six-curved-words**
(all six original based words and guarded reverse loops). -/
@[ledger "GAC2:native-six-curved-words"]
def wordsLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (c s d t : K),
    boost c s * boost d t = boost (c * d + s * t) (s * d + c * t)) ∧
    (∀ (c0 s0 c1 s1 : K) (_h0 : c0 ^ 2 - s0 ^ 2 = 1),
    basedPlaquette c0 s0 c1 s1 = fun r =>
      if r = 0 then boost (c0 * c1 - s0 * s1) (c0 * s1 - s0 * c1) else 1) ∧
    (∀ (c0 s0 c1 s1 : K) (_h0 : c0 ^ 2 - s0 ^ 2 = 1),
    reversePlaquette c0 s0 c1 s1 = fun r =>
      if r = 0 then boost (c0 * c1 - s0 * s1) (-(c0 * s1 - s0 * c1)) else 1) ∧
    (∀ (c0 s0 c1 s1 : K)
    (_h0 : c0 ^ 2 - s0 ^ 2 = 1) (_h1 : c1 ^ 2 - s1 ^ 2 = 1) (r : Fin 6),
    basedPlaquette c0 s0 c1 s1 r * reversePlaquette c0 s0 c1 s1 r = 1 ∧
      reversePlaquette c0 s0 c1 s1 r * basedPlaquette c0 s0 c1 s1 r = 1) ∧
    (∀ (c0 s0 c1 s1 : K) (_h0 : c0 ^ 2 - s0 ^ 2 = 1),
    (fun r => (-1 / 2 : K) • (basedPlaquette c0 s0 c1 s1 r - reversePlaquette c0 s0 c1 s1 r)) =
      fun r => if r = 0 then lie ![-(c0 * s1 - s0 * c1), 0, 0, 0, 0, 0] else 0)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
