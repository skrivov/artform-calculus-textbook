import ArtformScores.GravityBridge.Native.TTCross.Full24

/-! # Original full24 inverse as an odd degree-five polynomial -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



def inverseP1 : ℚ := (194 / 101 : ℚ)⁻¹ ^ 2 + (103 / 101 : ℚ)⁻¹ ^ 2 + (200 / 101 : ℚ)⁻¹ ^ 2

def inverseP3 : ℚ := -((194 / 101 : ℚ)⁻¹ ^ 2 * (103 / 101 : ℚ)⁻¹ ^ 2 +
  (194 / 101 : ℚ)⁻¹ ^ 2 * (200 / 101 : ℚ)⁻¹ ^ 2 + (103 / 101 : ℚ)⁻¹ ^ 2 * (200 / 101 : ℚ)⁻¹ ^ 2)

def inverseP5 : ℚ := (194 / 101 : ℚ)⁻¹ ^ 2 * (103 / 101 : ℚ)⁻¹ ^ 2 * (200 / 101 : ℚ)⁻¹ ^ 2

def oddInverse (B : Three (K := ℚ)) : Three (K := ℚ) :=
  inverseP1 • B + inverseP3 • (B ^ 3) + inverseP5 • (B ^ 5)

def nativePower : ℕ → Connection ℚ → Connection ℚ
  | 0, A => A
  | n + 1, A => fullBApply (nativePower n A)

def globalOddInverse (A : Connection ℚ) : Connection ℚ :=
  inverseP1 • nativePower 1 A + inverseP3 • nativePower 3 A + inverseP5 • nativePower 5 A

end Artform.Scores.GravityBridge.Native.RetroCertificates
