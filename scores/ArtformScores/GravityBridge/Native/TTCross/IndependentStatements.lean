import ArtformScores.GravityBridge.Native.TTCross.IndependentDefs

/-! # All24 independent connection residual and native physical sign -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-full24-independent-return**
(all24 independent connection residual and native physical sign). -/
@[ledger "GAC2:native-full24-independent-return"]
def independentLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (Z : Matrix (Fin 6) (Fin 4) K),
    fullBApply (independentReturn Z) + (2 / 101 : K) • nativeSourceAdjoint Z = 0) ∧
    (∀ (j a q v : K),
    independentReturn (onWaveCrossZ j a q v) =
      threeConnection
        (timeH *ᵥ ((-2 / 101 : K) • (timeT.transpose *ᵥ
          ![(-2 * a ^ 2 * q - j * a * v) / 4, -a ^ 2 * q / 2, j * a * v / 4])))
        (timeH *ᵥ ((-2 / 101 : K) • (timeT.transpose *ᵥ
          ![(-2 * a ^ 2 * q + j * a * v) / 4, -a ^ 2 * q / 2, -j * a * v / 4])))
        (spaceH *ᵥ ((-2 / 101 : K) • (spaceT.transpose *ᵥ
          ![0, -a ^ 2 * q / 2, -a ^ 2 * q / 2])))) ∧
    (∀ (h : K) (_hh : h ≠ 0)
    (Z : Matrix (Fin 6) (Fin 4) K),
    -h • ((-h)⁻¹ • independentReturn Z) = independentReturn Z) ∧
    (∀ (j : K),
    gDistinct (independentReturn (onWaveCrossZ j 1 0 1)) 1 =
      ![-101 * j / 19982, 2 * j / 9991, 101 * j / 19982])

end Artform.Scores.GravityBridge.Native.TTCross.Statement
