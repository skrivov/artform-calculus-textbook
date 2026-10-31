import ArtformScores.NonabelianGravity.NativeBoundary
import ArtformScores.Meta.Ledger

/-! # Literal conditional native-import diagnostic -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Artform.Scores.GravityBridge.Native.Full40 NativeRotation

/-- **NGB:native-rotation-import-test** (complete force and owned-window fidelity). -/
@[ledger "NGB:native-rotation-import-test"]
def nativeRotationImportTest : Prop :=
  (∀ (u v : Full ℚ) (x : ℤ), x ≠ 0 → x ≠ -1 →
    density integerStep (pulse u) (pulse v) x = 0) ∧
  (∀ u v : Full ℚ,
    density step (pulse u) (pulse v) (1 : Time) = 0 ∧
    (density step (pulse u) (pulse v) (0 : Time) =
      density integerStep (pulse u) (pulse v) 0 ∧
     density step (pulse u) (pulse v) (2 : Time) =
      density integerStep (pulse u) (pulse v) (-1)) ∧
    nativeBilinear step (1 / 101) (pulse u) (pulse v) = ownedBilinear u v) ∧
  (∀ (j : Fin 3) (c : Coordinate),
    nativeFirstVariation step (1 / 101) (basis j) (test c) = coefficient j c ∧
    fullForce step (1 / 101) (basis j) (0, c) = coefficient j c) ∧
  (∀ (v : Fin 3 → ℚ) (c : Coordinate),
    fullForce step (1 / 101) (trial v) (0, c) = forceTable v c ∧
    ownedBilinear (trial v 0) (unpack (Pi.single c 1)) +
      ownedBilinear (unpack (Pi.single c 1)) (trial v 0) = forceTable v c) ∧
  residual ![1, 1, 1] = (fun _ => -194 / 101) ∧
  (∀ v : Fin 3 → ℚ, v 0 + v 1 + v 2 = 0 → residual v = (103 / 101 : ℚ) • v) ∧
  (∀ v : Fin 3 → ℚ,
    (∀ c, fullForce step (1 / 101) (trial v) (0, c) = 0) ↔ v = 0)
end Artform.Scores.NonabelianGravity.Statement
