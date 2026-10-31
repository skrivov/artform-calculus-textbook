import ArtformScores.GravityBridge.Native.RetroCertificates.FacePartition

/-! # Complete original constitutive quadratic has both algebraic signs -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix Full40 TTCross RetroCertificates MeasureTheory Set Filter
open scoped ENNReal

variable {K : Type*} [Field K] [CharZero K]

noncomputable def orthogonalModes (z : Fin 3 → K) : Fin 3 → K :=
  ![z 0 + z 1 + z 2, -z 0 + z 1 + z 2, -2 * z 1 + z 2]

noncomputable def inverseModes (z : Fin 3 → K) : Fin 3 → K :=
  ![(z 0 - z 1) / 2, (z 0 + z 1 - 2 * z 2) / 6, (z 0 + z 1 + z 2) / 3]

noncomputable def faceModes (z : Fin 8 → Fin 3 → K) : NativeFace K := faceAssemble (fun s =>
  orthogonalModes (z s))

noncomputable def nativeFaceQuadratic (Z : NativeFace K) : K := ∑ r, ∑ a, Z r a *
  nativeConstitutiveQ Z r a

noncomputable def modeDiagonal (s : Fin 8) : Fin 3 → K :=
  let a := (faceAlpha (K := K) s)⁻¹
  let b := -faceBeta (K := K) s / (faceAlpha s * (faceAlpha s + 3 * faceBeta s))
  ![2 * a, 6 * a, 3 * (a + 3 * b)]

noncomputable def positiveModeCount : ℕ :=
  (Finset.univ.filter (fun p : Fin 8 × Fin 3 => 0 < modeDiagonal (K := ℚ) p.1 p.2)).card

noncomputable def negativeModeCount : ℕ :=
  (Finset.univ.filter (fun p : Fin 8 × Fin 3 => modeDiagonal (K := ℚ) p.1 p.2 < 0)).card

end Artform.Scores.GravityBridge.Native.NativeDetailTests
