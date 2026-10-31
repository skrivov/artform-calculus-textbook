import ArtformScores.GravityBridge.Native.Retrospective.HomogeneousDefs
/-! # The full original24 homogeneous connection partition and density -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
open Full40
/-- **GAC2:full24-homogeneous-decomposition**
(the full original24 homogeneous connection partition and density). -/
@[ledger "GAC2:full24-homogeneous-decomposition"]
def homogeneousLaw : Prop :=
    (∀ (t : ℚ) (d e : Fin 4 → Fin 3 → ℚ),
    connectionDensity t (assembleConnection d e) =
      (∑ s, distinctDensity s t (d s)) + ∑ b, repeatedDensity b t (e b)) ∧
    (∀ (A : Connection ℚ),
    assembleConnection (distinctCoordinates A) (repeatedCoordinates A) = A) ∧
    (∀ (d e : Fin 4 → Fin 3 → ℚ),
    distinctCoordinates (assembleConnection d e) = d) ∧
    (∀ (d e : Fin 4 → Fin 3 → ℚ),
    repeatedCoordinates (assembleConnection d e) = e) ∧
    (∀ (t : ℚ) (A : Connection ℚ),
    connectionDensity t A =
      (∑ s, distinctDensity s t (distinctCoordinates A s)) +
      ∑ b, repeatedDensity b t (repeatedCoordinates A b))
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
