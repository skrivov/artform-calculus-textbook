import ArtformScores.GravityBridge.PivotAuditDefs
/-! # Native guarded pivot substitution -/
namespace Artform.Scores.GravityBridge.Statement
open Native.R2
/-- **GAC:guarded-pivot-substitution** (native guarded pivot substitution). -/
@[ledger "GAC:guarded-pivot-substitution"]
def pivotAuditLaw : Prop :=
  (∀ (l n : Fin 4 → ℝ) (nu k : ℝ) (i : Fin 4) (_hi : l i ≠ 0),
    (pivotLatitude l n i) ^ 2 + nu * pivotLatitude l n i + k = 0 ↔
      pivotNormal l n nu k i = 0) ∧
  (∀ (l n : Fin 4 → ℝ) (nu k : ℝ) (i : Fin 4)
    (_hi : l i ≠ 0) (P : ℝ → Prop),
    (∃ s : ℝ, s ^ 2 + nu * s + k = 0 ∧ (∀ j, l j * s + n j = 0) ∧ P s) ↔
      pivotNormal l n nu k i = 0 ∧ (∀ j, l i * n j - l j * n i = 0) ∧
        P (pivotLatitude l n i)) ∧
  (∀ (R a G : ℝ) (i : Fin 4)
    (_hi : ell a G (rowPolys R a G i) ≠ 0) (P : ℝ → Prop),
    (∃ s : ℝ, normal a G s = 0 ∧ (∀ j, rows R a G s j = 0) ∧ P s) ↔
      pivotNormal (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j))
        (5 - 8 * a + 6 * G) (2 * (2 - 3 * a) ^ 2) i = 0 ∧
      (∀ j, ell a G (rowPolys R a G i) * remainderConst a G (rowPolys R a G j) -
        ell a G (rowPolys R a G j) * remainderConst a G (rowPolys R a G i) = 0) ∧
      P (pivotLatitude (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j)) i)) ∧
  (∀ (q R a G gamma : ℝ)
    (_hq : q ^ 2 = 103 / 2) (_hg : gamma ^ 2 = G) (_hq0 : q ≠ 0) (_hg0 : gamma ≠ 0)
    (i : Fin 4) (_hi : ell a G (rowPolys R a G i) ≠ 0) (P : ℝ → Prop),
    (∃ s : ℝ, normal a G s = 0 ∧
      (originalJ q R a gamma s = 0 ∧ originalJ q R a (-gamma) s = 0) ∧ P s) ↔
      pivotNormal (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j))
        (5 - 8 * a + 6 * G) (2 * (2 - 3 * a) ^ 2) i = 0 ∧
      (∀ j, ell a G (rowPolys R a G i) * remainderConst a G (rowPolys R a G j) -
        ell a G (rowPolys R a G j) * remainderConst a G (rowPolys R a G i) = 0) ∧
      P (pivotLatitude (fun j => ell a G (rowPolys R a G j))
        (fun j => remainderConst a G (rowPolys R a G j)) i))
end Artform.Scores.GravityBridge.Statement
