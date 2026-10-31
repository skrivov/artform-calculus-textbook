import ArtformScores.NonabelianGravity.NonlinearIsotropicLeading
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.Normed

/-! # Original nonlinear source on an open full-matrix neighborhood

Ambient middle coframe/link matrices are unrestricted. Physical Full40
Lorentz charts are maps into this larger neighborhood, so ambient criticality
will include every one of their second-order correction directions.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
abbrev Env := (Mat × Mat) × (Fin 4 → Mat)

noncomputable def flat : Env := ((1, 1), fun _ => 1)
noncomputable def lapse : Mat := fun i j => if i = 0 ∧ j = 0 then 1 else 0
noncomputable def lapseDirection : Env := ((lapse, 0), 0)
noncomputable def frames (q : Env) (t : ℕ) : Mat := if t = 0 then q.1.1 else q.1.2
noncomputable def links (q : Env) (t : ℕ) (k : Fin 4) : Mat := if t = 0 then q.2 k else 1
noncomputable def inverseLinks (q : Env) (t : ℕ) (k : Fin 4) : Mat := (links q t k)⁻¹

noncomputable def metric (E : Mat) : Mat :=
  E⁻¹ * Matrix.diagonal (fun i => (eta i : ℝ)) * (E⁻¹).transpose

noncomputable def weight (q : Env) (r s : Fin 6) : ℝ :=
  q.1.1.det * (metric q.1.1 (face r).1 (face s).1 *
    metric q.1.1 (face r).2 (face s).2 -
    metric q.1.1 (face r).1 (face s).2 * metric q.1.1 (face r).2 (face s).1)

noncomputable def tau (q : Env) (r : Fin 6) : Vec ℝ :=
  cellTorsionFace (frames q) (inverseLinks q) r

noncomputable def localCurvature (q : Env) : ℝ :=
  ∑ r, cellCurvatureFace (frames q) (links q) (inverseLinks q) r

noncomputable def localTorsion (q : Env) : ℝ :=
  (1 / 101 : ℝ) * ∑ r, ∑ s, weight q r s * etaPair (tau q r) (tau q s)

noncomputable def precedingFrames (q : Env) (t : ℕ) : Mat := if t = 1 then q.1.1 else 1
noncomputable def precedingLinks (q : Env) (t : ℕ) (k : Fin 4) : Mat := if t = 1 then q.2 k else 1

noncomputable def precedingCurvature (q : Env) : ℝ :=
  ∑ r, cellCurvatureFace (precedingFrames q) (precedingLinks q)
    (fun t k => (precedingLinks q t k)⁻¹) r

noncomputable def precedingTorsion (q : Env) : ℝ :=
  (1 / 101 : ℝ) * ∑ r, ∑ s,
    ((eta (face r).1 : ℝ) * (if (face r).1 = (face s).1 then 1 else 0) *
      (eta (face r).2 : ℝ) * (if (face r).2 = (face s).2 then 1 else 0) -
     (eta (face r).1 : ℝ) * (if (face r).1 = (face s).2 then 1 else 0) *
      (eta (face r).2 : ℝ) * (if (face r).2 = (face s).1 then 1 else 0)) *
    etaPair (cellTorsionFace (precedingFrames q)
      (fun t k => (precedingLinks q t k)⁻¹) r)
      (cellTorsionFace (precedingFrames q)
        (fun t k => (precedingLinks q t k)⁻¹) s)

noncomputable def action (q : Env) : ℝ :=
  precedingCurvature q + precedingTorsion q + localCurvature q + localTorsion q

noncomputable def force (q : Env) : ℝ := fderiv ℝ action q lapseDirection

end Artform.Scores.NonabelianGravity.NonlinearAmbient
