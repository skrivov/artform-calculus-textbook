import ArtformScores.NonabelianGravity.QuaternionForm

/-! # Differential two-form preservation along actual quaternion curves

Left and right Maurer values use `deriv` of actual word maps. The edge and
fusion summands use the original AMM convention; the finite certificates are
connected to these values through the analytic inverse and product rules.
The result does not construct the regular reduced manifold or prove its
nondegeneracy, closedness, or a native gravity interpretation.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Maurer

def rightCurve (c : ℕ → ℝ → H) (w : Word) (t : ℝ) : H :=
  deriv (curveWord c w) t*(curveWord c w t)⁻¹
def leftCurve (c : ℕ → ℝ → H) (w : Word) (t : ℝ) : H :=
  (curveWord c w t)⁻¹*deriv (curveWord c w) t

lemma rightCurve_value (c : ℕ → ℝ → H) (g : ℕ → Hˣ) (x : ℕ → H) (t : ℝ)
    (hc : ∀ i, c i t = (g i : H))
    (hd : ∀ i, HasDerivAt (c i) (x i * (g i : H)) t) (w : Word) :
    rightCurve c w t=oneValue g x (right w) := by
  rw [rightCurve,(curveWord_derivative c g x t hc hd w).deriv,curveWord_at c g t hc]
  simp
lemma leftCurve_value (c : ℕ → ℝ → H) (g : ℕ → Hˣ) (x : ℕ → H) (t : ℝ)
    (hc : ∀ i, c i t = (g i : H))
    (hd : ∀ i, HasDerivAt (c i) (x i * (g i : H)) t) (w : Word) :
    leftCurve c w t=oneValue g x (left w) := by
  rw [leftCurve,(curveWord_derivative c g x t hc hd w).deriv,curveWord_at c g t hc,
    oneValue_left,oneValue_right]
  simp [adjoint,mul_assoc]

def exteriorPair (ax ay bx byv : H) : ℝ := pairing ax byv-pairing bx ay
def edgeCurve (c d : ℕ → ℝ → H) (t : ℝ) (s : State Word) (e : canvas.E) : ℝ :=
  let a := s.U e
  let b := wm (wi a) (s.P e)
  exteriorPair (leftCurve c a t) (leftCurve d a t) (rightCurve c b t) (rightCurve d b t)+
    exteriorPair (rightCurve c a t) (rightCurve d a t) (leftCurve c b t) (leftCurve d b t)
def fusionCurve (c d : ℕ → ℝ → H) (t : ℝ) (s : State Word) (v : canvas.V) : ℝ :=
  ((star v).foldl (fun (acc : Word × ℝ) a =>
    let m := if a.2 then s.P a.1 else outgoingWord s a.1
    (wm acc.1 m,acc.2+exteriorPair (leftCurve c acc.1 t) (leftCurve d acc.1 t)
      (rightCurve c m t) (rightCurve d m t))) ([],0)).2
def analyticTwiceOmega (c d : ℕ → ℝ → H) (t : ℝ) (s : State Word) : ℝ :=
  ((List.finRange 7).map (edgeCurve c d t s)).sum+
    ((List.finRange 6).map (fusionCurve c d t s)).sum

variable (c d : ℕ → ℝ → H) (g : ℕ → Hˣ) (x y : ℕ → H) (t : ℝ)
  (hc : ∀ i, c i t = (g i : H)) (hd : ∀ i, d i t = (g i : H))
  (hcx : ∀ i, HasDerivAt (c i) (x i * (g i : H)) t)
  (hdy : ∀ i, HasDerivAt (d i) (y i * (g i : H)) t)

include hc hd hcx hdy

lemma edgeCurve_value (s : State Word) (e : canvas.E) :
    edgeCurve c d t s e=twoValue g x y (edgeForm s e) := by
  simp only [edgeCurve,edgeForm,twoValue_append,twoValue_wedge,exteriorPair,
    leftCurve_value c g x t hc hcx,leftCurve_value d g y t hd hdy,
    rightCurve_value c g x t hc hcx,rightCurve_value d g y t hd hdy]

lemma fusionCurve_value_aux (s : State Word) (as : List (canvas.E × Bool))
    (u : Word) (a : TwoForm) :
    (as.foldl (fun (acc : Word × ℝ) z =>
      let m := if z.2 then s.P z.1 else outgoingWord s z.1
      (wm acc.1 m,acc.2+exteriorPair (leftCurve c acc.1 t) (leftCurve d acc.1 t)
        (rightCurve c m t) (rightCurve d m t))) (u,twoValue g x y a)).2=
    twoValue g x y (as.foldl (fun (acc : Word × TwoForm) z =>
      let m := if z.2 then s.P z.1 else outgoingWord s z.1
      (wm acc.1 m,acc.2++wedge (left acc.1) (right m))) (u,a)).2 := by
  induction as generalizing u a with
  | nil => rfl
  | cons z as ih =>
    simp only [List.foldl_cons]
    have hw : exteriorPair (leftCurve c u t) (leftCurve d u t)
        (rightCurve c (if z.2 then s.P z.1 else outgoingWord s z.1) t)
        (rightCurve d (if z.2 then s.P z.1 else outgoingWord s z.1) t)=
        twoValue g x y (wedge (left u)
          (right (if z.2 then s.P z.1 else outgoingWord s z.1))) := by
      simp only [exteriorPair,twoValue_wedge,leftCurve_value c g x t hc hcx,
        leftCurve_value d g y t hd hdy,rightCurve_value c g x t hc hcx,
        rightCurve_value d g y t hd hdy]
    rw [hw,← twoValue_append]
    exact ih _ _

lemma fusionCurve_value (s : State Word) (v : canvas.V) :
    fusionCurve c d t s v=twoValue g x y (fusion s v) := by
  exact fusionCurve_value_aux c d g x y t hc hd hcx hdy s (star v) [] []

omit hc hd hcx hdy in
lemma twoValue_flatMap (a : List (TwoForm)) :
    twoValue g x y a.flatten=(a.map (twoValue g x y)).sum := by
  induction a with
  | nil => rfl
  | cons b a ih => simp [twoValue_append,ih]

lemma analyticTwiceOmega_value (s : State Word) :
    analyticTwiceOmega c d t s=twoValue g x y (twiceOmega s) := by
  simp only [analyticTwiceOmega,twiceOmega,twoValue_append,List.flatMap_def,
    twoValue_flatMap,List.map_map]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    exact edgeCurve_value c d g x y t hc hd hcx hdy s e
  · apply congrArg List.sum
    apply List.map_congr_left
    intro v _
    exact fusionCurve_value c d g x y t hc hd hcx hdy s v

lemma analytic_pullbacks :
    analyticTwiceOmega c d t (wordKick 0 original)=analyticTwiceOmega c d t original ∧
    analyticTwiceOmega c d t (wordKick 1 original)=analyticTwiceOmega c d t original ∧
    analyticTwiceOmega c d t (wordDrift original)=analyticTwiceOmega c d t original := by
  simp only [analyticTwiceOmega_value c d g x y t hc hd hcx hdy]
  have hp := universal_formal_pullbacks (pairKey g x y)
  change twoValue g x y (defect (wordKick 0))=0 ∧
    twoValue g x y (defect (wordKick 1))=0 ∧ twoValue g x y (defect wordDrift)=0 at hp
  simp only [defect,twoValue_append,twoValue_negative,← sub_eq_add_neg] at hp
  exact ⟨sub_eq_zero.mp hp.1,sub_eq_zero.mp hp.2.1,sub_eq_zero.mp hp.2.2⟩

/-! ## Non-vacuity -/
example (g : ℕ → Hˣ) :
    analyticTwiceOmega (fun i _ => (g i : H)) (fun i _ => (g i : H)) 0
      (wordKick 0 original)=
    analyticTwiceOmega (fun i _ => (g i : H)) (fun i _ => (g i : H)) 0 original := by
  exact (analytic_pullbacks _ _ g 0 0 0 (fun _ => rfl) (fun _ => rfl)
    (fun i => by simpa using hasDerivAt_const (0:ℝ) (g i : H))
    (fun i => by simpa using hasDerivAt_const (0:ℝ) (g i : H))).1
end Artform.Scores.NonabelianGravity.Maurer
