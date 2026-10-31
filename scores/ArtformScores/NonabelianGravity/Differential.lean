import ArtformScores.NonabelianGravity.WordBinding
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Interpreting the finite Maurer compiler in an actual division algebra

The coefficients below are actual right-trivialized tangent values. The final
derivative theorem uses the analytic product and noncommutative inverse rules;
it does not postulate Maurer identities or a manifold reduction theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Maurer
variable {A : Type}
section Algebra
variable [DivisionRing A]

def adjoint (u : Aˣ) (x : A) : A := (u : A)*x*(↑u⁻¹ : A)

@[simp] lemma adjoint_one (x : A) : adjoint (1 : Aˣ) x=x := by simp [adjoint]
@[simp] lemma adjoint_zero (u : Aˣ) : adjoint u 0=0 := by simp [adjoint]
lemma adjoint_add (u : Aˣ) (x y : A) :
    adjoint u (x+y)=adjoint u x+adjoint u y := by simp [adjoint,mul_add,add_mul]
lemma adjoint_neg (u : Aˣ) (x : A) : adjoint u (-x) = -adjoint u x := by
  simp [adjoint]
lemma adjoint_zsmul (u : Aˣ) (n : ℤ) (x : A) :
    adjoint u (n • x)=n • adjoint u x := by
  exact ((AddMonoidHom.mulRight (↑u⁻¹ : A)).comp
    (AddMonoidHom.mulLeft (u : A))).map_zsmul n x
lemma adjoint_mul (u v : Aˣ) (x : A) :
    adjoint (u*v) x=adjoint u (adjoint v x) := by simp [adjoint,mul_assoc]

def oneValue (g : ℕ → Aˣ) (x : ℕ → A) (a : OneForm) : A :=
  (a.map fun t => t.1 • adjoint (evalWord g t.2.2) (x t.2.1)).sum

@[simp] lemma oneValue_nil (g : ℕ → Aˣ) (x : ℕ → A) : oneValue g x []=0 := rfl
lemma oneValue_cons (g : ℕ → Aˣ) (x : ℕ → A) (t : OneTerm) (a : OneForm) :
    oneValue g x (t::a)=t.1 • adjoint (evalWord g t.2.2) (x t.2.1)+oneValue g x a := rfl
lemma oneValue_ad (g : ℕ → Aˣ) (x : ℕ → A) (w : Word) (a : OneForm) :
    oneValue g x (ad w a)=adjoint (evalWord g w) (oneValue g x a) := by
  induction a with
  | nil => simp [ad]
  | cons t a ih =>
    change t.1 • adjoint (evalWord g (wm w t.2.2)) (x t.2.1)+
      oneValue g x (ad w a)=_
    rw [ih,eval_wm,adjoint_mul,oneValue_cons,adjoint_add,adjoint_zsmul]

def rightLetter (g : ℕ → Aˣ) (x : ℕ → A) (a : Letter) : A :=
  if a.2 then x a.1 else -adjoint ((g a.1)⁻¹) (x a.1)
def rightWord (g : ℕ → Aˣ) (x : ℕ → A) : Word → A
  | [] => 0
  | a::w => rightLetter g x a+adjoint (evalLetter g a) (rightWord g x w)

lemma oneValue_rightAux (g : ℕ → Aˣ) (x : ℕ → A) (w cur : Word) :
    oneValue g x (rightAux cur w)=adjoint (evalWord g cur) (rightWord g x w) := by
  induction w generalizing cur with
  | nil => simp [rightAux,rightWord]
  | cons a w ih =>
    simp only [rightAux,oneValue_cons,ih,eval_wm,adjoint_mul,rightWord,adjoint_add]
    rcases a with ⟨i,b⟩
    cases b <;> simp [rightLetter,evalLetter,eval_wm,adjoint_mul,adjoint_neg,
      show evalWord g [(i,false)]=(g i)⁻¹ by simp [evalWord,evalLetter],
      show evalWord g [(i,true)]=g i by simp [evalWord,evalLetter]]

lemma oneValue_right (g : ℕ → Aˣ) (x : ℕ → A) (w : Word) :
    oneValue g x (right w)=rightWord g x w := by
  simpa [right,evalWord] using oneValue_rightAux g x w []
lemma oneValue_left (g : ℕ → Aˣ) (x : ℕ → A) (w : Word) :
    oneValue g x (left w)=adjoint ((evalWord g w)⁻¹) (rightWord g x w) := by
  rw [left,oneValue_ad,eval_wi,oneValue_right]

def curveLetter (c : ℕ → ℝ → A) (a : Letter) (t : ℝ) : A :=
  if a.2 then c a.1 t else (c a.1 t)⁻¹
def curveWord (c : ℕ → ℝ → A) (w : Word) (t : ℝ) : A :=
  ((w.map fun a => curveLetter c a t)).prod

lemma curveWord_at (c : ℕ → ℝ → A) (g : ℕ → Aˣ) (t : ℝ)
    (hc : ∀ i, c i t = (g i : A)) (w : Word) :
    curveWord c w t=(evalWord g w : Aˣ) := by
  induction w with
  | nil => simp [curveWord,evalWord]
  | cons a w ih =>
    rcases a with ⟨i,b⟩
    cases b <;> simp_all [curveWord,evalWord,curveLetter,evalLetter]

/-! ## Non-vacuity -/
example (g : ℕ → Aˣ) (x : ℕ → A) : oneValue g x (right [(0,true)])=x 0 := by
  simp [oneValue_right,rightWord,rightLetter]
end Algebra

section Analytic
variable [NormedDivisionRing A] [NormedAlgebra ℝ A]

lemma curveLetter_derivative (c : ℕ → ℝ → A) (g : ℕ → Aˣ) (x : ℕ → A) (t : ℝ)
    (hc : ∀ i, c i t = (g i : A))
    (hd : ∀ i, HasDerivAt (c i) (x i * (g i : A)) t) (a : Letter) :
    HasDerivAt (curveLetter c a)
      (rightLetter g x a*(evalLetter g a : Aˣ)) t := by
  rcases a with ⟨i,b⟩
  cases b
  · have hn : c i t ≠ 0 := hc i ▸ (g i).ne_zero
    have h := (hasFDerivAt_inv' (𝕜:=ℝ) hn).comp_hasDerivAt t (hd i)
    change HasDerivAt (fun t => (c i t)⁻¹) _ t
    convert h using 1
    · rfl
    · simp [rightLetter,evalLetter,adjoint,hc,mul_assoc]
  · change HasDerivAt (c i) _ t
    simpa [rightLetter,evalLetter] using hd i

lemma curveWord_derivative (c : ℕ → ℝ → A) (g : ℕ → Aˣ) (x : ℕ → A) (t : ℝ)
    (hc : ∀ i, c i t = (g i : A))
    (hd : ∀ i, HasDerivAt (c i) (x i * (g i : A)) t) (w : Word) :
    HasDerivAt (curveWord c w) (oneValue g x (right w)*(evalWord g w : Aˣ)) t := by
  rw [oneValue_right]
  induction w with
  | nil =>
    change HasDerivAt (fun _ => (1 : A)) (0*_) t
    simpa only [zero_mul] using hasDerivAt_const t (1 : A)
  | cons a w ih =>
    have h := (curveLetter_derivative c g x t hc hd a).mul ih
    have ha : curveLetter c a t=(evalLetter g a : Aˣ) := by
      rcases a with ⟨i,b⟩
      cases b <;> simp [curveLetter,evalLetter,hc]
    convert h using 1
    · funext r
      rfl
    · simp [rightWord,evalWord,curveWord_at c g t hc,ha,adjoint,mul_assoc,add_mul]

end Analytic
end Artform.Scores.NonabelianGravity.Maurer
